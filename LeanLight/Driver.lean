import LeanLight.Facts
import LeanLight.Codec

/-!
# What a client does with the bytes it fetches

Every decision a client makes about bytes it fetched, and nothing about how or when it fetches
them: start the store from a bootstrap (`start`), feed it an update (`feed`), read an account and
its storage at the store's anchor (`read`), accept code only when it hashes to the proved code hash
(`codeOk`). The command-line client (`LeanLightCli`) calls these and prints only what they return;
which objects it fetches, in what order, and how often it retries are its own, unproved.

`LeanLightProofs.Driver` proves what that buys (`read_sound`): a value `read` returns comes from a
store reached from the checkpoint by `Store.bootstrap` and `Store.receive` alone (`Reaches`),
whatever the client fed it and in whatever order; under the EL header `Anchor.bind` keeps for the
store's anchor; read from the endpoint's proof nodes by the trie's specification. So the unproved
fetch loop can make a read fail or the anchor stale (liveness), never make a value pass that
those checks refuse.
-/

namespace LeanLight.Lc.Driver

open LeanLight.Lc.Forks (Chain)

/-- The store a bootstrap starts, from its bytes and the fork its source named (`tag`), for the
checkpoint `root` at clock `now` (ms): decoded as that fork's `LightClientBootstrap`, then
`Store.bootstrap`. None when it does not decode or the store refuses it. -/
def start (c : Chain) (root : ByteArray) (now : Nat) (tag : Codec.Tag) (bs : ByteArray) :
    Option Store.Store :=
  match Codec.decodeBootstrap Codec.mainnet c tag bs with
  | none => none
  | some b => Store.bootstrap c root now b

/-- An update's bytes of kind `k` through the store at clock `now`: decoded as the fork `tag`
names, then `Store.receive`; the store after and the verdict. Bytes that do not decode leave the
store as it is, with no verdict. -/
def feed (c : Chain) (s : Store.Store) (now : Nat) (k : Codec.Kind) (tag : Codec.Tag)
    (bs : ByteArray) : Store.Store × Option Store.Verdict :=
  match Codec.decodeUpdate Codec.mainnet c k tag bs with
  | none => (s, none)
  | some u =>
    let r := Store.receive c s now u
    (r.1, some r.2)

/-- The store's anchor at clock `now` and the EL header `rlp` bound to it (`Anchor.bind`), if the
store anchors and the header binds. -/
def bindAnchor (c : Chain) (s : Store.Store) (now : Nat) (rlp : ByteArray) :
    Option (Store.Header × Spec.Header.Header) :=
  match Store.anchored c s now with
  | none => none
  | some a => (Anchor.bind c a.header rlp).map fun h => (a.header, h)

/-- The account at `addr` and its storage words at `slots` (each a key and its proof's nodes),
read at the store's anchor at clock `now`: `Facts.storage` under the EL header `rlp` bound to the
anchor's beacon header. With the header. -/
def read (c : Chain) (s : Store.Store) (now : Nat) (rlp : ByteArray) (addr : List UInt8)
    (nodes : ByteArray) (slots : List (List UInt8 × ByteArray)) :
    Option (Spec.Header.Header × Spec.Mpt.Account × List Nat) :=
  match Store.anchored c s now with
  | none => none
  | some a => Facts.storage c a.header rlp addr nodes slots

/-- Whether `code` is the account's: its Keccak-256 is the code hash the proof proved. -/
def codeOk (acct : Spec.Mpt.Account) (code : ByteArray) : Bool :=
  Spec.Common.keccak code.data.toList == acct.codeHash

end LeanLight.Lc.Driver
