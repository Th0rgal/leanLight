import LeanLight.Bytes
import LeanLight.El.Rlp

/-!
# Transactions and receipts, as a block's lists hold them (LC8, G12)

A block's transactions and receipts are EIP-2718 envelopes: a legacy one is an RLP list, a typed
one its type byte (1 to 4) then an RLP list; the transaction trie and the receipt trie hold
these bytes, and a transaction's hash is their Keccak-256 (EIP-2718; the execution
specification's `encode_transaction`, `get_transaction_hash`, `encode_receipt`, Amsterdam fork
at execution-specs `e1a316a0`). netd re-encodes `eth_getBlockByHash(h, true)` and
`eth_getBlockReceipts(h)` as one RLP list of byte strings each, each string an envelope; the
light client reads them in place (`items`), never trusting the JSON's fields.

`txType` and `receipt` refuse anything that is not one canonical envelope of a known type, each
field of its shape (`txFields`, `receiptOk`). The types are those of the pinned EIPs commit
`e858e91`: 0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844 (as blocks carry it, without blobs),
4 EIP-7702; Amsterdam (EIP-7773's scheduled list) adds no transaction type and no receipt field
(EIP-8037 changes what `cumulative_gas_used` counts, not its shape). A scalar field is canonical
and of at most its type's bytes (U64: 8; U8: 1; U256 and the specification's unbounded `Uint`:
32); an address is 20 bytes; `to` empty (a creation) or 20 bytes, and always 20 from type 3 on.
A receipt is `[status, cumulative_gas_used, bloom, logs]`, its status EIP-658's: `0x01` for
success, the empty string for failure (a pre-Byzantium state root is refused), its bloom 256
bytes, each log `[address, topics (at most four, 32 bytes each), data]`. The nested lists
(access lists, blob hashes, authorizations, logs) are read two levels deep at most, with
`itemsAtB`, in constant stack.

`LeanLightProofs.Typed` proves what an accepted envelope is: its type's byte, then one
canonical RLP list spanning the rest, whose first item, for a receipt, is the status
(`txType_spec`, `receipt_spec`).
-/

namespace LeanLight.Lc.Typed

open LeanLight.Spec.RlpDecode (Span itemAtB itemsAtB)
open LeanLight.Lc.Bytes (byteAt)

/-- A field's shape. -/
inductive Field where
  /-- A canonical scalar of at most `max` bytes. -/
  | scalar (max : Nat)
  /-- `to`: empty (a creation) or an address. -/
  | to
  /-- An address: 20 bytes. -/
  | address
  /-- Any byte string. -/
  | bytes
  /-- An access list: `[[address, [32-byte key, ...]], ...]`. -/
  | accessList
  /-- Blob versioned hashes: `[32 bytes, ...]`. -/
  | hashes
  /-- An authorization list: `[[chain_id, address, nonce, y_parity, r, s], ...]`. -/
  | authList
deriving DecidableEq, Repr

/-- The fields of a transaction of type `t`, in order (the execution specification's
`LegacyTransaction`, `AccessListTransaction`, `FeeMarketTransaction`, `BlobTransaction`,
`SetCodeTransaction`). -/
def txFields : Nat → Option (List Field)
  | 0 => some [.scalar 32, .scalar 32, .scalar 32, .to, .scalar 32, .bytes, .scalar 32,
      .scalar 32, .scalar 32]
  | 1 => some [.scalar 8, .scalar 32, .scalar 32, .scalar 32, .to, .scalar 32, .bytes,
      .accessList, .scalar 32, .scalar 32, .scalar 32]
  | 2 => some [.scalar 8, .scalar 32, .scalar 32, .scalar 32, .scalar 32, .to, .scalar 32,
      .bytes, .accessList, .scalar 32, .scalar 32, .scalar 32]
  | 3 => some [.scalar 8, .scalar 32, .scalar 32, .scalar 32, .scalar 32, .address, .scalar 32,
      .bytes, .accessList, .scalar 32, .hashes, .scalar 32, .scalar 32, .scalar 32]
  | 4 => some [.scalar 8, .scalar 8, .scalar 32, .scalar 32, .scalar 32, .address, .scalar 32,
      .bytes, .accessList, .authList, .scalar 32, .scalar 32, .scalar 32]
  | _ => none

/-- A byte string item of `bs` of exactly `n` bytes. -/
def sized (it : Span) (n : Nat) : Bool := !it.list && it.stop - it.start == n

/-- A byte string item of `bs` that is a canonical scalar of at most `max` bytes. -/
def scalar (bs : ByteArray) (it : Span) (max : Nat) : Bool :=
  !it.list && decide (it.stop - it.start ≤ max) &&
    (it.start == it.stop || byteAt bs it.start != 0)

/-- A list item of `bs` whose items all pass `p`. -/
def listOf (bs : ByteArray) (it : Span) (p : Span → Bool) : Bool :=
  it.list &&
    match itemsAtB bs it.start it.stop with
    | some cs => cs.all p
    | none => false

/-- A list item of `bs` of exactly the items `p` names, in order. -/
def tuple (bs : ByteArray) (it : Span) (p : List Span → Bool) : Bool :=
  it.list &&
    match itemsAtB bs it.start it.stop with
    | some cs => p cs
    | none => false

/-- An access list entry: `[address, [32-byte key, ...]]`. -/
def accessEntry (bs : ByteArray) (it : Span) : Bool :=
  tuple bs it fun
    | [a, ks] => sized a 20 && listOf bs ks (sized · 32)
    | _ => false

/-- An authorization: `[chain_id (U256), address, nonce (U64), y_parity (U8), r, s]`. -/
def authorization (bs : ByteArray) (it : Span) : Bool :=
  tuple bs it fun
    | [c, a, n, y, r, s] => scalar bs c 32 && sized a 20 && scalar bs n 8 && scalar bs y 1 &&
        scalar bs r 32 && scalar bs s 32
    | _ => false

/-- Whether item `it` of `bs` has the shape `f`. -/
def fieldOk (bs : ByteArray) : Field → Span → Bool
  | .scalar max, it => scalar bs it max
  | .to, it => sized it 0 || sized it 20
  | .address, it => sized it 20
  | .bytes, it => !it.list
  | .accessList, it => listOf bs it (accessEntry bs)
  | .hashes, it => listOf bs it (sized · 32)
  | .authList, it => listOf bs it (authorization bs)

/-- Whether the fields `cs` have the shapes `fs`, one for one. -/
def fieldsOk (bs : ByteArray) (fs : List Field) (cs : List Span) : Bool :=
  fs.length == cs.length && (fs.zip cs).all fun fc => fieldOk bs fc.1 fc.2

/-- The type an envelope at `[a, b)` of `bs` announces, and where its RLP list starts: legacy
(type 0) when its first byte starts a list (`0xc0` and above), a type from 1 to 4 when it is
that byte; `none` for any other first byte (EIP-2718's reserved and unknown types). -/
def envelope (bs : ByteArray) (a b : Nat) : Option (Nat × Nat) :=
  if a < b ∧ b ≤ bs.size then
    let t := (byteAt bs a).toNat
    if 0xc0 ≤ t then some (0, a)
    else if 1 ≤ t ∧ t ≤ 4 then some (t, a + 1)
    else none
  else none

/-- The items of the one canonical RLP list spanning `[a, b)` of `bs`. -/
def listAt (bs : ByteArray) (a b : Nat) : Option (List Span) :=
  match itemAtB bs a b with
  | some top => if top.list = true ∧ top.stop = b then itemsAtB bs top.start top.stop else none
  | none => none

/-- **A transaction's type**, when `[a, b)` of `bs` is one canonical envelope of a known type
whose fields have their shapes. -/
def txType (bs : ByteArray) (a b : Nat) : Option Nat :=
  match envelope bs a b with
  | none => none
  | some (t, s) =>
    match listAt bs s b, txFields t with
    | some cs, some fs => if fieldsOk bs fs cs then some t else none
    | _, _ => none

/-- A log: `[address, [topic, ...] (at most four, 32 bytes each), data]`. -/
def log (bs : ByteArray) (it : Span) : Bool :=
  tuple bs it fun
    | [a, ts, d] =>
      sized a 20 && !d.list &&
        tuple bs ts fun tops => decide (tops.length ≤ 4) && tops.all (sized · 32)
    | _ => false

/-- A receipt's fields past its status: `cumulative_gas_used`, a 256-byte bloom, its logs. -/
def receiptRest (bs : ByteArray) : List Span → Bool
  | [g, bloom, logs] => scalar bs g 32 && sized bloom 256 && listOf bs logs (log bs)
  | _ => false

/-- A status (EIP-658): `0x01`, success, or the empty string, failure. -/
def status (bs : ByteArray) (it : Span) : Option Bool :=
  if it.list then none
  else if it.start = it.stop then some false
  else if it.stop - it.start = 1 ∧ byteAt bs it.start = 1 then some true
  else none

/-- **A receipt's type and status**, when `[a, b)` of `bs` is one canonical envelope of a known
type: `[status, cumulative_gas_used, bloom, logs]`. -/
def receipt (bs : ByteArray) (a b : Nat) : Option (Nat × Bool) :=
  match envelope bs a b with
  | none => none
  | some (t, s) =>
    match listAt bs s b with
    | some (st :: rest) =>
      match status bs st with
      | some ok => if receiptRest bs rest then some (t, ok) else none
      | none => none
    | _ => none

/-- The byte strings of a block's list: the one canonical RLP list spanning `bs`, each of its
items a nonempty byte string (an envelope). -/
def items (bs : ByteArray) : Option (List Span) :=
  match listAt bs 0 bs.size with
  | some its => if its.all (fun it => !it.list && decide (it.start < it.stop)) then some its else none
  | none => none

end LeanLight.Lc.Typed
