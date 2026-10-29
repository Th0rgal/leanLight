import LeanLight.Anchor
import LeanLight.El.Trie
import LeanLight.El.Typed
import LeanLight.El.History

/-!
# Inclusion and receipts: the verdict (G12, LC8)

`docs/spec-16-light-client.md`, "Inclusion and receipts": a transaction the wallet sent, its receipt
naming block `N` and index `i`, is proved included under a proving EL block `A` (the anchor's, or
the finalized one's: `LeanLight.Included`):

1. `N`'s hash `hN`: `A`'s own when `N = A`; else read from the EIP-2935 history contract under
   `A`'s state root (`History.blockHash`), which holds it only when `A - 8191 ≤ N < A`
   (`History.inWindow`): older is `tooOld`, newer `ahead`;
2. `N`'s header: Keccak-256 of its RLP is `hN`, it is a known fork's header
   (`Spec.Header.verifyB`, 14b) and its number is `N`;
3. its transactions and receipts, as netd re-encodes them (`Typed.items`, each list below
   4 GiB): as many receipts as transactions (**the body's shape**);
4. both tries rebuilt (`Trie.orderedRoot`) to the header's `transactionsRoot` (field 4), then
   `receiptsRoot` (field 5);
5. only then the transaction whose Keccak-256 is `h`: at the index hint `i`, or, when the hint
   is wrong, the first one that has it (its index is the verdict's); none is `notInBlock`;
6. it is a known envelope (`Typed.txType`), and its receipt one of the same type with a status
   (`Typed.receipt`).

The order is D36's: the lists are checked against both roots before the hash is looked up, so
`notInBlock`, `transaction` and `receipt` say what the proved block holds, and the job settles on
them without asking again (`LeanLight.PlanIncl`); a refusal before both roots matched (`hashProof`,
`header`, `body`, `transactionsRoot`, `receiptsRoot`) may be the endpoint's, and is asked again.
Steps 2 to 6 are `settle`, which reads nothing of the anchor: `verdict` is step 1, the window,
then `settle` at `hN` with the anchor's finality (`LeanLightProofs.Inclusion.verdict_eq_settle`).

The verdict is `proved` with the index, the receipt's status and whether `A` is finalized: a
verdict at a non-final anchor is proved again once `N` is final. `tooLarge` is the caller's:
netd found the block or its receipts larger than it fetches (`MAX_BLOCK_BODY`), and the verdict
says so only for a header proved to be `N`'s. Every other failure is `refused`, with the first
check that failed. `LeanLightProofs.Inclusion` proves what `proved` implies (`verdict_proved`, 25l)
and what `notInBlock` does (`verdict_notInBlock`).

Cost: two tries, about the block's bytes hashed once each, and one transaction hashed (all of
them when the hint is wrong).
-/

namespace LeanLight.Lc.Inclusion

open LeanLight.Spec.RlpDecode (Span)

/-- Bytes as lists, as the EL readers keep them. -/
abbrev Bytes := List UInt8

/-- The anchored EL block: its hash, its state root, its number, and whether it is finalized. -/
structure Anchor where
  hash : Bytes
  stateRoot : Bytes
  number : Nat
  final : Bool
deriving DecidableEq, Repr

/-- How block `N`'s hash is proved: `N` is the anchor, or by the history contract's account and
storage proofs (`eth_getProof(HISTORY_STORAGE_ADDRESS, [N mod 8191], A)`). -/
inductive HashProof where
  | anchor
  | history (accountProof storageProof : ByteArray)

/-- What G12 asks: a transaction's hash, the block number and the index its receipt gave. -/
structure Ask where
  txHash : Bytes
  number : Nat
  index : Nat
deriving DecidableEq, Repr

/-- The first check a refused verdict failed. The constructors' order is the wire's (lcproto's
refusal codes 1 to 8, `Wire.refusedHashProof` to `Wire.refusedReceiptsRoot`), not the checks':
the checks run in D36's order (module doc). -/
inductive Refusal where
  /-- `N`'s hash is not proved under the anchor. -/
  | hashProof
  /-- The header is not `N`'s: not its hash, no known fork, or another number. -/
  | header
  /-- The lists are not lists of envelopes, or differ in length. -/
  | body
  /-- No transaction of the block has the hash. -/
  | notInBlock
  /-- The transaction is no known envelope. -/
  | transaction
  /-- The receipt is no known envelope, or not of the transaction's type. -/
  | receipt
  /-- The transactions do not rebuild the header's `transactionsRoot`. -/
  | transactionsRoot
  /-- The receipts do not rebuild the header's `receiptsRoot`. -/
  | receiptsRoot
deriving DecidableEq, Repr

/-- G12's verdict. -/
inductive Verdict where
  /-- Included at `index` of block `N`, its receipt's status `success`; `final` when the anchor
  is finalized. -/
  | proved (index : Nat) (success : Bool) (final : Bool)
  /-- `N` is newer than the anchor: not yet. -/
  | ahead
  /-- `N` is more than 8191 blocks older than the anchor: not provable. -/
  | tooOld
  /-- The block, or its receipts, is larger than netd fetches: not provable, the caller's. -/
  | tooLarge
  /-- A check failed. -/
  | refused (why : Refusal)
deriving DecidableEq, Repr

/-- The block hash a `HashProof` proves for block `n` under the anchor `a`, in its window. -/
def hashOf (a : Anchor) (n : Nat) : HashProof → Option Bytes
  | .anchor => if n = a.number then some a.hash else none
  | .history ap sp =>
    if n = a.number then some a.hash
    else if History.inWindow a.number n then History.blockHash a.stateRoot ap sp n
    else none

/-- The payload of item `s` of `bs`, as a list. -/
def payload (bs : ByteArray) (s : Span) : Bytes := Trie.valueOf bs s |>.data.toList

/-- The index of the transaction whose hash is `h`: the hint when it has it, else the first. -/
def indexOf (bs : ByteArray) (txs : List Span) (h : Bytes) (hint : Nat) : Option Nat :=
  let hashAt (s : Span) := Spec.Header.keccakB (Trie.valueOf bs s)
  match txs[hint]? with
  | some s => if hashAt s = h then some hint else
      (txs.zipIdx.find? fun si => hashAt si.1 = h).map (·.2)
  | none => (txs.zipIdx.find? fun si => hashAt si.1 = h).map (·.2)

/-- Whether a refusal comes before both roots matched: the history proof, the header, the
lists' shape and the two roots. The endpoint may have sent wrong bytes, so the job asks again
(`LeanLight.PlanIncl`); after the roots matched, the proved block itself says so. -/
def Refusal.beforeRoots : Refusal → Bool
  | .hashProof | .header | .body | .transactionsRoot | .receiptsRoot => true
  | .notInBlock | .transaction | .receipt => false

/-- A verdict at an anchor of finality `fin`: a proved verdict's `final` set, any other kept. -/
def Verdict.atFinal (fin : Bool) : Verdict → Verdict
  | .proved j ok _ => .proved j ok fin
  | v => v

/-- **What block `N` says** of the transaction `q.txHash`, `N`'s hash proved to be `hN`: `header`
is `N`'s header's RLP, `body` its transactions' and its receipts' lists (`none`: too large to
fetch). D36's order: the header, the body's shape, the transactions root, the receipts root, then
the hash looked up, then the envelopes. A proved result's `final` is `false`: the anchor's
finality is `verdict`'s (`Verdict.atFinal`). Reads nothing of the anchor. -/
def settle (q : Ask) (hN : Bytes) (header : ByteArray) (body : Option (ByteArray × ByteArray)) :
    Verdict :=
  match Spec.Header.verifyB header hN, Anchor.fieldsB header with
  | some hd, some fs =>
    if hd.number ≠ q.number then .refused .header
    else
      match body with
      | none => .tooLarge
      | some (txb, rcb) =>
        match Typed.items txb, Typed.items rcb with
        | some txs, some rcs =>
          if txs.length ≠ rcs.length ∨ 18446744073709551616 < txs.length ∨
              4294967296 ≤ txb.size ∨ 4294967296 ≤ rcb.size then .refused .body
          else if (Trie.orderedRoot txb txs).map (·.data.toList) ≠
              some (Spec.Header.field fs 4) then .refused .transactionsRoot
          else if (Trie.orderedRoot rcb rcs).map (·.data.toList) ≠
              some (Spec.Header.field fs 5) then .refused .receiptsRoot
          else
            match indexOf txb txs q.txHash q.index with
            | none => .refused .notInBlock
            | some j =>
              match txs[j]?, rcs[j]? with
              | some ts, some rs =>
                match Typed.txType txb ts.start ts.stop, Typed.receipt rcb rs.start rs.stop with
                | none, _ => .refused .transaction
                | some _, none => .refused .receipt
                | some ty, some (ry, ok) =>
                  if ty ≠ ry then .refused .receipt else .proved j ok false
              | _, _ => .refused .notInBlock
        | _, _ => .refused .body
  | _, _ => .refused .header

/-- **G12's verdict** on the transaction `q.txHash` in block `q.number`, under the anchor `a`:
`hp` proves block `N`'s hash, `header` is `N`'s header's RLP, `body` its transactions' and its
receipts' lists (`none`: too large to fetch). `N` newer than the anchor is `ahead`, more than
8191 blocks older `tooOld`; else `N`'s hash as `hp` proves it (`hashOf`), and what block `N`
says at that hash (`settle`), with the anchor's finality. -/
def verdict (a : Anchor) (q : Ask) (hp : HashProof) (header : ByteArray)
    (body : Option (ByteArray × ByteArray)) : Verdict :=
  if a.number < q.number then .ahead
  else if a.number > q.number + History.serveWindow then .tooOld
  else
    match hashOf a q.number hp with
    | none => .refused .hashProof
    | some hN => (settle q hN header body).atFinal a.final

end LeanLight.Lc.Inclusion
