import LeanLight.El.Mpt

/-!
# A block's hash under a later state root: EIP-2935 (LC8, G12)

EIP-2935 ("Serve historical block hashes from state", Final, at the pinned EIPs commit
`e858e912ff55370eb8125873455af531e322d9b2`, `EIPS/eip-2935.md`, lines 28-33 and 148-152): at the
start of each block `A`, a system call stores the parent's hash in the storage of the history
contract at `HISTORY_STORAGE_ADDRESS = 0x0000F90827F1C53a10cb7A02335B175320002935`, slot
`(A - 1) mod HISTORY_SERVE_WINDOW`, `HISTORY_SERVE_WINDOW = 8191`. So the state after block `A`,
whose root is `A`'s header's `stateRoot`, holds the hash of every block `N` with
`A - 8191 ≤ N < A` at slot `N mod 8191`, and nothing else there. Amsterdam (EIP-7773's
scheduled list) keeps the contract, its address and its layout: EIP-7928 records its one
storage write in the block access list, EIP-8037 changes the system call's gas limit.

`blockHash` reads that slot from an `eth_getProof` of the contract under an anchored state
root, with `Spec.Mpt`'s account and storage checks: the account must hold the contract's code
(`code`, the EIP's runtime bytecode: its deployment input after the 9-byte constructor
`60538060095f395ff3`), and the value must not be zero (a slot never written). The value is a
storage scalar, its leading zero bytes dropped; `word` gives it back its 32 bytes.
`LeanLightProofs.History` proves what it reads (`blockHash_spec`) and that two proofs reading
different hashes hold a Keccak-256 collision (`blockHash_binding`).
-/

namespace LeanLight.Lc.History

open LeanLight.Spec.Rlp (be)
open LeanLight.Spec.Header (keccak)

/-- Bytes as lists, as the EL readers keep them. -/
abbrev Bytes := List UInt8

/-- `HISTORY_STORAGE_ADDRESS`. -/
def address : Bytes :=
  [0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a, 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53,
   0x20, 0x00, 0x29, 0x35]

/-- `HISTORY_SERVE_WINDOW`. -/
def serveWindow : Nat := 8191

/-- The history contract's runtime code: EIP-2935's deployment input after its constructor. -/
def code : Bytes :=
  [0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0x14, 0x60, 0x46, 0x57, 0x60, 0x20, 0x36, 0x03, 0x60, 0x42,
   0x57, 0x5f, 0x35, 0x60, 0x01, 0x43, 0x03, 0x81, 0x11, 0x60, 0x42, 0x57, 0x61, 0x1f, 0xff, 0x81,
   0x43, 0x03, 0x11, 0x60, 0x42, 0x57, 0x61, 0x1f, 0xff, 0x90, 0x06, 0x54, 0x5f, 0x52, 0x60, 0x20,
   0x5f, 0xf3, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x5f, 0x35, 0x61, 0x1f, 0xff, 0x60, 0x01, 0x43, 0x03,
   0x06, 0x55, 0x00]

/-- A number as a 32-byte big-endian word (below 2^256). -/
def word (x : Nat) : Bytes := List.replicate (32 - (be x).length) 0 ++ be x

/-- The storage slot that holds block `n`'s hash: `n mod 8191`, as a word. -/
def slot (n : Nat) : Bytes := word (n % serveWindow)

/-- Whether the state after block `a` holds block `n`'s hash: `a - 8191 ≤ n < a`. -/
def inWindow (a n : Nat) : Bool := decide (n < a) && decide (a ≤ n + serveWindow)

/-- **Block `n`'s hash under a state root**, as an `eth_getProof` of the history contract with
the slot of `n` proves it: the account holds the contract's code, and the slot a nonzero
value. Whether the state is one that holds `n` (`inWindow`) is the caller's. -/
def blockHash (stateRoot : Bytes) (accountProof storageProof : ByteArray) (n : Nat) :
    Option Bytes :=
  match Spec.Mpt.accountB stateRoot address accountProof with
  | none => none
  | some acct =>
    if acct.codeHash = keccak code then
      match Spec.Mpt.storageB acct.storageRoot (slot n) storageProof with
      | some x => if x = 0 then none else some (word x)
      | none => none
    else none

end LeanLight.Lc.History
