import LeanLight.Inclusion
import LeanLightProofs.Trie
import LeanLightProofs.Typed
import LeanLightProofs.History

/-!
# What a proved inclusion verdict says (25l, LC8)

About `LeanLight.Inclusion.verdict` and `settle`, the code `lkd-lc` runs (`docs/spec-16-light-client.md`,
"Inclusion and receipts"). `verdict_proved`: a verdict `proved j ok fin` for the transaction hash
`h`, block number `N` and anchor `A` says

* **block `N`'s hash `hN`** is the anchor's own when `N = A`; else `A - 8191 ≤ N < A` and `hN` is
  what EIP-2935's history contract holds for `N` under `A`'s state root, as `Spec.Mpt` proves its
  account (with the contract's code) and its slot `N mod 8191` (`HashProved`);
* **the header** fetched is `N`'s: its Keccak-256 is `hN`, and it is the canonical RLP of a known
  fork's field list whose number is `N` (`HeaderOf`, 14b);
* **the transactions and receipts** fetched are canonical RLP lists of as many nonempty envelopes
  each (`ListOf`); transaction `j`'s Keccak-256 is `h`; transaction `j` is under the header's
  `transactionsRoot` and receipt `j` under its `receiptsRoot` (`UnderRoot`): each root is the
  Yellow Paper's TRIE of the list's ordered map (`Spec.Mpt.Trie.root`, item `i` under `rlp(i)`),
  the model's proof of `rlp(j)` reads the item under it with `Spec.Mpt.lookup`, and any proof that
  reads otherwise holds a Keccak-256 collision;
* transaction `j` is a known type's envelope (`Envelope`), and receipt `j` one of the same type
  whose first field is the status `ok` (`ReceiptSays`, EIP-658);
* `fin` is the anchor's finality.

`verdict_ahead_iff`, `verdict_tooOld_iff` and `verdict_tooLarge` say when the other outcomes are
given: `N` newer than the anchor, more than 8191 blocks older, and no body for a header proved to be
`N`'s. D36's order: `verdict_notInBlock`, the hash not in the block only for a header proved to be
`N`'s whose lists rebuild both of its roots, none of the transactions hashing to `h`;
`verdict_transaction` and `verdict_receipt`, an envelope refused only for such a header and lists,
the transaction `j` hashing to `h`: `Typed.txType` refuses it, or accepts it as a type receipt `j`
is no receipt of. `verdict_eq_settle`: within the window, the verdict is `settle`'s at the hash
`hashOf` proves, with the anchor's finality: the anchor matters only through `hashOf` and `final`,
so a result settled once (`LeanLight.PlanIncl`) is the verdict under any anchor proving the same `hN`.
-/

namespace LeanLight.Lc.Inclusion

open LeanLight.Spec.Rlp
open LeanLight.Spec.RlpDecode (Span window)

/-- How block `n`'s hash `hN` is proved under the anchor `a`: it is the anchor's own (`n` is the
anchor), or `a - 8191 ≤ n < a` and EIP-2935's history contract holds it under `a`'s state root:
its account, holding the contract's code, and its slot for `n`, a nonzero value, as `Spec.Mpt`
proves them from `hp`'s proofs. -/
def HashProved (a : Anchor) (n : Nat) (hp : HashProof) (hN : Bytes) : Prop :=
  (n = a.number ∧ hN = a.hash) ∨
    (n < a.number ∧ a.number ≤ n + History.serveWindow ∧
      ∃ ap sp acct x, hp = .history ap sp ∧
        Spec.Mpt.account a.stateRoot History.address ap.data.toList = some acct ∧
        acct.codeHash = Spec.Header.keccak History.code ∧
        Spec.Mpt.storage acct.storageRoot (History.slot n) sp.data.toList = some x ∧
        x ≠ 0 ∧ hN = History.word x)

/-- An EIP-2718 envelope of type `ty`: its type's byte (none for legacy), then one canonical RLP
list. -/
def Envelope (t : Bytes) (ty : Nat) : Prop :=
  ty ≤ 4 ∧ ∃ e p, t = Typed.typeBytes ty ++ e ∧ encodeList p = some e

/-- A receipt of type `ty` whose status is `ok` (EIP-658): its type's byte, then one canonical RLP
list whose first item is `0x01` (success) or the empty string `0x80` (failure). -/
def ReceiptSays (r : Bytes) (ty : Nat) (ok : Bool) : Prop :=
  ty ≤ 4 ∧ ∃ e p rest, r = Typed.typeBytes ty ++ e ∧ encodeList p = some e ∧
    p = (if ok then [0x01] else [0x80]) ++ rest

/-- The header `header` is `N`'s, as `hd` reads it: the canonical RLP of a known fork's field
list `fs` (`Spec.Header.ofFields`, 14b), whose number is `N`. -/
def HeaderOf (header : ByteArray) (N : Nat) (fs : List Bytes) (hd : Spec.Header.Header) : Prop :=
  encodeTree (.branch (fs.map .leaf)) = some header.data.toList ∧ Spec.Header.ofFields fs = some hd ∧
    hd.number = N

/-- `bs` is the canonical RLP list of the byte strings `items`, each nonempty. -/
def ListOf (bs : ByteArray) (items : List Bytes) : Prop :=
  encodeTree (.branch (items.map .leaf)) = some bs.data.toList ∧ ∀ x ∈ items, x ≠ []

/-- The key of item `j` of an ordered list: `rlp(j)`. -/
abbrev key (j : Nat) : Bytes := (encodeScalar j).getD []

/-- `item` is item `j` of the ordered list `items` under `root`: `root` is the Yellow Paper's
TRIE of the list's ordered map (`Spec.Mpt.Trie.root`), `item` is item `j`, the model's proof of
`rlp(j)` reads it under `root` with `Spec.Mpt.lookup`, and any proof `lookup` accepts for `rlp(j)`
under `root` reads it, or it and the model's proof are two different byte strings with one
Keccak-256. -/
def UnderRoot (root : Bytes) (items : List Bytes) (j : Nat) (item : Bytes) : Prop :=
  Spec.Mpt.Trie.root (Trie.orderedMap items) = root ∧ items[j]? = some item ∧
    Spec.Mpt.lookup root (key j) (Spec.Mpt.Trie.proofOf (Trie.orderedMap items) (key j)) =
      some (.value item) ∧
    ∀ p f, Spec.Mpt.lookup root (key j) p = some f →
      f = .value item ∨ Spec.Mpt.IsCollision (Spec.Mpt.collision root (key j) p
        (Spec.Mpt.Trie.proofOf (Trie.orderedMap items) (key j)))

theorem hashOf_spec {a : Anchor} {n : Nat} {hp : HashProof} {hN : Bytes}
    (h : hashOf a n hp = some hN) : HashProved a n hp hN := by
  unfold hashOf at h
  split at h
  · split at h
    · rename_i he; cases h; exact .inl ⟨he, rfl⟩
    · cases h
  · rename_i ap sp
    split at h
    · rename_i he; cases h; exact .inl ⟨he, rfl⟩
    · rename_i hne
      split at h
      · rename_i hw
        simp only [History.inWindow, Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨acct, x, ha, hc, hs, hx, -, rfl, -⟩ := History.blockHash_spec h
        exact .inr ⟨hw.1, hw.2, ap, sp, acct, x, rfl, ha, hc, hs, hx, rfl⟩
      · cases h

theorem indexOf_spec {bs : ByteArray} {txs : List Span} {h : Bytes} {hint j : Nat}
    (hi : indexOf bs txs h hint = some j) :
    ∃ hj : j < txs.length, Spec.Header.keccakB (Trie.valueOf bs txs[j]) = h := by
  have hfind : ∀ {j}, ((txs.zipIdx.find? fun si =>
      Spec.Header.keccakB (Trie.valueOf bs si.1) = h).map (·.2)) = some j →
      ∃ hj : j < txs.length, Spec.Header.keccakB (Trie.valueOf bs txs[j]) = h := by
    intro j hf
    simp only [Option.map_eq_some_iff] at hf
    obtain ⟨si, hsi, rfl⟩ := hf
    have hm := List.mem_of_find?_eq_some hsi
    have hp := List.find?_some hsi
    simp only [decide_eq_true_eq] at hp
    have hlt := List.snd_lt_of_mem_zipIdx hm
    refine ⟨by simpa using hlt, ?_⟩
    have := List.mem_zipIdx_iff_getElem?.mp hm
    rw [List.getElem?_eq_getElem (by simpa using hlt), Option.some.injEq] at this
    rw [this]; exact hp
  unfold indexOf at hi
  simp only at hi
  split at hi
  · rename_i s hs
    split at hi
    · rename_i he
      cases hi
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hs
      exact ⟨hlt, by rw [heq]; exact he⟩
    · exact hfind hi
  · exact hfind hi

/-- `indexOf` finds nothing only when no item hashes to `h`. -/
theorem indexOf_none {bs : ByteArray} {txs : List Span} {h : Bytes} {hint : Nat}
    (hi : indexOf bs txs h hint = none) :
    ∀ s ∈ txs, Spec.Header.keccakB (Trie.valueOf bs s) ≠ h := by
  have hfind : ((txs.zipIdx.find? fun si =>
      Spec.Header.keccakB (Trie.valueOf bs si.1) = h).map (·.2)) = none →
      ∀ s ∈ txs, Spec.Header.keccakB (Trie.valueOf bs s) ≠ h := by
    intro hf s hs
    simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq] at hf
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
    exact hf (txs[k], k) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
  unfold indexOf at hi
  simp only at hi
  split at hi
  · split at hi
    · cases hi
    · exact hfind hi
  · exact hfind hi

/-- A verdict at a finality: what is not proved is kept as it was. -/
theorem atFinal_of_ne {v w : Verdict} {fin : Bool} (hw : ∀ j ok f, w ≠ .proved j ok f)
    (h : v.atFinal fin = w) : v = w := by
  cases v with
  | proved j ok f => simp only [Verdict.atFinal] at h; exact absurd h.symm (hw _ _ _)
  | ahead => exact h
  | tooOld => exact h
  | tooLarge => exact h
  | refused r => exact h

/-- A proved verdict at a finality is a proved one with that finality. -/
theorem atFinal_eq_proved {v : Verdict} {fin : Bool} {j : Nat} {ok f : Bool}
    (h : v.atFinal fin = .proved j ok f) : (∃ f', v = .proved j ok f') ∧ f = fin := by
  cases v with
  | proved j' ok' f' =>
    simp only [Verdict.atFinal, Verdict.proved.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨⟨f', rfl⟩, rfl⟩
  | ahead => simp [Verdict.atFinal] at h
  | tooOld => simp [Verdict.atFinal] at h
  | tooLarge => simp [Verdict.atFinal] at h
  | refused r => simp [Verdict.atFinal] at h

/-- `settle` is never `ahead` nor `tooOld`, and proves with `final` false. -/
theorem settle_ne {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} {v : Verdict} (h : settle q hN header body = v) :
    v ≠ .ahead ∧ v ≠ .tooOld ∧ ∀ j ok f, v = .proved j ok f → f = false := by
  unfold settle at h
  repeat' split at h
  all_goals
    subst h
    refine ⟨by simp, by simp, ?_⟩
    intro j ok f hv
    simp_all

/-- What the header's checks give: Keccak-256 of the RLP is `hN`, the RLP is the canonical
encoding of the field list `fs`, and `hd` is what `ofFields` reads of it. -/
theorem header_facts {header : ByteArray} {hN : Bytes} {hd : Spec.Header.Header}
    {fs : List Bytes} (hv : Spec.Header.verifyB header hN = some hd)
    (hfs : Anchor.fieldsB header = some fs) :
    Spec.Common.keccak header.data.toList = hN ∧
      encodeTree (.branch (fs.map .leaf)) = some header.data.toList ∧
      Spec.Header.ofFields fs = some hd := by
  rw [Spec.Header.verifyB_eq] at hv
  unfold Spec.Header.verify at hv
  split at hv
  rotate_left
  · cases hv
  rename_i hk
  rw [Anchor.decode_fieldsL, ← Anchor.fieldsB_eq, hfs, Option.bind_some] at hv
  exact ⟨hk, Anchor.fieldsL_encode (by rw [← Anchor.fieldsB_eq]; exact hfs), hv⟩

/-- A list `Typed.items` reads is the canonical list of its items' payloads, each nonempty. -/
theorem items_listOf {bs : ByteArray} {its : List Span} (h : Typed.items bs = some its) :
    ListOf bs (its.map fun s => (Trie.valueOf bs s).data.toList) := by
  obtain ⟨he, hn⟩ := Typed.items_spec h
  exact ⟨he, fun x hx => by obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx; exact hn s hs⟩

/-- **What a proved `settle` says**, with no anchor: the header hashes to `hN` and is `N`'s, the
body is the canonical lists, transaction `j` hashes to `q.txHash`, both are item `j` under the
header's roots, and they are envelopes of one type, the receipt's status `ok`. -/
theorem settle_proved {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} {j : Nat} {ok fin : Bool}
    (h : settle q hN header body = .proved j ok fin) :
    fin = false ∧
    ∃ fs hd txb rcb txs rcs tx rc ty,
      Spec.Common.keccak header.data.toList = hN ∧
      HeaderOf header q.number fs hd ∧ body = some (txb, rcb) ∧ ListOf txb txs ∧ ListOf rcb rcs ∧
      txs.length = rcs.length ∧ Spec.Common.keccak tx = q.txHash ∧
      UnderRoot (Spec.Header.field fs 4) txs j tx ∧ UnderRoot (Spec.Header.field fs 5) rcs j rc ∧
      Envelope tx ty ∧ ReceiptSays rc ty ok := by
  unfold settle at h
  split at h
  rotate_left
  · cases h
  rename_i hd fs hv hfs
  split at h
  · cases h
  rename_i hnum
  split at h
  · cases h
  rename_i txb rcb
  split at h
  rotate_left
  · cases h
  rename_i txs rcs htxs hrcs
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i htr
  split at h
  · cases h
  rename_i hrr
  split at h
  · cases h
  rename_i j' hidx
  split at h
  rotate_left
  · cases h
  rename_i ts rs hts hrs
  split at h
  · cases h
  · cases h
  rename_i ty ry ok' hty hrc
  split at h
  · cases h
  rename_i hty_eq
  cases h
  obtain ⟨hk, henc, hv⟩ := header_facts hv hfs
  simp only [ne_eq, not_or, Decidable.not_not, Nat.not_lt] at hlen
  obtain ⟨hlen, hbig, htx32, hrc32⟩ := hlen
  obtain ⟨hj, hhj⟩ := indexOf_spec hidx
  have hj' : j < rcs.length := by omega
  obtain ⟨hjt, hts'⟩ := List.getElem?_eq_some_iff.mp hts
  obtain ⟨hjr, hrs'⟩ := List.getElem?_eq_some_iff.mp hrs
  subst hts' hrs'
  simp only [ne_eq, Decidable.not_not] at hty_eq htr hrr hnum
  subst hty_eq
  have hsz : ∀ (b : ByteArray) (s : Span), (Trie.valueOf b s).size ≤ b.size := by
    intro b s
    simp only [Trie.valueOf, Bytes.extract, ByteArray.size_extract]
    omega
  have htxn := (Typed.items_spec htxs).2
  have hrcn := (Typed.items_spec hrcs).2
  have hv₁ : ∀ s ∈ txs, (Trie.valueOf txb s).size ≠ 0 ∧ (Trie.valueOf txb s).size < 2 ^ 32 := by
    intro s hs
    refine ⟨fun h0 => htxn s hs (List.eq_nil_of_length_eq_zero (by simp [h0])), ?_⟩
    have := hsz txb s; omega
  have hv₂ : ∀ s ∈ rcs, (Trie.valueOf rcb s).size ≠ 0 ∧ (Trie.valueOf rcb s).size < 2 ^ 32 := by
    intro s hs
    refine ⟨fun h0 => hrcn s hs (List.eq_nil_of_length_eq_zero (by simp [h0])), ?_⟩
    have := hsz rcb s; omega
  have hwin : ∀ (b : ByteArray) (s : Span),
      (Trie.valueOf b s).data.toList = window b.data.toList s.start s.stop :=
    fun b s => Bytes.extract_eq b s.start s.stop
  obtain ⟨hty4, -, ttop, tfs, tcs, htw, htenc, -, -, -⟩ := Typed.txType_spec hty
  obtain ⟨hry4, -, rtop, rest, hrw, hrenc, hrst⟩ := Typed.receipt_spec hrc
  cases htrr : Trie.orderedRoot txb txs with
  | none => rw [htrr] at htr; cases htr
  | some tr =>
  cases hrcr : Trie.orderedRoot rcb rcs with
  | none => rw [hrcr] at hrr; cases hrr
  | some rr =>
  rw [htrr, Option.map_some, Option.some.injEq] at htr
  rw [hrcr, Option.map_some, Option.some.injEq] at hrr
  have under : ∀ (b : ByteArray) (items : List Span) (r : ByteArray) (field : Bytes),
      (∀ s ∈ items, (Trie.valueOf b s).size ≠ 0 ∧ (Trie.valueOf b s).size < 2 ^ 32) →
      items.length ≤ 2 ^ 64 → Trie.orderedRoot b items = some r → r.data.toList = field →
      (hj : j < items.length) →
      UnderRoot field (items.map fun s => (Trie.valueOf b s).data.toList) j
        (Trie.valueOf b items[j]).data.toList := by
    intro b items r field hv hn hr hf hj
    subst hf
    refine ⟨(Trie.orderedRoot_eq hr).symm, by simp [hj], Trie.orderedRoot_lookupB hv hn hr hj,
      fun p f hp => Trie.orderedRoot_soundB hv hn hr hj hp⟩
  refine ⟨rfl, fs, hd, txb, rcb, txs.map fun s => (Trie.valueOf txb s).data.toList,
    rcs.map fun s => (Trie.valueOf rcb s).data.toList, (Trie.valueOf txb txs[j]).data.toList,
    (Trie.valueOf rcb rcs[j]).data.toList, ty, hk, ⟨henc, hv, hnum⟩, rfl,
    items_listOf htxs, items_listOf hrcs, by simp [hlen], ?_,
    under txb txs tr _ hv₁ (by simpa using hbig) htrr htr hj,
    under rcb rcs rr _ hv₂ (by omega) hrcr hrr hj', ⟨hty4, _, _, ?_, htenc⟩,
    ⟨hry4, _, _, rest, ?_, hrenc, hrst⟩⟩
  · simpa [Spec.Header.keccakB_eq] using hhj
  · rw [hwin]; exact htw
  · rw [hwin]; exact hrw

/-- `hashOf` gives a hash only within the anchor's window: `N` its own block, or one of the 8191
before it. -/
theorem hashOf_window {a : Anchor} {n : Nat} {hp : HashProof} {hN : Bytes}
    (h : hashOf a n hp = some hN) : n ≤ a.number ∧ a.number ≤ n + History.serveWindow := by
  rcases hashOf_spec h with ⟨rfl, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  · exact ⟨Nat.le_of_lt h1, h2⟩

/-- **`verdict` is `settle` at the hash the anchor proves** (D36): when the anchor proves block
`N`'s hash `hN` (`hashOf`, which gives one only within its window), the verdict is `settle`'s at
`hN` with the anchor's finality. The anchor is read only through `hashOf` and `final`: a result
`settle` gave once is the verdict under any anchor proving the same `hN`. -/
theorem verdict_eq_settle {a : Anchor} {q : Ask} {hp : HashProof} {hN : Bytes}
    (h : hashOf a q.number hp = some hN) (header : ByteArray)
    (body : Option (ByteArray × ByteArray)) :
    verdict a q hp header body = (settle q hN header body).atFinal a.final := by
  obtain ⟨h1, h2⟩ := hashOf_window h
  unfold verdict
  rw [if_neg (by omega), if_neg (by omega), h]

/-- **25l: what a proved verdict says.** A verdict `proved j ok fin` on the transaction hash
`q.txHash` in block `q.number` under the anchor `a`: `fin` is the anchor's finality; some `hN` is
block `N`'s hash as `HashProved` says and the Keccak-256 of the header fetched, which is `N`'s
(`HeaderOf`); the body fetched is the transactions' and the receipts' canonical lists
(`ListOf`), as many of each; transaction `j` hashes to `q.txHash` and is item `j` under the
header's `transactionsRoot` (field 4), receipt `j` item `j` under its `receiptsRoot` (field 5)
(`UnderRoot`), and they are envelopes of one type, the receipt's status `ok` (`Envelope`,
`ReceiptSays`). Short of a Keccak-256 collision, which `UnderRoot` and `HashProved`'s proofs
name, nothing else is under those roots at `rlp(j)`. -/
theorem verdict_proved {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} {j : Nat} {ok fin : Bool}
    (h : verdict a q hp header body = .proved j ok fin) :
    fin = a.final ∧
    ∃ hN fs hd txb rcb txs rcs tx rc ty,
      HashProved a q.number hp hN ∧ Spec.Common.keccak header.data.toList = hN ∧
      HeaderOf header q.number fs hd ∧ body = some (txb, rcb) ∧ ListOf txb txs ∧ ListOf rcb rcs ∧
      txs.length = rcs.length ∧ Spec.Common.keccak tx = q.txHash ∧
      UnderRoot (Spec.Header.field fs 4) txs j tx ∧ UnderRoot (Spec.Header.field fs 5) rcs j rc ∧
      Envelope tx ty ∧ ReceiptSays rc ty ok := by
  unfold verdict at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hN hhash
  obtain ⟨⟨f', hs⟩, rfl⟩ := atFinal_eq_proved h
  obtain ⟨-, fs, hd, txb, rcb, txs, rcs, tx, rc, ty, hk, hof, hb, ht, hr, hl, hh, hut, hur, he,
    hrs⟩ := settle_proved hs
  exact ⟨rfl, hN, fs, hd, txb, rcb, txs, rcs, tx, rc, ty, hashOf_spec hhash, hk, hof, hb, ht, hr,
    hl, hh, hut, hur, he, hrs⟩

/-- The anchor's part of a verdict, once in the window: `settle`'s, never `ahead` nor `tooOld`. -/
theorem verdict_window {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} :
    (match hashOf a q.number hp with
      | none => Verdict.refused .hashProof
      | some hN => (settle q hN header body).atFinal a.final) ≠ .ahead ∧
    (match hashOf a q.number hp with
      | none => Verdict.refused .hashProof
      | some hN => (settle q hN header body).atFinal a.final) ≠ .tooOld := by
  split
  · exact ⟨by simp, by simp⟩
  · rename_i hN _
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact (settle_ne (atFinal_of_ne (by simp) h)).1 rfl
    · exact (settle_ne (atFinal_of_ne (by simp) h)).2.1 rfl

/-- `ahead` exactly when `N` is newer than the anchor. -/
theorem verdict_ahead_iff {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} :
    verdict a q hp header body = .ahead ↔ a.number < q.number := by
  constructor
  · intro h
    unfold verdict at h
    split at h
    · assumption
    · split at h
      · cases h
      · exact absurd h verdict_window.1
  · intro h
    unfold verdict
    rw [ite_eq_left h]

/-- `tooOld` exactly when `N` is more than 8191 blocks before the anchor. -/
theorem verdict_tooOld_iff {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} :
    verdict a q hp header body = .tooOld ↔ q.number + History.serveWindow < a.number := by
  constructor
  · intro h
    unfold verdict at h
    split at h
    · cases h
    · split at h
      · assumption
      · exact absurd h verdict_window.2
  · intro h
    unfold verdict
    rw [ite_eq_right (by omega), ite_eq_left h]

/-- What `settle` says when the body is too large: no body, and a header proved to be `N`'s. -/
theorem settle_tooLarge {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} (h : settle q hN header body = .tooLarge) :
    body = none ∧ Spec.Common.keccak header.data.toList = hN ∧
      ∃ fs hd, encodeTree (.branch (fs.map .leaf)) = some header.data.toList ∧
        Spec.Header.ofFields fs = some hd ∧ hd.number = q.number := by
  unfold settle at h
  split at h
  rotate_left
  · cases h
  rename_i hd fs hv hfs
  split at h
  · cases h
  rename_i hnum
  split at h
  · obtain ⟨hk, henc, hv⟩ := header_facts hv hfs
    simp only [ne_eq, Decidable.not_not] at hnum
    exact ⟨rfl, hk, fs, hd, henc, hv, hnum⟩
  · repeat (split at h <;> try cases h)

/-- `tooLarge` only for a header proved to be block `N`'s, when netd fetched no body. -/
theorem verdict_tooLarge {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} (h : verdict a q hp header body = .tooLarge) :
    body = none ∧ ∃ hN, HashProved a q.number hp hN ∧ Spec.Common.keccak header.data.toList = hN ∧
      ∃ fs hd, encodeTree (.branch (fs.map .leaf)) = some header.data.toList ∧
        Spec.Header.ofFields fs = some hd ∧ hd.number = q.number := by
  unfold verdict at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hN hhash
  obtain ⟨hb, hk, rest⟩ := settle_tooLarge (atFinal_of_ne (by simp) h)
  exact ⟨hb, hN, hashOf_spec hhash, hk, rest⟩

/-- What `settle` says of a hash not in the block (D36): the header is `N`'s at `hN`, the body is
the canonical lists, as many of each, which rebuild both of the header's roots, and no
transaction of the list hashes to `q.txHash`. -/
theorem settle_notInBlock {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} (h : settle q hN header body = .refused .notInBlock) :
    ∃ fs hd txb rcb txs rcs,
      Spec.Common.keccak header.data.toList = hN ∧ HeaderOf header q.number fs hd ∧
      body = some (txb, rcb) ∧ ListOf txb txs ∧ ListOf rcb rcs ∧ txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap txs) = Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap rcs) = Spec.Header.field fs 5 ∧
      ∀ tx ∈ txs, Spec.Common.keccak tx ≠ q.txHash := by
  unfold settle at h
  split at h
  rotate_left
  · cases h
  rename_i hd fs hv hfs
  split at h
  · cases h
  rename_i hnum
  split at h
  · cases h
  rename_i txb rcb
  split at h
  rotate_left
  · cases h
  rename_i txs rcs htxs hrcs
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i htr
  split at h
  · cases h
  rename_i hrr
  obtain ⟨hk, henc, hv⟩ := header_facts hv hfs
  simp only [ne_eq, not_or, Decidable.not_not, Nat.not_lt] at hlen
  obtain ⟨hlen, -, -, -⟩ := hlen
  simp only [ne_eq, Decidable.not_not] at htr hrr hnum
  cases htrr : Trie.orderedRoot txb txs with
  | none => rw [htrr] at htr; cases htr
  | some tr =>
  cases hrcr : Trie.orderedRoot rcb rcs with
  | none => rw [hrcr] at hrr; cases hrr
  | some rr =>
  rw [htrr, Option.map_some, Option.some.injEq] at htr
  rw [hrcr, Option.map_some, Option.some.injEq] at hrr
  have hnone : ∀ tx ∈ txs.map fun s => (Trie.valueOf txb s).data.toList,
      Spec.Common.keccak tx ≠ q.txHash := by
    split at h
    · rename_i hidx
      intro tx htx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htx
      have := indexOf_none hidx s hs
      simpa [Spec.Header.keccakB_eq] using this
    · rename_i j' hidx
      obtain ⟨hj, -⟩ := indexOf_spec hidx
      split at h
      · repeat (split at h <;> try cases h)
      · rename_i hne
        exfalso
        have hj' : j' < rcs.length := by omega
        exact hne _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')
  refine ⟨fs, hd, txb, rcb, txs.map fun s => (Trie.valueOf txb s).data.toList,
    rcs.map fun s => (Trie.valueOf rcb s).data.toList, hk, ⟨henc, hv, hnum⟩, rfl,
    items_listOf htxs, items_listOf hrcs, by simp [hlen], ?_, ?_, hnone⟩
  · rw [← Trie.orderedRoot_eq htrr, htr]
  · rw [← Trie.orderedRoot_eq hrcr, hrr]

/-- What `settle` says of a transaction of no known type (D36): the header is `N`'s at `hN`, the
body is the canonical lists, as many of each, which rebuild both of the header's roots, and
transaction `j` of the list, which hashes to `q.txHash`, is one `Typed.txType` refuses. -/
theorem settle_transaction {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} (h : settle q hN header body = .refused .transaction) :
    ∃ fs hd txb rcb, ∃ txs rcs : List Span,
      Spec.Common.keccak header.data.toList = hN ∧ HeaderOf header q.number fs hd ∧
      body = some (txb, rcb) ∧ ListOf txb (txs.map fun s => (Trie.valueOf txb s).data.toList) ∧
      ListOf rcb (rcs.map fun s => (Trie.valueOf rcb s).data.toList) ∧ txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (txs.map fun s => (Trie.valueOf txb s).data.toList)) =
        Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (rcs.map fun s => (Trie.valueOf rcb s).data.toList)) =
        Spec.Header.field fs 5 ∧
      ∃ j, ∃ hj : j < txs.length,
        Spec.Common.keccak (Trie.valueOf txb txs[j]).data.toList = q.txHash ∧
        Typed.txType txb txs[j].start txs[j].stop = none := by
  unfold settle at h
  split at h
  rotate_left
  · cases h
  rename_i hd fs hv hfs
  split at h
  · cases h
  rename_i hnum
  split at h
  · cases h
  rename_i txb rcb
  split at h
  rotate_left
  · cases h
  rename_i txs rcs htxs hrcs
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i htr
  split at h
  · cases h
  rename_i hrr
  split at h
  · cases h
  rename_i j hidx
  split at h
  rotate_left
  · cases h
  rename_i ts rs hts hrs
  split at h
  rotate_left
  · cases h
  · split at h <;> cases h
  rename_i hty
  obtain ⟨hk, henc, hv⟩ := header_facts hv hfs
  simp only [ne_eq, not_or, Decidable.not_not, Nat.not_lt] at hlen
  obtain ⟨hlen, -, -, -⟩ := hlen
  simp only [ne_eq, Decidable.not_not] at htr hrr hnum
  obtain ⟨hj, hhj⟩ := indexOf_spec hidx
  obtain ⟨hjt, hts'⟩ := List.getElem?_eq_some_iff.mp hts
  subst hts'
  cases htrr : Trie.orderedRoot txb txs with
  | none => rw [htrr] at htr; cases htr
  | some tr =>
  cases hrcr : Trie.orderedRoot rcb rcs with
  | none => rw [hrcr] at hrr; cases hrr
  | some rr =>
  rw [htrr, Option.map_some, Option.some.injEq] at htr
  rw [hrcr, Option.map_some, Option.some.injEq] at hrr
  refine ⟨fs, hd, txb, rcb, txs, rcs, hk, ⟨henc, hv, hnum⟩, rfl, items_listOf htxs,
    items_listOf hrcs, hlen, ?_, ?_, j, hj, ?_, hty⟩
  · rw [← Trie.orderedRoot_eq htrr, htr]
  · rw [← Trie.orderedRoot_eq hrcr, hrr]
  · simpa [Spec.Header.keccakB_eq] using hhj

/-- What `settle` says of a receipt that is not the transaction's (D36): the header is `N`'s at
`hN`, the body is the canonical lists, as many of each, which rebuild both of the header's roots,
and transaction `j` of the list, which hashes to `q.txHash`, is an envelope of a type `ty`
`Typed.txType` accepts, while receipt `j` is no receipt of type `ty` with a status
(`Typed.receipt`: none, or one of another type). -/
theorem settle_receipt {q : Ask} {hN : Bytes} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)} (h : settle q hN header body = .refused .receipt) :
    ∃ fs hd txb rcb, ∃ txs rcs : List Span,
      Spec.Common.keccak header.data.toList = hN ∧ HeaderOf header q.number fs hd ∧
      body = some (txb, rcb) ∧ ListOf txb (txs.map fun s => (Trie.valueOf txb s).data.toList) ∧
      ListOf rcb (rcs.map fun s => (Trie.valueOf rcb s).data.toList) ∧ txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (txs.map fun s => (Trie.valueOf txb s).data.toList)) =
        Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (rcs.map fun s => (Trie.valueOf rcb s).data.toList)) =
        Spec.Header.field fs 5 ∧
      ∃ j, ∃ hj : j < txs.length, ∃ hj' : j < rcs.length,
        Spec.Common.keccak (Trie.valueOf txb txs[j]).data.toList = q.txHash ∧
        ∃ ty, Typed.txType txb txs[j].start txs[j].stop = some ty ∧
          ∀ ok, Typed.receipt rcb rcs[j].start rcs[j].stop ≠ some (ty, ok) := by
  unfold settle at h
  split at h
  rotate_left
  · cases h
  rename_i hd fs hv hfs
  split at h
  · cases h
  rename_i hnum
  split at h
  · cases h
  rename_i txb rcb
  split at h
  rotate_left
  · cases h
  rename_i txs rcs htxs hrcs
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i htr
  split at h
  · cases h
  rename_i hrr
  split at h
  · cases h
  rename_i j hidx
  split at h
  rotate_left
  · cases h
  rename_i ts rs hts hrs
  obtain ⟨hk, henc, hv⟩ := header_facts hv hfs
  simp only [ne_eq, not_or, Decidable.not_not, Nat.not_lt] at hlen
  obtain ⟨hlen, -, -, -⟩ := hlen
  simp only [ne_eq, Decidable.not_not] at htr hrr hnum
  obtain ⟨hj, hhj⟩ := indexOf_spec hidx
  obtain ⟨hj', hrs'⟩ := List.getElem?_eq_some_iff.mp hrs
  obtain ⟨hjt, hts'⟩ := List.getElem?_eq_some_iff.mp hts
  subst hts' hrs'
  cases htrr : Trie.orderedRoot txb txs with
  | none => rw [htrr] at htr; cases htr
  | some tr =>
  cases hrcr : Trie.orderedRoot rcb rcs with
  | none => rw [hrcr] at hrr; cases hrr
  | some rr =>
  rw [htrr, Option.map_some, Option.some.injEq] at htr
  rw [hrcr, Option.map_some, Option.some.injEq] at hrr
  have hroots : Spec.Mpt.Trie.root (Trie.orderedMap (txs.map fun s =>
        (Trie.valueOf txb s).data.toList)) = Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (rcs.map fun s =>
        (Trie.valueOf rcb s).data.toList)) = Spec.Header.field fs 5 :=
    ⟨by rw [← Trie.orderedRoot_eq htrr, htr], by rw [← Trie.orderedRoot_eq hrcr, hrr]⟩
  have hkj : Spec.Common.keccak (Trie.valueOf txb txs[j]).data.toList = q.txHash := by
    simpa [Spec.Header.keccakB_eq] using hhj
  split at h
  · cases h
  · rename_i ty hty hrc
    refine ⟨fs, hd, txb, rcb, txs, rcs, hk, ⟨henc, hv, hnum⟩, rfl, items_listOf htxs,
      items_listOf hrcs, hlen, hroots.1, hroots.2, j, hj, hj', hkj, ty, hty,
      fun ok hok => ?_⟩
    rw [hrc] at hok
    cases hok
  · rename_i ty ry ok' hty hrc
    split at h
    · rename_i hne
      refine ⟨fs, hd, txb, rcb, txs, rcs, hk, ⟨henc, hv, hnum⟩, rfl, items_listOf htxs,
        items_listOf hrcs, hlen, hroots.1, hroots.2, j, hj, hj', hkj, ty, hty,
        fun ok hok => ?_⟩
      rw [hrc, Option.some.injEq, Prod.mk.injEq] at hok
      exact hne hok.1.symm
    · cases h

/-- **A transaction of no known type (D36).** A verdict `transaction` says: block `N`'s hash `hN` is
proved under the anchor (`HashProved`), the header fetched hashes to it and is `N`'s
(`HeaderOf`), the body is the canonical lists, as many of each, which rebuild the header's
`transactionsRoot` and `receiptsRoot`, and transaction `j` of the list, which hashes to
`q.txHash`, is one `Typed.txType` refuses. So it says what the proved block holds, as
`notInBlock` does, and the job settles it without asking again (`Refusal.beforeRoots`). -/
theorem verdict_transaction {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)}
    (h : verdict a q hp header body = .refused .transaction) :
    ∃ hN fs hd txb rcb, ∃ txs rcs : List Span,
      HashProved a q.number hp hN ∧ Spec.Common.keccak header.data.toList = hN ∧
      HeaderOf header q.number fs hd ∧
      body = some (txb, rcb) ∧ ListOf txb (txs.map fun s => (Trie.valueOf txb s).data.toList) ∧
      ListOf rcb (rcs.map fun s => (Trie.valueOf rcb s).data.toList) ∧ txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (txs.map fun s => (Trie.valueOf txb s).data.toList)) =
        Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (rcs.map fun s => (Trie.valueOf rcb s).data.toList)) =
        Spec.Header.field fs 5 ∧
      ∃ j, ∃ hj : j < txs.length,
        Spec.Common.keccak (Trie.valueOf txb txs[j]).data.toList = q.txHash ∧
        Typed.txType txb txs[j].start txs[j].stop = none := by
  unfold verdict at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hN hhash
  obtain ⟨fs, hd, txb, rcb, txs, rcs, rest⟩ := settle_transaction (atFinal_of_ne (by simp) h)
  exact ⟨hN, fs, hd, txb, rcb, txs, rcs, hashOf_spec hhash, rest⟩

/-- **A receipt that is not the transaction's (D36).** A verdict `receipt` says: block `N`'s hash
`hN` is proved under the anchor (`HashProved`), the header fetched hashes to it and is `N`'s
(`HeaderOf`), the body is the canonical lists, as many of each, which rebuild the header's
`transactionsRoot` and `receiptsRoot`, and transaction `j` of the list, which hashes to
`q.txHash`, is an envelope of a type `ty` `Typed.txType` accepts while receipt `j` is no receipt
of type `ty` with a status (`Typed.receipt`). So it says what the proved block holds, and the job
settles it without asking again (`Refusal.beforeRoots`). -/
theorem verdict_receipt {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)}
    (h : verdict a q hp header body = .refused .receipt) :
    ∃ hN fs hd txb rcb, ∃ txs rcs : List Span,
      HashProved a q.number hp hN ∧ Spec.Common.keccak header.data.toList = hN ∧
      HeaderOf header q.number fs hd ∧
      body = some (txb, rcb) ∧ ListOf txb (txs.map fun s => (Trie.valueOf txb s).data.toList) ∧
      ListOf rcb (rcs.map fun s => (Trie.valueOf rcb s).data.toList) ∧ txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (txs.map fun s => (Trie.valueOf txb s).data.toList)) =
        Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap (rcs.map fun s => (Trie.valueOf rcb s).data.toList)) =
        Spec.Header.field fs 5 ∧
      ∃ j, ∃ hj : j < txs.length, ∃ hj' : j < rcs.length,
        Spec.Common.keccak (Trie.valueOf txb txs[j]).data.toList = q.txHash ∧
        ∃ ty, Typed.txType txb txs[j].start txs[j].stop = some ty ∧
          ∀ ok, Typed.receipt rcb rcs[j].start rcs[j].stop ≠ some (ty, ok) := by
  unfold verdict at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hN hhash
  obtain ⟨fs, hd, txb, rcb, txs, rcs, rest⟩ := settle_receipt (atFinal_of_ne (by simp) h)
  exact ⟨hN, fs, hd, txb, rcb, txs, rcs, hashOf_spec hhash, rest⟩

/-- **The hash is not in the block (D36).** A verdict `notInBlock` says: block `N`'s hash `hN` is
proved under the anchor (`HashProved`), the header fetched hashes to it and is `N`'s
(`HeaderOf`), the body is the canonical lists, as many of each, the transactions list rebuilds
the header's `transactionsRoot` and the receipts list its `receiptsRoot` (`Spec.Mpt.Trie.root`
of the ordered maps), and no transaction of the list hashes to `q.txHash`. So the proved block
says the transaction is not in it: no endpoint's bytes can make it so short of a Keccak-256
collision, and the job settles it without asking again. -/
theorem verdict_notInBlock {a : Anchor} {q : Ask} {hp : HashProof} {header : ByteArray}
    {body : Option (ByteArray × ByteArray)}
    (h : verdict a q hp header body = .refused .notInBlock) :
    ∃ hN fs hd txb rcb txs rcs,
      HashProved a q.number hp hN ∧ Spec.Common.keccak header.data.toList = hN ∧
      HeaderOf header q.number fs hd ∧ body = some (txb, rcb) ∧ ListOf txb txs ∧ ListOf rcb rcs ∧
      txs.length = rcs.length ∧
      Spec.Mpt.Trie.root (Trie.orderedMap txs) = Spec.Header.field fs 4 ∧
      Spec.Mpt.Trie.root (Trie.orderedMap rcs) = Spec.Header.field fs 5 ∧
      ∀ tx ∈ txs, Spec.Common.keccak tx ≠ q.txHash := by
  unfold verdict at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hN hhash
  obtain ⟨fs, hd, txb, rcb, txs, rcs, rest⟩ := settle_notInBlock (atFinal_of_ne (by simp) h)
  exact ⟨hN, fs, hd, txb, rcb, txs, rcs, hashOf_spec hhash, rest⟩

end LeanLight.Lc.Inclusion
