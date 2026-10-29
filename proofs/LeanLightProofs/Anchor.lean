import LeanLight.Facts

/-!
# The EL binding (25j) and account facts (25k)

About `LeanLight.Anchor.bind` and `LeanLight.Facts.account`, the code `lkd-lc` runs.

* **25j** (`bind_spec`): an EL header `bind` keeps for a beacon header `b` is a known fork's
  field list `fs` whose canonical RLP is the bytes fetched and whose Keccak-256 is `b`'s EL hash;
  the header read is `fs`'s (`Spec.Header.ofFields`, 14b); `b`'s tag is `Parent` exactly from the
  Gloas fork on; under `Own`, the timestamp is the slot's time, `parentBeaconBlockRoot`
  (field 19) is `b`'s parent root, and for an Electra-typed header `execution_matches` holds
  (state root, number, gas limit, gas used, timestamp, base fee, receipts root, field 5); under
  `Parent`, an Amsterdam header's `slotNumber` (field 22) is before `b`'s slot and its timestamp
  that slot's time, or an earlier header's timestamp is before the Gloas fork's and is the time of
  a slot before `b`'s.
* **25k** (`account_spec`): an account fact is `Spec.Mpt.account`'s reading of the proof under the
  state root of the header `bind` kept; (`contract_spec`) a contract's code hash is that
  account's; (`storage_spec`, LC7) a storage fact is the account `Spec.Mpt.account` reads under
  that root and, under the account's storage root, each slot's value as `Spec.Mpt.storage` reads
  it from the slot's proof (zero for a slot proved absent); `storageAt_spec` is the same reading
  under a root given, and `values_eq_some` characterizes the slots' loop.

`fieldsB_eq`, `decode_fieldsL` and `fieldsL_encode` tie the field list `bind` reads to the one
`Spec.Header.decode` reads and to the bytes hashed.
-/

namespace LeanLight.Lc.Anchor

open LeanLight.Spec.RlpDecode
open LeanLight.Spec.Rlp (encodeTree encodeTrees encodeBytes beValue)
open LeanLight.Spec.Header (ofFields field payloadOf headerOf)
open LeanLight.Lc.Forks (Chain)

/-- `fieldsB`, over a list. -/
def fieldsL (bs : Bytes) : Option (List Bytes) :=
  match itemAt bs 0 bs.length with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = bs.length then
      match itemsAt bs top.start top.stop with
      | none => none
      | some its => if its.all (fun it => !it.list) then some (its.map (payloadOf bs)) else none
    else none

theorem fieldsB_eq (bs : ByteArray) : fieldsB bs = fieldsL bs.data.toList := by
  have hp : Spec.Header.payloadOfB bs = payloadOf bs.data.toList :=
    funext (Spec.Header.payloadOfB_eq bs)
  simp only [fieldsB, fieldsL, itemAtB_eq, itemsAtB_eq, hp, Lc.Bytes.size_eq]
  rfl

/-- `Spec.Header.decode` is `ofFields` of the field list `fieldsL` reads. -/
theorem decode_fieldsL (bs : Bytes) : Spec.Header.decode bs = (fieldsL bs).bind ofFields := by
  unfold Spec.Header.decode fieldsL
  cases itemAt bs 0 bs.length with
  | none => rfl
  | some top =>
    simp only
    split
    · cases itemsAt bs top.start top.stop with
      | none => rfl
      | some its => simp only; split <;> rfl
    · rfl

/-- The field list `fieldsL` reads is the one the bytes are the canonical RLP of. -/
theorem fieldsL_encode {bs : Bytes} {fs : List Bytes} (h : fieldsL bs = some fs) :
    encodeTree (.branch (fs.map .leaf)) = some bs := by
  unfold fieldsL at h
  split at h
  · contradiction
  · rename_i top htop
    split at h
    · rename_i hc
      split at h
      · contradiction
      · rename_i its hits
        split at h
        · rename_i hall
          injection h with h
          subst h
          obtain ⟨-, -, -, -, -, -, -, htopenc⟩ := itemAt_span htop
          obtain ⟨hspans, hflat⟩ := itemsAt_spans hits
          have hleaf : ∀ it ∈ its,
              encodeBytes (payloadOf bs it) = some (window bs it.pos it.stop) := by
            intro it hit
            obtain ⟨-, -, hat⟩ := hspans it hit
            obtain ⟨hp, -, -, -, -, -, -, henc⟩ := itemAt_span hat
            have hl : it.list = false := by
              have := List.all_eq_true.mp hall it hit
              simpa using this
            rw [hl] at henc
            rw [hp] at henc
            exact henc
          simp only [encodeTree, List.map_map]
          have := Spec.Header.encodeTrees_spans bs its hleaf
          simp only [Function.comp_def]
          rw [this, hflat, Option.bind_some]
          rw [hc.1, hc.2, Spec.Header.window_all] at htopenc
          rw [hc.2]
          exact htopenc
        · contradiction
    · contradiction

/-- A header's tag is `Parent` exactly from the Gloas fork on. -/
theorem elTag_parent_iff (c : Chain) (b : Store.Header) :
    Store.elTag c b = .parent ↔ c.gloasAt b.beacon.slot = true := by
  unfold Store.elTag
  split <;> simp_all

theorem extraOf_parentBeaconBlockRoot {fs : List Bytes} {r : Bytes}
    (h : (extraOf fs).parentBeaconBlockRoot = some r) : 20 ≤ fs.length ∧ field fs 19 = r := by
  simp only [extraOf] at h
  split at h
  · injection h with h; exact ⟨by assumption, h⟩
  · cases h

theorem extraOf_slotNumber {fs : List Bytes} {n : Nat}
    (h : (extraOf fs).slotNumber = some n) : 23 ≤ fs.length ∧ beValue (field fs 22) = n := by
  simp only [extraOf] at h
  split at h
  · injection h with h; exact ⟨by assumption, h⟩
  · cases h

theorem extraOf_slotNumber_none {fs : List Bytes} (h : (extraOf fs).slotNumber = none) :
    fs.length < 23 := by
  simp only [extraOf] at h
  split at h
  · cases h
  · omega

/-- What `fieldsOk` checks, under each tag. -/
theorem fieldsOk_spec {c : Chain} {b : Store.Header} {h : Spec.Header.Header} {fs : List Bytes}
    (hf : fieldsOk c b h (extraOf fs) = true) :
    (Store.elTag c b = .own →
      h.timestamp = c.slotTime b.beacon.slot / 1000 ∧ 20 ≤ fs.length ∧
        field fs 19 = b.beacon.parentRoot.data.toList ∧
        ∀ e, b.exec = .payload e →
          e.stateRoot.data.toList = h.stateRoot ∧ e.blockNumber = h.number ∧
            e.gasLimit = h.gasLimit ∧ e.gasUsed = h.gasUsed ∧ e.timestamp = h.timestamp ∧
            e.baseFeePerGas = h.baseFee ∧ e.receiptsRoot.data.toList = field fs 5) ∧
    (Store.elTag c b = .parent →
      (23 ≤ fs.length ∧ beValue (field fs 22) < b.beacon.slot ∧
          h.timestamp = c.slotTime (beValue (field fs 22)) / 1000) ∨
        (fs.length < 23 ∧ ∃ e k, c.gloasEpoch = some e ∧
          h.timestamp < c.slotTime (c.startSlot e) / 1000 ∧ k < b.beacon.slot ∧
          h.timestamp = c.slotTime k / 1000)) := by
  unfold fieldsOk at hf
  constructor
  · intro ht
    rw [ht] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨hx, ho⟩ := hf
    simp only [ownOk, Bool.and_eq_true, beq_iff_eq] at ho
    obtain ⟨hts, hpb⟩ := ho
    obtain ⟨h20, h19⟩ := extraOf_parentBeaconBlockRoot hpb
    refine ⟨hts, h20, h19, fun e he => ?_⟩
    rw [he] at hx
    simp only [execMatches, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hx
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · intro ht
    rw [ht] at hf
    dsimp only at hf
    unfold parentOk at hf
    split at hf
    · rename_i n hn
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
      obtain ⟨h23, rfl⟩ := extraOf_slotNumber hn
      exact .inl ⟨h23, hf.1, hf.2⟩
    · rename_i hn
      split at hf
      · rename_i e he
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
        obtain ⟨⟨h1, h2⟩, h3⟩ := hf
        exact .inr ⟨extraOf_slotNumber_none hn, e, _, he, h1, h2, h3⟩
      · cases hf

/-- **The EL binding (25j).** An EL header `bind` keeps for beacon header `b` is a known fork's
field list `fs`: the bytes fetched are its canonical RLP, their Keccak-256 is `b`'s EL hash, the
header read is `fs`'s; `b`'s tag is `Parent` exactly from the Gloas fork on; under `Own`, the
timestamp is the slot's time, field 19 (`parentBeaconBlockRoot`) is `b`'s parent root, and an
Electra-typed `b`'s payload header agrees with it (`execution_matches`, receipts root field 5);
under `Parent`, an Amsterdam header's `slotNumber` (field 22) is before `b`'s slot with the
timestamp that slot's time, or an earlier header's timestamp is before the Gloas fork's and is
the time of some slot before `b`'s. -/
theorem bind_spec {c : Chain} {b : Store.Header} {rlp : ByteArray} {h : Spec.Header.Header}
    (hb : bind c b rlp = some h) :
    ∃ fs, encodeTree (.branch (fs.map .leaf)) = some rlp.data.toList ∧
      Spec.Common.keccak rlp.data.toList = b.elHash.data.toList ∧ ofFields fs = some h ∧
      (Store.elTag c b = .parent ↔ c.gloasAt b.beacon.slot = true) ∧
      (Store.elTag c b = .own →
        h.timestamp = c.slotTime b.beacon.slot / 1000 ∧ 20 ≤ fs.length ∧
          field fs 19 = b.beacon.parentRoot.data.toList ∧
          ∀ e, b.exec = .payload e →
            e.stateRoot.data.toList = h.stateRoot ∧ e.blockNumber = h.number ∧
              e.gasLimit = h.gasLimit ∧ e.gasUsed = h.gasUsed ∧ e.timestamp = h.timestamp ∧
              e.baseFeePerGas = h.baseFee ∧ e.receiptsRoot.data.toList = field fs 5) ∧
      (Store.elTag c b = .parent →
        (23 ≤ fs.length ∧ beValue (field fs 22) < b.beacon.slot ∧
            h.timestamp = c.slotTime (beValue (field fs 22)) / 1000) ∨
          (fs.length < 23 ∧ ∃ e k, c.gloasEpoch = some e ∧
            h.timestamp < c.slotTime (c.startSlot e) / 1000 ∧ k < b.beacon.slot ∧
            h.timestamp = c.slotTime k / 1000)) := by
  unfold bind at hb
  split at hb
  · cases hb
  · rename_i h' hv
    split at hb
    · cases hb
    · rename_i fs hfs
      split at hb
      · rename_i hok
        injection hb with hb
        subst hb
        rw [Spec.Header.verifyB_eq] at hv
        unfold Spec.Header.verify at hv
        split at hv
        · rename_i hk
          rw [fieldsB_eq] at hfs
          rw [decode_fieldsL, hfs, Option.bind_some] at hv
          exact ⟨fs, fieldsL_encode hfs, hk, hv, elTag_parent_iff c b, (fieldsOk_spec hok).1,
            (fieldsOk_spec hok).2⟩
        · cases hv
      · cases hb

end LeanLight.Lc.Anchor

namespace LeanLight.Lc.Facts

/-- **An account fact (25k).** What `account` gives is the header `Anchor.bind` keeps for the
beacon header, and the account `Spec.Mpt.account` reads from the proof under that header's state
root. -/
theorem account_spec {c : Forks.Chain} {b : Store.Header} {rlp : ByteArray} {a : Anchor.Bytes}
    {nodes : ByteArray} {h : Spec.Header.Header} {acct : Spec.Mpt.Account}
    (hf : account c b rlp a nodes = some (h, acct)) :
    Anchor.bind c b rlp = some h ∧ Spec.Mpt.account h.stateRoot a nodes.data.toList = some acct := by
  unfold account at hf
  split at hf
  · cases hf
  · rename_i h' hb
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
    obtain ⟨acct', hacc, rfl, rfl⟩ := hf
    exact ⟨hb, by rw [← Spec.Mpt.accountB_eq]; exact hacc⟩

/-- **A contract's code (25k).** What `contract` gives is the header `Anchor.bind` keeps for the
beacon header, and the code hash of the account `Spec.Mpt.account` reads from the proof under
that header's state root. -/
theorem contract_spec {c : Forks.Chain} {b : Store.Header} {rlp : ByteArray} {a : Anchor.Bytes}
    {nodes : ByteArray} {h : Spec.Header.Header} {code : Anchor.Bytes}
    (hf : contract c b rlp a nodes = some (h, code)) :
    ∃ acct, Anchor.bind c b rlp = some h ∧
      Spec.Mpt.account h.stateRoot a nodes.data.toList = some acct ∧ acct.codeHash = code := by
  unfold contract at hf
  split at hf
  · cases hf
  · rename_i h' acct ha
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨hb, hacc⟩ := account_spec ha
    exact ⟨acct, hb, hacc, rfl⟩

/-- The slots' loop, after `acc`, is `values` after it. -/
theorem valuesFrom_eq (root : Anchor.Bytes) : ∀ (slots : List (Anchor.Bytes × ByteArray))
    (acc : List Nat), valuesFrom root slots acc = (values root slots).map (acc.reverse ++ ·)
  | [], acc => by simp [values, valuesFrom]
  | (k, p) :: rest, acc => by
    simp only [values, valuesFrom]
    cases Spec.Mpt.storageB root k p with
    | none => rfl
    | some v =>
      simp only
      rw [valuesFrom_eq root rest (v :: acc), valuesFrom_eq root rest [v]]
      cases values root rest <;> simp

/-- What `values` reads, over the `ByteArray` reader `lkd-lc` runs. -/
theorem values_eq_someB (root : Anchor.Bytes) (slots : List (Anchor.Bytes × ByteArray))
    (vs : List Nat) :
    values root slots = some vs ↔ slots.map (fun s => Spec.Mpt.storageB root s.1 s.2) = vs.map some := by
  induction slots generalizing vs with
  | nil =>
    simp only [values, valuesFrom, List.reverse_nil, Option.some.injEq, List.map_nil]
    constructor
    · rintro rfl; rfl
    · intro h; exact (List.map_eq_nil_iff.mp h.symm).symm
  | cons s rest ih =>
    obtain ⟨k, p⟩ := s
    simp only [values, valuesFrom, List.map_cons]
    cases hk : Spec.Mpt.storageB root k p with
    | none =>
      simp only [reduceCtorEq, false_iff]
      intro h
      cases vs with
      | nil => cases h
      | cons v vs => simp at h
    | some v =>
      simp only
      rw [valuesFrom_eq, List.reverse_singleton]
      cases vs with
      | nil => simp
      | cons w ws =>
        simp only [List.map_cons, List.cons.injEq, Option.some.injEq]
        rw [← ih ws]
        constructor
        · intro h
          cases hr : values root rest with
          | none => rw [hr] at h; cases h
          | some xs =>
            rw [hr] at h
            simp only [Option.map_some, List.singleton_append, Option.some.injEq,
              List.cons.injEq] at h
            exact ⟨h.1, by rw [h.2]⟩
        · rintro ⟨rfl, h⟩
          simp [h]

/-- **What `values` reads**: one value for each slot, in order, each the one `Spec.Mpt.storage`
reads from the slot's proof for its key under `root` (zero for a slot proved absent). -/
theorem values_eq_some (root : Anchor.Bytes) (slots : List (Anchor.Bytes × ByteArray))
    (vs : List Nat) :
    values root slots = some vs ↔
      slots.map (fun s => Spec.Mpt.storage root s.1 s.2.data.toList) = vs.map some := by
  rw [values_eq_someB]
  simp only [Spec.Mpt.storageB_eq]

/-- **Storage under a state root (25k, LC7).** What `storageAt` gives is the account
`Spec.Mpt.account` reads at `a` under `root` from `nodes`, and, under that account's storage root,
one value for each slot, each the one `Spec.Mpt.storage` reads from the slot's proof for its key
(zero for a slot proved absent). -/
theorem storageAt_spec {root a : Anchor.Bytes} {nodes : ByteArray}
    {slots : List (Anchor.Bytes × ByteArray)} {acct : Spec.Mpt.Account} {vs : List Nat}
    (hf : storageAt root a nodes slots = some (acct, vs)) :
    Spec.Mpt.account root a nodes.data.toList = some acct ∧
      slots.map (fun s => Spec.Mpt.storage acct.storageRoot s.1 s.2.data.toList) = vs.map some := by
  unfold storageAt at hf
  split at hf
  · cases hf
  · rename_i acct' ha
    split at hf
    · cases hf
    · rename_i vs' hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨by rw [← Spec.Mpt.accountB_eq]; exact ha, (values_eq_some _ _ _).mp hv⟩

/-- **A storage fact (25k, LC7).** What `storage` gives is the header `Anchor.bind` keeps for the
beacon header (25j), the account `Spec.Mpt.account` reads at `a` from the proof under that
header's state root, and, under that account's storage root, one value for each slot asked, each
the one `Spec.Mpt.storage` reads from the slot's proof for its key (zero for a slot proved
absent). -/
theorem storage_spec {c : Forks.Chain} {b : Store.Header} {rlp : ByteArray} {a : Anchor.Bytes}
    {nodes : ByteArray} {slots : List (Anchor.Bytes × ByteArray)} {h : Spec.Header.Header}
    {acct : Spec.Mpt.Account} {vs : List Nat}
    (hf : storage c b rlp a nodes slots = some (h, acct, vs)) :
    Anchor.bind c b rlp = some h ∧ Spec.Mpt.account h.stateRoot a nodes.data.toList = some acct ∧
      slots.map (fun s => Spec.Mpt.storage acct.storageRoot s.1 s.2.data.toList) = vs.map some := by
  unfold storage at hf
  split at hf
  · cases hf
  · rename_i h' hb
    split at hf
    · cases hf
    · rename_i acct' vs' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨hb, storageAt_spec hs⟩

end LeanLight.Lc.Facts
