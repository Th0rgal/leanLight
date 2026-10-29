import LeanLight.El.Trie
import LeanLightProofs.Spec.MptTrie

/-!
# The ordered trie root that runs is the Yellow Paper's (LC8)

`LeanLight.El.Trie` builds the trie's nodes in `ByteArray`s; `Spec.Mpt.Trie` (`LeanLightProofs.Spec.MptTrie`)
is the Yellow Paper's trie, Appendix D, with `Spec.Mpt.lookup` complete and sound on it. Here:

* `node_eq`: `node`'s RLP is the RLP of `Spec.Mpt.Trie.compose`, c(𝔍, i), of the same pairs (the
  keys, and each item's payload), `none` exactly when that RLP cannot be written. The keys'
  functions are the model's (`common_eq`, `sub_eq`, `terminal_eq`, `hp_eq`), RLP into a
  `ByteArray` is `Spec.Rlp`'s (`encBytes_eq`, `encList_eq`), and what a parent embeds, `ref`, is
  the RLP of the node cap n(𝔍, i) (`encodeTree_cap`).
* `orderedRoot_eq`: a root `orderedRoot` returns is `Spec.Mpt.Trie.root` of the ordered map
  `orderedMap`, item `i` (its payload) under `rlp(i)`.
* `orderedRoot_lookupB` and `orderedRoot_soundB`: under such a root, the model's proof of
  `rlp(i)` is one `Spec.Mpt.lookup` accepts and reads item `i` from
  (`Spec.Mpt.Trie.lookup_complete`), and any proof it accepts reads item `i` or holds a
  Keccak-256 collision (`Spec.Mpt.Trie.lookup_sound`'s argument).
-/

namespace LeanLight.Lc.Trie

open LeanLight.Spec.Rlp
open LeanLight.Spec.RlpDecode (Span)
open LeanLight.Spec.Header (keccak)

/-- A `ByteArray` as the list of its bytes. -/
abbrev toL (b : ByteArray) : Bytes := b.data.toList

/-- The model's pairs a runtime `Obj` over `bs` stands for: each key, and its item's payload. -/
def toObj (bs : ByteArray) (obj : Obj) : List Spec.Mpt.Trie.Entry :=
  obj.map fun kv => (kv.1, (valueOf bs kv.2).data.toList)

/-! ## The keys: the model's functions -/

theorem lcp_eq : ∀ (a b : Nibbles), lcp a b = Spec.Mpt.Trie.lcp a b
  | a :: x, b :: z => by simp only [lcp, Spec.Mpt.Trie.lcp, lcp_eq x z]
  | [], _ => by simp [lcp, Spec.Mpt.Trie.lcp]
  | _ :: _, [] => by simp [lcp, Spec.Mpt.Trie.lcp]

theorem lcp_assoc : ∀ (a b c : Nibbles),
    Spec.Mpt.Trie.lcp (Spec.Mpt.Trie.lcp a b) c = Spec.Mpt.Trie.lcp a (Spec.Mpt.Trie.lcp b c)
  | a :: x, b :: z, c :: w => by
    simp only [Spec.Mpt.Trie.lcp]
    by_cases hab : a = b
    · subst hab
      by_cases hac : a = c
      · subst hac; simp only [Spec.Mpt.Trie.lcp, ite_true, lcp_assoc x z w]
      · simp [hac, Spec.Mpt.Trie.lcp]
    · by_cases hbc : b = c
      · subst hbc; simp [hab, Spec.Mpt.Trie.lcp]
      · simp [hab, hbc, Spec.Mpt.Trie.lcp]
  | [], _, _ => by simp [Spec.Mpt.Trie.lcp]
  | _ :: _, [], _ => by simp [Spec.Mpt.Trie.lcp]
  | a :: x, b :: z, [] => by
    simp only [Spec.Mpt.Trie.lcp]
    split <;> simp [Spec.Mpt.Trie.lcp]

theorem foldl_lcp (bs : ByteArray) : ∀ (l : Obj) (c : Nibbles), l ≠ [] →
    l.foldl (fun c kv => lcp c kv.1) c = Spec.Mpt.Trie.lcp c (Spec.Mpt.Trie.common (toObj bs l))
  | [], _, h => absurd rfl h
  | [e], c, _ => by
    simp [toObj, Spec.Mpt.Trie.common, lcp_eq]
  | e :: e' :: l, c, _ => by
    rw [List.foldl_cons, foldl_lcp bs (e' :: l) (lcp c e.1) (List.cons_ne_nil _ _)]
    simp only [toObj, List.map_cons, Spec.Mpt.Trie.common]
    rw [lcp_eq, lcp_assoc]

theorem common_eq (bs : ByteArray) (obj : Obj) :
    Spec.Mpt.Trie.common (toObj bs obj) = common obj := by
  match obj with
  | [] => rfl
  | [e] => rfl
  | e :: e' :: l =>
    simp only [common]
    rw [foldl_lcp bs (e' :: l) e.1 (List.cons_ne_nil _ _)]
    rfl

theorem pack_eq : ∀ (x : Nibbles), pack x = Spec.Mpt.Trie.pack x
  | a :: b :: rest => by simp only [pack, Spec.Mpt.Trie.pack, pack_eq rest]
  | [] => rfl
  | [_] => rfl

theorem hp_eq (x : Nibbles) (t : Bool) : hp x t = Spec.Mpt.Trie.hp x t := by
  simp only [hp, Spec.Mpt.Trie.hp, Spec.Mpt.Trie.hpFlag, pack_eq]

theorem sub_eq (bs : ByteArray) (obj : Obj) (i x : Nat) :
    Spec.Mpt.Trie.sub (toObj bs obj) i x = toObj bs (sub obj i x) := by
  simp only [Spec.Mpt.Trie.sub, sub, toObj, List.filter_map]
  rfl

theorem terminal_eq (bs : ByteArray) (obj : Obj) (i : Nat) :
    Spec.Mpt.Trie.terminal (toObj bs obj) i = (valueOrEmpty bs (terminal obj i)).data.toList := by
  simp only [Spec.Mpt.Trie.terminal, terminal, toObj, List.find?_map]
  have : ((fun e : Spec.Mpt.Trie.Entry => decide (e.1.length = i)) ∘
      fun kv : Nibbles × Span => (kv.1, (valueOf bs kv.2).data.toList)) =
      fun kv => decide (kv.1.length = i) := rfl
  rw [this]
  cases List.find? (fun kv : Nibbles × Span => decide (kv.1.length = i)) obj <;> rfl

theorem toObj_cons (bs : ByteArray) (kv : Nibbles × Span) (rest : Obj) :
    toObj bs (kv :: rest) = (kv.1, (valueOf bs kv.2).data.toList) :: toObj bs rest := rfl

/-! ## RLP into a `ByteArray` -/

@[simp] theorem mk_toList (l : List UInt8) : (ByteArray.mk l.toArray).data.toList = l := rfl

theorem encBytes_eq (x : ByteArray) :
    (encBytes x).map (·.data.toList) = encodeBytes x.data.toList := by
  have hlen : x.data.toList.length = x.size := by simp
  have h0 : x.data.toList[0]?.getD 0 = x[0]?.getD 0 :=
    (Lc.Bytes.byteAt_eq x 0).symm
  unfold encBytes encodeBytes head
  rw [hlen, h0]
  by_cases h1 : x.size = 1 ∧ x[0]?.getD 0 < 128
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : x.size < 56
    · rw [ite_eq_left h2, ite_eq_left h2]; simp
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : x.size < 18446744073709551616
      · rw [ite_eq_left h3, ite_eq_left (by simpa using h3)]; simp
      · rw [ite_eq_right h3, ite_eq_right (by simpa using h3)]; rfl

theorem encList_eq (s : ByteArray) :
    (encList s).map (·.data.toList) = encodeList s.data.toList := by
  have hlen : s.data.toList.length = s.size := by simp
  unfold encList encodeList head
  rw [hlen]
  by_cases h2 : s.size < 56
  · rw [ite_eq_left h2, ite_eq_left h2]; simp
  · rw [ite_eq_right h2, ite_eq_right h2]
    by_cases h3 : s.size < 18446744073709551616
    · rw [ite_eq_left h3, ite_eq_left (by simpa using h3)]; simp
    · rw [ite_eq_right h3, ite_eq_right (by simpa using h3)]; rfl

/-- What a parent embeds for a node whose RLP is `e`, over lists. -/
def refL (e : Bytes) : Bytes := if e.length < 32 then e else 0xa0 :: keccak e

theorem ref_eq (e : ByteArray) : (ref e).data.toList = refL e.data.toList := by
  unfold ref refL
  have hlen : e.data.toList.length = e.size := by simp
  rw [hlen]
  split
  · rfl
  · simp only [ByteArray.toList_data_append]
    rfl

/-- The node cap n(𝔍, i), encoded, is `refL` of c(𝔍, i)'s RLP: the node inline when its RLP is
shorter than 32 bytes, else the RLP of its hash. -/
theorem encodeTree_cap (J : List Spec.Mpt.Trie.Entry) (i : Nat) :
    encodeTree (Spec.Mpt.Trie.cap J i) = (encodeTree (Spec.Mpt.Trie.compose J i)).map refL := by
  match J with
  | [] =>
    rw [Spec.Mpt.Trie.cap, Spec.Mpt.Trie.compose]
    rfl
  | e :: J =>
    rw [Spec.Mpt.Trie.cap]
    cases he : encodeTree (Spec.Mpt.Trie.compose (e :: J) i) with
    | none =>
      have : (Spec.Mpt.Trie.rlp (Spec.Mpt.Trie.compose (e :: J) i)).length < 32 := by
        simp [Spec.Mpt.Trie.rlp, he]
      rw [ite_eq_left this, he]
      rfl
    | some x =>
      have hr : Spec.Mpt.Trie.rlp (Spec.Mpt.Trie.compose (e :: J) i) = x := by
        simp [Spec.Mpt.Trie.rlp, he]
      rw [hr]
      unfold refL
      split
      · rename_i hl
        rw [he, Option.map_some, ite_eq_left hl]
      · rename_i hl
        rw [encodeTree, Spec.Mpt.Trie.encodeBytes_hash, Option.map_some, ite_eq_right hl]
        rfl

/-! ## The construction -/

/-- s of a sequence, then another. -/
theorem encodeTrees_append_eq : ∀ (ts us : List Tree),
    encodeTrees (ts ++ us) = (encodeTrees ts).bind fun s => (encodeTrees us).map (s ++ ·)
  | [], us => by simp [encodeTrees]
  | t :: ts, us => by
    simp only [List.cons_append, encodeTrees, encodeTrees_append_eq ts us]
    cases encodeTree t with
    | none => rfl
    | some e =>
      simp only [Option.bind_some]
      cases encodeTrees ts with
      | none => rfl
      | some s =>
        simp only [Option.map_some, Option.bind_some, Option.map_map]
        congr 1
        funext x
        simp

/-- The sixteen subnodes: what `node`'s loop appends is the RLP of the model's sixteen caps, one
after the other. -/
theorem foldlM_ref (g : Nat → Option ByteArray) (T : Nat → Tree)
    (h : ∀ d, (g d).map (fun s => (ref s).data.toList) = encodeTree (T d)) :
    ∀ (ds : List Nat) (acc : ByteArray),
    (ds.foldlM (fun acc d => (g d).bind fun sub => pure (acc ++ ref sub)) acc).map toL =
      (encodeTrees (ds.map T)).map (toL acc ++ ·)
  | [], acc => by simp [encodeTrees, pure]
  | d :: ds, acc => by
    have hd := h d
    simp only [List.foldlM_cons, List.map_cons, encodeTrees]
    cases hg : g d with
    | none =>
      rw [hg, Option.map_none] at hd
      simp only [bind, Option.bind_none, Option.map_none, ← hd]
    | some sub =>
      rw [hg, Option.map_some] at hd
      have ih := foldlM_ref g T h ds (acc ++ ref sub)
      simp only [pure] at ih
      simp only [bind, Option.bind_some, pure, ← hd]
      rw [ih]
      cases encodeTrees (ds.map T) with
      | none => rfl
      | some es => simp only [Option.map_some, ByteArray.toList_data_append, List.append_assoc]

/-- `node` of two keys or more. -/
theorem node_of_cons {bs : ByteArray} {obj : Obj} {e e' : Nibbles × Span} {rest : Obj}
    (h : obj = e :: e' :: rest) (i : Nat) :
    node bs obj i =
      (if i < (common obj).length then do
        let path ← encBytes ⟨(hp ((common obj).drop i) false).toArray⟩
        let sub ← node bs obj (common obj).length
        encList (path ++ ref sub)
      else do
        let subnodes ← (List.range 16).foldlM (fun acc x => do
            let s ← node bs (sub obj i x) (i + 1)
            pure (acc ++ ref s)) ByteArray.empty
        let value ← encBytes (valueOrEmpty bs (terminal obj i))
        encList (subnodes ++ value)) := by
  subst h
  rw [node]

/-- c(𝔍, i) of two pairs or more. -/
theorem compose_of_cons {J : List Spec.Mpt.Trie.Entry} {e e' : Spec.Mpt.Trie.Entry}
    {rest : List Spec.Mpt.Trie.Entry} (h : J = e :: e' :: rest) (i : Nat) :
    Spec.Mpt.Trie.compose J i =
      if i < (Spec.Mpt.Trie.common J).length then
        .branch [.leaf (Spec.Mpt.Trie.hp ((Spec.Mpt.Trie.common J).drop i) false),
          Spec.Mpt.Trie.cap J (Spec.Mpt.Trie.common J).length]
      else
        .branch ((List.range 16).map (fun x => Spec.Mpt.Trie.cap (Spec.Mpt.Trie.sub J i x) (i + 1))
          ++ [.leaf (Spec.Mpt.Trie.terminal J i)]) := by
  subst h
  rw [Spec.Mpt.Trie.compose]

/-- **`node` is c(𝔍, i), encoded**: the RLP `node` builds is the RLP of the model's `compose` of
the same pairs, `none` exactly when that RLP cannot be written. -/
theorem node_eq (bs : ByteArray) (obj : Obj) (i : Nat) :
    (node bs obj i).map toL = encodeTree (Spec.Mpt.Trie.compose (toObj bs obj) i) := by
  match obj with
  | [] =>
    rw [node, toObj, List.map_nil, Spec.Mpt.Trie.compose]
    rfl
  | [(k, v)] =>
    rw [node, toObj, List.map_cons, List.map_nil, Spec.Mpt.Trie.compose]
    simp only [encodeTree, encodeTrees, bind]
    have hc : (encBytes ⟨(hp (k.drop i) true).toArray⟩).map toL =
        encodeBytes (Spec.Mpt.Trie.hp (k.drop i) true) := by
      rw [encBytes_eq, mk_toList, hp_eq]
    have hv := encBytes_eq (valueOf bs v)
    cases hpb : encBytes ⟨(hp (k.drop i) true).toArray⟩ with
    | none =>
      rw [hpb, Option.map_none] at hc
      simp [← hc]
    | some path =>
      rw [hpb, Option.map_some] at hc
      simp only [Option.bind_some, ← hc]
      cases hvb : encBytes (valueOf bs v) with
      | none =>
        rw [hvb, Option.map_none] at hv
        simp [← hv]
      | some value =>
        rw [hvb, Option.map_some] at hv
        simp only [Option.bind_some, ← hv, Option.map_some, List.append_nil]
        rw [← ByteArray.toList_data_append, ← encList_eq]
  | e :: e' :: rest =>
    have hc := common_eq bs (e :: e' :: rest)
    rw [node_of_cons rfl, compose_of_cons (J := toObj bs (e :: e' :: rest))
      (e := (e.1, (valueOf bs e.2).data.toList)) (e' := (e'.1, (valueOf bs e'.2).data.toList))
      (rest := toObj bs rest) rfl, hc]
    by_cases h0 : i < (common (e :: e' :: rest)).length
    · rw [ite_eq_left h0, ite_eq_left h0]
      have ih := node_eq bs (e :: e' :: rest) (common (e :: e' :: rest)).length
      have hpath : (encBytes ⟨(hp ((common (e :: e' :: rest)).drop i) false).toArray⟩).map toL =
          encodeBytes (Spec.Mpt.Trie.hp ((common (e :: e' :: rest)).drop i) false) := by
        rw [encBytes_eq, mk_toList, hp_eq]
      have hcap := encodeTree_cap (toObj bs (e :: e' :: rest)) (common (e :: e' :: rest)).length
      rw [← ih, Option.map_map] at hcap
      simp only [encodeTree, encodeTrees, bind]
      cases hpb : encBytes ⟨(hp ((common (e :: e' :: rest)).drop i) false).toArray⟩ with
      | none =>
        rw [hpb, Option.map_none] at hpath
        simp [← hpath]
      | some path =>
        rw [hpb, Option.map_some] at hpath
        simp only [Option.bind_some, ← hpath, hcap]
        cases node bs (e :: e' :: rest) (common (e :: e' :: rest)).length with
        | none => rfl
        | some sub =>
          simp only [Option.bind_some, Option.map_some, Function.comp_apply, List.append_nil]
          rw [← ref_eq, ← ByteArray.toList_data_append, ← encList_eq]
    · rw [ite_eq_right h0, ite_eq_right h0]
      have ih := fun x => node_eq bs (sub (e :: e' :: rest) i x) (i + 1)
      have hT : ∀ x, (node bs (sub (e :: e' :: rest) i x) (i + 1)).map
            (fun s => (ref s).data.toList) =
          encodeTree (Spec.Mpt.Trie.cap (Spec.Mpt.Trie.sub (toObj bs (e :: e' :: rest)) i x)
            (i + 1)) := by
        intro x
        rw [encodeTree_cap, sub_eq, ← ih x, Option.map_map]
        congr 1
        funext s
        exact ref_eq s
      have hf := foldlM_ref _ _ hT (List.range 16) ByteArray.empty
      have hv := encBytes_eq (valueOrEmpty bs (terminal (e :: e' :: rest) i))
      simp only [bind, pure] at hf ⊢
      simp only [encodeTree, encodeTrees_append_eq, encodeTrees, terminal_eq]
      cases hfo : List.foldlM (fun acc x =>
          (node bs (sub (e :: e' :: rest) i x) (i + 1)).bind fun s => some (acc ++ ref s))
          ByteArray.empty (List.range 16) with
      | none =>
        rw [hfo, Option.map_none] at hf
        simp only [Option.bind_none, Option.map_none]
        cases he : encodeTrees ((List.range 16).map fun x =>
            Spec.Mpt.Trie.cap (Spec.Mpt.Trie.sub (toObj bs (e :: e' :: rest)) i x) (i + 1)) with
        | none => rfl
        | some es => rw [he] at hf; cases hf
      | some subs =>
        rw [hfo, Option.map_some] at hf
        cases he : encodeTrees ((List.range 16).map fun x =>
            Spec.Mpt.Trie.cap (Spec.Mpt.Trie.sub (toObj bs (e :: e' :: rest)) i x) (i + 1)) with
        | none => rw [he] at hf; cases hf
        | some es =>
          rw [he, Option.map_some, Option.some.injEq] at hf
          have hes : es = toL subs := by rw [hf]; rfl
          simp only [Option.bind_some]
          cases hvb : encBytes (valueOrEmpty bs (terminal (e :: e' :: rest) i)) with
          | none =>
            rw [hvb, Option.map_none] at hv
            simp [← hv]
          | some value =>
            rw [hvb, Option.map_some] at hv
            simp only [Option.bind_some, ← hv, Option.map_some, List.append_nil, hes]
            rw [← ByteArray.toList_data_append, ← encList_eq]
termination_by measure obj i
decreasing_by
  all_goals first
    | exact measure_extension (List.cons_ne_nil _ _) h0 (common_le _)
    | exact measure_sub i _

/-- The root `root` builds is Keccak-256 of c(𝔍, 0)'s RLP. -/
theorem root_eq (bs : ByteArray) (obj : Obj) :
    (root bs obj).map toL = (encodeTree (Spec.Mpt.Trie.compose (toObj bs obj) 0)).map keccak := by
  rw [root, Option.map_map, ← node_eq, Option.map_map]
  rfl

/-! ## The ordered map -/

/-- An ordered list's map, 𝔍 for its trie: item `i` under `rlp(i)` (`rlp.encode(Uint(i))`), in
order. -/
def orderedMap (items : List Bytes) : Spec.Mpt.Trie.Map :=
  items.zipIdx.map fun vi => ((encodeScalar vi.2).getD [], vi.1)

/-- **The ordered root that runs is the Yellow Paper's**: a root `orderedRoot` returns is
TRIE(𝔍) of the ordered map of the items' payloads. -/
theorem orderedRoot_eq {bs : ByteArray} {items : List Span} {r : ByteArray}
    (h : orderedRoot bs items = some r) :
    r.data.toList =
      Spec.Mpt.Trie.root (orderedMap (items.map fun s => (valueOf bs s).data.toList)) := by
  have he := root_eq bs (items.zipIdx.map fun vi => (indexNibbles vi.2, vi.1))
  rw [← orderedRoot, h, Option.map_some] at he
  have hy : toObj bs (items.zipIdx.map fun vi => (indexNibbles vi.2, vi.1)) =
      Spec.Mpt.Trie.y (orderedMap (items.map fun s => (valueOf bs s).data.toList)) := by
    simp only [toObj, Spec.Mpt.Trie.y, orderedMap, List.map_map, List.zipIdx_map]
    rfl
  rw [hy] at he
  unfold Spec.Mpt.Trie.root Spec.Mpt.Trie.rlp
  cases hc : encodeTree (Spec.Mpt.Trie.compose
      (Spec.Mpt.Trie.y (orderedMap (items.map fun s => (valueOf bs s).data.toList))) 0) with
  | none => rw [hc] at he; cases he
  | some x =>
    rw [hc, Option.map_some, Option.some.injEq] at he
    exact he

/-- An item's key is its index's RLP, below 2^64 items. -/
theorem indexKey_some {i : Nat} (h : i < 2 ^ 64) :
    encodeScalar i = some ((encodeScalar i).getD []) := by
  have hl : (be i).length ≤ 8 := be_length_le_eight h
  unfold encodeScalar encodeBytes
  split
  · rfl
  · rw [ite_eq_left (by omega)]; rfl

theorem indexKey_injective {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : (encodeScalar i).getD [] = (encodeScalar j).getD []) : i = j :=
  encodeScalar_injective (indexKey_some hi) (h ▸ indexKey_some hj)

theorem indexKey_length {i : Nat} (hi : i < 2 ^ 64) :
    ((encodeScalar i).getD []).length ≤ 32 := by
  have := encodeScalar_length_le (k := 8) (by simpa using hi) (indexKey_some hi)
  omega

/-- What the ordered map holds at item `i`'s key: item `i`. -/
theorem get_orderedMap {items : List Bytes} (hn : items.length ≤ 2 ^ 64) {i : Nat}
    (hi : i < items.length) :
    Spec.Mpt.Trie.get (orderedMap items) ((encodeScalar i).getD []) = .value items[i] := by
  unfold Spec.Mpt.Trie.get orderedMap
  rw [List.find?_map]
  have : List.find? ((fun p : Bytes × Bytes => decide (p.1 = (encodeScalar i).getD [])) ∘
      fun vi : Bytes × Nat => ((encodeScalar vi.2).getD [], vi.1)) items.zipIdx =
      some (items[i], i) := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, i, by simpa using hi, by simp, fun j hj => ?_⟩
    simp only [Function.comp_apply, List.getElem_zipIdx, Nat.zero_add, Bool.not_eq_true',
      decide_eq_false_iff_not]
    intro h
    have := indexKey_injective (by omega) (by omega) h
    omega
  rw [this]
  rfl

/-- The ordered map of at most 2^64 items, each nonempty and below 4 GiB, is `WellFormed`. -/
theorem wellFormed_orderedMap {items : List Bytes} (hn : items.length ≤ 2 ^ 64)
    (hv : ∀ x ∈ items, x ≠ [] ∧ x.length < 2 ^ 32) :
    Spec.Mpt.Trie.WellFormed (orderedMap items) := by
  constructor
  · intro p hp
    obtain ⟨vi, hvi, rfl⟩ := List.mem_map.mp hp
    have := List.snd_lt_of_mem_zipIdx hvi
    exact indexKey_length (by simp at this; omega)
  · intro p hp
    obtain ⟨vi, hvi, rfl⟩ := List.mem_map.mp hp
    exact hv vi.1 (List.fst_mem_of_mem_zipIdx hvi)

/-- **Item `i` under the root that runs.** Under the root `orderedRoot` builds from at most 2^64
items whose payloads are nonempty and below 4 GiB, `Spec.Mpt.lookup` accepts the model's proof
of `rlp(i)` and reads item `i`'s payload. -/
theorem orderedRoot_lookupB {bs : ByteArray} {items : List Span}
    (hv : ∀ s ∈ items, (valueOf bs s).size ≠ 0 ∧ (valueOf bs s).size < 2 ^ 32)
    (hn : items.length ≤ 2 ^ 64) {r : ByteArray} (hr : orderedRoot bs items = some r) {i : Nat}
    (hi : i < items.length) :
    Spec.Mpt.lookup (toL r) ((encodeScalar i).getD [])
        (Spec.Mpt.Trie.proofOf (orderedMap (items.map fun s => (valueOf bs s).data.toList))
          ((encodeScalar i).getD [])) =
      some (.value (valueOf bs items[i]).data.toList) := by
  have hw : Spec.Mpt.Trie.WellFormed
      (orderedMap (items.map fun s => (valueOf bs s).data.toList)) :=
    wellFormed_orderedMap (by simpa using hn) (by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h0, h32⟩ := hv s hs
      exact ⟨fun h => h0 (by simpa using congrArg List.length h), by simpa using h32⟩)
  have hroot : toL r = Spec.Mpt.Trie.root
      (orderedMap (items.map fun s => (valueOf bs s).data.toList)) := orderedRoot_eq hr
  rw [hroot, Spec.Mpt.Trie.lookup_complete hw (indexKey_length (by omega)),
    get_orderedMap (by simpa using hn) (by simpa using hi)]
  simp

/-- **Soundness under the root that runs.** A proof `Spec.Mpt.lookup` accepts for `rlp(i)` under
the root `orderedRoot` builds reads item `i`, or it and the model's proof are two different byte
strings with one Keccak-256 (`Spec.Mpt.collision`). -/
theorem orderedRoot_soundB {bs : ByteArray} {items : List Span}
    (hv : ∀ s ∈ items, (valueOf bs s).size ≠ 0 ∧ (valueOf bs s).size < 2 ^ 32)
    (hn : items.length ≤ 2 ^ 64) {r : ByteArray} (hr : orderedRoot bs items = some r) {i : Nat}
    (hi : i < items.length) {p : Bytes} {f : Spec.Mpt.Found}
    (hp : Spec.Mpt.lookup (toL r) ((encodeScalar i).getD []) p = some f) :
    f = .value (valueOf bs items[i]).data.toList ∨
      Spec.Mpt.IsCollision (Spec.Mpt.collision (toL r) ((encodeScalar i).getD []) p
        (Spec.Mpt.Trie.proofOf (orderedMap (items.map fun s => (valueOf bs s).data.toList))
          ((encodeScalar i).getD []))) := by
  by_cases hf : f = .value (valueOf bs items[i]).data.toList
  · exact .inl hf
  · exact .inr (Spec.Mpt.binding hp (orderedRoot_lookupB hv hn hr hi) hf)

end LeanLight.Lc.Trie
