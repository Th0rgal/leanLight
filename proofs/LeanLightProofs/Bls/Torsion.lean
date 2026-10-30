import LeanLightProofs.Bls.CofactorPrimes
import LeanLightProofs.Bls.Curves
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.QuotientGroup

/-!
# BLS12-381: the twist's cardinality and cofactor clearing (25c)

The twist curve `E'(𝔽_{p²})` has order `h₂ · r` (`card_E2`), proved without Hasse's theorem:

* **The upper bound** (`card_E2_le`): `pointCode` maps `0` to `none` and `(x, y)` to
  `(x, y = chosenY x)`, injecting `E'(𝔽_{p²})` into `Option (𝔽_{p²} × Bool)`, so `E'(𝔽_{p²})` is
  finite of cardinality at most `2 p² + 1` (counted via `Nat.card`, with no `Fintype` instance).
* **The torsion witnesses**: eight points of `E'(𝔽_{p²})` (`q13`, `independent13`, `q23`,
  `independent23`, `q2713`, `q11953`, `q262069`, `qLarge`), certified on `E'` and annihilated by
  their prime orders by the kernel running `G2J.mulA`, with the `13`- and `23`-pairs independent
  (`G2J.eq_iff_toAffine_eq`). Together with `g2Gen_order` and pairwise coprimality, `h₂ · r`
  divides `|E'(𝔽_{p²})|`; since `p² < h₂ · r`, `|E'(𝔽_{p²})| = h₂ · r`.
* **Cofactor clearing** (`h2_dvd_hEff`, `nsmul_R_hEff_eq_zero`): `h₂ ∣ h_eff`, so `[h_eff]` sends
  every point of `E'(𝔽_{p²})` into the `r`-torsion subgroup `G2`.

Adapted from `EthLib/Cryptography/Proofs/Bls/CofactorCardinality.lean`, `CofactorSpan.lean`,
`CofactorIndependence.lean`, and `CofactorPoint*.lean` of `github.com/ethereum/EthLib` at commit
`b4480f4f297301d72f97dfb6ca4ccfa8600fb061`, dedicated to the public domain under CC0-1.0
(`LeanLightProofs/Vendor/EthLib/LICENSE`).
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

private noncomputable def chosenY (x : GFp2) : GFp2 := by
  classical
  exact if h : ∃ y, E2.toAffine.Nonsingular x y then Classical.choose h else 0

private theorem chosenY_valid {x y : GFp2} (h : E2.toAffine.Nonsingular x y) :
    E2.toAffine.Nonsingular x (chosenY x) := by
  have he : ∃ y, E2.toAffine.Nonsingular x y := ⟨y, h⟩
  simpa only [chosenY, dite_eq_left he] using Classical.choose_spec he

private theorem y_eq_or_neg_chosen {x y : GFp2} (h : E2.toAffine.Nonsingular x y) :
    y = chosenY x ∨ y = -(chosenY x) := by
  have h1 := E2_nonsingular_iff.mp ((nonsingular_some ..).mpr h)
  have h2 := E2_nonsingular_iff.mp ((nonsingular_some ..).mpr (chosenY_valid h))
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (h1.trans h2.symm)

/-- Maps `0` to `none` and `(x, y)` to `some (x, y = chosenY x)`. -/
noncomputable def pointCode : E2.toAffine.Point → Option (GFp2 × Bool) := by
  classical
  exact fun p => match p with
    | .zero => none
    | .some x y _ => some (x, decide (y = chosenY x))

theorem pointCode_injective : Function.Injective pointCode := by
  classical
  intro p q h
  cases p with
  | zero => cases q <;> simp_all [pointCode]
  | some x y hp =>
    cases q with
    | zero => simp [pointCode] at h
    | some xx yy hq =>
      have he : x = xx ∧ decide (y = chosenY x) = decide (yy = chosenY xx) := by
        simpa only [pointCode, Option.some.injEq, Prod.mk.injEq] using h
      rcases he with ⟨rfl, he⟩
      have hy : y = yy := by
        by_cases hy : y = chosenY x
        · have hyy : yy = chosenY x := of_decide_eq_true
            (by simpa only [hy, decide_true] using he.symm)
          exact hy.trans hyy.symm
        · have hyy : yy ≠ chosenY x := of_decide_eq_false
            (by simpa only [decide_eq_false hy] using he.symm)
          exact ((y_eq_or_neg_chosen hp).resolve_left hy).trans
            ((y_eq_or_neg_chosen hq).resolve_left hyy).symm
      subst yy
      rfl

instance : Finite E2.toAffine.Point := Finite.of_injective pointCode pointCode_injective

/-- Elementary upper bound `|E'(𝔽_{p²})| ≤ 2 p² + 1` via `pointCode`. -/
theorem card_E2_le : Nat.card E2.toAffine.Point ≤ 2 * P ^ 2 + 1 := by
  have h := Nat.card_le_card_of_injective pointCode pointCode_injective
  rw [Finite.card_option, Nat.card_prod, card_GFp2,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  simpa only [Nat.mul_comm] using h

/-- The cofactor `h₂ = 13² · 23² · 2713 · 11953 · 262069 · largePrime` of `E'(𝔽_{p²})`. -/
def h2 : Nat := 13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069 * largePrime

namespace G2J

/-- Runtime projective equality `G2J.eq` agrees with affine point equality on reduced nonsingular
triples. -/
theorem eq_iff_toAffine_eq {p q : G2J} (hp : p.Reduced) (hq : q.Reduced)
    (hnp : E2.Nonsingular p.toJ) (hnq : E2.Nonsingular q.toJ) :
    p.eq q = true ↔ Point.toAffine E2 p.toJ = Point.toAffine E2 q.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp
  obtain ⟨hx', hy', hz'⟩ := hq
  unfold eq
  by_cases hpz : p.z.isZero = true
  · rw [ite_eq_left hpz, show q.z.isZero = q.isInf from rfl, isInf_iff_zero ⟨hx', hy', hz'⟩ hnq,
      Point.toAffine_of_Z_eq_zero (P := p.toJ) ((Fp2.isZero_iff hz).mp hpz), eq_comm]
  rw [ite_eq_right hpz]
  have hpz' : p.toJ 2 ≠ 0 := fun h => hpz ((Fp2.isZero_iff hz).mpr h)
  by_cases hqz : q.z.isZero = true
  · rw [ite_eq_left hqz, Point.toAffine_of_Z_eq_zero (P := q.toJ) ((Fp2.isZero_iff hz').mp hqz),
      Point.toAffine_of_Z_ne_zero hnp hpz']
    simp only [Bool.false_eq_true, Affine.Point.some_ne_zero]
  rw [ite_eq_right hqz]
  have hqz' : q.toJ 2 ≠ 0 := fun h => hqz ((Fp2.isZero_iff hz').mpr h)
  rw [Bool.and_eq_true, Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul,
    Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul,
    Point.toAffine_of_Z_ne_zero hnp hpz', Point.toAffine_of_Z_ne_zero hnq hqz',
    Affine.Point.some.injEq]
  fp2_push
  rw [← X_eq_iff hpz' hqz', ← Y_eq_iff hpz' hqz']
  simp only [toJ_0, toJ_1, toJ_2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linear_combination h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linear_combination h1, by linear_combination h2⟩

end G2J

private theorem nsmul_zero_cert {p : G2A} (hp : p.Reduced)
    (hn : E2.Nonsingular p.toJ) (n : ℕ) (hc : (G2J.mulA p n).isInf = true) :
    n • Point.toAffine E2 p.toJ = 0 := by
  obtain ⟨hr, hn', he⟩ := G2J.mulA_spec hp hn n
  rw [← he]
  exact (G2J.isInf_iff_zero hr hn').mp hc

private theorem affine_nonzero {p : G2A} (hn : E2.Nonsingular p.toJ) :
    Point.toAffine E2 p.toJ ≠ 0 := by
  rw [show p.toJ = ![p.x.toGF, p.y.toGF, 1] from rfl, Point.toAffine_some hn]
  exact Affine.Point.some_ne_zero _

private theorem not_nsmul_cert {p q : G2A} (hp : p.Reduced) (hq : q.Reduced)
    (hnp : E2.Nonsingular p.toJ) (hnq : E2.Nonsingular q.toJ) (n : ℕ)
    (hc : (G2J.ofAffine q).eq (G2J.mulA p n) = false) :
    Point.toAffine E2 q.toJ ≠ n • Point.toAffine E2 p.toJ := by
  obtain ⟨hr, hn, he⟩ := G2J.mulA_spec hp hnp n
  have hj : (G2J.ofAffine q).toJ = q.toJ := by
    funext i; fin_cases i <;> simp [G2J.toJ, G2J.ofAffine, G2A.toJ]
  intro h
  have ht := (G2J.eq_iff_toAffine_eq ⟨hq.1, hq.2, Fp2.reduced_one⟩ hr
    (by rw [hj]; exact hnq) hn).mpr (by rw [hj, he]; exact h)
  rw [hc] at ht
  cases ht

private theorem prime_dvd_card_of_annihilated {G : Type*} [AddCommGroup G]
    {q : ℕ} (hq : q.Prime) (p : G) (hp : q • p = 0) (hne : p ≠ 0) :
    q ∣ Nat.card G := by
  let _ : Fact q.Prime := ⟨hq⟩
  rw [← addOrderOf_eq_prime hp hne]
  exact addOrderOf_dvd_natCard p

private theorem prime_sq_dvd_card_of_independent {G : Type*} [AddCommGroup G] [Finite G]
    {q : ℕ} (hq : q.Prime) (p s : G) (hp : q • p = 0) (hs : q • s = 0)
    (hne : p ≠ 0) (hind : ∀ i : Fin q, s ≠ i.val • p) : q ^ 2 ∣ Nat.card G := by
  classical
  let _ : Fact q.Prime := ⟨hq⟩
  have hpord : addOrderOf p = q := addOrderOf_eq_prime hp hne
  let S : AddSubgroup G := AddSubgroup.zmultiples p
  have hnotmem : s ∉ S := by
    intro hm
    change s ∈ AddSubgroup.zmultiples p at hm
    rw [mem_zmultiples_iff_mem_range_addOrderOf, hpord] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact hind ⟨i, Finset.mem_range.mp hi⟩ he.symm
  have hquot : q • (QuotientAddGroup.mk s : G ⧸ S) = 0 := by
    change q • (QuotientAddGroup.mk' S s) = 0
    rw [← map_nsmul, hs, map_zero]
  have hquotne : (QuotientAddGroup.mk s : G ⧸ S) ≠ 0 := by
    intro h
    exact hnotmem ((QuotientAddGroup.eq_zero_iff s).mp h)
  have hdiv := prime_dvd_card_of_annihilated hq _ hquot hquotne
  rw [S.card_eq_card_quotient_mul_card_addSubgroup,
    show Nat.card S = q by dsimp [S]; rw [Nat.card_zmultiples, hpord]]
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  rw [hk]
  ring

namespace Torsion

def q13 : G2A :=
  ⟨⟨1516098791699854445898040942928908183909589580246243101257906827426941180554051446550909392579893885218899574105342,
    3238348490633667398671220956466993747193162347072298219945119514673806511256992531672936690515562397981251002873140⟩,
   ⟨1335703926339566895459396325186780453917867606042000656714301712043796819408375335349836437088055061353604837545944,
    2109266869945624999895480995372359165588627724687444010520175867072438469009929776678291010240416096404626491488021⟩⟩

def independent13 : G2A :=
  ⟨⟨3785287291595963449363006157517216238553350702866930745119159863557026318432990055432590987617994111761605730590096,
    184693031912202050728408694521708133615870844071267710200043165266197174504058993766601268896503937827921675108037⟩,
   ⟨2195351338994857125885432308745262298009915734180443935023142416529216833251357026902328260293191354579154915458365,
    1169630515586987845958993562785169716010090905281211931821796767787587650059725646863962186262369911948032443419257⟩⟩

def q23 : G2A :=
  ⟨⟨2739514132123941011419517956760862005679983982245647736180827416338821616902655461283968649770562245565651778429134,
    2808334985466809599109983998418602290148679938845248472406492739371341701874467784583103417930025166484777514627271⟩,
   ⟨823838782298367016162934668769581913696070428562677941071263521524279588658526909716995604446071443076365015951250,
    2031906053439228426992397463759315426993470729766381570058783639267049648019329365797683926182988977613511984373688⟩⟩

def independent23 : G2A :=
  ⟨⟨2709995428003268608871894472228856346337839268359478051610933685877360518813348186307165653556980764463340627527317,
    3554443526158050189626448917867136396708755108860714478547527567704052590003136535872275788661066543853688497564247⟩,
   ⟨1473716000648057153732370793749569872625382979758951807858832989805910300066502167700706499893185223611335808515777,
    3344235560376118688516689358070514142701873435005234113818031012772657324870196060098815547126141301608517003735704⟩⟩

def q2713 : G2A :=
  ⟨⟨2080236299627846373313113152824626203828184878063747179226546086444465609661079682578791473829990551645806380696196,
    3052341607489697950751387535491288379717343093870489916200010831014739062904699435842761599142350073607242643439346⟩,
   ⟨138786684136621197043348134664970982874021436480982065149993747241869262426861989119475052140103788150961461939542,
    259935730919452527837578491626280728785308707164694630602396646913616192390693965039250352290890968067282376421371⟩⟩

def q11953 : G2A :=
  ⟨⟨3326039129978847390790895384478687990261604743660595966617629581407403980239182135876795661655021205373622298170592,
    46869467146548478527694938494365300357293527333765386730280567959420038413149881837924443320450215905785660061369⟩,
   ⟨1132298756428184765003661052478247226395618160691419912279189534963795943103439813278630167376312089258869064647885,
    2270702702637852964440832104507229096623166001003608211729388228622052313321327540920170329339284344643394921561805⟩⟩

def q262069 : G2A :=
  ⟨⟨445689349790021496226481610041960119670818562344445314198349534378437798461866468235427851300387466736185843810614,
    642130957506457077337037835884583121750509984993480752870042996214680726133991353560451529535834214250305831471661⟩,
   ⟨3689501235694109950530354610934256590544644337586092604586486870082856386990140772018231157092461477750358316929703,
    3689569798356755572404451911002206581319892419086545502402118524503951312562101915464666252217297686865197893821263⟩⟩

def qLarge : G2A :=
  ⟨⟨1592116047283719468669193162030467753456694847234708179870476801025438070458019633474731003990186295259901501546861,
    2685483867292967829500309692339442019865065526160693435280091690226906840485243676872892132082982750579013295285380⟩,
   ⟨2153227564488006655201801380203143865235357625215362982019169134884644306246884712257357377457997472008781237721174,
    3045953118673494913655837492927771364176209721199360415909813293948466421781853948458745690208773373209972542695613⟩⟩

theorem q13_reduced : q13.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem independent13_reduced : independent13.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem q23_reduced : q23.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem independent23_reduced : independent23.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem q2713_reduced : q2713.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem q11953_reduced : q11953.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem q262069_reduced : q262069.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩
theorem qLarge_reduced : qLarge.Reduced :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩

theorem q13_nonsingular : E2.Nonsingular q13.toJ :=
  (G2A.onCurve_iff q13_reduced).mp (by decide +kernel)
theorem independent13_nonsingular : E2.Nonsingular independent13.toJ :=
  (G2A.onCurve_iff independent13_reduced).mp (by decide +kernel)
theorem q23_nonsingular : E2.Nonsingular q23.toJ :=
  (G2A.onCurve_iff q23_reduced).mp (by decide +kernel)
theorem independent23_nonsingular : E2.Nonsingular independent23.toJ :=
  (G2A.onCurve_iff independent23_reduced).mp (by decide +kernel)
theorem q2713_nonsingular : E2.Nonsingular q2713.toJ :=
  (G2A.onCurve_iff q2713_reduced).mp (by decide +kernel)
theorem q11953_nonsingular : E2.Nonsingular q11953.toJ :=
  (G2A.onCurve_iff q11953_reduced).mp (by decide +kernel)
theorem q262069_nonsingular : E2.Nonsingular q262069.toJ :=
  (G2A.onCurve_iff q262069_reduced).mp (by decide +kernel)
theorem qLarge_nonsingular : E2.Nonsingular qLarge.toJ :=
  (G2A.onCurve_iff qLarge_reduced).mp (by decide +kernel)

theorem q13_annihilator : 13 • Point.toAffine E2 q13.toJ = 0 :=
  nsmul_zero_cert q13_reduced q13_nonsingular 13 (by decide +kernel)
theorem independent13_annihilator : 13 • Point.toAffine E2 independent13.toJ = 0 :=
  nsmul_zero_cert independent13_reduced independent13_nonsingular 13 (by decide +kernel)
theorem q23_annihilator : 23 • Point.toAffine E2 q23.toJ = 0 :=
  nsmul_zero_cert q23_reduced q23_nonsingular 23 (by decide +kernel)
theorem independent23_annihilator : 23 • Point.toAffine E2 independent23.toJ = 0 :=
  nsmul_zero_cert independent23_reduced independent23_nonsingular 23 (by decide +kernel)
theorem q2713_annihilator : 2713 • Point.toAffine E2 q2713.toJ = 0 :=
  nsmul_zero_cert q2713_reduced q2713_nonsingular 2713 (by decide +kernel)
theorem q11953_annihilator : 11953 • Point.toAffine E2 q11953.toJ = 0 :=
  nsmul_zero_cert q11953_reduced q11953_nonsingular 11953 (by decide +kernel)
theorem q262069_annihilator : 262069 • Point.toAffine E2 q262069.toJ = 0 :=
  nsmul_zero_cert q262069_reduced q262069_nonsingular 262069 (by decide +kernel)
theorem qLarge_annihilator : largePrime • Point.toAffine E2 qLarge.toJ = 0 :=
  nsmul_zero_cert qLarge_reduced qLarge_nonsingular largePrime (by decide +kernel)

theorem independent13_not_span (i : Fin 13) :
    Point.toAffine E2 independent13.toJ ≠ i.val • Point.toAffine E2 q13.toJ := by
  have hc : ∀ i : Fin 13, (G2J.ofAffine independent13).eq (G2J.mulA q13 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q13_reduced independent13_reduced q13_nonsingular
    independent13_nonsingular i.val (hc i)

theorem independent23_not_span (i : Fin 23) :
    Point.toAffine E2 independent23.toJ ≠ i.val • Point.toAffine E2 q23.toJ := by
  have hc : ∀ i : Fin 23, (G2J.ofAffine independent23).eq (G2J.mulA q23 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q23_reduced independent23_reduced q23_nonsingular
    independent23_nonsingular i.val (hc i)

end Torsion

export Torsion (q13 independent13 q23 independent23 q2713 q11953 q262069 qLarge)
open Torsion

private theorem h2_mul_R_dvd : h2 * R ∣ Nat.card E2.toAffine.Point := by
  have h13 : 13 ^ 2 ∣ Nat.card E2.toAffine.Point :=
    prime_sq_dvd_card_of_independent prime_13 _ _ q13_annihilator independent13_annihilator
      (affine_nonzero q13_nonsingular) independent13_not_span
  have h23 : 23 ^ 2 ∣ Nat.card E2.toAffine.Point :=
    prime_sq_dvd_card_of_independent prime_23 _ _ q23_annihilator independent23_annihilator
      (affine_nonzero q23_nonsingular) independent23_not_span
  have h2713 : 2713 ∣ Nat.card E2.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_2713 _ q2713_annihilator (affine_nonzero q2713_nonsingular)
  have h11953 : 11953 ∣ Nat.card E2.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_11953 _ q11953_annihilator
      (affine_nonzero q11953_nonsingular)
  have h262069 : 262069 ∣ Nat.card E2.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_262069 _ q262069_annihilator
      (affine_nonzero q262069_nonsingular)
  have hlarge : largePrime ∣ Nat.card E2.toAffine.Point :=
    prime_dvd_card_of_annihilated largePrime_prime _ qLarge_annihilator
      (affine_nonzero qLarge_nonsingular)
  have hr : R ∣ Nat.card E2.toAffine.Point := by
    rw [← g2Gen_order]
    exact addOrderOf_dvd_natCard _
  have c1 := (show Nat.Coprime (13 ^ 2) (23 ^ 2) by decide +kernel).mul_dvd_of_dvd_of_dvd h13 h23
  have c2 := (show Nat.Coprime (13 ^ 2 * 23 ^ 2) 2713 by decide +kernel).mul_dvd_of_dvd_of_dvd
    c1 h2713
  have c3 := (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713) 11953 by
    decide +kernel).mul_dvd_of_dvd_of_dvd c2 h11953
  have c4 := (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713 * 11953) 262069 by
    decide +kernel).mul_dvd_of_dvd_of_dvd c3 h262069
  have c5 : h2 ∣ Nat.card E2.toAffine.Point :=
    (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069) largePrime by
      decide +kernel).mul_dvd_of_dvd_of_dvd c4 hlarge
  exact (show Nat.Coprime h2 R by decide +kernel).mul_dvd_of_dvd_of_dvd c5 hr

private theorem P_sq_lt_h2_mul_R : P ^ 2 < h2 * R := by decide +kernel

/-- `|E'(𝔽_{p²})| = h₂ · r`, by the eight torsion witnesses and `card_E2_le`. -/
theorem card_E2 : Nat.card E2.toAffine.Point = h2 * R := by
  obtain ⟨k, hk⟩ := h2_mul_R_dvd
  have hcpos : 0 < Nat.card E2.toAffine.Point := Nat.card_pos
  have hnpos : 0 < h2 * R := Nat.lt_of_le_of_lt (Nat.zero_le _) P_sq_lt_h2_mul_R
  have hbound : Nat.card E2.toAffine.Point < 2 * (h2 * R) := by
    have := card_E2_le
    have := P_sq_lt_h2_mul_R
    omega
  have hk0 : k ≠ 0 := by intro hz; rw [hz, Nat.mul_zero] at hk; omega
  have hk2 : k < 2 := by
    apply (Nat.mul_lt_mul_left hnpos).mp
    rw [← hk, Nat.mul_comm (h2 * R) 2]
    exact hbound
  have hk1 : k = 1 := by omega
  simpa only [hk1, Nat.mul_one] using hk

/-- `h₂ ∣ h_eff`, checked in the kernel. -/
theorem h2_dvd_hEff : h2 ∣ hEff := Nat.dvd_of_mod_eq_zero (by decide +kernel)

/-- `[h_eff]` maps every point of `E'(𝔽_{p²})` into the `r`-torsion subgroup. -/
theorem nsmul_R_hEff_eq_zero (Q : E2.toAffine.Point) : R • (hEff • Q) = 0 := by
  obtain ⟨k, hk⟩ := h2_dvd_hEff
  rw [← mul_smul, hk, show R * (h2 * k) = k * (h2 * R) by ring, mul_smul, ← card_E2,
    card_nsmul_eq_zero', smul_zero]

end LeanLight.Lc.Bls
