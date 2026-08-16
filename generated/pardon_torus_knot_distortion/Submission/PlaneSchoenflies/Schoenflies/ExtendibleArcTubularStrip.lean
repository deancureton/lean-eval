import Submission.PlaneSchoenflies.Schoenflies.Main
import Submission.PlaneSchoenflies.Schoenflies.PolygonalPaths
import Submission.PlaneSchoenflies.Schoenflies.TrimmedHairCrosscuts
import Submission.PlaneSchoenflies.Schoenflies.TwoArcCarrierHomeomorph

/-!
# Extendible planar arcs: tails, trimming, and an auxiliary Jordan curve

This file isolates the low-level topology needed before one can construct a tubular strip around
an embedded planar arc.  An `ExtendibleInjectivePath` is an injective path with the displayed arc
strictly inside its parameter interval.  Its two closed tails meet the core only at the expected
endpoint.  A separate connector may then be trimmed by arbitrary closed endpoint sets, and an
honest simple return path produces a two-arc Jordan circle.

Nothing here assumes that an arbitrary embedded arc is tame or locally flat.  Instead, the strict
extension hypothesis closes the core with an avoiding return arc.  Exact boundary control in the
proved Moise--Schoenflies theorem then gives an ambient straightener preserving the core parameter.
An explicit product rectangle, with rational tails fixed on the horizontal seam, yields an open
tubular strip inside every prescribed neighborhood of the core.
-/

namespace Schoenflies

open Function Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

variable {a b : Plane}

private theorem convexComb_injective {u v : unitInterval} (huv : u < v) :
    Injective (Icc.convexComb u v) := by
  intro s t hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hst
  simp only [Icc.coe_convexComb] at hval
  have hfactor :
      ((s : ℝ) - t) * ((v : ℝ) - u) = 0 := by
    nlinarith
  have hvu : (v : ℝ) - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have hst : (s : ℝ) - t = 0 := (mul_eq_zero.mp hfactor).resolve_right hvu
  exact sub_eq_zero.mp hst

/-! ## A line-to-interval homeomorphism fixed on the displayed core -/

namespace FixedCoreSqueeze

/-- Rational tails squeeze the line into `(-1-δ, 1+δ)` while leaving `[-1,1]`
pointwise fixed. -/
def squeeze (δ x : ℝ) : ℝ :=
  if x < -1 then -1 - δ - δ / x else if x ≤ 1 then x else 1 + δ - δ / x

/-- The explicit inverse of `squeeze` on its open image interval. -/
def unsqueeze (δ y : ℝ) : ℝ :=
  if y < -1 then -δ / (y + 1 + δ) else if y ≤ 1 then y else δ / (1 + δ - y)

theorem squeeze_eq_self {δ x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    squeeze δ x = x := by
  simp [squeeze, not_lt_of_ge hx₀, hx₁]

private theorem squeeze_left_lt_neg_one {δ x : ℝ} (hδ : 0 < δ) (hx : x < -1) :
    squeeze δ x < -1 := by
  rw [squeeze, if_pos hx]
  have hxneg : x < 0 := hx.trans (by norm_num)
  have hinv : (-1 : ℝ) < 1 / x := by
    simpa using one_div_lt_one_div_of_neg_of_lt (by norm_num : (-1 : ℝ) < 0) hx
  have hmul := mul_lt_mul_of_pos_left hinv hδ
  rw [mul_neg, mul_one, mul_one_div] at hmul
  linarith

private theorem neg_one_lt_squeeze_right {δ x : ℝ} (hδ : 0 < δ) (hx : 1 < x) :
    1 < squeeze δ x := by
  rw [squeeze, if_neg (by linarith), if_neg (not_le_of_gt hx)]
  have hinv : 1 / x < (1 : ℝ) := (div_lt_one (by linarith)).mpr hx
  have hmul := mul_lt_mul_of_pos_left hinv hδ
  rw [mul_one_div, mul_one] at hmul
  linarith

theorem squeeze_mem_Ioo {δ x : ℝ} (hδ : 0 < δ) :
    squeeze δ x ∈ Ioo (-1 - δ) (1 + δ) := by
  by_cases hx₀ : x < -1
  · constructor
    · rw [squeeze, if_pos hx₀]
      have hxneg : x < 0 := hx₀.trans (by norm_num)
      have hdiv : δ / x < 0 := div_neg_of_pos_of_neg hδ hxneg
      linarith
    · exact (squeeze_left_lt_neg_one hδ hx₀).trans (by linarith)
  · by_cases hx₁ : x ≤ 1
    · rw [squeeze_eq_self (le_of_not_gt hx₀) hx₁]
      constructor <;> linarith
    · constructor
      · exact (by linarith : -1 - δ < (1 : ℝ)).trans
          (neg_one_lt_squeeze_right hδ (lt_of_not_ge hx₁))
      · rw [squeeze, if_neg hx₀, if_neg hx₁]
        have hxpos : 0 < x := by linarith
        have hdiv : 0 < δ / x := div_pos hδ hxpos
        linarith

private theorem squeeze_strictMono {δ : ℝ} (hδ : 0 < δ) : StrictMono (squeeze δ) := by
  intro x y hxy
  by_cases hy₀ : y < -1
  · have hx₀ : x < -1 := hxy.trans hy₀
    rw [squeeze, if_pos hx₀, squeeze, if_pos hy₀]
    have hxneg : x < 0 := hx₀.trans (by norm_num)
    have hyneg : y < 0 := hy₀.trans (by norm_num)
    have hinv : 1 / y < 1 / x := one_div_lt_one_div_of_neg_of_lt hyneg hxy
    have hmul := mul_lt_mul_of_pos_left hinv hδ
    rw [mul_one_div, mul_one_div] at hmul
    linarith
  · by_cases hx₀ : x < -1
    · exact (squeeze_left_lt_neg_one hδ hx₀).trans_le (by
        by_cases hy₁ : y ≤ 1
        · rw [squeeze_eq_self (le_of_not_gt hy₀) hy₁]
          exact le_of_not_gt hy₀
        · exact (by linarith : -1 ≤ (1 : ℝ)).trans
            (neg_one_lt_squeeze_right hδ (lt_of_not_ge hy₁)).le)
    · by_cases hy₁ : y ≤ 1
      · rw [squeeze_eq_self (le_of_not_gt hx₀) (hxy.le.trans hy₁),
          squeeze_eq_self (le_of_not_gt hy₀) hy₁]
        exact hxy
      · by_cases hx₁ : x ≤ 1
        · rw [squeeze_eq_self (le_of_not_gt hx₀) hx₁]
          exact hx₁.trans_lt
            (neg_one_lt_squeeze_right hδ (lt_of_not_ge hy₁))
        · rw [squeeze, if_neg hx₀, if_neg hx₁,
            squeeze, if_neg hy₀, if_neg hy₁]
          have hxpos : 0 < x := by linarith
          have hinv : 1 / y < 1 / x := one_div_lt_one_div (by linarith) hxpos |>.mpr hxy
          have hmul := mul_lt_mul_of_pos_left hinv hδ
          rw [mul_one_div, mul_one_div] at hmul
          linarith

private theorem squeeze_unsqueeze {δ y : ℝ} (hδ : 0 < δ)
    (hy : y ∈ Ioo (-1 - δ) (1 + δ)) : squeeze δ (unsqueeze δ y) = y := by
  by_cases hy₀ : y < -1
  · have hden : 0 < y + 1 + δ := by linarith [hy.1]
    have hden_lt : y + 1 + δ < δ := by linarith
    have hquot : 1 < δ / (y + 1 + δ) := (one_lt_div hden).mpr hden_lt
    have hx : -δ / (y + 1 + δ) < -1 := by
      rw [neg_div]
      linarith
    rw [unsqueeze, if_pos hy₀, squeeze, if_pos hx]
    field_simp [ne_of_gt hden]
    ring
  · by_cases hy₁ : y ≤ 1
    · rw [unsqueeze, if_neg hy₀, if_pos hy₁,
        squeeze_eq_self (le_of_not_gt hy₀) hy₁]
    · have hden : 0 < 1 + δ - y := by linarith [hy.2]
      have hden_lt : 1 + δ - y < δ := by linarith
      have hx : 1 < δ / (1 + δ - y) := (one_lt_div hden).mpr hden_lt
      rw [unsqueeze, if_neg hy₀, if_neg hy₁, squeeze,
        if_neg (by linarith), if_neg (not_le_of_gt hx)]
      field_simp [ne_of_gt hden]
      ring

/-- Order isomorphism from the line onto a slightly wider interval which is literally the
identity on the closed core interval `[-1,1]`. -/
noncomputable def intervalOrderIso (δ : ℝ) (hδ : 0 < δ) :
    ℝ ≃o Ioo (-1 - δ) (1 + δ) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x ↦ ⟨squeeze δ x, squeeze_mem_Ioo hδ⟩)
    ((squeeze_strictMono hδ).codRestrict _) (fun y ↦ unsqueeze δ y) ?_
  intro y
  apply Subtype.ext
  exact squeeze_unsqueeze hδ y.2

/-- Topological form of `intervalOrderIso`. -/
noncomputable def intervalHomeomorph (δ : ℝ) (hδ : 0 < δ) :
    ℝ ≃ₜ Ioo (-1 - δ) (1 + δ) :=
  (intervalOrderIso δ hδ).toHomeomorph

theorem intervalHomeomorph_apply_of_mem_Icc {δ x : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ((intervalHomeomorph δ hδ x : Ioo (-1 - δ) (1 + δ)) : ℝ) = x := by
  exact squeeze_eq_self hx.1 hx.2

/-- Positive scaling identifies the fixed model interval `(-2,2)` with `(-ρ,ρ)`. -/
noncomputable def symmetricScaleOrderIso (ρ : ℝ) (hρ : 0 < ρ) :
    Ioo (-1 - 1 : ℝ) (1 + 1) ≃o Ioo (-ρ) ρ where
  toFun y := ⟨ρ / 2 * y, by
    constructor <;> nlinarith [y.2.1, y.2.2]⟩
  invFun z := ⟨2 / ρ * z, by
    have hzleft := mul_lt_mul_of_pos_left z.2.1 (by norm_num : (0 : ℝ) < 2)
    have hzright := mul_lt_mul_of_pos_left z.2.2 (by norm_num : (0 : ℝ) < 2)
    have hleft : (-2 : ℝ) < 2 * z / ρ := by
      rw [lt_div_iff₀ hρ]
      rw [show (-2 : ℝ) * ρ = 2 * (-ρ) by ring]
      exact hzleft
    have hright : 2 * z / ρ < (2 : ℝ) := by
      rw [div_lt_iff₀ hρ]
      exact hzright
    constructor
    · simpa only [show (-1 - 1 : ℝ) = -2 by norm_num,
        div_mul_eq_mul_div] using hleft
    · simpa only [show (1 + 1 : ℝ) = 2 by norm_num,
        div_mul_eq_mul_div] using hright⟩
  left_inv y := by
    apply Subtype.ext
    field_simp [ne_of_gt hρ]
  right_inv z := by
    apply Subtype.ext
    field_simp [ne_of_gt hρ]
  map_rel_iff' := by
    intro y z
    change ρ / 2 * (y : ℝ) ≤ ρ / 2 * (z : ℝ) ↔ (y : ℝ) ≤ (z : ℝ)
    have hscale : 0 < ρ / 2 := div_pos hρ (by norm_num)
    constructor
    · intro h
      exact le_of_mul_le_mul_left h hscale
    · intro h
      exact mul_le_mul_of_nonneg_left h hscale.le

/-- A line-to-thin-interval homeomorphism fixing the horizontal axis point `0`. -/
noncomputable def verticalHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    ℝ ≃ₜ Ioo (-ρ) ρ :=
  ((intervalOrderIso 1 zero_lt_one).trans (symmetricScaleOrderIso ρ hρ)).toHomeomorph

theorem verticalHomeomorph_apply_zero (ρ : ℝ) (hρ : 0 < ρ) :
    ((verticalHomeomorph ρ hρ 0 : Ioo (-ρ) ρ) : ℝ) = 0 := by
  change ρ / 2 * squeeze 1 0 = 0
  rw [squeeze_eq_self (by norm_num) (by norm_num)]
  ring

end FixedCoreSqueeze

/-- Coordinates identify the Euclidean plane with a product of two real lines. -/
noncomputable def planeCoordinates : Plane ≃ₜ ℝ × ℝ where
  toFun z := (z 0, z 1)
  invFun p := planePoint p.1 p.2
  left_inv z := by
    apply plane_ext <;> simp
  right_inv p := by
    ext <;> simp
  continuous_toFun :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 ↦ ℝ) 0).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 ↦ ℝ) 1)
  continuous_invFun := by
    change Continuous fun p : ℝ × ℝ ↦ WithLp.toLp 2 ![p.1, p.2]
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp ?_
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

@[simp]
theorem planeCoordinates_apply (z : Plane) : planeCoordinates z = (z 0, z 1) := rfl

@[simp]
theorem planeCoordinates_symm_apply (p : ℝ × ℝ) :
    planeCoordinates.symm p = planePoint p.1 p.2 := rfl

namespace JordanCircle

/-- The ambient Schoenflies homeomorphism chosen by the completed regional construction. -/
noncomputable def exactAmbientNormalizer (J : JordanCircle) : Plane ≃ₜ Plane :=
  J.regionalExtensionData.diskExtensionData.ambientHomeomorph

/-- The regional construction sends every carrier point to its exact inverse circle parameter,
not merely to an unspecified point of the unit circle. -/
theorem exactAmbientNormalizer_apply_carrier (J : JordanCircle) {x : Plane}
    (hx : x ∈ J.carrier) :
    J.exactAmbientNormalizer x = (J.carrierHomeomorph.symm ⟨x, hx⟩ : Plane) := by
  let E := J.regionalExtensionData
  have hxi : x ∈ closure J.inside := by
    rw [J.closure_inside]
    exact Or.inr hx
  let f : C(closure J.inside, Plane) :=
    ⟨fun y ↦ E.insideHomeomorph y,
      continuous_subtype_val.comp E.insideHomeomorph.continuous⟩
  change E.diskExtensionData.ambientHomeomorph x = _
  rw [E.diskExtensionData.ambientHomeomorph_apply_curve hx]
  change (Classical.choose
    (f.exists_extension isClosed_closure.isClosedEmbedding_subtypeVal)) x = _
  have hext := Classical.choose_spec
    (f.exists_extension isClosed_closure.isClosedEmbedding_subtypeVal)
  calc
    Classical.choose
        (f.exists_extension isClosed_closure.isClosedEmbedding_subtypeVal) x =
        f ⟨x, hxi⟩ := DFunLike.congr_fun hext ⟨x, hxi⟩
    _ = (J.carrierHomeomorph.symm ⟨x, hx⟩ : Plane) := E.inside_boundary ⟨x, hx⟩

end JordanCircle

namespace TwoArcJordan

/-- Exact first-arc formula for the ambient normalizer of a two-arc Jordan circle. -/
theorem exactAmbientNormalizer_apply_first
    (p : Path a b) (q : Path b a) (hp : Injective p) (hq : Injective q)
    (hinter : range p ∩ range q = {a, b}) (t : unitInterval) :
    (toJordanCircle p q hp hq hinter).exactAmbientNormalizer (p t) =
      (circleHomeomorph (firstCoordinate t) : Plane) := by
  let J := toJordanCircle p q hp hq hinter
  have hx : p t ∈ J.carrier := by
    rw [show J.carrier = range p ∪ range q from
      carrier_toJordanCircle p q hp hq hinter]
    exact Or.inl ⟨t, rfl⟩
  have hz :
      J.carrierHomeomorph (circleHomeomorph (firstCoordinate t)) =
        ⟨p t, hx⟩ := by
    apply Subtype.ext
    change sphereMap p q (circleHomeomorph (firstCoordinate t)) = p t
    rw [sphereMap, Function.comp_apply, circleHomeomorph.symm_apply_apply,
      circleMap_firstCoordinate]
  rw [J.exactAmbientNormalizer_apply_carrier hx, ← hz,
    J.carrierHomeomorph.symm_apply_apply]

end TwoArcJordan

/-- An injective ambient path whose selected core occurs strictly after the source and strictly
before the target.  This is the honest extension hypothesis used in the arc-straightening route. -/
structure ExtendibleInjectivePath where
  extensionSource : Plane
  extensionTarget : Plane
  extension : Path extensionSource extensionTarget
  coreLeft : unitInterval
  coreRight : unitInterval
  coreLeft_pos : (0 : unitInterval) < coreLeft
  coreLeft_lt_coreRight : coreLeft < coreRight
  coreRight_lt_one : coreRight < (1 : unitInterval)
  extension_injective : Injective extension

namespace ExtendibleInjectivePath

/-- Initial and final points of the selected core. -/
def coreSource (E : ExtendibleInjectivePath) : Plane := E.extension E.coreLeft

def coreTarget (E : ExtendibleInjectivePath) : Plane := E.extension E.coreRight

/-- The selected core arc and its two closed extension tails. -/
def corePath (E : ExtendibleInjectivePath) : Path E.coreSource E.coreTarget :=
  E.extension.subpath E.coreLeft E.coreRight

def leftTailPath (E : ExtendibleInjectivePath) :
    Path (E.extension 0) E.coreSource :=
  E.extension.subpath 0 E.coreLeft

def rightTailPath (E : ExtendibleInjectivePath) :
    Path E.coreTarget (E.extension 1) :=
  E.extension.subpath E.coreRight 1

def coreRange (E : ExtendibleInjectivePath) : Set Plane :=
  E.extension '' Icc E.coreLeft E.coreRight

def leftTailRange (E : ExtendibleInjectivePath) : Set Plane :=
  E.extension '' Icc 0 E.coreLeft

def rightTailRange (E : ExtendibleInjectivePath) : Set Plane :=
  E.extension '' Icc E.coreRight 1

theorem range_corePath (E : ExtendibleInjectivePath) :
    range E.corePath = E.coreRange := by
  exact Path.range_subpath_of_le E.extension E.coreLeft E.coreRight
    E.coreLeft_lt_coreRight.le

theorem range_leftTailPath (E : ExtendibleInjectivePath) :
    range E.leftTailPath = E.leftTailRange := by
  exact Path.range_subpath_of_le E.extension 0 E.coreLeft E.coreLeft.2.1

theorem range_rightTailPath (E : ExtendibleInjectivePath) :
    range E.rightTailPath = E.rightTailRange := by
  exact Path.range_subpath_of_le E.extension E.coreRight 1 E.coreRight.2.2

theorem isClosed_leftTailRange (E : ExtendibleInjectivePath) : IsClosed E.leftTailRange := by
  exact (isCompact_Icc.image E.extension.continuous).isClosed

theorem isClosed_rightTailRange (E : ExtendibleInjectivePath) : IsClosed E.rightTailRange := by
  exact (isCompact_Icc.image E.extension.continuous).isClosed

theorem isCompact_coreRange (E : ExtendibleInjectivePath) : IsCompact E.coreRange := by
  exact isCompact_Icc.image E.extension.continuous

theorem isClosed_coreRange (E : ExtendibleInjectivePath) : IsClosed E.coreRange :=
  E.isCompact_coreRange.isClosed

theorem corePath_injective (E : ExtendibleInjectivePath) : Injective E.corePath := by
  exact E.extension_injective.comp (convexComb_injective E.coreLeft_lt_coreRight)

/-- The selected core, as a subspace, is exactly a closed interval. -/
noncomputable def coreRangeHomeomorphUnitInterval (E : ExtendibleInjectivePath) :
    E.coreRange ≃ₜ unitInterval := by
  let toRange : unitInterval → E.coreRange := fun t =>
    ⟨E.corePath t, by
      rw [← E.range_corePath]
      exact ⟨t, rfl⟩⟩
  have hcontinuous : Continuous toRange := E.corePath.continuous.subtype_mk _
  have hinjective : Injective toRange := by
    intro s t hst
    exact E.corePath_injective (congrArg Subtype.val hst)
  have hsurjective : Surjective toRange := by
    rintro ⟨x, hx⟩
    rw [← E.range_corePath] at hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t, rfl⟩
  let e₀ : unitInterval ≃ E.coreRange :=
    Equiv.ofBijective toRange ⟨hinjective, hsurjective⟩
  let e : unitInterval ≃ₜ E.coreRange :=
    Continuous.homeoOfEquivCompactToT2 (f := e₀) hcontinuous
  exact e.symm

theorem extension_zero_not_mem_coreRange (E : ExtendibleInjectivePath) :
    E.extension 0 ∉ E.coreRange := by
  rintro ⟨t, ht, hEq⟩
  have htZero : t = 0 := E.extension_injective hEq
  exact (not_le_of_gt E.coreLeft_pos) (htZero ▸ ht.1)

theorem extension_one_not_mem_coreRange (E : ExtendibleInjectivePath) :
    E.extension 1 ∉ E.coreRange := by
  rintro ⟨t, ht, hEq⟩
  have htOne : t = 1 := E.extension_injective hEq
  exact (not_le_of_gt E.coreRight_lt_one) (htOne ▸ ht.2)

theorem leftTailPath_injective (E : ExtendibleInjectivePath) : Injective E.leftTailPath := by
  exact E.extension_injective.comp (convexComb_injective E.coreLeft_pos)

theorem rightTailPath_injective (E : ExtendibleInjectivePath) :
    Injective E.rightTailPath := by
  exact E.extension_injective.comp (convexComb_injective E.coreRight_lt_one)

/-- The closed left extension tail meets the selected core only at the core source. -/
theorem leftTailRange_inter_coreRange (E : ExtendibleInjectivePath) :
    E.leftTailRange ∩ E.coreRange = {E.coreSource} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
    have hparam : u = v := E.extension_injective huv.symm
    have huEq : u = E.coreLeft := le_antisymm hu.2 (hparam ▸ hv.1)
    simp [coreSource, huEq]
  · intro hx
    have hx : x = E.coreSource := mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨E.coreLeft, ⟨E.coreLeft.2.1, le_rfl⟩, rfl⟩,
      ⟨E.coreLeft, ⟨le_rfl, E.coreLeft_lt_coreRight.le⟩, rfl⟩⟩

/-- The closed right extension tail meets the selected core only at the core target. -/
theorem coreRange_inter_rightTailRange (E : ExtendibleInjectivePath) :
    E.coreRange ∩ E.rightTailRange = {E.coreTarget} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
    have hparam : u = v := E.extension_injective huv.symm
    have huEq : u = E.coreRight := le_antisymm hu.2 (hparam ▸ hv.1)
    simp [coreTarget, huEq]
  · intro hx
    have hx : x = E.coreTarget := mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨E.coreRight, ⟨E.coreLeft_lt_coreRight.le, le_rfl⟩, rfl⟩,
      ⟨E.coreRight, ⟨le_rfl, E.coreRight.2.2⟩, rfl⟩⟩

/-- Removing the shared endpoint makes either tail strictly disjoint from the core. -/
theorem leftTailRange_sdiff_coreSource_disjoint_coreRange
    (E : ExtendibleInjectivePath) :
    Disjoint (E.leftTailRange \ {E.coreSource}) E.coreRange := by
  rw [Set.disjoint_left]
  intro x hxTail hxCore
  exact hxTail.2 (by
    rw [← E.leftTailRange_inter_coreRange]
    exact ⟨hxTail.1, hxCore⟩)

theorem coreRange_disjoint_rightTailRange_sdiff_coreTarget
    (E : ExtendibleInjectivePath) :
    Disjoint E.coreRange (E.rightTailRange \ {E.coreTarget}) := by
  rw [Set.disjoint_left]
  intro x hxCore hxTail
  exact hxTail.2 (by
    rw [← E.coreRange_inter_rightTailRange]
    exact ⟨hxCore, hxTail.1⟩)

/-- The two closed extension tails are disjoint because a nondegenerate core lies between them. -/
theorem leftTailRange_disjoint_rightTailRange (E : ExtendibleInjectivePath) :
    Disjoint E.leftTailRange E.rightTailRange := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
  have huvParam : u = v := E.extension_injective huv.symm
  have hle : E.coreRight ≤ E.coreLeft := by
    calc
      E.coreRight ≤ v := hv.1
      _ = u := huvParam.symm
      _ ≤ E.coreLeft := hu.2
  exact (not_le_of_gt E.coreLeft_lt_coreRight) hle

end ExtendibleInjectivePath

/-! ## Trimming against arbitrary closed endpoint tails -/

/-- Last contact with a closed source tail and first later contact with a disjoint closed target
tail.  This is `HairTrimData` with no Jordan-circle or access-hair structure attached. -/
structure ClosedTailTrimData (P : Path a b) (sourceTail targetTail : Set Plane) where
  sourceTime : unitInterval
  targetTime : unitInterval
  source_lt_target : sourceTime < targetTime
  source_mem : P sourceTime ∈ sourceTail
  target_mem : P targetTime ∈ targetTail
  source_greatest : ∀ t, P t ∈ sourceTail → t ≤ sourceTime
  target_least_after : ∀ t, sourceTime ≤ t → P t ∈ targetTail → targetTime ≤ t

namespace ClosedTailTrimData

def trimmedPath {P : Path a b} {sourceTail targetTail : Set Plane}
    (T : ClosedTailTrimData P sourceTail targetTail) :
    Path (P T.sourceTime) (P T.targetTime) :=
  P.subpath T.sourceTime T.targetTime

theorem trimmedPath_injective {P : Path a b} {sourceTail targetTail : Set Plane}
    (T : ClosedTailTrimData P sourceTail targetTail) (hP : Injective P) :
    Injective T.trimmedPath :=
  hP.comp (convexComb_injective T.source_lt_target)

theorem range_trimmedPath_subset {P : Path a b} {sourceTail targetTail U : Set Plane}
    (T : ClosedTailTrimData P sourceTail targetTail) (hP : range P ⊆ U) :
    range T.trimmedPath ⊆ U := by
  rw [trimmedPath, Path.range_subpath_of_le P T.sourceTime T.targetTime
    T.source_lt_target.le]
  rintro x ⟨t, -, rfl⟩
  exact hP ⟨t, rfl⟩

theorem range_trimmedPath_inter_sourceTail
    {P : Path a b} {sourceTail targetTail : Set Plane}
    (T : ClosedTailTrimData P sourceTail targetTail) :
    range T.trimmedPath ∩ sourceTail = {P T.sourceTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxRange, hxTail⟩
    rw [trimmedPath, Path.range_subpath_of_le P T.sourceTime T.targetTime
      T.source_lt_target.le] at hxRange
    obtain ⟨t, ht, rfl⟩ := hxRange
    have htEq : t = T.sourceTime := le_antisymm (T.source_greatest t hxTail) ht.1
    simp [htEq]
  · rintro x hx
    have hx : x = P T.sourceTime := mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨0, by simp [trimmedPath]⟩, T.source_mem⟩

theorem range_trimmedPath_inter_targetTail
    {P : Path a b} {sourceTail targetTail : Set Plane}
    (T : ClosedTailTrimData P sourceTail targetTail) :
    range T.trimmedPath ∩ targetTail = {P T.targetTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxRange, hxTail⟩
    rw [trimmedPath, Path.range_subpath_of_le P T.sourceTime T.targetTime
      T.source_lt_target.le] at hxRange
    obtain ⟨t, ht, rfl⟩ := hxRange
    have htEq : t = T.targetTime :=
      le_antisymm ht.2 (T.target_least_after t ht.1 hxTail)
    simp [htEq]
  · rintro x hx
    have hx : x = P T.targetTime := mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨1, by simp [trimmedPath]⟩, T.target_mem⟩

end ClosedTailTrimData

/-- Compactness supplies the generalized trimming extrema for arbitrary disjoint closed tails. -/
theorem nonempty_closedTailTrimData (P : Path a b) (sourceTail targetTail : Set Plane)
    (hsource : IsClosed sourceTail) (htarget : IsClosed targetTail)
    (hdisjoint : Disjoint sourceTail targetTail)
    (ha : a ∈ sourceTail) (hb : b ∈ targetTail) :
    Nonempty (ClosedTailTrimData P sourceTail targetTail) := by
  let E : Set unitInterval := P ⁻¹' sourceTail
  have hEcompact : IsCompact E := (hsource.preimage P.continuous).isCompact
  have hEne : E.Nonempty := by
    refine ⟨0, ?_⟩
    change P 0 ∈ sourceTail
    simpa only [P.source] using ha
  obtain ⟨u, huE, huGreatest⟩ := hEcompact.exists_isGreatest hEne
  have huOne : u < (1 : unitInterval) := by
    apply lt_of_le_of_ne le_top
    intro hu
    apply Set.disjoint_left.mp hdisjoint huE
    rw [hu]
    change P 1 ∈ targetTail
    rw [P.target]
    exact hb
  let F : Set unitInterval := (P ⁻¹' targetTail) ∩ Ici u
  have hFcompact : IsCompact F :=
    ((htarget.preimage P.continuous).inter isClosed_Ici).isCompact
  have hFne : F.Nonempty := ⟨⊤, by
    constructor
    · change P 1 ∈ targetTail
      rw [P.target]
      exact hb
    · change u ≤ (⊤ : unitInterval)
      exact le_top⟩
  obtain ⟨v, hvF, hvLeast⟩ := hFcompact.exists_isLeast hFne
  have huv : u < v := by
    apply lt_of_le_of_ne hvF.2
    intro huv
    apply Set.disjoint_left.mp hdisjoint huE
    rw [huv]
    exact hvF.1
  exact ⟨{
    sourceTime := u
    targetTime := v
    source_lt_target := huv
    source_mem := huE
    target_mem := hvF.1
    source_greatest := fun t ht ↦ huGreatest ht
    target_least_after := fun t hut ht ↦ hvLeast ⟨ht, hut⟩ }⟩

/-! ## Return paths and the exact two-arc Jordan carrier -/

/-- A connector that avoids the selected core but may meet either extension tail many times.
The compact-extrema construction removes precisely those extra contacts. -/
structure CoreAvoidingConnector (E : ExtendibleInjectivePath) where
  connector : Path (E.extension 1) (E.extension 0)
  connector_injective : Injective connector
  connector_disjoint_core : Disjoint (range connector) E.coreRange

namespace CoreAvoidingConnector

private theorem extension_one_ne_zero (E : ExtendibleInjectivePath) :
    E.extension 1 ≠ E.extension 0 := by
  intro h
  exact one_ne_zero (E.extension_injective h)

/-- Maehara nonseparation and Moise polygonal loop erasure supply the connector; this uses no
local-flatness or tubular-neighborhood theorem for the core arc. -/
noncomputable def canonical (E : ExtendibleInjectivePath) : CoreAvoidingConnector E := by
  let U : Set Plane := E.coreRangeᶜ
  have hconnected : IsConnected U :=
    JordanCurve.arc_not_separates JordanCurve.Brouwer.brouwerFPT
      E.coreRangeHomeomorphUnitInterval
  have hopen : IsOpen U := E.isClosed_coreRange.isOpen_compl
  have hjoined :
      LeanEval.Topology.ClassificationOfSurfaces.Moise.JoinedByBrokenLine U
        (E.extension 1) (E.extension 0) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.IsPreconnected.joinedByBrokenLine
      hopen hconnected.isPreconnected E.extension_one_not_mem_coreRange
      E.extension_zero_not_mem_coreRange
  let B := JordanCircle.simpleBrokenLineOfJoined hjoined
  let P : Path (E.extension 1) (E.extension 0) := B.toPath (extension_one_ne_zero E)
  have hPsubset : range P ⊆ U := B.range_toPath_subset (extension_one_ne_zero E)
  exact
    { connector := P
      connector_injective := B.toPath_injective (extension_one_ne_zero E)
      connector_disjoint_core := by
        rw [Set.disjoint_left]
        intro x hxP hxCore
        exact hPsubset hxP hxCore }

noncomputable def trimData {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    ClosedTailTrimData C.connector E.rightTailRange E.leftTailRange :=
  Classical.choice <| nonempty_closedTailTrimData C.connector
    E.rightTailRange E.leftTailRange E.isClosed_rightTailRange E.isClosed_leftTailRange
    E.leftTailRange_disjoint_rightTailRange.symm
    (by
      exact ⟨1, ⟨E.coreRight.2.2, le_rfl⟩, rfl⟩)
    (by
      exact ⟨0, ⟨le_rfl, E.coreLeft.2.1⟩, rfl⟩)

def trimmedConnector {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    Path (C.connector C.trimData.sourceTime) (C.connector C.trimData.targetTime) :=
  C.trimData.trimmedPath

theorem trimmedConnector_injective {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : Injective C.trimmedConnector :=
  C.trimData.trimmedPath_injective C.connector_injective

theorem range_trimmedConnector_subset {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    range C.trimmedConnector ⊆ range C.connector :=
  C.trimData.range_trimmedPath_subset Subset.rfl

theorem range_trimmedConnector_inter_rightTail {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    range C.trimmedConnector ∩ E.rightTailRange =
      {C.connector C.trimData.sourceTime} :=
  C.trimData.range_trimmedPath_inter_sourceTail

theorem range_trimmedConnector_inter_leftTail {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    range C.trimmedConnector ∩ E.leftTailRange =
      {C.connector C.trimData.targetTime} :=
  C.trimData.range_trimmedPath_inter_targetTail

/-- The extension parameter at the trimmed connector's right-tail endpoint. -/
noncomputable def rightContactTime {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : unitInterval :=
  Classical.choose C.trimData.source_mem

theorem rightContactTime_mem {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    C.rightContactTime ∈ Icc E.coreRight 1 :=
  (Classical.choose_spec C.trimData.source_mem).1

theorem rightContact_eq {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    E.extension C.rightContactTime = C.connector C.trimData.sourceTime :=
  (Classical.choose_spec C.trimData.source_mem).2

theorem coreRight_lt_rightContactTime {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : E.coreRight < C.rightContactTime := by
  apply lt_of_le_of_ne C.rightContactTime_mem.1
  intro heq
  have hConnector : E.extension C.rightContactTime ∈ range C.connector := by
    rw [C.rightContact_eq]
    exact ⟨C.trimData.sourceTime, rfl⟩
  have hCore : E.extension C.rightContactTime ∈ E.coreRange := by
    exact ⟨C.rightContactTime,
      ⟨E.coreLeft_lt_coreRight.le.trans C.rightContactTime_mem.1,
        heq.ge⟩, rfl⟩
  exact Set.disjoint_left.mp C.connector_disjoint_core hConnector hCore

/-- The extension parameter at the trimmed connector's left-tail endpoint. -/
noncomputable def leftContactTime {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : unitInterval :=
  Classical.choose C.trimData.target_mem

theorem leftContactTime_mem {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    C.leftContactTime ∈ Icc 0 E.coreLeft :=
  (Classical.choose_spec C.trimData.target_mem).1

theorem leftContact_eq {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    E.extension C.leftContactTime = C.connector C.trimData.targetTime :=
  (Classical.choose_spec C.trimData.target_mem).2

theorem leftContactTime_lt_coreLeft {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : C.leftContactTime < E.coreLeft := by
  apply lt_of_le_of_ne C.leftContactTime_mem.2
  intro heq
  have hConnector : E.extension C.leftContactTime ∈ range C.connector := by
    rw [C.leftContact_eq]
    exact ⟨C.trimData.targetTime, rfl⟩
  have hCore : E.extension C.leftContactTime ∈ E.coreRange := by
    exact ⟨C.leftContactTime,
      ⟨heq.ge,
        C.leftContactTime_mem.2.trans E.coreLeft_lt_coreRight.le⟩, rfl⟩
  exact Set.disjoint_left.mp C.connector_disjoint_core hConnector hCore

/-- The two retained extension-tail pieces, with endpoints cast to the trimmed connector's
literal endpoint expressions. -/
def rightReturnTail {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    Path E.coreTarget (C.connector C.trimData.sourceTime) :=
  (E.extension.subpath E.coreRight C.rightContactTime).cast rfl C.rightContact_eq.symm

def leftReturnTail {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    Path (C.connector C.trimData.targetTime) E.coreSource :=
  (E.extension.subpath C.leftContactTime E.coreLeft).cast C.leftContact_eq.symm rfl

theorem rightReturnTail_injective {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : Injective C.rightReturnTail := by
  intro s t hst
  simp only [rightReturnTail] at hst
  exact convexComb_injective C.coreRight_lt_rightContactTime
    (E.extension_injective hst)

theorem leftReturnTail_injective {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : Injective C.leftReturnTail := by
  intro s t hst
  simp only [leftReturnTail] at hst
  exact convexComb_injective C.leftContactTime_lt_coreLeft
    (E.extension_injective hst)

theorem range_rightReturnTail_subset {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : range C.rightReturnTail ⊆ E.rightTailRange := by
  have hfun : (C.rightReturnTail : unitInterval → Plane) =
      E.extension.subpath E.coreRight C.rightContactTime := by
    exact Path.cast_coe _ _ _
  rw [hfun]
  rw [Path.range_subpath_of_le E.extension E.coreRight C.rightContactTime
    C.rightContactTime_mem.1]
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ht.1, ht.2.trans C.rightContactTime_mem.2⟩, rfl⟩

theorem range_leftReturnTail_subset {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : range C.leftReturnTail ⊆ E.leftTailRange := by
  have hfun : (C.leftReturnTail : unitInterval → Plane) =
      E.extension.subpath C.leftContactTime E.coreLeft := by
    exact Path.cast_coe _ _ _
  rw [hfun]
  rw [Path.range_subpath_of_le E.extension C.leftContactTime E.coreLeft
    C.leftContactTime_mem.2]
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ⟨C.leftContactTime_mem.1.trans ht.1, ht.2⟩, rfl⟩

private theorem rightReturnTail_inter_trimmedConnector
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range C.rightReturnTail ∩ range C.trimmedConnector =
      {C.connector C.trimData.sourceTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxRight, hxConnector⟩
    have hx : x ∈ range C.trimmedConnector ∩ E.rightTailRange :=
      ⟨hxConnector, C.range_rightReturnTail_subset hxRight⟩
    rw [C.range_trimmedConnector_inter_rightTail] at hx
    exact hx
  · rintro x hx
    have hx : x = C.connector C.trimData.sourceTime := mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range C.rightReturnTail,
      Path.source_mem_range C.trimmedConnector⟩

private theorem trimmedConnector_inter_leftReturnTail
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range C.trimmedConnector ∩ range C.leftReturnTail =
      {C.connector C.trimData.targetTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxConnector, hxLeft⟩
    have hx : x ∈ range C.trimmedConnector ∩ E.leftTailRange :=
      ⟨hxConnector, C.range_leftReturnTail_subset hxLeft⟩
    rw [C.range_trimmedConnector_inter_leftTail] at hx
    exact hx
  · rintro x hx
    have hx : x = C.connector C.trimData.targetTime := mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range C.trimmedConnector,
      Path.source_mem_range C.leftReturnTail⟩

private def connectorLeftReturn {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    Path (C.connector C.trimData.sourceTime) E.coreSource :=
  C.trimmedConnector.trans C.leftReturnTail

private theorem connectorLeftReturn_injective {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : Injective C.connectorLeftReturn :=
  Path.trans_injective_of_range_inter C.trimmedConnector C.leftReturnTail
    C.trimmedConnector_injective C.leftReturnTail_injective
    C.trimmedConnector_inter_leftReturnTail

private theorem rightReturnTail_inter_connectorLeftReturn
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range C.rightReturnTail ∩ range C.connectorLeftReturn =
      {C.connector C.trimData.sourceTime} := by
  rw [connectorLeftReturn, Path.trans_range, inter_union_distrib_left,
    C.rightReturnTail_inter_trimmedConnector]
  have hdisjoint : Disjoint (range C.rightReturnTail) (range C.leftReturnTail) :=
    E.leftTailRange_disjoint_rightTailRange.symm.mono
      C.range_rightReturnTail_subset C.range_leftReturnTail_subset
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisjoint, union_empty]

/-- The trimmed simple return built from the two retained tails and the connector middle. -/
def returnPath {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    Path E.coreTarget E.coreSource :=
  C.rightReturnTail.trans C.connectorLeftReturn

theorem returnPath_injective {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) : Injective C.returnPath :=
  Path.trans_injective_of_range_inter C.rightReturnTail C.connectorLeftReturn
    C.rightReturnTail_injective C.connectorLeftReturn_injective
    C.rightReturnTail_inter_connectorLeftReturn

theorem range_returnPath {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range C.returnPath =
      range C.rightReturnTail ∪ range C.trimmedConnector ∪ range C.leftReturnTail := by
  simp only [returnPath, connectorLeftReturn, Path.trans_range, union_assoc]

private theorem corePath_inter_rightReturnTail
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range E.corePath ∩ range C.rightReturnTail = {E.coreTarget} := by
  apply Subset.antisymm
  · rintro x ⟨hxCore, hxRight⟩
    have hx : x ∈ E.coreRange ∩ E.rightTailRange :=
      ⟨E.range_corePath ▸ hxCore, C.range_rightReturnTail_subset hxRight⟩
    rw [E.coreRange_inter_rightTailRange] at hx
    exact hx
  · rintro x hx
    have hx : x = E.coreTarget := mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range E.corePath,
      Path.source_mem_range C.rightReturnTail⟩

private theorem corePath_disjoint_trimmedConnector
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    Disjoint (range E.corePath) (range C.trimmedConnector) := by
  rw [E.range_corePath]
  exact C.connector_disjoint_core.symm.mono Subset.rfl C.range_trimmedConnector_subset

private theorem corePath_inter_leftReturnTail
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    range E.corePath ∩ range C.leftReturnTail = {E.coreSource} := by
  apply Subset.antisymm
  · rintro x ⟨hxCore, hxLeft⟩
    have hx : x ∈ E.leftTailRange ∩ E.coreRange :=
      ⟨C.range_leftReturnTail_subset hxLeft, E.range_corePath ▸ hxCore⟩
    rw [E.leftTailRange_inter_coreRange] at hx
    exact hx
  · rintro x hx
    have hx : x = E.coreSource := mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.source_mem_range E.corePath,
      Path.target_mem_range C.leftReturnTail⟩

theorem corePath_inter_returnPath {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    range E.corePath ∩ range C.returnPath = {E.coreSource, E.coreTarget} := by
  rw [C.range_returnPath, inter_union_distrib_left, inter_union_distrib_left,
    C.corePath_inter_rightReturnTail,
    Set.disjoint_iff_inter_eq_empty.mp C.corePath_disjoint_trimmedConnector,
    union_empty, C.corePath_inter_leftReturnTail, singleton_union]
  exact Set.pair_comm E.coreTarget E.coreSource

/-- The trimmed return and the core form an exact `TwoArcJordan` presentation. -/
def jordanCircle {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) : JordanCircle :=
  TwoArcJordan.toJordanCircle E.corePath C.returnPath E.corePath_injective
    C.returnPath_injective C.corePath_inter_returnPath

@[simp]
theorem carrier_jordanCircle {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E) :
    C.jordanCircle.carrier = range E.corePath ∪ range C.returnPath :=
  TwoArcJordan.carrier_toJordanCircle E.corePath C.returnPath E.corePath_injective
    C.returnPath_injective C.corePath_inter_returnPath

/-- The proved Moise--Schoenflies theorem straightens the resulting auxiliary Jordan carrier. -/
theorem exists_ambient_straightening {E : ExtendibleInjectivePath}
    (C : CoreAvoidingConnector E) :
    ∃ h : Plane ≃ₜ Plane,
      h '' (range E.corePath ∪ range C.returnPath) = Metric.sphere (0 : Plane) 1 := by
  obtain ⟨h, hh⟩ := schoenflies C.jordanCircle.parametrization
    C.jordanCircle.continuous C.jordanCircle.injective
  refine ⟨h, ?_⟩
  rw [← C.carrier_jordanCircle]
  exact hh

/-- On the carrier, the standard two-arc homeomorphism preserves the parameter of the core.
This is stronger than the set-level ambient straightening, but is deliberately not claimed to
extend to the ambient plane with the same prescribed boundary values. -/
def exactCarrierCorrespondence {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E)
    {a' b' : Plane} (p' : Path a' b') (q' : Path b' a')
    (hp' : Injective p') (hq' : Injective q')
    (hinter' : range p' ∩ range q' = {a', b'}) :
    (range E.corePath ∪ range C.returnPath : Set Plane) ≃ₜ
      (range p' ∪ range q' : Set Plane) :=
  TwoArcJordan.carrierCorrespondence E.corePath C.returnPath E.corePath_injective
    C.returnPath_injective C.corePath_inter_returnPath p' q' hp' hq' hinter'

theorem exactCarrierCorrespondence_apply_core
    {E : ExtendibleInjectivePath} (C : CoreAvoidingConnector E)
    {a' b' : Plane} (p' : Path a' b') (q' : Path b' a')
    (hp' : Injective p') (hq' : Injective q')
    (hinter' : range p' ∩ range q' = {a', b'}) (t : unitInterval) :
    C.exactCarrierCorrespondence p' q' hp' hq' hinter'
        ⟨E.corePath t, Or.inl ⟨t, rfl⟩⟩ =
      ⟨p' t, Or.inl ⟨t, rfl⟩⟩ := by
  exact TwoArcJordan.carrierCorrespondence_apply_first
    E.corePath C.returnPath E.corePath_injective C.returnPath_injective
    C.corePath_inter_returnPath p' q' hp' hq' hinter' t

end CoreAvoidingConnector

namespace ExtendibleInjectivePath

/-- The straight reference extension whose selected core is the horizontal seam from `-1` to
`1`. -/
noncomputable def standardBandExtension : ExtendibleInjectivePath where
  extensionSource := planePoint (-2) 0
  extensionTarget := planePoint 2 0
  extension := Path.segment (planePoint (-2) 0) (planePoint 2 0)
  coreLeft := ⟨1 / 4, by norm_num⟩
  coreRight := ⟨3 / 4, by norm_num⟩
  coreLeft_pos := by
    change (0 : ℝ) < 1 / 4
    norm_num
  coreLeft_lt_coreRight := by norm_num
  coreRight_lt_one := by
    change (3 / 4 : ℝ) < 1
    norm_num
  extension_injective := Path.segment_injective_of_ne (by
    intro h
    have hcoord := congrArg (fun z : Plane ↦ z 0) h
    norm_num at hcoord)

/-- The reference horizontal seam, with the same unit-interval parameter as every target core. -/
noncomputable def bandSeamPath :
    Path standardBandExtension.coreSource standardBandExtension.coreTarget :=
  standardBandExtension.corePath

theorem bandSeamPath_eq_planePoint (t : unitInterval) :
    bandSeamPath t = planePoint (2 * (t : ℝ) - 1) 0 := by
  dsimp only [bandSeamPath, corePath, standardBandExtension, Path.subpath]
  change Path.segment (planePoint (-2) 0) (planePoint 2 0)
      (Icc.convexComb ⟨1 / 4, by norm_num⟩ ⟨3 / 4, by norm_num⟩ t) = _
  rw [Path.segment_apply]
  ext i
  fin_cases i
  · norm_num [Icc.coe_convexComb, AffineMap.lineMap_apply_module, planePoint]
    ring
  · norm_num [Icc.coe_convexComb, AffineMap.lineMap_apply_module, planePoint]

/-- A standard open rectangle around the horizontal core seam. -/
def standardRectangle (δ ρ : ℝ) : Set Plane :=
  planeCoordinates.symm ''
    (Ioo (-1 - δ) (1 + δ) ×ˢ Ioo (-ρ) ρ)

theorem isOpen_standardRectangle (δ ρ : ℝ) : IsOpen (standardRectangle δ ρ) := by
  rw [standardRectangle, planeCoordinates.symm.isOpen_image]
  exact isOpen_Ioo.prod isOpen_Ioo

/-- Explicit product coordinates identify the whole plane with every positive standard
rectangle and leave the displayed horizontal seam pointwise fixed. -/
noncomputable def standardRectangleHomeomorph (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) :
    Plane ≃ₜ standardRectangle δ ρ :=
  planeCoordinates.trans <|
    ((FixedCoreSqueeze.intervalHomeomorph δ hδ).prodCongr
      (FixedCoreSqueeze.verticalHomeomorph ρ hρ)).trans <|
      (Homeomorph.Set.prod _ _).symm.trans <|
        Homeomorph.image planeCoordinates.symm _

theorem standardRectangleHomeomorph_apply_bandSeamPath
    (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) (t : unitInterval) :
    ((standardRectangleHomeomorph δ ρ hδ hρ (bandSeamPath t) :
      standardRectangle δ ρ) : Plane) = bandSeamPath t := by
  rw [bandSeamPath_eq_planePoint]
  have hx : 2 * (t : ℝ) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1, t.2.2]
  change planePoint
      ((FixedCoreSqueeze.intervalHomeomorph δ hδ (2 * (t : ℝ) - 1) :
        Ioo (-1 - δ) (1 + δ)) : ℝ)
      ((FixedCoreSqueeze.verticalHomeomorph ρ hρ 0 : Ioo (-ρ) ρ) : ℝ) = _
  rw [FixedCoreSqueeze.intervalHomeomorph_apply_of_mem_Icc hδ hx,
    FixedCoreSqueeze.verticalHomeomorph_apply_zero]

private theorem dist_planePoint_le_abs_add_abs (x y u v : ℝ) :
    dist (planePoint x y) (planePoint u v) ≤ |x - u| + |y - v| := by
  rw [dist_eq_norm]
  have hsplit :
      planePoint x y - planePoint u v =
        planePoint (x - u) 0 + planePoint 0 (y - v) := by
    apply plane_ext <;> simp
  rw [hsplit]
  refine (norm_add_le _ _).trans_eq ?_
  congr 1 <;>
    simp [planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

private theorem abs_sub_clamp_lt {ρ x : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ Ioo (-1 - ρ) (1 + ρ)) :
    |x - max (-1) (min 1 x)| < ρ := by
  by_cases hx₀ : x < -1
  · rw [min_eq_right (by linarith), max_eq_left hx₀.le]
    rw [abs_of_neg (by linarith)]
    linarith [hx.1]
  · have hxlow : -1 ≤ x := le_of_not_gt hx₀
    by_cases hx₁ : x ≤ 1
    · rw [min_eq_right hx₁, max_eq_right hxlow, sub_self, abs_zero]
      exact hρ
    · have hxhigh : 1 < x := lt_of_not_ge hx₁
      rw [min_eq_left hxhigh.le, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [abs_of_pos (sub_pos.mpr hxhigh)]
      linarith [hx.2]

/-- A sufficiently thin explicit rectangle lies in the metric tube of the reference seam. -/
theorem standardRectangle_subset_thickening {ε : ℝ} (hε : 0 < ε) :
    standardRectangle (ε / 3) (ε / 3) ⊆
      Metric.thickening ε (range bandSeamPath) := by
  rintro z ⟨p, hp, rfl⟩
  rw [Metric.mem_thickening_iff]
  let u : ℝ := max (-1) (min 1 p.1)
  have hu : u ∈ Icc (-1 : ℝ) 1 := by
    dsimp [u]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  let t : unitInterval := ⟨(u + 1) / 2, by
    constructor <;> nlinarith [hu.1, hu.2]⟩
  refine ⟨bandSeamPath t, ⟨t, rfl⟩, ?_⟩
  rw [bandSeamPath_eq_planePoint]
  have ht : 2 * (t : ℝ) - 1 = u := by
    dsimp [t]
    ring
  rw [ht, planeCoordinates_symm_apply]
  refine (dist_planePoint_le_abs_add_abs p.1 p.2 u 0).trans_lt ?_
  have hx : |p.1 - u| < ε / 3 := abs_sub_clamp_lt (by linarith) hp.1
  have hy : |p.2| < ε / 3 := abs_lt.mpr hp.2
  simpa using (show |p.1 - u| + |p.2| < ε by linarith)

/-- The exact ambient homeomorphism obtained by normalizing the reference and target auxiliary
Jordan circles by the same parametrized unit circle. -/
noncomputable def ambientCoreStraightener (E : ExtendibleInjectivePath) : Plane ≃ₜ Plane :=
  (CoreAvoidingConnector.canonical
      standardBandExtension).jordanCircle.exactAmbientNormalizer |>.trans
    (CoreAvoidingConnector.canonical E).jordanCircle.exactAmbientNormalizer.symm

/-- The ambient straightener preserves the unit-interval parameter pointwise on the core. -/
theorem ambientCoreStraightener_apply_bandSeamPath (E : ExtendibleInjectivePath)
    (t : unitInterval) :
    E.ambientCoreStraightener (bandSeamPath t) = E.corePath t := by
  let C₀ := CoreAvoidingConnector.canonical standardBandExtension
  let C := CoreAvoidingConnector.canonical E
  have h₀ := TwoArcJordan.exactAmbientNormalizer_apply_first
    standardBandExtension.corePath C₀.returnPath standardBandExtension.corePath_injective
    C₀.returnPath_injective C₀.corePath_inter_returnPath t
  have h := TwoArcJordan.exactAmbientNormalizer_apply_first
    E.corePath C.returnPath E.corePath_injective C.returnPath_injective
    C.corePath_inter_returnPath t
  change C₀.jordanCircle.exactAmbientNormalizer
      (standardBandExtension.corePath t) = _ at h₀
  change C.jordanCircle.exactAmbientNormalizer (E.corePath t) = _ at h
  change C.jordanCircle.exactAmbientNormalizer.symm
      (C₀.jordanCircle.exactAmbientNormalizer (standardBandExtension.corePath t)) =
    E.corePath t
  rw [h₀, ← h, C.jordanCircle.exactAmbientNormalizer.symm_apply_apply]

/-- Every extendible injective planar core has an arbitrarily small open strip neighborhood,
parametrized by the whole plane.  The parametrization agrees pointwise, with the same
unit-interval parameter, on the displayed core seam. -/
theorem exists_tubularStrip_of_extendible (E : ExtendibleInjectivePath)
    {U : Set Plane} (hU : IsOpen U) (hcoreU : E.coreRange ⊆ U) :
    ∃ V : Set Plane, IsOpen V ∧ V ⊆ U ∧
      ∃ e : Plane ≃ₜ V, ∀ t : unitInterval,
        (e (bandSeamPath t) : Plane) = E.corePath t := by
  let H : Plane ≃ₜ Plane := E.ambientCoreStraightener
  let W : Set Plane := H ⁻¹' U
  have hWopen : IsOpen W := H.isOpen_preimage.mpr hU
  have hseamW : range bandSeamPath ⊆ W := by
    rintro _ ⟨t, rfl⟩
    change H (bandSeamPath t) ∈ U
    rw [show H (bandSeamPath t) = E.corePath t from
      E.ambientCoreStraightener_apply_bandSeamPath t]
    exact hcoreU (E.range_corePath ▸ ⟨t, rfl⟩)
  have hseamCompact : IsCompact (range bandSeamPath) := by
    simpa only [image_univ] using
      (isCompact_univ.image bandSeamPath.continuous)
  obtain ⟨ε, hε, hthickW⟩ :=
    hseamCompact.exists_thickening_subset_open hWopen hseamW
  let r : ℝ := ε / 3
  have hr : 0 < r := by dsimp [r]; linarith
  let R : Set Plane := standardRectangle r r
  have hRopen : IsOpen R := isOpen_standardRectangle r r
  have hRW : R ⊆ W := by
    exact (standardRectangle_subset_thickening hε).trans hthickW
  let V : Set Plane := H '' R
  have hVopen : IsOpen V := by
    dsimp [V]
    exact H.isOpen_image.mpr hRopen
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hxR, rfl⟩
    exact hRW hxR
  let e₀ : Plane ≃ₜ R := standardRectangleHomeomorph r r hr hr
  let e : Plane ≃ₜ V := e₀.trans (Homeomorph.image H R)
  refine ⟨V, hVopen, hVU, e, ?_⟩
  intro t
  change H ((e₀ (bandSeamPath t) : R) : Plane) = E.corePath t
  rw [show ((e₀ (bandSeamPath t) : R) : Plane) = bandSeamPath t from
      standardRectangleHomeomorph_apply_bandSeamPath r r hr hr t,
    E.ambientCoreStraightener_apply_bandSeamPath]

/-- The canonical auxiliary Jordan circle attached to an extendible injective arc. -/
noncomputable def auxiliaryJordanCircle (E : ExtendibleInjectivePath) : JordanCircle :=
  (CoreAvoidingConnector.canonical E).jordanCircle

@[simp]
theorem carrier_auxiliaryJordanCircle (E : ExtendibleInjectivePath) :
    E.auxiliaryJordanCircle.carrier =
      range E.corePath ∪ range (CoreAvoidingConnector.canonical E).returnPath :=
  (CoreAvoidingConnector.canonical E).carrier_jordanCircle

/-- Unconditional set-level ambient straightening of the auxiliary Jordan carrier. -/
theorem exists_ambient_straightening (E : ExtendibleInjectivePath) :
    ∃ h : Plane ≃ₜ Plane,
      h '' (range E.corePath ∪ range (CoreAvoidingConnector.canonical E).returnPath) =
        Metric.sphere (0 : Plane) 1 :=
  (CoreAvoidingConnector.canonical E).exists_ambient_straightening

end ExtendibleInjectivePath


end

end Schoenflies
