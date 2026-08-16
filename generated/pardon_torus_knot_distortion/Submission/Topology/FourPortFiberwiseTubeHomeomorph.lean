import Submission.Topology.FourPortMorseGraphPatch

/-!
# A fiberwise tube homeomorphism for the four-port Morse graph

The open normal interval is first rescaled to `(-1,1)`.  For `a,b ∈ (-1,1)`, the real Möbius
map

`x ↦ (x + k) / (1 + k*x)`, where `k = (b-a)/(1-a*b)`,

is increasing, sends `a` to `b`, and has the map with parameter `-k` as inverse.  Its extension
to the closed interval fixes both endpoints.  This gives a continuously varying fiber
homeomorphism over the quadratic four-port disk.

The resulting homeomorphism is deliberately bundled on the pulled-back patch tube.  Composing
with `fourPortTorusBaseMap` embeds that tube in `StandardTorusNormalTube`; no unsupported global
extension outside the base patch is asserted here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-! ## Möbius homeomorphisms of the open unit interval -/

/-- The symmetric open unit interval. -/
abbrev FourPortOpenUnitInterval := Set.Ioo (-(1 : ℝ)) 1

/-- Möbius parameter of the unique endpoint-fixing fractional-linear map carrying `a` to `b`. -/
def fourPortMobiusParameter (a b : FourPortOpenUnitInterval) : ℝ :=
  (b.1 - a.1) / (1 - a.1 * b.1)

/-- The underlying fractional-linear map. -/
def fourPortMobiusMap (k x : ℝ) : ℝ :=
  (x + k) / (1 + k * x)

private theorem abs_lt_one_of_mem_fourPortOpenUnitInterval
    (x : FourPortOpenUnitInterval) : |x.1| < 1 :=
  abs_lt.mpr x.2

private theorem fourPort_one_sub_mul_pos
    (a b : FourPortOpenUnitInterval) : 0 < 1 - a.1 * b.1 := by
  have ha := abs_lt_one_of_mem_fourPortOpenUnitInterval a
  have hb := abs_lt_one_of_mem_fourPortOpenUnitInterval b
  have habs : |a.1 * b.1| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a.1) ha hb.le
  nlinarith [le_abs_self (a.1 * b.1)]

/-- The Möbius parameter remains in `(-1,1)`. -/
theorem fourPortMobiusParameter_mem
    (a b : FourPortOpenUnitInterval) :
    fourPortMobiusParameter a b ∈ Ioo (-(1 : ℝ)) 1 := by
  have hden := fourPort_one_sub_mul_pos a b
  rw [mem_Ioo, fourPortMobiusParameter]
  constructor
  · rw [lt_div_iff₀ hden]
    have hprod : 0 < (1 - a.1) * (1 + b.1) :=
      mul_pos (sub_pos.mpr a.2.2) (by linarith [b.2.1])
    nlinarith
  · rw [div_lt_iff₀ hden]
    have hprod : 0 < (1 + a.1) * (1 - b.1) :=
      mul_pos (by linarith [a.2.1]) (sub_pos.mpr b.2.2)
    nlinarith

private theorem fourPortMobius_denominator_pos
    {k x : ℝ} (hk : k ∈ Ioo (-(1 : ℝ)) 1)
    (hx : x ∈ Ioo (-(1 : ℝ)) 1) :
    0 < 1 + k * x := by
  have hkabs : |k| < 1 := abs_lt.mpr hk
  have hxabs : |x| < 1 := abs_lt.mpr hx
  have hkx : |k * x| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg k) hkabs hxabs.le
  nlinarith [neg_le_abs (k * x)]

/-- A Möbius map with parameter in `(-1,1)` preserves the open unit interval. -/
theorem fourPortMobiusMap_mem
    {k x : ℝ} (hk : k ∈ Ioo (-(1 : ℝ)) 1)
    (hx : x ∈ Ioo (-(1 : ℝ)) 1) :
    fourPortMobiusMap k x ∈ Ioo (-(1 : ℝ)) 1 := by
  have hden := fourPortMobius_denominator_pos hk hx
  have hplus :
      fourPortMobiusMap k x + 1 =
        ((1 + k) * (1 + x)) / (1 + k * x) := by
    rw [fourPortMobiusMap, div_add_one]
    congr 1
    ring
    exact hden.ne'
  have hminus :
      1 - fourPortMobiusMap k x =
        ((1 - k) * (1 - x)) / (1 + k * x) := by
    rw [fourPortMobiusMap, one_sub_div]
    congr 1
    ring
    exact hden.ne'
  constructor
  · have hpositive : 0 < fourPortMobiusMap k x + 1 := by
      rw [hplus]
      exact div_pos (mul_pos (by linarith [hk.1]) (by linarith [hx.1])) hden
    linarith
  · have hpositive : 0 < 1 - fourPortMobiusMap k x := by
      rw [hminus]
      exact div_pos (mul_pos (sub_pos.mpr hk.2) (sub_pos.mpr hx.2)) hden
    linarith

/-- Swapping source and target negates the Möbius parameter. -/
theorem fourPortMobiusParameter_swap
    (a b : FourPortOpenUnitInterval) :
    fourPortMobiusParameter b a = -fourPortMobiusParameter a b := by
  unfold fourPortMobiusParameter
  rw [mul_comm b.1 a.1]
  ring

/-- Joint continuity of the marked-point Möbius parameter. -/
theorem continuous_fourPortMobiusParameter :
    Continuous (fun p : FourPortOpenUnitInterval × FourPortOpenUnitInterval ↦
      fourPortMobiusParameter p.1 p.2) := by
  unfold fourPortMobiusParameter
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p hp
    exact (fourPort_one_sub_mul_pos p.1 p.2).ne' hp

/-- The chosen Möbius map carries its marked source point to its marked target point. -/
theorem fourPortMobiusMap_parameter_source
    (a b : FourPortOpenUnitInterval) :
    fourPortMobiusMap (fourPortMobiusParameter a b) a.1 = b.1 := by
  have hab := (fourPort_one_sub_mul_pos a b).ne'
  have hk := fourPortMobiusParameter_mem a b
  have hmapDen := (fourPortMobius_denominator_pos hk a.2).ne'
  rw [fourPortMobiusMap]
  apply (div_eq_iff hmapDen).mpr
  rw [fourPortMobiusParameter]
  field_simp [hab]
  ring

/-- The map with parameter `-k` is the inverse of the map with parameter `k`. -/
theorem fourPortMobiusMap_neg_comp
    {k x : ℝ} (hk : k ∈ Ioo (-(1 : ℝ)) 1)
    (hx : x ∈ Ioo (-(1 : ℝ)) 1) :
    fourPortMobiusMap (-k) (fourPortMobiusMap k x) = x := by
  have hkneg : -k ∈ Ioo (-(1 : ℝ)) 1 := by
    constructor <;> linarith [hk.1, hk.2]
  have hden := (fourPortMobius_denominator_pos hk hx).ne'
  have hdenComm : 1 + x * k ≠ 0 := by
    rw [mul_comm]
    exact hden
  have hy := fourPortMobiusMap_mem hk hx
  have hinvDen := (fourPortMobius_denominator_pos hkneg hy).ne'
  rw [fourPortMobiusMap]
  apply (div_eq_iff hinvDen).mpr
  rw [fourPortMobiusMap]
  field_simp [hden, hdenComm]
  ring

/-- Exact identity when the marked source and target agree. -/
@[simp] theorem fourPortMobiusMap_parameter_self
    (a x : FourPortOpenUnitInterval) :
    fourPortMobiusMap (fourPortMobiusParameter a a) x.1 = x.1 := by
  have haa := (fourPort_one_sub_mul_pos a a).ne'
  simp [fourPortMobiusMap, fourPortMobiusParameter]

/-- The closed extension fixes the left endpoint. -/
theorem fourPortMobiusMap_neg_one
    {k : ℝ} (hk : k ∈ Ioo (-(1 : ℝ)) 1) :
    fourPortMobiusMap k (-1) = -1 := by
  have hne : 1 - k ≠ 0 := (sub_pos.mpr hk.2).ne'
  rw [fourPortMobiusMap]
  rw [show 1 + k * (-1) = 1 - k by ring]
  change (-1 + k) / (1 - k) = -1
  apply (div_eq_iff hne).mpr
  ring

/-- The closed extension fixes the right endpoint. -/
theorem fourPortMobiusMap_one
    {k : ℝ} (hk : k ∈ Ioo (-(1 : ℝ)) 1) :
    fourPortMobiusMap k 1 = 1 := by
  have hne : 1 + k ≠ 0 := by linarith [hk.1]
  rw [fourPortMobiusMap]
  rw [show 1 + k * 1 = 1 + k by ring]
  change (1 + k) / (1 + k) = 1
  exact div_self hne

/-- Möbius reparameterization as a homeomorphism of the open unit interval. -/
def fourPortMobiusHomeomorph
    (a b : FourPortOpenUnitInterval) :
    FourPortOpenUnitInterval ≃ₜ FourPortOpenUnitInterval where
  toFun x := ⟨fourPortMobiusMap (fourPortMobiusParameter a b) x.1,
    fourPortMobiusMap_mem (fourPortMobiusParameter_mem a b) x.2⟩
  invFun x := ⟨fourPortMobiusMap (-fourPortMobiusParameter a b) x.1,
    fourPortMobiusMap_mem (by
      have hk := fourPortMobiusParameter_mem a b
      constructor <;> linarith [hk.1, hk.2]) x.2⟩
  left_inv x := Subtype.ext (fourPortMobiusMap_neg_comp
    (fourPortMobiusParameter_mem a b) x.2)
  right_inv x := by
    apply Subtype.ext
    have hk := fourPortMobiusParameter_mem a b
    have hkneg : -fourPortMobiusParameter a b ∈ Ioo (-(1 : ℝ)) 1 := by
      constructor <;> linarith [hk.1, hk.2]
    simpa only [neg_neg] using fourPortMobiusMap_neg_comp hkneg x.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact (fourPortMobius_denominator_pos
        (fourPortMobiusParameter_mem a b) x.2).ne' hx
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x hx
      have hk := fourPortMobiusParameter_mem a b
      exact (fourPortMobius_denominator_pos (by
        constructor <;> linarith [hk.1, hk.2]) x.2).ne' hx

@[simp] theorem fourPortMobiusHomeomorph_source
    (a b : FourPortOpenUnitInterval) :
    fourPortMobiusHomeomorph a b a = b :=
  Subtype.ext (fourPortMobiusMap_parameter_source a b)

/-- Swapping the marked source and target gives the inverse unit-interval map. -/
theorem fourPortMobiusHomeomorph_swap_apply
    (a b x : FourPortOpenUnitInterval) :
    fourPortMobiusHomeomorph b a x = (fourPortMobiusHomeomorph a b).symm x := by
  apply Subtype.ext
  change fourPortMobiusMap (fourPortMobiusParameter b a) x.1 =
    fourPortMobiusMap (-fourPortMobiusParameter a b) x.1
  rw [fourPortMobiusParameter_swap]

/-! ## Rescaling the standard normal interval -/

/-- Linear rescaling from the standard half-width normal interval to `(-1,1)`. -/
def fourPortNormalToUnit :
    Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ≃ₜ FourPortOpenUnitInterval where
  toFun x := ⟨2 * x.1, by constructor <;> nlinarith [x.2.1, x.2.2]⟩
  invFun x := ⟨x.1 / 2, by constructor <;> nlinarith [x.2.1, x.2.2]⟩
  left_inv x := Subtype.ext (by norm_num)
  right_inv x := Subtype.ext (by ring)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Real-valued closed-interval extension of the normal-fiber map. -/
def fourPortNormalFiberExtension
    (a b : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourPortMobiusMap
    (fourPortMobiusParameter (fourPortNormalToUnit a) (fourPortNormalToUnit b)) (2 * r)

/-- The closed extension fixes the left tube endpoint. -/
theorem fourPortNormalFiberExtension_leftEndpoint
    (a b : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberExtension a b (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) := by
  rw [fourPortNormalFiberExtension]
  have hk := fourPortMobiusParameter_mem (fourPortNormalToUnit a) (fourPortNormalToUnit b)
  rw [show (2 : ℝ) * -(1 / 2) = -1 by norm_num,
    fourPortMobiusMap_neg_one hk]
  norm_num

/-- The closed extension fixes the right tube endpoint. -/
theorem fourPortNormalFiberExtension_rightEndpoint
    (a b : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberExtension a b (1 / 2 : ℝ) = 1 / 2 := by
  rw [fourPortNormalFiberExtension]
  have hk := fourPortMobiusParameter_mem (fourPortNormalToUnit a) (fourPortNormalToUnit b)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    fourPortMobiusMap_one hk]
  norm_num

/-- Fiber homeomorphism of the standard normal interval sending `a` to `b`. -/
def fourPortNormalFiberHomeomorph
    (a b : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ≃ₜ
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  fourPortNormalToUnit.trans
    ((fourPortMobiusHomeomorph (fourPortNormalToUnit a)
      (fourPortNormalToUnit b)).trans fourPortNormalToUnit.symm)

/-- The open-interval homeomorphism agrees with its explicit closed-interval extension. -/
theorem fourPortNormalFiberHomeomorph_coe
    (a b r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    (fourPortNormalFiberHomeomorph a b r : ℝ) =
      fourPortNormalFiberExtension a b r.1 := by
  simp only [fourPortNormalFiberHomeomorph, fourPortNormalFiberExtension,
    Homeomorph.trans_apply]
  change fourPortMobiusMap
    (fourPortMobiusParameter (fourPortNormalToUnit a) (fourPortNormalToUnit b))
      (2 * r.1) / 2 = _
  ring

@[simp] theorem fourPortNormalFiberHomeomorph_source
    (a b : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberHomeomorph a b a = b := by
  apply fourPortNormalToUnit.injective
  simp [fourPortNormalFiberHomeomorph]

/-- Exact identity when source and target normal heights agree. -/
theorem fourPortNormalFiberHomeomorph_self
    (a r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberHomeomorph a a r = r := by
  apply fourPortNormalToUnit.injective
  apply Subtype.ext
  simp [fourPortNormalFiberHomeomorph, fourPortMobiusHomeomorph]

/-- Swapping the marked heights gives the inverse fiber homeomorphism. -/
theorem fourPortNormalFiberHomeomorph_swap_apply
    (a b r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberHomeomorph b a r =
      (fourPortNormalFiberHomeomorph a b).symm r := by
  change fourPortNormalToUnit.symm
      (fourPortMobiusHomeomorph (fourPortNormalToUnit b)
        (fourPortNormalToUnit a) (fourPortNormalToUnit r)) =
    fourPortNormalToUnit.symm
      ((fourPortMobiusHomeomorph (fourPortNormalToUnit a)
        (fourPortNormalToUnit b)).symm (fourPortNormalToUnit r))
  congr 1
  exact fourPortMobiusHomeomorph_swap_apply _ _ _

private theorem fourPortNormalFiberHomeomorph_leftInverse
    (a b r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberHomeomorph b a (fourPortNormalFiberHomeomorph a b r) = r := by
  rw [fourPortNormalFiberHomeomorph_swap_apply]
  exact (fourPortNormalFiberHomeomorph a b).symm_apply_apply r

private theorem fourPortNormalFiberHomeomorph_rightInverse
    (a b r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortNormalFiberHomeomorph a b (fourPortNormalFiberHomeomorph b a r) = r := by
  rw [fourPortNormalFiberHomeomorph_swap_apply]
  exact (fourPortNormalFiberHomeomorph b a).symm_apply_apply r

/-- Joint continuity in source height, target height, and fiber coordinate. -/
theorem continuous_fourPortNormalFiberHomeomorph_family :
    Continuous (fun q :
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortNormalFiberHomeomorph q.1.1 q.1.2 q.2) := by
  apply fourPortNormalToUnit.symm.continuous.comp
  apply Continuous.subtype_mk
  have hsource : Continuous (fun q :
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortNormalToUnit q.1.1) := by fun_prop
  have htarget : Continuous (fun q :
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortNormalToUnit q.1.2) := by fun_prop
  have hfiber : Continuous (fun q :
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortNormalToUnit q.2) := by fun_prop
  have hparameter : Continuous (fun q :
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortMobiusParameter (fourPortNormalToUnit q.1.1)
        (fourPortNormalToUnit q.1.2)) :=
    continuous_fourPortMobiusParameter.comp (hsource.prodMk htarget)
  apply Continuous.div
  · exact (continuous_subtype_val.comp hfiber).add hparameter
  · exact continuous_const.add
      (hparameter.mul (continuous_subtype_val.comp hfiber))
  · intro q hzero
    let a := fourPortNormalToUnit q.1.1
    let b := fourPortNormalToUnit q.1.2
    let x := fourPortNormalToUnit q.2
    exact (fourPortMobius_denominator_pos
      (fourPortMobiusParameter_mem a b) x.2).ne' hzero

/-- Continuous source, target, and fiber-coordinate functions induce a continuous family of
normal-fiber homeomorphisms. -/
theorem continuous_fourPortNormalFiberHomeomorph_comp
    {X : Type*} [TopologicalSpace X]
    {a b r : X → Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)}
    (ha : Continuous a) (hb : Continuous b) (hr : Continuous r) :
    Continuous (fun x ↦ fourPortNormalFiberHomeomorph (a x) (b x) (r x)) := by
  change Continuous ((fun q :
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ×
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↦
      fourPortNormalFiberHomeomorph q.1.1 q.1.2 q.2) ∘
        fun x ↦ ((a x, b x), r x))
  exact continuous_fourPortNormalFiberHomeomorph_family.comp
    ((ha.prodMk hb).prodMk hr)

/-! ## The pulled-back four-port patch tube -/

/-- Normal coordinate of the initial vertical graph. -/
def fourPortVerticalNormalCoordinate (u : FourPortQuadraticDisk) :
    Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  fourPortNormalCoordinate ⟨0, by norm_num⟩ u

theorem fourPortVerticalNormalCoordinate_continuous :
    Continuous fourPortVerticalNormalCoordinate := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul <|
    (continuous_fourPortMorseHeight 0).comp continuous_subtype_val)

/-- The pulled-back tube over the quadratic four-port disk. -/
abbrev FourPortPatchNormalTube :=
  FourPortQuadraticDisk × Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- The fiberwise patch map.  It leaves the base coordinate fixed and carries the initial normal
graph height to the height at time `t`. -/
def fourPortPatchTubeMap (t : FourPortMorseTime)
    (p : FourPortPatchNormalTube) : FourPortPatchNormalTube :=
  (p.1, fourPortNormalFiberHomeomorph
    (fourPortVerticalNormalCoordinate p.1) (fourPortNormalCoordinate t p.1) p.2)

theorem fourPortPatchTubeMap_continuous (t : FourPortMorseTime) :
    Continuous (fourPortPatchTubeMap t) := by
  change Continuous (fun p : FourPortPatchNormalTube ↦
    (p.1, fourPortNormalFiberHomeomorph
      (fourPortVerticalNormalCoordinate p.1) (fourPortNormalCoordinate t p.1) p.2))
  apply continuous_fst.prodMk
  have hsource : Continuous (fun p : FourPortPatchNormalTube ↦
      fourPortVerticalNormalCoordinate p.1) :=
    fourPortVerticalNormalCoordinate_continuous.comp continuous_fst
  have htarget : Continuous (fun p : FourPortPatchNormalTube ↦
      fourPortNormalCoordinate t p.1) :=
    (fourPortTubeCoordinates_continuous t).snd.comp continuous_fst
  exact continuous_fourPortNormalFiberHomeomorph_comp hsource htarget continuous_snd

/-- The concrete fixed-base homeomorphism of the pulled-back patch tube. -/
def fourPortPatchTubeHomeomorph (t : FourPortMorseTime) :
    FourPortPatchNormalTube ≃ₜ FourPortPatchNormalTube where
  toFun := fourPortPatchTubeMap t
  invFun p :=
    (p.1, fourPortNormalFiberHomeomorph
      (fourPortNormalCoordinate t p.1) (fourPortVerticalNormalCoordinate p.1) p.2)
  left_inv p := by
    change (p.1, fourPortNormalFiberHomeomorph
      (fourPortNormalCoordinate t p.1) (fourPortVerticalNormalCoordinate p.1)
        (fourPortNormalFiberHomeomorph (fourPortVerticalNormalCoordinate p.1)
          (fourPortNormalCoordinate t p.1) p.2)) = p
    apply Prod.ext
    · rfl
    exact fourPortNormalFiberHomeomorph_leftInverse _ _ _
  right_inv p := by
    change (p.1, fourPortNormalFiberHomeomorph
      (fourPortVerticalNormalCoordinate p.1) (fourPortNormalCoordinate t p.1)
        (fourPortNormalFiberHomeomorph (fourPortNormalCoordinate t p.1)
          (fourPortVerticalNormalCoordinate p.1) p.2)) = p
    apply Prod.ext
    · rfl
    exact fourPortNormalFiberHomeomorph_rightInverse _ _ _
  continuous_toFun := fourPortPatchTubeMap_continuous t
  continuous_invFun := by
    apply continuous_fst.prodMk
    have hsource : Continuous (fun p : FourPortPatchNormalTube ↦
        fourPortNormalCoordinate t p.1) :=
      (fourPortTubeCoordinates_continuous t).snd.comp continuous_fst
    have htarget : Continuous (fun p : FourPortPatchNormalTube ↦
        fourPortVerticalNormalCoordinate p.1) :=
      fourPortVerticalNormalCoordinate_continuous.comp continuous_fst
    exact continuous_fourPortNormalFiberHomeomorph_comp hsource htarget continuous_snd

/-- The patch homeomorphism sends the initial vertical graph exactly to the graph at time `t`. -/
theorem fourPortPatchTubeHomeomorph_verticalGraph
    (t : FourPortMorseTime) (u : FourPortQuadraticDisk) :
    fourPortPatchTubeHomeomorph t (u, fourPortVerticalNormalCoordinate u) =
      (u, fourPortNormalCoordinate t u) := by
  change (u, fourPortNormalFiberHomeomorph
    (fourPortVerticalNormalCoordinate u) (fourPortNormalCoordinate t u)
      (fourPortVerticalNormalCoordinate u)) = _
  apply Prod.ext
  · rfl
  exact fourPortNormalFiberHomeomorph_source _ _

/-- On the quadratic frontier, source and target normal heights agree. -/
theorem fourPortNormalCoordinate_eq_vertical_of_mem_frontier
    (t : FourPortMorseTime) {u : FourPortQuadraticDisk}
    (hu : u.1 ∈ frontier fourPortQuadraticRegion) :
    fourPortNormalCoordinate t u = fourPortVerticalNormalCoordinate u := by
  apply Subtype.ext
  change (1 / 4 : ℝ) * fourPortMorseHeight t u.1 =
    (1 / 4 : ℝ) * fourPortMorseHeight 0 u.1
  rw [fourPortMorseHeight_eq_verticalHeight_of_mem_frontier t hu,
    fourPortMorseHeight_zero]

/-- The entire normal fiber is fixed over the quadratic frontier. -/
theorem fourPortPatchTubeHomeomorph_fixed_frontier
    (t : FourPortMorseTime) {u : FourPortQuadraticDisk}
    (hu : u.1 ∈ frontier fourPortQuadraticRegion)
    (r : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    fourPortPatchTubeHomeomorph t (u, r) = (u, r) := by
  change (u, fourPortNormalFiberHomeomorph
    (fourPortVerticalNormalCoordinate u) (fourPortNormalCoordinate t u) r) = _
  apply Prod.ext
  · rfl
  rw [fourPortNormalCoordinate_eq_vertical_of_mem_frontier t hu]
  exact fourPortNormalFiberHomeomorph_self _ _

/-- Embed the pulled-back patch tube into the standard torus normal tube. -/
def fourPortPatchTubeEmbedding (p : FourPortPatchNormalTube) :
    StandardTorusNormalTube :=
  (fourPortTorusBaseMap p.1, p.2)

theorem fourPortPatchTubeEmbedding_isEmbedding :
    IsEmbedding fourPortPatchTubeEmbedding :=
  fourPortTorusBaseMap_isClosedEmbedding.isEmbedding.prodMap IsEmbedding.id

/-- After embedding in the standard tube, the image of the initial graph is exactly the existing
time-`t` tube-coordinate graph. -/
theorem fourPortPatchTubeEmbedding_map_verticalGraph
    (t : FourPortMorseTime) (u : FourPortQuadraticDisk) :
    fourPortPatchTubeEmbedding
        (fourPortPatchTubeHomeomorph t (u, fourPortVerticalNormalCoordinate u)) =
      fourPortTubeCoordinates t u := by
  rw [fourPortPatchTubeHomeomorph_verticalGraph]
  rfl

end Submission.Topology
