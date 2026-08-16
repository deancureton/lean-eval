import Submission.Topology.CircleIntersectionLocalIFT
import Submission.Topology.SuperellipsoidBarrierLoopCharging
import Submission.Topology.SuperellipsoidGlobalFourPortCarrier

/-!
# Regular-side continuation for the global four-port model

The quadratic four-port height has one singular time, `t = 1 / 2`.  On either
component of its complement its zero carrier has four explicit half-branches.
This file writes those branches down, proves that they exhaust the zero
carrier, and transports them through a global superellipsoid band chart.

The last section records the exact additional input needed for charging a
*closed* intersection loop.  The local four-port equation does not determine
how its four ports are joined outside the band and an arbitrary global band
chart does not contain derivative data for the standard torus knot.  Thus the
closed-loop completion and its local transverse circle atlas are explicit
fields.  Covering monodromy then constructs endpoint matching; no endpoint
matching is assumed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-! ## The four regular half-branches -/

/-- The two signs used to label the ports. -/
inductive FourPortSign
  | neg
  | pos

namespace FourPortSign

/-- The real value of a port sign. -/
def value : FourPortSign → ℝ
  | neg => -1
  | pos => 1

@[simp] theorem value_neg : value neg = -(1 : ℝ) := rfl

@[simp] theorem value_pos : value pos = (1 : ℝ) := rfl

@[simp] theorem value_sq (e : FourPortSign) : value e ^ 2 = (1 : ℝ) := by
  cases e <;> norm_num

end FourPortSign

/-- Regular times before the saddle crossing. -/
abbrev FourPortLeftRegularTime := Set.Ico (0 : ℝ) (1 / 2 : ℝ)

/-- Regular times after the saddle crossing. -/
abbrev FourPortRightRegularTime := Set.Ioc (1 / 2 : ℝ) 1

/-- The closed parameter interval along one half-branch. -/
abbrev FourPortArmParameter := unitInterval

def fourPortLeftTime (t : FourPortLeftRegularTime) : FourPortMorseTime :=
  ⟨t.1, ⟨t.2.1, t.2.2.le.trans (by norm_num)⟩⟩

def fourPortRightTime (t : FourPortRightRegularTime) : FourPortMorseTime :=
  ⟨t.1, ⟨(by linarith [t.2.1] : 0 ≤ t.1), t.2.2⟩⟩

theorem fourPortLeftRegularTime_ne_half (t : FourPortLeftRegularTime) :
    t.1 ≠ (1 / 2 : ℝ) := by
  linarith [t.2.2]

theorem fourPortRightRegularTime_ne_half (t : FourPortRightRegularTime) :
    t.1 ≠ (1 / 2 : ℝ) := by
  linarith [t.2.1]

/-- Squared first coordinate of the left-side zero carrier, as a function of
the second coordinate. -/
def fourPortLeftRadicand (t y : ℝ) : ℝ :=
  (1 - 2 * t + t * y ^ 2) / (1 - t)

/-- Squared second coordinate of the right-side zero carrier, as a function
of the first coordinate. -/
def fourPortRightRadicand (t x : ℝ) : ℝ :=
  (2 * t - 1 + (1 - t) * x ^ 2) / t

theorem fourPortLeftRadicand_nonneg (t : FourPortLeftRegularTime) (y : ℝ) :
    0 ≤ fourPortLeftRadicand t y := by
  apply div_nonneg
  · exact add_nonneg (by linarith [t.2.2])
      (mul_nonneg t.2.1 (sq_nonneg y))
  · linarith [t.2.2]

theorem fourPortRightRadicand_nonneg (t : FourPortRightRegularTime) (x : ℝ) :
    0 ≤ fourPortRightRadicand t x := by
  apply div_nonneg
  · exact add_nonneg (by linarith [t.2.1])
      (mul_nonneg (by linarith [t.2.2]) (sq_nonneg x))
  · linarith [t.2.1]

/-- One of the four left-side half-branches.  `ex` chooses the left or right
component and `ey` chooses its lower or upper half. -/
def fourPortLeftArmPoint (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) : FourPortPlane :=
  (ex.value * Real.sqrt (fourPortLeftRadicand t (ey.value * s.1)),
    ey.value * s.1)

/-- One of the four right-side half-branches. -/
def fourPortRightArmPoint (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) : FourPortPlane :=
  (ex.value * s.1,
    ey.value * Real.sqrt (fourPortRightRadicand t (ex.value * s.1)))

theorem fourPortLeftArmPoint_mem_region (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    fourPortLeftArmPoint t ex ey s ∈ fourPortQuadraticRegion := by
  have hs : s.1 ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)]
  have hrad := fourPortLeftRadicand_nonneg t (ey.value * s.1)
  have hden : 0 < 1 - t.1 := by linarith [t.2.2]
  change (ex.value * Real.sqrt
      (fourPortLeftRadicand t (ey.value * s.1))) ^ 2 +
      (ey.value * s.1) ^ 2 ≤ 2
  rw [mul_pow, ex.value_sq, one_mul, Real.sq_sqrt hrad,
    mul_pow, ey.value_sq, one_mul]
  have heq :
      fourPortLeftRadicand t (ey.value * s.1) + s.1 ^ 2 =
        (1 - 2 * t.1 + t.1 * (ey.value * s.1) ^ 2 +
          s.1 ^ 2 * (1 - t.1)) / (1 - t.1) := by
    unfold fourPortLeftRadicand
    field_simp [hden.ne']
  rw [heq]
  apply (div_le_iff₀ hden).2
  rw [mul_pow, ey.value_sq, one_mul]
  nlinarith

theorem fourPortRightArmPoint_mem_region (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    fourPortRightArmPoint t ex ey s ∈ fourPortQuadraticRegion := by
  have hs : s.1 ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)]
  have hrad := fourPortRightRadicand_nonneg t (ex.value * s.1)
  have hden : 0 < t.1 := by linarith [t.2.1]
  change (ex.value * s.1) ^ 2 +
      (ey.value * Real.sqrt
        (fourPortRightRadicand t (ex.value * s.1))) ^ 2 ≤ 2
  rw [mul_pow, ex.value_sq, one_mul, mul_pow, ey.value_sq, one_mul,
    Real.sq_sqrt hrad]
  have heq :
      s.1 ^ 2 + fourPortRightRadicand t (ex.value * s.1) =
        (s.1 ^ 2 * t.1 + 2 * t.1 - 1 +
          (1 - t.1) * (ex.value * s.1) ^ 2) / t.1 := by
    unfold fourPortRightRadicand
    field_simp [hden.ne']
    ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  rw [mul_pow, ex.value_sq, one_mul]
  nlinarith

theorem fourPortMorseHeight_leftArmPoint (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    fourPortMorseHeight t (fourPortLeftArmPoint t ex ey s) = 0 := by
  have hrad := fourPortLeftRadicand_nonneg t (ey.value * s.1)
  have hden : 1 - t.1 ≠ 0 := by linarith [t.2.2]
  simp only [fourPortMorseHeight, fourPortVerticalHeight,
    fourPortHorizontalHeight, fourPortLeftArmPoint, mul_pow,
    FourPortSign.value_sq, one_mul, Real.sq_sqrt hrad]
  unfold fourPortLeftRadicand
  field_simp [hden]
  rw [ey.value_sq]
  ring

theorem fourPortMorseHeight_rightArmPoint (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    fourPortMorseHeight t (fourPortRightArmPoint t ex ey s) = 0 := by
  have hrad := fourPortRightRadicand_nonneg t (ex.value * s.1)
  have hden : t.1 ≠ 0 := by linarith [t.2.1]
  simp only [fourPortMorseHeight, fourPortVerticalHeight,
    fourPortHorizontalHeight, fourPortRightArmPoint, mul_pow,
    FourPortSign.value_sq, one_mul, Real.sq_sqrt hrad]
  unfold fourPortRightRadicand
  field_simp [hden]
  rw [ex.value_sq]
  ring

theorem continuous_fourPortLeftArmPoint (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) :
    Continuous (fourPortLeftArmPoint t ex ey) := by
  unfold fourPortLeftArmPoint fourPortLeftRadicand
  fun_prop

theorem continuous_fourPortRightArmPoint (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) :
    Continuous (fourPortRightArmPoint t ex ey) := by
  unfold fourPortRightArmPoint fourPortRightRadicand
  fun_prop

/-- Keeping the two port signs and the arm parameter fixed gives the canonical
matching between any two regular times on the left of the crossing. -/
theorem continuous_fourPortLeftArmFamily (ex ey : FourPortSign) :
    Continuous (fun z : FourPortLeftRegularTime × FourPortArmParameter ↦
      fourPortLeftArmPoint z.1 ex ey z.2) := by
  unfold fourPortLeftArmPoint fourPortLeftRadicand
  have ht : Continuous (fun z : FourPortLeftRegularTime × FourPortArmParameter ↦
      (z.1.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun z : FourPortLeftRegularTime × FourPortArmParameter ↦
      (z.2.1 : ℝ)) := continuous_subtype_val.comp continuous_snd
  have hrad : Continuous (fun z : FourPortLeftRegularTime × FourPortArmParameter ↦
      (1 - 2 * z.1.1 + z.1.1 * (ey.value * z.2.1) ^ 2) /
        (1 - z.1.1)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z hz
      exact (by linarith [z.1.2.2] : 1 - z.1.1 ≠ 0) hz
  exact (continuous_const.mul (Real.continuous_sqrt.comp hrad)).prodMk
    (continuous_const.mul hs)

/-- Keeping the two port signs and the arm parameter fixed gives the canonical
matching between any two regular times on the right of the crossing. -/
theorem continuous_fourPortRightArmFamily (ex ey : FourPortSign) :
    Continuous (fun z : FourPortRightRegularTime × FourPortArmParameter ↦
      fourPortRightArmPoint z.1 ex ey z.2) := by
  unfold fourPortRightArmPoint fourPortRightRadicand
  have ht : Continuous (fun z : FourPortRightRegularTime × FourPortArmParameter ↦
      (z.1.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun z : FourPortRightRegularTime × FourPortArmParameter ↦
      (z.2.1 : ℝ)) := continuous_subtype_val.comp continuous_snd
  have hrad : Continuous (fun z : FourPortRightRegularTime × FourPortArmParameter ↦
      (2 * z.1.1 - 1 + (1 - z.1.1) * (ex.value * z.2.1) ^ 2) /
        z.1.1) := by
    apply Continuous.div
    · fun_prop
    · exact ht
    · intro z hz
      exact (by linarith [z.1.2.1] : z.1.1 ≠ 0) hz
  exact (continuous_const.mul hs).prodMk
    (continuous_const.mul (Real.continuous_sqrt.comp hrad))

theorem fourPortLeftArmPoint_injective (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) :
    Function.Injective (fourPortLeftArmPoint t ex ey) := by
  intro s v hsv
  apply Subtype.ext
  have hy := congrArg Prod.snd hsv
  cases ey <;> simp [fourPortLeftArmPoint] at hy <;> linarith

theorem fourPortRightArmPoint_injective (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) :
    Function.Injective (fourPortRightArmPoint t ex ey) := by
  intro s v hsv
  apply Subtype.ext
  have hx := congrArg Prod.fst hsv
  cases ex <;> simp [fourPortRightArmPoint] at hx <;> linarith

/-- Every left-regular zero is on one of the four explicit half-branches. -/
theorem exists_fourPortLeftArmPoint_eq (t : FourPortLeftRegularTime)
    {u : FourPortPlane} (huQ : u ∈ fourPortQuadraticRegion)
    (hu0 : fourPortMorseHeight t u = 0) :
    ∃ ex ey s, fourPortLeftArmPoint t ex ey s = u := by
  rcases u with ⟨x, y⟩
  have hden : 0 < 1 - t.1 := by linarith [t.2.2]
  change x ^ 2 + y ^ 2 ≤ 2 at huQ
  have hQ : x ^ 2 + y ^ 2 - 2 ≤ 0 := by linarith
  have hmul : (1 - t.1) * (x ^ 2 + y ^ 2 - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hden.le hQ
  have hySq : y ^ 2 ≤ 1 := by
    simp only [fourPortMorseHeight, fourPortVerticalHeight,
      fourPortHorizontalHeight] at hu0
    nlinarith
  have hxSq : x ^ 2 = fourPortLeftRadicand t y := by
    unfold fourPortLeftRadicand
    apply (eq_div_iff hden.ne').2
    simp only [fourPortMorseHeight, fourPortVerticalHeight,
      fourPortHorizontalHeight] at hu0
    nlinarith
  have hsqrt : Real.sqrt (fourPortLeftRadicand t y) = |x| := by
    rw [← hxSq, Real.sqrt_sq_eq_abs]
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · let s : FourPortArmParameter := ⟨y, ⟨hy, by nlinarith⟩⟩
      refine ⟨FourPortSign.pos, FourPortSign.pos, s, ?_⟩
      simp [fourPortLeftArmPoint, s, hsqrt, abs_of_nonneg hx]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      let s : FourPortArmParameter := ⟨-y, ⟨by linarith, by nlinarith⟩⟩
      refine ⟨FourPortSign.pos, FourPortSign.neg, s, ?_⟩
      simp [fourPortLeftArmPoint, s, hsqrt, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · let s : FourPortArmParameter := ⟨y, ⟨hy, by nlinarith⟩⟩
      refine ⟨FourPortSign.neg, FourPortSign.pos, s, ?_⟩
      simp [fourPortLeftArmPoint, s, hsqrt, abs_of_nonpos hx']
    · have hy' : y ≤ 0 := le_of_not_ge hy
      let s : FourPortArmParameter := ⟨-y, ⟨by linarith, by nlinarith⟩⟩
      refine ⟨FourPortSign.neg, FourPortSign.neg, s, ?_⟩
      simp [fourPortLeftArmPoint, s, hsqrt, abs_of_nonpos hx']

/-- Every right-regular zero is on one of the four explicit half-branches. -/
theorem exists_fourPortRightArmPoint_eq (t : FourPortRightRegularTime)
    {u : FourPortPlane} (huQ : u ∈ fourPortQuadraticRegion)
    (hu0 : fourPortMorseHeight t u = 0) :
    ∃ ex ey s, fourPortRightArmPoint t ex ey s = u := by
  rcases u with ⟨x, y⟩
  change x ^ 2 + y ^ 2 ≤ 2 at huQ
  have hQ : x ^ 2 + y ^ 2 - 2 ≤ 0 := by linarith
  have hmul : t.1 * (x ^ 2 + y ^ 2 - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [t.2.1]) hQ
  have hxSqOne : x ^ 2 ≤ 1 := by
    simp only [fourPortMorseHeight, fourPortVerticalHeight,
      fourPortHorizontalHeight] at hu0
    nlinarith
  have hySq : y ^ 2 = fourPortRightRadicand t x := by
    unfold fourPortRightRadicand
    apply (eq_div_iff (by linarith [t.2.1] : t.1 ≠ 0)).2
    simp only [fourPortMorseHeight, fourPortVerticalHeight,
      fourPortHorizontalHeight] at hu0
    nlinarith
  have hsqrt : Real.sqrt (fourPortRightRadicand t x) = |y| := by
    rw [← hySq, Real.sqrt_sq_eq_abs]
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · let s : FourPortArmParameter := ⟨x, ⟨hx, by nlinarith⟩⟩
      refine ⟨FourPortSign.pos, FourPortSign.pos, s, ?_⟩
      simp [fourPortRightArmPoint, s, hsqrt, abs_of_nonneg hy]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      let s : FourPortArmParameter := ⟨x, ⟨hx, by nlinarith⟩⟩
      refine ⟨FourPortSign.pos, FourPortSign.neg, s, ?_⟩
      simp [fourPortRightArmPoint, s, hsqrt, abs_of_nonpos hy']
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · let s : FourPortArmParameter := ⟨-x, ⟨by linarith, by nlinarith⟩⟩
      refine ⟨FourPortSign.neg, FourPortSign.pos, s, ?_⟩
      simp [fourPortRightArmPoint, s, hsqrt, abs_of_nonneg hy]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      let s : FourPortArmParameter := ⟨-x, ⟨by linarith, by nlinarith⟩⟩
      refine ⟨FourPortSign.neg, FourPortSign.neg, s, ?_⟩
      simp [fourPortRightArmPoint, s, hsqrt, abs_of_nonpos hy']

/-- The four left half-branches, as a planar set. -/
def fourPortLeftArmCarrier (t : FourPortLeftRegularTime) : Set FourPortPlane :=
  ⋃ ex, ⋃ ey, Set.range (fourPortLeftArmPoint t ex ey)

/-- The four right half-branches, as a planar set. -/
def fourPortRightArmCarrier (t : FourPortRightRegularTime) : Set FourPortPlane :=
  ⋃ ex, ⋃ ey, Set.range (fourPortRightArmPoint t ex ey)

theorem fourPortLeftArmCarrier_eq_zeroCarrier (t : FourPortLeftRegularTime) :
    fourPortLeftArmCarrier t =
      fourPortQuadraticRegion ∩ fourPortMorseHeight t ⁻¹' {0} := by
  ext u
  constructor
  · simp only [fourPortLeftArmCarrier, mem_iUnion, mem_range,
      mem_inter_iff, mem_preimage, mem_singleton_iff]
    rintro ⟨ex, ey, s, rfl⟩
    exact ⟨fourPortLeftArmPoint_mem_region t ex ey s,
      fourPortMorseHeight_leftArmPoint t ex ey s⟩
  · rintro ⟨huQ, hu0⟩
    obtain ⟨ex, ey, s, rfl⟩ := exists_fourPortLeftArmPoint_eq t huQ hu0
    simp only [fourPortLeftArmCarrier, mem_iUnion, mem_range]
    exact ⟨ex, ey, s, rfl⟩

theorem fourPortRightArmCarrier_eq_zeroCarrier (t : FourPortRightRegularTime) :
    fourPortRightArmCarrier t =
      fourPortQuadraticRegion ∩ fourPortMorseHeight t ⁻¹' {0} := by
  ext u
  constructor
  · simp only [fourPortRightArmCarrier, mem_iUnion, mem_range,
      mem_inter_iff, mem_preimage, mem_singleton_iff]
    rintro ⟨ex, ey, s, rfl⟩
    exact ⟨fourPortRightArmPoint_mem_region t ex ey s,
      fourPortMorseHeight_rightArmPoint t ex ey s⟩
  · rintro ⟨huQ, hu0⟩
    obtain ⟨ex, ey, s, rfl⟩ := exists_fourPortRightArmPoint_eq t huQ hu0
    simp only [fourPortRightArmCarrier, mem_iUnion, mem_range]
    exact ⟨ex, ey, s, rfl⟩

/-! ## Transport through a global band chart -/

namespace FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

def globalBandFourPortLeftArm
    (T : GlobalBandTubularChartData F b) (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) : Circle × Circle :=
  globalBandFourPortBase T
    ⟨fourPortLeftArmPoint t ex ey s,
      fourPortLeftArmPoint_mem_region t ex ey s⟩

def globalBandFourPortRightArm
    (T : GlobalBandTubularChartData F b) (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) : Circle × Circle :=
  globalBandFourPortBase T
    ⟨fourPortRightArmPoint t ex ey s,
      fourPortRightArmPoint_mem_region t ex ey s⟩

theorem continuous_globalBandFourPortLeftArm
    (T : GlobalBandTubularChartData F b) (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) :
    Continuous (globalBandFourPortLeftArm T t ex ey) := by
  apply (globalBandFourPortBase_continuous T).comp
  exact Continuous.subtype_mk (continuous_fourPortLeftArmPoint t ex ey) _

theorem continuous_globalBandFourPortRightArm
    (T : GlobalBandTubularChartData F b) (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) :
    Continuous (globalBandFourPortRightArm T t ex ey) := by
  apply (globalBandFourPortBase_continuous T).comp
  exact Continuous.subtype_mk (continuous_fourPortRightArmPoint t ex ey) _

theorem continuous_globalBandFourPortLeftArmFamily
    (T : GlobalBandTubularChartData F b) (ex ey : FourPortSign) :
    Continuous (fun z : FourPortLeftRegularTime × FourPortArmParameter ↦
      globalBandFourPortLeftArm T z.1 ex ey z.2) := by
  apply (globalBandFourPortBase_continuous T).comp
  exact Continuous.subtype_mk (continuous_fourPortLeftArmFamily ex ey) _

theorem continuous_globalBandFourPortRightArmFamily
    (T : GlobalBandTubularChartData F b) (ex ey : FourPortSign) :
    Continuous (fun z : FourPortRightRegularTime × FourPortArmParameter ↦
      globalBandFourPortRightArm T z.1 ex ey z.2) := by
  apply (globalBandFourPortBase_continuous T).comp
  exact Continuous.subtype_mk (continuous_fourPortRightArmFamily ex ey) _

theorem globalBandFourPortMorseGraph_leftArm_mem_transportedTorus
    (T : GlobalBandTubularChartData F b) (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    globalBandFourPortMorseGraph T (fourPortLeftTime t)
        ⟨fourPortLeftArmPoint t ex ey s,
          fourPortLeftArmPoint_mem_region t ex ey s⟩ ∈ transportedTorus Phi := by
  rw [globalBandFourPortMorseGraph_mem_transportedTorus_iff]
  exact fourPortMorseHeight_leftArmPoint t ex ey s

theorem globalBandFourPortMorseGraph_rightArm_mem_transportedTorus
    (T : GlobalBandTubularChartData F b) (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    globalBandFourPortMorseGraph T (fourPortRightTime t)
        ⟨fourPortRightArmPoint t ex ey s,
          fourPortRightArmPoint_mem_region t ex ey s⟩ ∈ transportedTorus Phi := by
  rw [globalBandFourPortMorseGraph_mem_transportedTorus_iff]
  exact fourPortMorseHeight_rightArmPoint t ex ey s

theorem globalBandFourPortMorseGraph_leftArm_eq_chart
    (T : GlobalBandTubularChartData F b) (t : FourPortLeftRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    globalBandFourPortMorseGraph T (fourPortLeftTime t)
        ⟨fourPortLeftArmPoint t ex ey s,
          fourPortLeftArmPoint_mem_region t ex ey s⟩ =
      T.toPairedSeamBandChart.chart (fourPortLeftArmPoint t ex ey s) := by
  exact globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
    (fourPortLeftTime t) _ (fourPortMorseHeight_leftArmPoint t ex ey s)

theorem globalBandFourPortMorseGraph_rightArm_eq_chart
    (T : GlobalBandTubularChartData F b) (t : FourPortRightRegularTime)
    (ex ey : FourPortSign) (s : FourPortArmParameter) :
    globalBandFourPortMorseGraph T (fourPortRightTime t)
        ⟨fourPortRightArmPoint t ex ey s,
          fourPortRightArmPoint_mem_region t ex ey s⟩ =
      T.toPairedSeamBandChart.chart (fourPortRightArmPoint t ex ey s) := by
  exact globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
    (fourPortRightTime t) _ (fourPortMorseHeight_rightArmPoint t ex ey s)

end FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

/-! ## Closed-loop continuation and charging -/

open Submission.PardonDistortion.SuperellipsoidDoubleBubbleSelection

/-- A closed regular-side four-port homotopy with the precise transverse data
that is not present in `GlobalBandTubularChartData` itself.  Endpoint fiber
identifications only identify parameterizations with endpoint fibers.  The
matching between the two endpoints is constructed by covering monodromy. -/
structure FourPortRegularChargingHomotopy
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
    {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (sourceLoop targetLoop : ℝ → Circle × Circle)
    (m n : ℤ) where
  circleHomotopy : ℝ → Circle → Circle × Circle
  atlas : CircleIntersectionLocalGraphAtlas p q circleHomotopy
  continuous_circleHomotopy : Continuous (Function.uncurry circleHomotopy)
  source_eq : (fun u ↦ circleHomotopy 0 (Circle.exp u)) = sourceLoop
  target_eq : (fun u ↦ circleHomotopy 1 (Circle.exp u)) = targetLoop
  sourceCertificate : TransverseIntersectionCertificate p q sourceLoop m n
  sourceCharging : LoopCharging selection p q sourceLoop
  sourceFiberEquiv : {t // t ∈ sourceCertificate.parameters} ≃
    (circleIntersectionProjection (p := p) (q := q) (H := circleHomotopy) ⁻¹'
      {(0 : unitInterval)})
  targetFiberEquiv :
    (circleIntersectionProjection (p := p) (q := q) (H := circleHomotopy) ⁻¹'
      {(1 : unitInterval)}) ≃
    {z // z ∈ circleLoopIntersectionParameters p q (circleHomotopy 1)}

namespace FourPortRegularChargingHomotopy

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  {p q : ℕ} {sourceLoop targetLoop : ℝ → Circle × Circle} {m n : ℤ}

theorem transversality
    (D : FourPortRegularChargingHomotopy selection p q sourceLoop targetLoop m n) :
    CircleIntersectionTransversality p q D.circleHomotopy :=
  D.atlas.toTransversality D.continuous_circleHomotopy

def endpointBridge
    (D : FourPortRegularChargingHomotopy selection p q sourceLoop targetLoop m n) :
    CircleCoveringEndpointBridge p q D.circleHomotopy D.sourceCertificate
      D.transversality where
  homotopy_zero := D.source_eq
  sourceFiberEquiv := D.sourceFiberEquiv
  targetFiberEquiv := D.targetFiberEquiv

/-- The sign-preserving endpoint continuation obtained from regular covering
monodromy. -/
def regularIntersectionContinuation
    (D : FourPortRegularChargingHomotopy selection p q sourceLoop targetLoop m n) :
    RegularIntersectionContinuation p q sourceLoop targetLoop m n
      D.sourceCertificate := by
  let R := D.endpointBridge.toRegularIntersectionContinuation
  exact {
    homotopy := R.homotopy
    continuous_homotopy := R.continuous_homotopy
    periodic_homotopy := R.periodic_homotopy
    homotopy_zero := R.homotopy_zero
    homotopy_one := R.homotopy_one.trans D.target_eq
    targetParameters := R.targetParameters
    targetParameters_eq := R.targetParameters_eq.trans
      (congrArg (torusLoopIntersectionParameters p q) D.target_eq)
    matching := R.matching
    targetSign := R.targetSign
    targetSign_natAbs := R.targetSign_natAbs
    sign_preserved := R.sign_preserved
  }

/-- The downstream charging package.  In particular, its endpoint matching
is derived from the regular intersection covering rather than supplied as a
field. -/
def toSmoothedLoopChargingTransport
    (D : FourPortRegularChargingHomotopy selection p q sourceLoop targetLoop m n) :
    SmoothedLoopChargingTransport selection p q targetLoop m n where
  sourceLoop := sourceLoop
  sourceCertificate := D.sourceCertificate
  sourceCharging := D.sourceCharging
  continuation := D.regularIntersectionContinuation

end FourPortRegularChargingHomotopy

end Submission.Topology
