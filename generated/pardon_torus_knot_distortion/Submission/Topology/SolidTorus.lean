import Submission.Topology.Representativity

/-!
# Coordinate extensions over the two sides of the standard torus

The standard torus is the level set `tubeGauge = 1`.  On the closed tube side,
the complex `xy` coordinate never vanishes, so its circle direction extends the
longitude coordinate.  On the closed exterior side, the complex coordinate
`(cylindricalRadius - 2) + z * I` never vanishes, so its circle direction
extends the meridian coordinate.

For elementary continuity it is convenient to use `conj z / z`, whose angle is
minus twice the angle of `z`.  This doubled coordinate is just as effective for
winding: extension over a disk forces `-2m = 0` or `-2n = 0`, hence forces the
corresponding slope coefficient to vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ComplexConjugate

noncomputable section

namespace Submission.PardonDistortion

/-- Cylindrical radius about the third coordinate axis. -/
def cylindricalRadius (x : R3) : ℝ :=
  Real.sqrt (x 0 ^ 2 + x 1 ^ 2)

/-- Squared distance from the core circle in the meridional half-plane. -/
def tubeGauge (x : R3) : ℝ :=
  (cylindricalRadius x - 2) ^ 2 + x 2 ^ 2

/-- The closed solid-torus side of the standard torus. -/
def standardTubeSide : Set R3 :=
  {x | tubeGauge x ≤ 1}

/-- The closed exterior side of the standard torus. -/
def standardExteriorSide : Set R3 :=
  {x | 1 ≤ tubeGauge x}

theorem geometricStandardTorus_eq_gauge_level :
    Submission.Torus.geometricStandardTorus = {x | tubeGauge x = 1} := by
  rfl

lemma cylindricalRadius_nonneg (x : R3) : 0 ≤ cylindricalRadius x := by
  exact Real.sqrt_nonneg _

lemma one_le_cylindricalRadius_of_mem_standardTubeSide
    {x : R3} (hx : x ∈ standardTubeSide) :
    1 ≤ cylindricalRadius x := by
  have hz : 0 ≤ x 2 ^ 2 := sq_nonneg _
  change (cylindricalRadius x - 2) ^ 2 + x 2 ^ 2 ≤ 1 at hx
  nlinarith [cylindricalRadius_nonneg x]

/-- The first two real coordinates regarded as one complex coordinate. -/
def xyComplex (x : R3) : ℂ :=
  (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

@[simp] lemma xyComplex_re (x : R3) : (xyComplex x).re = x 0 := by
  simp [xyComplex]

@[simp] lemma xyComplex_im (x : R3) : (xyComplex x).im = x 1 := by
  simp [xyComplex]

lemma norm_xyComplex (x : R3) : ‖xyComplex x‖ = cylindricalRadius x := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp [cylindricalRadius]

lemma xyComplex_ne_zero_of_mem_standardTubeSide
    {x : R3} (hx : x ∈ standardTubeSide) : xyComplex x ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_xyComplex]
  exact ((one_le_cylindricalRadius_of_mem_standardTubeSide hx).trans_lt'
    zero_lt_one).ne'

/-- The meridional complex coordinate, centered at cylindrical radius two. -/
def meridionalComplex (x : R3) : ℂ :=
  ((cylindricalRadius x - 2 : ℝ) : ℂ) + (x 2 : ℂ) * Complex.I

@[simp] lemma meridionalComplex_re (x : R3) :
    (meridionalComplex x).re = cylindricalRadius x - 2 := by
  simp [meridionalComplex]

@[simp] lemma meridionalComplex_im (x : R3) :
    (meridionalComplex x).im = x 2 := by
  simp [meridionalComplex]

lemma meridionalComplex_ne_zero_of_mem_standardExteriorSide
    {x : R3} (hx : x ∈ standardExteriorSide) : meridionalComplex x ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [meridionalComplex_re] at hre
  simp only [meridionalComplex_im] at him
  norm_num at hre him
  change 1 ≤ (cylindricalRadius x - 2) ^ 2 + x 2 ^ 2 at hx
  nlinarith

/-- The doubled angular coordinate of a nonzero complex number. -/
def doubledCircleCoordinate (z : ℂ) (hz : z ≠ 0) : Circle :=
  Circle.ofConjDivSelf z hz

/-- The doubled longitude coordinate extended over the tube side. -/
def tubeLongitudeCoordinate (x : standardTubeSide) : Circle :=
  doubledCircleCoordinate (xyComplex x)
    (xyComplex_ne_zero_of_mem_standardTubeSide x.property)

/-- The doubled meridian coordinate extended over the exterior side. -/
def exteriorMeridianCoordinate (x : standardExteriorSide) : Circle :=
  doubledCircleCoordinate (meridionalComplex x)
    (meridionalComplex_ne_zero_of_mem_standardExteriorSide x.property)

lemma continuous_cylindricalRadius : Continuous cylindricalRadius := by
  unfold cylindricalRadius
  fun_prop

lemma continuous_xyComplex : Continuous xyComplex := by
  unfold xyComplex
  fun_prop

lemma continuous_meridionalComplex : Continuous meridionalComplex := by
  unfold meridionalComplex
  exact ((Complex.continuous_ofReal.comp
    (continuous_cylindricalRadius.sub continuous_const)).add
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const))

lemma continuous_tubeGauge : Continuous tubeGauge := by
  unfold tubeGauge
  exact ((continuous_cylindricalRadius.sub continuous_const).pow 2).add
    ((by fun_prop : Continuous fun x : R3 ↦ x 2).pow 2)

lemma continuous_tubeLongitudeCoordinate :
    Continuous tubeLongitudeCoordinate := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_conj.comp
    (continuous_xyComplex.comp continuous_subtype_val)).div
    (continuous_xyComplex.comp continuous_subtype_val)
    (fun x ↦ xyComplex_ne_zero_of_mem_standardTubeSide x.property)

lemma continuous_exteriorMeridianCoordinate :
    Continuous exteriorMeridianCoordinate := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_conj.comp
    (continuous_meridionalComplex.comp continuous_subtype_val)).div
    (continuous_meridionalComplex.comp continuous_subtype_val)
    (fun x ↦ meridionalComplex_ne_zero_of_mem_standardExteriorSide x.property)

lemma circle_re_lower_bound (z : Circle) : -1 ≤ (z : ℂ).re := by
  have h := Complex.abs_re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at h
  exact neg_le_of_abs_le h

lemma circle_re_im_sq (z : Circle) :
    (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  simpa [Complex.normSq_apply, pow_two] using
    (show Complex.normSq (z : ℂ) = 1 by simp)

lemma xyComplex_circleTorusMap (z w : Circle) :
    xyComplex (Submission.Torus.circleTorusMap z w) =
      (((2 + (w : ℂ).re : ℝ) : ℂ) * (z : ℂ)) := by
  apply Complex.ext <;>
    simp [xyComplex, Submission.Torus.circleTorusMap]

lemma cylindricalRadius_circleTorusMap (z w : Circle) :
    cylindricalRadius (Submission.Torus.circleTorusMap z w) =
      2 + (w : ℂ).re := by
  unfold cylindricalRadius
  rw [show
      (Submission.Torus.circleTorusMap z w 0) ^ 2 +
          (Submission.Torus.circleTorusMap z w 1) ^ 2 =
        (2 + (w : ℂ).re) ^ 2 by
    simp only [Submission.Torus.circleTorusMap_coord_zero,
      Submission.Torus.circleTorusMap_coord_one]
    nlinarith [circle_re_im_sq z]]
  rw [Real.sqrt_sq]
  linarith [circle_re_lower_bound w]

lemma meridionalComplex_circleTorusMap (z w : Circle) :
    meridionalComplex (Submission.Torus.circleTorusMap z w) = (w : ℂ) := by
  apply Complex.ext
  · rw [meridionalComplex_re, cylindricalRadius_circleTorusMap]
    simp
  · rw [meridionalComplex_im,
      Submission.Torus.circleTorusMap_coord_two]

lemma circleTorusMap_tubeGauge (z w : Circle) :
    tubeGauge (Submission.Torus.circleTorusMap z w) = 1 := by
  rw [tubeGauge, cylindricalRadius_circleTorusMap,
    Submission.Torus.circleTorusMap_coord_two]
  nlinarith [circle_re_im_sq w]

lemma circleTorusMap_mem_standardTubeSide (z w : Circle) :
    Submission.Torus.circleTorusMap z w ∈ standardTubeSide := by
  change tubeGauge (Submission.Torus.circleTorusMap z w) ≤ 1
  rw [circleTorusMap_tubeGauge]

lemma circleTorusMap_mem_standardExteriorSide (z w : Circle) :
    Submission.Torus.circleTorusMap z w ∈ standardExteriorSide := by
  change 1 ≤ tubeGauge (Submission.Torus.circleTorusMap z w)
  rw [circleTorusMap_tubeGauge]

lemma tubeLongitudeCoordinate_circleTorusMap (z w : Circle) :
    tubeLongitudeCoordinate
      ⟨Submission.Torus.circleTorusMap z w,
        circleTorusMap_mem_standardTubeSide z w⟩ = z⁻¹ ^ 2 := by
  apply Circle.ext
  change conj
      (xyComplex (Submission.Torus.circleTorusMap z w)) /
      xyComplex (Submission.Torus.circleTorusMap z w) = ((z : ℂ)⁻¹) ^ 2
  rw [xyComplex_circleTorusMap]
  have ha : (2 + (w : ℂ).re : ℝ) ≠ 0 := by
    linarith [circle_re_lower_bound w]
  have hnorm : Complex.normSq (z : ℂ) = 1 := by simp
  have hz : (z : ℂ) ≠ 0 := by
    intro hz
    rw [hz] at hnorm
    norm_num at hnorm
  have hconj : conj (z : ℂ) = (z : ℂ)⁻¹ := by
    rw [Complex.inv_def, hnorm]
    simp
  rw [map_mul, Complex.conj_ofReal, hconj]
  have haComplex : ((2 + (w : ℂ).re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ha
  rw [mul_div_mul_left _ _ haComplex]
  field_simp [hz]

lemma exteriorMeridianCoordinate_circleTorusMap (z w : Circle) :
    exteriorMeridianCoordinate
      ⟨Submission.Torus.circleTorusMap z w,
        circleTorusMap_mem_standardExteriorSide z w⟩ = w⁻¹ ^ 2 := by
  apply Circle.ext
  change conj
      (meridionalComplex (Submission.Torus.circleTorusMap z w)) /
      meridionalComplex (Submission.Torus.circleTorusMap z w) = ((w : ℂ)⁻¹) ^ 2
  rw [meridionalComplex_circleTorusMap]
  have hnorm : Complex.normSq (w : ℂ) = 1 := by simp
  have hw : (w : ℂ) ≠ 0 := by
    intro hw
    rw [hw] at hnorm
    norm_num at hnorm
  have hconj : conj (w : ℂ) = (w : ℂ)⁻¹ := by
    rw [Complex.inv_def, hnorm]
    simp
  rw [hconj]
  field_simp [hw]

lemma circle_exp_inv_sq (theta : ℝ) :
    (Circle.exp theta)⁻¹ ^ 2 = Circle.exp (-2 * theta) := by
  rw [← Circle.exp_neg, ← Circle.exp_nsmul]
  congr 1
  simp

/-! ## Transport through the ambient homeomorphism -/

/-- The tube side pulled back to the original coordinates of the knot. -/
def transportedTubeSide (Phi : AmbientIsotopy) : Set R3 :=
  {x | Phi.H 1 x ∈ standardTubeSide}

/-- The exterior side pulled back to the original coordinates of the knot. -/
def transportedExteriorSide (Phi : AmbientIsotopy) : Set R3 :=
  {x | Phi.H 1 x ∈ standardExteriorSide}

/-- The doubled longitude coordinate on the transported tube side. -/
def transportedTubeLongitudeCoordinate (Phi : AmbientIsotopy)
    (x : transportedTubeSide Phi) : Circle :=
  tubeLongitudeCoordinate ⟨Phi.H 1 x, x.property⟩

/-- The doubled meridian coordinate on the transported exterior side. -/
def transportedExteriorMeridianCoordinate (Phi : AmbientIsotopy)
    (x : transportedExteriorSide Phi) : Circle :=
  exteriorMeridianCoordinate ⟨Phi.H 1 x, x.property⟩

lemma continuous_timeOne_map (Phi : AmbientIsotopy) :
    Continuous (Phi.H 1) :=
  Phi.smooth.continuous.comp (continuous_const.prodMk continuous_id)

lemma continuous_transportedTubeLongitudeCoordinate (Phi : AmbientIsotopy) :
    Continuous (transportedTubeLongitudeCoordinate Phi) := by
  apply continuous_tubeLongitudeCoordinate.comp
  exact (continuous_timeOne_map Phi).comp continuous_subtype_val |>.subtype_mk _

lemma continuous_transportedExteriorMeridianCoordinate
    (Phi : AmbientIsotopy) :
    Continuous (transportedExteriorMeridianCoordinate Phi) := by
  apply continuous_exteriorMeridianCoordinate.comp
  exact (continuous_timeOne_map Phi).comp continuous_subtype_val |>.subtype_mk _

lemma transportedTorusMap_mem_transportedTubeSide
    (Phi : AmbientIsotopy) (z w : Circle) :
    Submission.Torus.transportedTorusMap Phi (z, w) ∈
      transportedTubeSide Phi := by
  change Phi.H 1 (Submission.Torus.transportedTorusMap Phi (z, w)) ∈
    standardTubeSide
  rw [Submission.Torus.timeOne_map_transportedTorusMap]
  exact circleTorusMap_mem_standardTubeSide z w

lemma transportedTorusMap_mem_transportedExteriorSide
    (Phi : AmbientIsotopy) (z w : Circle) :
    Submission.Torus.transportedTorusMap Phi (z, w) ∈
      transportedExteriorSide Phi := by
  change Phi.H 1 (Submission.Torus.transportedTorusMap Phi (z, w)) ∈
    standardExteriorSide
  rw [Submission.Torus.timeOne_map_transportedTorusMap]
  exact circleTorusMap_mem_standardExteriorSide z w

lemma transportedTubeLongitudeCoordinate_torusMap
    (Phi : AmbientIsotopy) (z w : Circle) :
    transportedTubeLongitudeCoordinate Phi
      ⟨Submission.Torus.transportedTorusMap Phi (z, w),
        transportedTorusMap_mem_transportedTubeSide Phi z w⟩ = z⁻¹ ^ 2 := by
  unfold transportedTubeLongitudeCoordinate
  rw [show
    (⟨Phi.H 1 (Submission.Torus.transportedTorusMap Phi (z, w)), by
        exact transportedTorusMap_mem_transportedTubeSide Phi z w⟩ :
      standardTubeSide) =
      ⟨Submission.Torus.circleTorusMap z w,
        circleTorusMap_mem_standardTubeSide z w⟩ by
    apply Subtype.ext
    exact Submission.Torus.timeOne_map_transportedTorusMap Phi (z, w)]
  exact tubeLongitudeCoordinate_circleTorusMap z w

lemma transportedExteriorMeridianCoordinate_torusMap
    (Phi : AmbientIsotopy) (z w : Circle) :
    transportedExteriorMeridianCoordinate Phi
      ⟨Submission.Torus.transportedTorusMap Phi (z, w),
        transportedTorusMap_mem_transportedExteriorSide Phi z w⟩ = w⁻¹ ^ 2 := by
  unfold transportedExteriorMeridianCoordinate
  rw [show
    (⟨Phi.H 1 (Submission.Torus.transportedTorusMap Phi (z, w)), by
        exact transportedTorusMap_mem_transportedExteriorSide Phi z w⟩ :
      standardExteriorSide) =
      ⟨Submission.Torus.circleTorusMap z w,
        circleTorusMap_mem_standardExteriorSide z w⟩ by
    apply Subtype.ext
    exact Submission.Torus.timeOne_map_transportedTorusMap Phi (z, w)]
  exact exteriorMeridianCoordinate_circleTorusMap z w

lemma transportedTubeLongitudeCoordinate_slopeLoop
    (Phi : AmbientIsotopy) (m n : ℤ) (phase₁ phase₂ t : ℝ) :
    transportedTubeLongitudeCoordinate Phi
      ⟨transportedSlopeLoop Phi m n phase₁ phase₂ t,
        transportedTorusMap_mem_transportedTubeSide Phi
          (Circle.exp ((m : ℝ) * t + phase₁))
          (Circle.exp ((n : ℝ) * t + phase₂))⟩ =
      Circle.exp (((-2 * m : ℤ) : ℝ) * t + (-2 * phase₁)) := by
  unfold transportedSlopeLoop
  rw [transportedTubeLongitudeCoordinate_torusMap, circle_exp_inv_sq]
  congr 1
  push_cast
  ring

lemma transportedExteriorMeridianCoordinate_slopeLoop
    (Phi : AmbientIsotopy) (m n : ℤ) (phase₁ phase₂ t : ℝ) :
    transportedExteriorMeridianCoordinate Phi
      ⟨transportedSlopeLoop Phi m n phase₁ phase₂ t,
        transportedTorusMap_mem_transportedExteriorSide Phi
          (Circle.exp ((m : ℝ) * t + phase₁))
          (Circle.exp ((n : ℝ) * t + phase₂))⟩ =
      Circle.exp (((-2 * n : ℤ) : ℝ) * t + (-2 * phase₂)) := by
  unfold transportedSlopeLoop
  rw [transportedExteriorMeridianCoordinate_torusMap, circle_exp_inv_sq]
  congr 1
  push_cast
  ring

/-! ## Consequences for a compressing disk contained on one side -/

/-- Every point of the disk lies on the transported tube side. -/
def CompressingDiskWitness.LiesInTubeSide {Phi : AmbientIsotopy}
    (D : CompressingDiskWitness Phi) : Prop :=
  ∀ z, D.disk z ∈ transportedTubeSide Phi

/-- Every point of the disk lies on the transported exterior side. -/
def CompressingDiskWitness.LiesInExteriorSide {Phi : AmbientIsotopy}
    (D : CompressingDiskWitness Phi) : Prop :=
  ∀ z, D.disk z ∈ transportedExteriorSide Phi

theorem CompressingDiskWitness.m_eq_zero_of_liesInTubeSide
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hside : D.LiesInTubeSide) : D.m = 0 := by
  let g : ClosedUnitDisk → transportedTubeSide Phi :=
    fun z ↦ ⟨D.disk z, hside z⟩
  have hg : Continuous g := D.continuous.subtype_mk _
  have hboundary : ∀ t : ℝ,
      transportedTubeLongitudeCoordinate Phi (g (unitDiskBoundary t)) =
        Circle.exp (((-2 * D.m : ℤ) : ℝ) * t + (-2 * D.phase₁)) := by
    intro t
    have hdisk := D.boundary t
    change transportedTubeLongitudeCoordinate Phi
      ⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedTubeSide Phi) =
      ⟨transportedSlopeLoop Phi D.m D.n D.phase₁ D.phase₂ t,
        transportedTorusMap_mem_transportedTubeSide Phi
          (Circle.exp ((D.m : ℝ) * t + D.phase₁))
          (Circle.exp ((D.n : ℝ) * t + D.phase₂))⟩ by
      apply Subtype.ext
      exact hdisk]
    exact transportedTubeLongitudeCoordinate_slopeLoop Phi
      D.m D.n D.phase₁ D.phase₂ t
  have hzero := winding_eq_zero_of_continuous_coordinate_filling
    (-2 * D.m) (-2 * D.phase₁) g hg
    (transportedTubeLongitudeCoordinate Phi)
    (continuous_transportedTubeLongitudeCoordinate Phi) hboundary
  omega

theorem CompressingDiskWitness.n_eq_zero_of_liesInExteriorSide
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hside : D.LiesInExteriorSide) : D.n = 0 := by
  let g : ClosedUnitDisk → transportedExteriorSide Phi :=
    fun z ↦ ⟨D.disk z, hside z⟩
  have hg : Continuous g := D.continuous.subtype_mk _
  have hboundary : ∀ t : ℝ,
      transportedExteriorMeridianCoordinate Phi (g (unitDiskBoundary t)) =
        Circle.exp (((-2 * D.n : ℤ) : ℝ) * t + (-2 * D.phase₂)) := by
    intro t
    have hdisk := D.boundary t
    change transportedExteriorMeridianCoordinate Phi
      ⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedExteriorSide Phi) =
      ⟨transportedSlopeLoop Phi D.m D.n D.phase₁ D.phase₂ t,
        transportedTorusMap_mem_transportedExteriorSide Phi
          (Circle.exp ((D.m : ℝ) * t + D.phase₁))
          (Circle.exp ((D.n : ℝ) * t + D.phase₂))⟩ by
      apply Subtype.ext
      exact hdisk]
    exact transportedExteriorMeridianCoordinate_slopeLoop Phi
      D.m D.n D.phase₁ D.phase₂ t
  have hzero := winding_eq_zero_of_continuous_coordinate_filling
    (-2 * D.n) (-2 * D.phase₂) g hg
    (transportedExteriorMeridianCoordinate Phi)
    (continuous_transportedExteriorMeridianCoordinate Phi) hboundary
  omega

/-! ## Embedded slope loops are primitive -/

lemma circle_exp_coe_eq_unitCircleParam (t : ℝ) :
    (Circle.exp t : ℂ) = unitCircleParam t := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  simp [unitCircleParam]

lemma unitDiskBoundary_injOn :
    Set.InjOn unitDiskBoundary (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hs ht
  apply Circle.ext
  rw [circle_exp_coe_eq_unitCircleParam,
    circle_exp_coe_eq_unitCircleParam]
  exact congrArg Subtype.val hst

private lemma slopeLoop_repeats_after_natAbs
    (Phi : AmbientIsotopy) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (hm : m = 0) (hn : n ≠ 0) :
    transportedSlopeLoop Phi m n phase₁ phase₂ 0 =
      transportedSlopeLoop Phi m n phase₁ phase₂
        (2 * Real.pi / (n.natAbs : ℝ)) := by
  have hN : (n.natAbs : ℝ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr hn
  have hnCast : (n : ℝ) = (n.sign : ℝ) * (n.natAbs : ℝ) := by
    have hInt : n = n.sign * (n.natAbs : ℤ) := n.sign_mul_natAbs.symm
    calc
      (n : ℝ) = ((n.sign * (n.natAbs : ℤ) : ℤ) : ℝ) :=
        congrArg (fun a : ℤ ↦ (a : ℝ)) hInt
      _ = (n.sign : ℝ) * (n.natAbs : ℝ) := by
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
  have hsnd :
      Circle.exp ((n : ℝ) * (2 * Real.pi / (n.natAbs : ℝ)) + phase₂) =
        Circle.exp phase₂ := by
    apply Circle.exp_eq_exp.mpr
    refine ⟨n.sign, ?_⟩
    rw [hnCast]
    field_simp [hN]
    ring
  unfold transportedSlopeLoop
  apply congrArg (Submission.Torus.transportedTorusMap Phi)
  apply Prod.ext
  · simp [hm]
  · simpa using hsnd.symm

private lemma slopeLoop_repeats_after_natAbs_first
    (Phi : AmbientIsotopy) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (hm : m ≠ 0) (hn : n = 0) :
    transportedSlopeLoop Phi m n phase₁ phase₂ 0 =
      transportedSlopeLoop Phi m n phase₁ phase₂
        (2 * Real.pi / (m.natAbs : ℝ)) := by
  have hM : (m.natAbs : ℝ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr hm
  have hmCast : (m : ℝ) = (m.sign : ℝ) * (m.natAbs : ℝ) := by
    have hInt : m = m.sign * (m.natAbs : ℤ) := m.sign_mul_natAbs.symm
    calc
      (m : ℝ) = ((m.sign * (m.natAbs : ℤ) : ℤ) : ℝ) :=
        congrArg (fun a : ℤ ↦ (a : ℝ)) hInt
      _ = (m.sign : ℝ) * (m.natAbs : ℝ) := by
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
  have hfst :
      Circle.exp ((m : ℝ) * (2 * Real.pi / (m.natAbs : ℝ)) + phase₁) =
        Circle.exp phase₁ := by
    apply Circle.exp_eq_exp.mpr
    refine ⟨m.sign, ?_⟩
    rw [hmCast]
    field_simp [hM]
    ring
  unfold transportedSlopeLoop
  apply congrArg (Submission.Torus.transportedTorusMap Phi)
  apply Prod.ext
  · simpa using hfst.symm
  · simp [hn]

theorem CompressingDiskWitness.n_natAbs_eq_one_of_m_eq_zero
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hm : D.m = 0) : D.n.natAbs = 1 := by
  have hn : D.n ≠ 0 := by
    rcases D.essential with hmne | hnne
    · exact (hmne hm).elim
    · exact hnne
  have hNpos : 0 < D.n.natAbs := Int.natAbs_pos.mpr hn
  by_contra hnone
  have hNtwo : 2 ≤ D.n.natAbs := by omega
  let delta : ℝ := 2 * Real.pi / (D.n.natAbs : ℝ)
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hdeltalt : delta < 2 * Real.pi := by
    dsimp [delta]
    have hNreal : (2 : ℝ) ≤ D.n.natAbs := by exact_mod_cast hNtwo
    have hNrealPos : (0 : ℝ) < D.n.natAbs := by positivity
    rw [div_lt_iff₀ hNrealPos]
    nlinarith [Real.pi_pos]
  have hboundaryImage :
      D.disk (unitDiskBoundary 0) = D.disk (unitDiskBoundary delta) := by
    rw [D.boundary, D.boundary]
    exact slopeLoop_repeats_after_natAbs Phi D.m D.n D.phase₁ D.phase₂ hm hn
  have hboundaryPoint := D.isEmbedding.injective hboundaryImage
  have hdeltaEq : (0 : ℝ) = delta :=
    unitDiskBoundary_injOn
      ⟨le_rfl, mul_pos zero_lt_two Real.pi_pos⟩
      ⟨hdelta0, hdeltalt⟩ hboundaryPoint
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) (by exact_mod_cast hNpos)
  linarith

theorem CompressingDiskWitness.m_natAbs_eq_one_of_n_eq_zero
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hn : D.n = 0) : D.m.natAbs = 1 := by
  have hm : D.m ≠ 0 := by
    rcases D.essential with hmne | hnne
    · exact hmne
    · exact (hnne hn).elim
  have hMpos : 0 < D.m.natAbs := Int.natAbs_pos.mpr hm
  by_contra hmone
  have hMtwo : 2 ≤ D.m.natAbs := by omega
  let delta : ℝ := 2 * Real.pi / (D.m.natAbs : ℝ)
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hdeltalt : delta < 2 * Real.pi := by
    dsimp [delta]
    have hMreal : (2 : ℝ) ≤ D.m.natAbs := by exact_mod_cast hMtwo
    have hMrealPos : (0 : ℝ) < D.m.natAbs := by positivity
    rw [div_lt_iff₀ hMrealPos]
    nlinarith [Real.pi_pos]
  have hboundaryImage :
      D.disk (unitDiskBoundary 0) = D.disk (unitDiskBoundary delta) := by
    rw [D.boundary, D.boundary]
    exact slopeLoop_repeats_after_natAbs_first Phi D.m D.n
      D.phase₁ D.phase₂ hm hn
  have hboundaryPoint := D.isEmbedding.injective hboundaryImage
  have hdeltaEq : (0 : ℝ) = delta :=
    unitDiskBoundary_injOn
      ⟨le_rfl, mul_pos zero_lt_two Real.pi_pos⟩
      ⟨hdelta0, hdeltalt⟩ hboundaryPoint
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) (by exact_mod_cast hMpos)
  linarith

theorem CompressingDiskWitness.isPrimitiveAxisSlope_of_liesInTubeSide
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hside : D.LiesInTubeSide) : IsPrimitiveAxisSlope D.m D.n := by
  have hm := D.m_eq_zero_of_liesInTubeSide hside
  exact Or.inr ⟨hm, D.n_natAbs_eq_one_of_m_eq_zero hm⟩

theorem CompressingDiskWitness.isPrimitiveAxisSlope_of_liesInExteriorSide
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (hside : D.LiesInExteriorSide) : IsPrimitiveAxisSlope D.m D.n := by
  have hn := D.n_eq_zero_of_liesInExteriorSide hside
  exact Or.inl ⟨D.m_natAbs_eq_one_of_n_eq_zero hn, hn⟩

/-- The remaining separation statement after the two explicit coordinate
extensions have been constructed: every compressing disk lies wholly on one
of the two closed sides. -/
def EveryCompressingDiskLiesOnOneSide (Phi : AmbientIsotopy) : Prop :=
  ∀ D : CompressingDiskWitness Phi,
    D.LiesInTubeSide ∨ D.LiesInExteriorSide

/-- Side separation plus the explicit coordinate extensions proves the full
axis-slope classification required by representativity. -/
theorem hasAxisSlopeClassification_of_everyCompressingDisk_liesOnOneSide
    (Phi : AmbientIsotopy)
    (hside : EveryCompressingDiskLiesOnOneSide Phi) :
    HasAxisSlopeClassification Phi := by
  intro D
  rcases hside D with hin | hout
  · exact D.isPrimitiveAxisSlope_of_liesInTubeSide hin
  · exact D.isPrimitiveAxisSlope_of_liesInExteriorSide hout

/-! ## Separation of a compressing disk -/

lemma tubeGauge_timeOne_transportedSlopeLoop
    (Phi : AmbientIsotopy) (m n : ℤ) (phase₁ phase₂ t : ℝ) :
    tubeGauge (Phi.H 1 (transportedSlopeLoop Phi m n phase₁ phase₂ t)) = 1 := by
  unfold transportedSlopeLoop
  rw [Submission.Torus.timeOne_map_transportedTorusMap]
  change tubeGauge (Submission.Torus.circleTorusMap
    (Circle.exp ((m : ℝ) * t + phase₁))
    (Circle.exp ((n : ℝ) * t + phase₂))) = 1
  exact circleTorusMap_tubeGauge _ _

lemma mem_transportedTorus_of_tubeGauge_timeOne_eq_one
    (Phi : AmbientIsotopy) {x : R3}
    (hx : tubeGauge (Phi.H 1 x) = 1) :
    x ∈ Submission.Torus.transportedTorus Phi := by
  rw [Submission.Torus.transportedTorus_eq_timeOneInverse_image]
  refine ⟨Phi.H 1 x, ?_, Phi.inv_left 1 x⟩
  rw [geometricStandardTorus_eq_gauge_level]
  exact hx

lemma CompressingDiskWitness.boundary_tubeGauge_eq_one
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    {z : ClosedUnitDisk} (hz : ‖(z : ℂ)‖ = 1) :
    tubeGauge (Phi.H 1 (D.disk z)) = 1 := by
  let w : Circle := ⟨(z : ℂ), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hz⟩
  obtain ⟨t, ht⟩ := Circle.exp_surjective w
  have hzBoundary : unitDiskBoundary t = z := by
    apply Subtype.ext
    change unitCircleParam t = (z : ℂ)
    rw [← circle_exp_coe_eq_unitCircleParam, ht]
  rw [← hzBoundary, D.boundary]
  exact tubeGauge_timeOne_transportedSlopeLoop Phi
    D.m D.n D.phase₁ D.phase₂ t

/-- The gauge of the transported disk after radially projecting the complex
plane to its closed unit-disk domain. -/
def CompressingDiskWitness.radialGauge {Phi : AmbientIsotopy}
    (D : CompressingDiskWitness Phi) (z : ℂ) : ℝ :=
  tubeGauge (Phi.H 1 (D.disk (radialProjection z)))

lemma CompressingDiskWitness.continuous_radialGauge
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi) :
    Continuous D.radialGauge := by
  unfold CompressingDiskWitness.radialGauge
  exact continuous_tubeGauge.comp
    ((continuous_timeOne_map Phi).comp
      (D.continuous.comp continuous_radialProjection))

lemma CompressingDiskWitness.radialGauge_coe
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi)
    (z : ClosedUnitDisk) : D.radialGauge (z : ℂ) =
      tubeGauge (Phi.H 1 (D.disk z)) := by
  unfold CompressingDiskWitness.radialGauge
  congr 3
  apply Subtype.ext
  apply radialProjection_eq_self
  have hz := z.property
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  exact hz

theorem CompressingDiskWitness.liesInTubeSide_or_liesInExteriorSide
    {Phi : AmbientIsotopy} (D : CompressingDiskWitness Phi) :
    D.LiesInTubeSide ∨ D.LiesInExteriorSide := by
  by_cases hin : ∀ z, tubeGauge (Phi.H 1 (D.disk z)) ≤ 1
  · left
    intro z
    exact hin z
  right
  intro z
  change 1 ≤ tubeGauge (Phi.H 1 (D.disk z))
  by_contra hzlow
  have hzlow' : tubeGauge (Phi.H 1 (D.disk z)) < 1 := lt_of_not_ge hzlow
  push Not at hin
  obtain ⟨w, hwhigh⟩ := hin
  have hzInterior : ‖(z : ℂ)‖ < 1 := by
    have hzle := z.property
    rw [Metric.mem_closedBall, dist_zero_right] at hzle
    refine lt_of_le_of_ne hzle ?_
    intro hzone
    have hboundary := D.boundary_tubeGauge_eq_one hzone
    linarith
  have hwInterior : ‖(w : ℂ)‖ < 1 := by
    have hwle := w.property
    rw [Metric.mem_closedBall, dist_zero_right] at hwle
    refine lt_of_le_of_ne hwle ?_
    intro hwone
    have hboundary := D.boundary_tubeGauge_eq_one hwone
    linarith
  have hzGauge : D.radialGauge (z : ℂ) < 1 := by
    rw [D.radialGauge_coe]
    exact hzlow'
  have hwGauge : 1 < D.radialGauge (w : ℂ) := by
    rw [D.radialGauge_coe]
    exact hwhigh
  have hone : (1 : ℝ) ∈ Icc (D.radialGauge (z : ℂ))
      (D.radialGauge (w : ℂ)) := ⟨hzGauge.le, hwGauge.le⟩
  obtain ⟨u, huBall, huGauge⟩ :=
    (convex_ball (0 : ℂ) 1).isPreconnected.intermediate_value
      (by simpa [Metric.mem_ball, dist_zero_right] using hzInterior)
      (by simpa [Metric.mem_ball, dist_zero_right] using hwInterior)
      D.continuous_radialGauge.continuousOn hone
  have huNorm : ‖u‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using huBall
  have huProjection : (radialProjection u : ℂ) = u :=
    radialProjection_eq_self huNorm.le
  have huDiskInterior : ‖(radialProjection u : ℂ)‖ < 1 := by
    rw [huProjection]
    exact huNorm
  have huNotTorus := D.interior_disjoint (radialProjection u) huDiskInterior
  apply huNotTorus
  apply mem_transportedTorus_of_tubeGauge_timeOne_eq_one Phi
  change D.radialGauge u = 1
  exact huGauge

theorem everyCompressingDiskLiesOnOneSide (Phi : AmbientIsotopy) :
    EveryCompressingDiskLiesOnOneSide Phi := by
  intro D
  exact D.liesInTubeSide_or_liesInExteriorSide

/-- Every compressing boundary of the explicitly transported unknotted torus
is a primitive meridian or longitude. -/
theorem transportedTorus_hasAxisSlopeClassification (Phi : AmbientIsotopy) :
    HasAxisSlopeClassification Phi :=
  hasAxisSlopeClassification_of_everyCompressingDisk_liesOnOneSide Phi
    (everyCompressingDiskLiesOnOneSide Phi)

/-- The completed representativity consequence for the transported `(p, q)`
torus knot. -/
theorem transportedTorus_hasSlopeRepresentativityAtLeast_min_unconditional
    (Phi : AmbientIsotopy) (p q : ℕ) :
    HasSlopeRepresentativityAtLeast Phi p q (min p q) :=
  transportedTorus_hasSlopeRepresentativityAtLeast_min Phi p q
    (transportedTorus_hasAxisSlopeClassification Phi)

end Submission.PardonDistortion
