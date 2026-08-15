import Submission.SuperellipsoidGeometry
import Submission.Coarea.FacewiseRegularOuterBoundarySelection
import Submission.SardMoreira.Planar

/-!
# Coarea selection for a smooth superellipsoid

This file separates the metric part of the outer sweep from its planar-Sard input.  The metric
argument uses the `L^256` gauge and yields an outer knot count below `76 D`.  Surface regularity is
encoded by the polynomial lift to the universal covering plane.  The selector accepts nullity of
the corresponding bad scale set explicitly; proving that nullity by transporting planar Sard
through the positive `256`th-root chart is the remaining analytic adapter.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.SurfaceRegularValue

/-- The elementary `PiLp` comparison constant. -/
def superellipsoidPiLpFactor : ℝ≥0 :=
  (3 : ℝ≥0) ^ (1 / (256 : ℝ≥0∞)).toReal

lemma coe_superellipsoidPiLpFactor :
    (superellipsoidPiLpFactor : ℝ) = (3 : ℝ) ^ (1 / (256 : ℝ)) := by
  simp [superellipsoidPiLpFactor]

lemma superellipsoidPiLpFactor_lt_innerFactor :
    (superellipsoidPiLpFactor : ℝ) < superellipsoidInnerFactor := by
  rw [coe_superellipsoidPiLpFactor]
  exact three_rpow_inv_exponent_lt_innerFactor

/-- The normalized coordinate map is one-Lipschitz from Euclidean space to the sup product. -/
lemma lipschitzWith_normalizedOrientedBoxCoordinates
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    LipschitzWith 1 (normalizedOrientedBoxCoordinates frame c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [NNReal.coe_one, one_mul, dist_eq_norm] using
    norm_normalizedOrientedBoxCoordinates_sub_le frame c x y

/-- The elementary comparison gives a global `193/192` Lipschitz constant for the smooth gauge. -/
lemma lipschitzWith_superellipsoidGauge
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    LipschitzWith ⟨superellipsoidInnerFactor, superellipsoidInnerFactor_pos.le⟩
      (superellipsoidGauge frame c) := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hcoordinate :=
    ((PiLp.lipschitzWith_toLp (p := (256 : ℝ≥0∞)) (fun _ : Fin 3 ↦ ℝ)).comp
      (lipschitzWith_normalizedOrientedBoxCoordinates frame c)).dist_le_mul x y
  calc
    dist (superellipsoidGauge frame c x) (superellipsoidGauge frame c y) ≤
        dist (superellipsoidCoordinates frame c x)
          (superellipsoidCoordinates frame c y) := dist_norm_norm_le _ _
    _ ≤ (superellipsoidPiLpFactor : ℝ) * dist x y := by
      simpa [superellipsoidCoordinates, superellipsoidPiLpFactor] using hcoordinate
    _ ≤ superellipsoidInnerFactor * dist x y := by
      exact mul_le_mul_of_nonneg_right superellipsoidPiLpFactor_lt_innerFactor.le dist_nonneg

lemma continuous_superellipsoidGauge
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    Continuous (superellipsoidGauge frame c) :=
  (lipschitzWith_superellipsoidGauge frame c).continuous

lemma isClosed_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsClosed (closedSuperellipsoidBody frame c R) := by
  exact isClosed_Iic.preimage (continuous_superellipsoidGauge frame c)

/-- Smooth-shell coordinate along the knot. -/
def superellipsoidShellParameter
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (t : ℝ) : ℝ :=
  superellipsoidGauge frame c (K.curve t)

lemma exists_lipschitzWith_superellipsoidShellParameter
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    ∃ C : ℝ≥0, LipschitzWith C (superellipsoidShellParameter K frame c) := by
  obtain ⟨C, hcurve⟩ :=
    Submission.Coarea.PardonApplication.exists_lipschitzWith_knotCurve K
  exact ⟨⟨superellipsoidInnerFactor, superellipsoidInnerFactor_pos.le⟩ * C,
    (lipschitzWith_superellipsoidGauge frame c).comp hcurve⟩

/-- A generic derivative bound for a Lipschitz outer function and a differentiable inner curve. -/
lemma abs_deriv_comp_le_lipschitz_mul_norm_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ℝ≥0} (g : E → ℝ) (f : ℝ → E) (t : ℝ)
    (hg : LipschitzWith C g) (hf : DifferentiableAt ℝ f t)
    (hcomp : DifferentiableAt ℝ (g ∘ f) t) :
    |deriv (g ∘ f) t| ≤ C * ‖deriv f t‖ := by
  have hgderiv := hcomp.hasDerivAt
  have hfderiv := hf.hasDerivAt
  rw [← Real.norm_eq_abs]
  refine le_of_tendsto_of_tendsto hgderiv.tendsto_slope.norm
    ((tendsto_const_nhds.mul hfderiv.tendsto_slope.norm)) ?_
  filter_upwards with u
  rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
  have hdist : ‖g (f u) - g (f t)‖ ≤ C * ‖f u - f t‖ := by
    simpa [Real.dist_eq, dist_eq_norm] using hg.dist_le_mul (f u) (f t)
  calc
    ‖(u - t)⁻¹‖ * ‖g (f u) - g (f t)‖ ≤
        ‖(u - t)⁻¹‖ * (C * ‖f u - f t‖) :=
      mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
    _ = C * (‖(u - t)⁻¹‖ * ‖f u - f t‖) := by ring

/-- The shell derivative costs at most the elementary `193/192` comparison factor. -/
lemma abs_deriv_superellipsoidShellParameter_le_speed
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (t : ℝ) :
    |deriv (superellipsoidShellParameter K frame c) t| ≤
      superellipsoidInnerFactor * speed K t := by
  by_cases hdiff : DifferentiableAt ℝ (superellipsoidShellParameter K frame c) t
  · exact abs_deriv_comp_le_lipschitz_mul_norm_deriv
      (superellipsoidGauge frame c) K.curve t
      (lipschitzWith_superellipsoidGauge frame c)
      (K.smooth.differentiable (by simp) t) hdiff
  · rw [deriv_zero_of_not_differentiableAt hdiff, abs_zero]
    exact mul_nonneg superellipsoidInnerFactor_pos.le (norm_nonneg _)

/-- Compact parameters whose knot points lie in the closed smooth body. -/
def closedSuperellipsoidParameters
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set ℝ :=
  Icc (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' closedSuperellipsoidBody frame c R

lemma isCompact_closedSuperellipsoidParameters
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsCompact (closedSuperellipsoidParameters K frame c R) := by
  exact isCompact_Icc.inter_right
    ((isClosed_closedSuperellipsoidBody frame c R).preimage K.smooth.continuous)

/-- Local arclength in the closed smooth body uses its sharp diameter bound. -/
lemma lintegral_speed_preimage_closedSuperellipsoidBody_le
    (K : Knot) {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}
    (hR : 0 < R) (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedSuperellipsoidBody frame c R,
        ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal (9 * R * (distortion K).toReal) := by
  let A : Set ℝ := Ico (0 : ℝ) (2 * Real.pi) ∩
    K.curve ⁻¹' closedSuperellipsoidBody frame c R
  change (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤
    ENNReal.ofReal (9 * R * (distortion K).toReal)
  have hAmeas : MeasurableSet A := measurableSet_Ico.inter
    ((isClosed_closedSuperellipsoidBody frame c R).measurableSet.preimage
      K.smooth.continuous.measurable)
  by_cases hne : A.Nonempty
  · obtain ⟨s, hsI, hsB⟩ := hne
    calc
      (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤
          ENNReal.ofReal (2 * ((9 / 2 : ℝ) * R * (distortion K).toReal)) := by
        apply lintegral_speed_le_two_mul_of_intrinsic K hAmeas inter_subset_left
          ⟨hsI, hsB⟩
        intro t ht
        by_cases hst : s = t
        · subst t
          have hnonneg : 0 ≤ (9 / 2 : ℝ) * R * (distortion K).toReal := by positivity
          simpa [intrinsicDistance, parameterArcLength,
            totalArcLength_pos K |>.le] using hnonneg
        · calc
            intrinsicDistance K s t ≤
                (distortion K).toReal * dist (K.curve s) (K.curve t) :=
              intrinsicDistance_le_toReal_distortion_mul_dist K hsI ht.1 hst hfinite
            _ ≤ (distortion K).toReal * ((9 / 2 : ℝ) * R) :=
              mul_le_mul_of_nonneg_left
                (dist_lt_nine_halves_mul_scale_of_mem_closedSuperellipsoidBody
                  frame c hR hsB ht.2).le ENNReal.toReal_nonneg
            _ = (9 / 2 : ℝ) * R * (distortion K).toReal := by ring
      _ = ENNReal.ofReal (9 * R * (distortion K).toReal) := by
        congr 1
        ring
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Adding the right endpoint for compactness does not alter the arclength integral. -/
lemma lintegral_closedSuperellipsoidParameters_speed_eq_halfOpen
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    (∫⁻ t in closedSuperellipsoidParameters K frame c R,
        ENNReal.ofReal (speed K t)) =
      ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedSuperellipsoidBody frame c R,
        ENNReal.ofReal (speed K t) := by
  have hsets : closedSuperellipsoidParameters K frame c R =ᵐ[volume]
      ((Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedSuperellipsoidBody frame c R) : Set ℝ) := by
    filter_upwards [MeasureTheory.Ico_ae_eq_Icc (μ := volume)
      (a := (0 : ℝ)) (b := 2 * Real.pi)] with t ht
    exact congrArg
      (fun p : Prop ↦ p ∧ K.curve t ∈ closedSuperellipsoidBody frame c R) ht.symm
  rw [Measure.restrict_congr_set hsets]

/-- Integrated shell variation on the compact parameter set. -/
lemma lintegral_abs_deriv_superellipsoidShellParameter_le
    (K : Knot) {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}
    (hR : 0 < R) (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in closedSuperellipsoidParameters K frame c R,
        ENNReal.ofReal |deriv (superellipsoidShellParameter K frame c) t|) ≤
      ENNReal.ofReal
        (superellipsoidInnerFactor * 9 * R * (distortion K).toReal) := by
  calc
    (∫⁻ t in closedSuperellipsoidParameters K frame c R,
        ENNReal.ofReal |deriv (superellipsoidShellParameter K frame c) t|) ≤
        ∫⁻ t in closedSuperellipsoidParameters K frame c R,
          ENNReal.ofReal (superellipsoidInnerFactor * speed K t) := by
      exact lintegral_mono fun t ↦ ENNReal.ofReal_le_ofReal
        (abs_deriv_superellipsoidShellParameter_le_speed K frame c t)
    _ = ENNReal.ofReal superellipsoidInnerFactor *
        ∫⁻ t in closedSuperellipsoidParameters K frame c R,
          ENNReal.ofReal (speed K t) := by
      rw [← MeasureTheory.lintegral_const_mul'
        (ENNReal.ofReal superellipsoidInnerFactor) _ ENNReal.ofReal_ne_top]
      congr 1
      funext t
      rw [← ENNReal.ofReal_mul superellipsoidInnerFactor_pos.le]
    _ ≤ ENNReal.ofReal superellipsoidInnerFactor *
        ENNReal.ofReal (9 * R * (distortion K).toReal) := by
      gcongr
      rw [lintegral_closedSuperellipsoidParameters_speed_eq_halfOpen]
      exact lintegral_speed_preimage_closedSuperellipsoidBody_le K hR hfinite
    _ = ENNReal.ofReal
        (superellipsoidInnerFactor * 9 * R * (distortion K).toReal) := by
      rw [← ENNReal.ofReal_mul superellipsoidInnerFactor_pos.le]
      congr 1
      ring

/-- Polynomial lift of the outer surface equation to the transported torus covering plane. -/
def superellipsoidPolynomialLift
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) : ℝ :=
  superellipsoidPolynomial frame c (transportedTorusPlaneMap Phi uv)

lemma contDiff_superellipsoidPolynomialLift
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (superellipsoidPolynomialLift Phi frame c) := by
  exact (contDiff_superellipsoidPolynomial frame c).comp
    (transportedTorusPlaneMap_contDiff Phi)

/-- Positive scales at which the polynomial outer surface is not transverse to the transported
torus.  Restricting this set to a positive compact interval and proving it null is the precise
root-chart adapter needed after planar Sard. -/
def superellipsoidSurfaceBadScales
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) : Set ℝ :=
  {R | R ^ 256 ∈ criticalValues (superellipsoidPolynomialLift Phi frame c)}

lemma regularValue_superellipsoidPolynomialLift_of_not_bad
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ}
    (hR : R ∉ superellipsoidSurfaceBadScales Phi frame c) :
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256) := by
  apply (isRegularValue_iff_not_mem_criticalValues _ _).2
  exact hR

/-- Output of the smooth outer coarea sweep. -/
structure SuperellipsoidOuterSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  scale : ℝ
  scale_mem : scale ∈ Ioc
    (superellipsoidInnerFactor * r) (superellipsoidOuterFactor * r)
  knotNonexceptional :
    scale ∉ (superellipsoidShellParameter K frame c) ''
      Submission.Coarea.lipschitzExceptionalSet
        (superellipsoidShellParameter K frame c)
  knotFiberFinite :
    (Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) scale).Finite
  knotBoundaryCount_le :
    (Submission.Coarea.fiberCount (superellipsoidShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) scale : ℝ≥0∞) ≤
        ENNReal.ofReal (76 * (distortion K).toReal)
  surfaceRegular :
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (scale ^ 256)

namespace SuperellipsoidOuterSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ}

lemma scale_pos (S : SuperellipsoidOuterSelection K Phi frame c r) (hr : 0 < r) :
    0 < S.scale :=
  (mul_pos superellipsoidInnerFactor_pos hr).trans S.scale_mem.1

/-- The selected smooth body contains the original carrier box. -/
lemma orientedBox_subset_body
    (S : SuperellipsoidOuterSelection K Phi frame c r) (hr : 0 < r) :
    orientedBox frame c r ⊆ superellipsoidBody frame c S.scale := by
  exact (orientedBox_subset_superellipsoidBody_innerFactor frame c hr).trans
    (superellipsoidBody_mono frame c S.scale_mem.1.le)

/-- It remains inside the rational box at its selected outer scale. -/
lemma body_subset_orientedBox
    (S : SuperellipsoidOuterSelection K Phi frame c r) (hr : 0 < r) :
    superellipsoidBody frame c S.scale ⊆ orientedBox frame c S.scale :=
  superellipsoidBody_subset_orientedBox frame c (S.scale_pos hr)

lemma scale_le_outerFactor_mul
    (S : SuperellipsoidOuterSelection K Phi frame c r) :
    S.scale ≤ superellipsoidOuterFactor * r :=
  S.scale_mem.2

/-- The selected lower half fits the usual successor box. -/
lemma lowerHalf_subset_successor
    (S : SuperellipsoidOuterSelection K Phi frame c r) (hr : 0 < r) {d : ℝ}
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    superellipsoidBody frame c S.scale ∩ {x | x.ofLp (frame 2) ≤ d} ⊆
      orientedBox (axisCycle.trans frame) (lowerHalfCenter frame c S.scale d)
        (successorScale S.scale r) :=
  lowerSuperellipsoidHalf_subset_successor frame c (S.scale_pos hr) hr hd

/-- The selected upper half fits the usual successor box. -/
lemma upperHalf_subset_successor
    (S : SuperellipsoidOuterSelection K Phi frame c r) (hr : 0 < r) {d : ℝ}
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    superellipsoidBody frame c S.scale ∩ {x | d ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame) (upperHalfCenter frame c S.scale d)
        (successorScale S.scale r) :=
  upperSuperellipsoidHalf_subset_successor frame c (S.scale_pos hr) hr hd

end SuperellipsoidOuterSelection

/-- Coarea selector once the positive root-chart image of the planar critical values is known to
be null.  This hypothesis is analytic and strictly weaker than assuming the selected surface is
regular: the theorem chooses a single scale outside it while retaining the quantitative count. -/
theorem exists_superellipsoidOuterSelection_of_badScales_null
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (hbadNull : volume
      (superellipsoidSurfaceBadScales Phi frame c ∩
        Ioc (superellipsoidInnerFactor * r) (superellipsoidOuterFactor * r)) = 0) :
    Nonempty (SuperellipsoidOuterSelection K Phi frame c r) := by
  let lower := superellipsoidInnerFactor * r
  let upper := superellipsoidOuterFactor * r
  have hlower : 0 < lower := mul_pos superellipsoidInnerFactor_pos hr
  have hupper : 0 < upper := mul_pos superellipsoidOuterFactor_pos hr
  have hlu : lower < upper :=
    mul_lt_mul_of_pos_right superellipsoidInnerFactor_lt_outerFactor hr
  obtain ⟨C, hC⟩ := exists_lipschitzWith_superellipsoidShellParameter K frame c
  obtain ⟨R, hR, hRexceptional, hRbadInterval, hfiniteCompact, hbound⟩ :=
    Submission.Coarea.exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact_avoiding
      hC (isCompact_closedSuperellipsoidParameters K frame c upper) hlu hbadNull
  have hRbad : R ∉ superellipsoidSurfaceBadScales Phi frame c := by
    intro hbad
    exact hRbadInterval ⟨hbad, hR⟩
  have hsub :
      Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
          (Ico (0 : ℝ) (2 * Real.pi)) R ⊆
        Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
          (closedSuperellipsoidParameters K frame c upper) R := by
    intro t ht
    rw [Submission.Coarea.fiberSet] at ht ⊢
    rcases ht with ⟨htIco, htlevel⟩
    refine ⟨⟨⟨htIco.1, htIco.2.le⟩, ?_⟩, htlevel⟩
    have htEq : superellipsoidShellParameter K frame c t = R := by
      simpa only [mem_preimage, mem_singleton_iff] using htlevel
    change superellipsoidGauge frame c (K.curve t) ≤ upper
    rw [show superellipsoidGauge frame c (K.curve t) = R from htEq]
    exact hR.2
  have hfiniteIco :
      (Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) R).Finite :=
    hfiniteCompact.subset hsub
  refine ⟨{
    scale := R
    scale_mem := hR
    knotNonexceptional := hRexceptional
    knotFiberFinite := hfiniteIco
    knotBoundaryCount_le := ?_
    surfaceRegular := regularValue_superellipsoidPolynomialLift_of_not_bad
      Phi frame c hRbad
  }⟩
  have hcount :
      (Submission.Coarea.fiberCount (superellipsoidShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) R : ℝ≥0∞) ≤
      (Submission.Coarea.fiberCount (superellipsoidShellParameter K frame c)
        (closedSuperellipsoidParameters K frame c upper) R : ℝ≥0∞) := by
    change ((Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) R).ncard : ℝ≥0∞) ≤
        ((Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
          (closedSuperellipsoidParameters K frame c upper) R).ncard : ℝ≥0∞)
    exact_mod_cast Set.ncard_le_ncard hsub hfiniteCompact
  refine hcount.trans (hbound.trans ?_)
  calc
    (∫⁻ t in closedSuperellipsoidParameters K frame c upper,
        ENNReal.ofReal |deriv (superellipsoidShellParameter K frame c) t|) /
          ENNReal.ofReal (upper - lower) ≤
        ENNReal.ofReal
          (superellipsoidInnerFactor * 9 * upper * (distortion K).toReal) /
            ENNReal.ofReal (upper - lower) := by
      exact ENNReal.div_le_div
        (lintegral_abs_deriv_superellipsoidShellParameter_le K hupper hfinite) le_rfl
    _ = ENNReal.ofReal
        ((superellipsoidInnerFactor * 9 * superellipsoidOuterFactor /
          (superellipsoidOuterFactor - superellipsoidInnerFactor)) *
            (distortion K).toReal) := by
      rw [← ENNReal.ofReal_div_of_pos (sub_pos.mpr hlu)]
      congr 1
      dsimp [upper, lower]
      field_simp [ne_of_gt hr,
        ne_of_gt (sub_pos.mpr superellipsoidInnerFactor_lt_outerFactor)]
    _ ≤ ENNReal.ofReal (76 * (distortion K).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        innerFactor_mul_nine_mul_outerFactor_div_shellWidth_lt_seventySix.le
        ENNReal.toReal_nonneg

end Submission.PardonDistortion
