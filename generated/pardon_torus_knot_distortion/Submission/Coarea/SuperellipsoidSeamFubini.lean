import Submission.SuperellipsoidDoubleBubbleSelection
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Seam-height nullity from Sard and Fubini

Instead of classifying the regular outer seam into finitely many ODE orbits, apply
equal-dimensional Sard to the planar map whose coordinates are the outer polynomial and the
cutting height.  Fubini then says that almost every outer polynomial value has a null set of
critical cutting heights.  The outer coarea selector can avoid the exceptional polynomial
values at the same time as the ordinary surface-critical values.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Topology

/-- The two functions whose simultaneous Jacobian detects a non-transverse seam cut. -/
def superellipsoidSeamPairMap
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) : Plane :=
  (superellipsoidPolynomialLift Phi frame c uv,
    orientedCoordinateLift Phi frame 2 uv)

lemma contDiff_superellipsoidSeamPairMap
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamPairMap Phi frame c) := by
  exact (contDiff_superellipsoidPolynomialLift Phi frame c).prodMk
    (orientedCoordinateLift_contDiff Phi frame 2)

private lemma continuousLinearMap_plane_row
    (L : Plane →L[ℝ] ℝ) :
    L = L planeBasisFirst • ContinuousLinearMap.fst ℝ ℝ ℝ +
      L planeBasisSecond • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  ext z
  rw [show z = z.1 • planeBasisFirst + z.2 • planeBasisSecond by
    ext <;> simp [planeBasisFirst, planeBasisSecond]]
  simp [map_add, map_smul, planeBasisFirst, planeBasisSecond, smul_eq_mul]

/-- Matrix form of the derivative of the polynomial-height pair. -/
lemma fderiv_superellipsoidSeamPairMap_eq_matrix
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) :
    fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv =
      (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
        !![fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv planeBasisFirst,
            fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv planeBasisSecond;
          fderiv ℝ (orientedCoordinateLift Phi frame 2) uv planeBasisFirst,
            fderiv ℝ (orientedCoordinateLift Phi frame 2) uv planeBasisSecond]).toContinuousLinearMap := by
  have hf : DifferentiableAt ℝ (superellipsoidPolynomialLift Phi frame c) uv :=
    (contDiff_superellipsoidPolynomialLift Phi frame c).differentiableAt
  have hg : DifferentiableAt ℝ (orientedCoordinateLift Phi frame 2) uv :=
    (orientedCoordinateLift_contDiff Phi frame 2).differentiableAt
  rw [superellipsoidSeamPairMap, hf.fderiv_prodMk hg,
    continuousLinearMap_plane_row (fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv),
    continuousLinearMap_plane_row (fderiv ℝ (orientedCoordinateLift Phi frame 2) uv)]
  exact (Matrix.toLin_finTwoProd_toContinuousLinearMap _ _ _ _).symm

/-- The abstract Jacobian determinant is the explicit differential determinant used by the cut
selector. -/
lemma det_fderiv_superellipsoidSeamPairMap
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) :
    (fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv).det =
      planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) uv := by
  rw [fderiv_superellipsoidSeamPairMap_eq_matrix]
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, planarDifferentialDet]

/-- The determinant-critical points of the simultaneous polynomial-height map. -/
def superellipsoidSeamPairCriticalPoints
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) : Set Plane :=
  {uv | planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
    (orientedCoordinateLift Phi frame 2) uv = 0}

/-- Their two-dimensional critical-value image. -/
def superellipsoidSeamPairCriticalValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) : Set Plane :=
  superellipsoidSeamPairMap Phi frame c ''
    superellipsoidSeamPairCriticalPoints Phi frame c

/-- Equal-dimensional Sard: the simultaneous critical-value image has planar measure zero. -/
theorem volume_superellipsoidSeamPairCriticalValues_eq_zero
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    volume (superellipsoidSeamPairCriticalValues Phi frame c) = 0 := by
  let _ : Measure.IsAddHaarMeasure (volume : Measure Plane) :=
    Measure.prod.instIsAddHaarMeasure _ _
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := volume)
    (f' := fun uv ↦ fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv)
  · intro uv _
    exact ((contDiff_superellipsoidSeamPairMap Phi frame c).differentiableAt).hasFDerivAt
      |>.hasFDerivWithinAt
  · intro uv huv
    rw [det_fderiv_superellipsoidSeamPairMap]
    exact huv

/-- Polynomial values whose vertical critical-value section is not null. -/
def superellipsoidSeamSectionExceptionalPolynomialValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) : Set ℝ :=
  {s | volume (Prod.mk s ⁻¹'
    superellipsoidSeamPairCriticalValues Phi frame c) ≠ 0}

/-- Fubini turns planar Sard into nullity of the exceptional polynomial levels. -/
theorem volume_superellipsoidSeamSectionExceptionalPolynomialValues_eq_zero
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    volume (superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c) = 0 := by
  have hprod : (volume : Measure ℝ).prod volume
      (superellipsoidSeamPairCriticalValues Phi frame c) = 0 := by
    simpa only [MeasureTheory.volume_eq_prod] using
      volume_superellipsoidSeamPairCriticalValues_eq_zero Phi frame c
  have hae := MeasureTheory.measure_ae_null_of_prod_null hprod
  apply ae_iff.mp
  simpa only [superellipsoidSeamSectionExceptionalPolynomialValues, not_ne_iff] using hae

/-- A seam critical height at polynomial level `R^256` lies in the corresponding vertical
section of the simultaneous critical-value image. -/
lemma seamHeightCriticalValues_subset_pairCriticalValues_section
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    superellipsoidSeamHeightCriticalValues Phi frame c R ⊆
      Prod.mk (R ^ 256) ⁻¹' superellipsoidSeamPairCriticalValues Phi frame c := by
  rintro d ⟨uv, ⟨hlevel, hdet⟩, rfl⟩
  change (R ^ 256, orientedCoordinateLift Phi frame 2 uv) ∈
    superellipsoidSeamPairCriticalValues Phi frame c
  refine ⟨uv, hdet, ?_⟩
  exact Prod.ext hlevel rfl

/-- Outside the Fubini-exceptional polynomial values, all critical seam heights are null. -/
theorem volume_superellipsoidSeamHeightCriticalValues_eq_zero_of_not_exceptional
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ}
    (hR : R ^ 256 ∉
      superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c) :
    volume (superellipsoidSeamHeightCriticalValues Phi frame c R) = 0 := by
  apply measure_mono_null
    (seamHeightCriticalValues_subset_pairCriticalValues_section Phi frame c R)
  exact not_ne_iff.mp hR

/-- Radii whose polynomial level is exceptional for the Fubini seam section. -/
def superellipsoidSeamSectionBadScales
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) : Set ℝ :=
  {R | R ^ 256 ∈
    superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c}

lemma seamSectionBadScales_inter_Ioc_subset_positiveRoot_image
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {lower upper : ℝ} (hlower : 0 < lower) (_hlu : lower ≤ upper) :
    superellipsoidSeamSectionBadScales Phi frame c ∩ Ioc lower upper ⊆
      superellipsoidPositiveRoot ''
        (superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c ∩
          Icc (lower ^ 256) (upper ^ 256)) := by
  rintro R ⟨hbad, hR⟩
  have hRpos : 0 < R := hlower.trans hR.1
  refine ⟨R ^ 256, ⟨hbad, ?_⟩, ?_⟩
  · exact ⟨pow_le_pow_left₀ hlower.le hR.1.le 256,
      pow_le_pow_left₀ hRpos.le hR.2 256⟩
  · simpa [superellipsoidPositiveRoot] using
      (Real.pow_rpow_inv_natCast hRpos.le (by norm_num : (256 : ℕ) ≠ 0))

/-- The exceptional radii form a null set on every positive compact interval. -/
theorem volume_superellipsoidSeamSectionBadScales_inter_Ioc_eq_zero
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {lower upper : ℝ} (hlower : 0 < lower) (hlu : lower ≤ upper) :
    volume (superellipsoidSeamSectionBadScales Phi frame c ∩ Ioc lower upper) = 0 := by
  have hlowerPow : 0 < lower ^ 256 := pow_pos hlower _
  have hpows : lower ^ 256 ≤ upper ^ 256 :=
    pow_le_pow_left₀ hlower.le hlu 256
  have hrestricted : volume
      (superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c ∩
        Icc (lower ^ 256) (upper ^ 256)) = 0 :=
    measure_mono_null inter_subset_left
      (volume_superellipsoidSeamSectionExceptionalPolynomialValues_eq_zero Phi frame c)
  obtain ⟨C, hroot⟩ :=
    exists_lipschitzOnWith_superellipsoidPositiveRoot hlowerPow hpows
  have himage : volume (superellipsoidPositiveRoot ''
      (superellipsoidSeamSectionExceptionalPolynomialValues Phi frame c ∩
        Icc (lower ^ 256) (upper ^ 256))) = 0 :=
    volume_image_eq_zero_of_lipschitzOnWith
      (hroot.mono inter_subset_right) hrestricted
  exact measure_mono_null
    (seamSectionBadScales_inter_Ioc_subset_positiveRoot_image
      Phi frame c hlower hlu) himage

/-- Select a regular outer surface whose seam-critical cutting heights are also null. -/
theorem exists_superellipsoidOuterSelection_with_seamCriticalValues_null
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    ∃ outer : SuperellipsoidOuterSelection K Phi frame c r,
      volume (superellipsoidSeamHeightCriticalValues Phi frame c outer.scale) = 0 := by
  let lower := superellipsoidInnerFactor * r
  let upper := superellipsoidOuterFactor * r
  let bad := superellipsoidSurfaceBadScales Phi frame c ∪
    superellipsoidSeamSectionBadScales Phi frame c
  have hlower : 0 < lower := mul_pos superellipsoidInnerFactor_pos hr
  have hupper : 0 < upper := mul_pos superellipsoidOuterFactor_pos hr
  have hlu : lower < upper :=
    mul_lt_mul_of_pos_right superellipsoidInnerFactor_lt_outerFactor hr
  have hbadNull : volume (bad ∩ Ioc lower upper) = 0 := by
    rw [show bad ∩ Ioc lower upper =
      (superellipsoidSurfaceBadScales Phi frame c ∩ Ioc lower upper) ∪
        (superellipsoidSeamSectionBadScales Phi frame c ∩ Ioc lower upper) by
      ext x
      simp [bad, and_or_left]]
    exact measure_union_null
      (volume_superellipsoidSurfaceBadScales_inter_Ioc_eq_zero
        Phi frame c hlower hlu.le)
      (volume_superellipsoidSeamSectionBadScales_inter_Ioc_eq_zero
        Phi frame c hlower hlu.le)
  obtain ⟨C, hC⟩ := exists_lipschitzWith_superellipsoidShellParameter K frame c
  obtain ⟨R, hR, hRexceptional, hRbadInterval, hfiniteCompact, hbound⟩ :=
    Submission.Coarea.exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact_avoiding
      hC (isCompact_closedSuperellipsoidParameters K frame c upper) hlu hbadNull
  have hRsurface : R ∉ superellipsoidSurfaceBadScales Phi frame c := by
    intro hbad
    exact hRbadInterval ⟨Or.inl hbad, hR⟩
  have hRseam : R ∉ superellipsoidSeamSectionBadScales Phi frame c := by
    intro hbad
    exact hRbadInterval ⟨Or.inr hbad, hR⟩
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
  let outer : SuperellipsoidOuterSelection K Phi frame c r := {
    scale := R
    scale_mem := hR
    knotNonexceptional := hRexceptional
    knotFiberFinite := hfiniteIco
    knotBoundaryCount_le := by
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
    surfaceRegular := regularValue_superellipsoidPolynomialLift_of_not_bad
      Phi frame c hRsurface
  }
  refine ⟨outer, ?_⟩
  exact volume_superellipsoidSeamHeightCriticalValues_eq_zero_of_not_exceptional
    Phi frame c hRseam

/-- The smooth double-bubble selector is unconditional: planar Sard, equal-dimensional Sard,
Fubini, and the two coarea choices supply every genericity condition. -/
theorem exists_superellipsoidDoubleBubbleSelection_unconditional
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)) :
    Nonempty (SuperellipsoidDoubleBubbleSelection K Phi frame c r W) := by
  obtain ⟨outer, hseam⟩ :=
    exists_superellipsoidOuterSelection_with_seamCriticalValues_null
      K Phi frame c hr hfinite
  obtain ⟨cut⟩ := exists_superellipsoidRegularCutSelection_of_seamCriticalValues_null
    K Phi frame c hr hfinite W outer hseam
  exact ⟨⟨outer, cut⟩⟩

end Submission.PardonDistortion
