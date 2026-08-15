import Submission.Coarea.SuperellipsoidOuterSelection

/-!
# Nullity of the exceptional superellipsoid scales

Planar Sard gives a null set of critical *polynomial values*.  The outer coarea
argument varies the positive radius `R`, whose polynomial value is `R ^ 256`.
On every compact interval bounded away from zero, the positive `256`th-root
map is Lipschitz.  This file uses that chart to pull Sard nullity back to the
scale interval used by the outer selector.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.SurfaceRegularValue

/-- The positive real `256`th-root chart. -/
def superellipsoidPositiveRoot (y : ℝ) : ℝ :=
  y ^ ((256 : ℝ)⁻¹)

/-- On a compact interval bounded away from zero, the positive root chart has a finite
Lipschitz constant.  No quantitative bound on that constant is needed to transport null sets. -/
lemma exists_lipschitzOnWith_superellipsoidPositiveRoot
    {A B : ℝ} (hA : 0 < A) (_hAB : A ≤ B) :
    ∃ C : ℝ≥0, LipschitzOnWith C superellipsoidPositiveRoot (Icc A B) := by
  have hsmooth : ContDiffOn ℝ 1 superellipsoidPositiveRoot (Icc A B) := by
    intro y hy
    exact (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (hA.trans_le hy.1))).contDiffWithinAt
  exact hsmooth.exists_lipschitzOnWith one_ne_zero (convex_Icc A B) isCompact_Icc

/-- A Lipschitz image of a Lebesgue-null subset of the real line is null. -/
lemma volume_image_eq_zero_of_lipschitzOnWith
    {f : ℝ → ℝ} {s : Set ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  apply le_antisymm
  · have hmeasure := hf.hausdorffMeasure_image_le (d := (1 : ℝ)) zero_le_one
    simpa [MeasureTheory.hausdorffMeasure_real, hs] using hmeasure
  · exact bot_le

/-- Planar Sard critical values remain null after applying the positive root on a compact
positive interval. -/
lemma volume_positiveRoot_image_criticalValues_inter_Icc_eq_zero
    (f : Plane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    volume (superellipsoidPositiveRoot '' (criticalValues f ∩ Icc A B)) = 0 := by
  have hcritical : volume (criticalValues f) = 0 := by
    exact criticalValuesNull_of_sardMoreiraConclusion (planarSardTheorem f hf)
  have hrestricted : volume (criticalValues f ∩ Icc A B) = 0 :=
    measure_mono_null inter_subset_left hcritical
  obtain ⟨C, hroot⟩ :=
    exists_lipschitzOnWith_superellipsoidPositiveRoot hA hAB
  exact volume_image_eq_zero_of_lipschitzOnWith
    (hroot.mono inter_subset_right) hrestricted

/-- On a positive compact scale interval, every bad radius is the positive root of a planar
critical polynomial value in the corresponding polynomial-value interval. -/
lemma badScales_inter_Ioc_subset_positiveRoot_image
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {lower upper : ℝ} (hlower : 0 < lower) (_hlu : lower ≤ upper) :
    superellipsoidSurfaceBadScales Phi frame c ∩ Ioc lower upper ⊆
      superellipsoidPositiveRoot ''
        (criticalValues (superellipsoidPolynomialLift Phi frame c) ∩
          Icc (lower ^ 256) (upper ^ 256)) := by
  intro R hR
  rcases hR with ⟨hbad, hR⟩
  have hRpos : 0 < R := hlower.trans hR.1
  refine ⟨R ^ 256, ⟨hbad, ?_⟩, ?_⟩
  · exact ⟨pow_le_pow_left₀ hlower.le hR.1.le 256,
      pow_le_pow_left₀ hRpos.le hR.2 256⟩
  · simpa [superellipsoidPositiveRoot] using
      (Real.pow_rpow_inv_natCast hRpos.le (by norm_num : (256 : ℕ) ≠ 0))

/-- The exact root-chart adapter required by the smooth outer coarea selector. -/
theorem volume_superellipsoidSurfaceBadScales_inter_Ioc_eq_zero
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {lower upper : ℝ} (hlower : 0 < lower) (hlu : lower ≤ upper) :
    volume
      (superellipsoidSurfaceBadScales Phi frame c ∩ Ioc lower upper) = 0 := by
  have hlowerPow : 0 < lower ^ 256 := pow_pos hlower _
  have hpows : lower ^ 256 ≤ upper ^ 256 :=
    pow_le_pow_left₀ hlower.le hlu 256
  have himage := volume_positiveRoot_image_criticalValues_inter_Icc_eq_zero
    (superellipsoidPolynomialLift Phi frame c)
    (contDiff_superellipsoidPolynomialLift Phi frame c) hlowerPow hpows
  exact measure_mono_null
    (badScales_inter_Ioc_subset_positiveRoot_image Phi frame c hlower hlu) himage

/-- Unconditional smooth outer selection: planar Sard plus the positive root chart supplies the
only null-set hypothesis of `exists_superellipsoidOuterSelection_of_badScales_null`. -/
theorem exists_superellipsoidOuterSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    Nonempty (SuperellipsoidOuterSelection K Phi frame c r) := by
  apply exists_superellipsoidOuterSelection_of_badScales_null K Phi frame c hr hfinite
  exact volume_superellipsoidSurfaceBadScales_inter_Ioc_eq_zero Phi frame c
    (mul_pos superellipsoidInnerFactor_pos hr)
    (mul_le_mul_of_nonneg_right superellipsoidInnerFactor_lt_outerFactor.le hr.le)

end Submission.PardonDistortion
