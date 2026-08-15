import ChallengeDeps
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

open Set
open scoped ENNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

/-- The speed of a smooth knot is continuous. -/
lemma continuous_speed (K : Knot) : Continuous (speed K) := by
  exact (K.smooth.continuous_deriv (by simp)).norm

/-- The speed of a smooth knot is interval integrable. -/
lemma intervalIntegrable_speed (K : Knot) (a b : ℝ) :
    IntervalIntegrable (speed K) MeasureTheory.volume a b :=
  (continuous_speed K).intervalIntegrable a b

/-- A parameter arc has nonnegative length. -/
lemma parameterArcLength_nonneg (K : Knot) (a b : ℝ) :
    0 ≤ parameterArcLength K a b :=
  abs_nonneg _

/-- On an interval with increasing endpoints, the parameter arc length is the integral of speed. -/
lemma parameterArcLength_eq_integral (K : Knot) {a b : ℝ} (hab : a ≤ b) :
    parameterArcLength K a b = ∫ t in a..b, speed K t := by
  rw [parameterArcLength, abs_of_nonneg]
  exact intervalIntegral.integral_nonneg_of_forall hab fun _ ↦ norm_nonneg _

/-- Euclidean displacement is bounded by the length of the corresponding parameter arc. -/
lemma dist_curve_le_parameterArcLength (K : Knot) {a b : ℝ} (hab : a ≤ b) :
    dist (K.curve a) (K.curve b) ≤ parameterArcLength K a b := by
  rw [parameterArcLength_eq_integral K hab]
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := K.curve) (B := speed K) hab K.smooth.continuous.continuousOn
    (K.smooth.differentiable (by simp)).differentiableOn
    (Filter.Eventually.of_forall fun _ _ ↦ le_rfl) (intervalIntegrable_speed K a b)
  simpa [speed, dist_eq_norm, norm_sub_rev] using h

/-- The two half-period arcs add to the total length. -/
lemma totalArcLength_eq_half_add_half (K : Knot) :
    totalArcLength K =
      parameterArcLength K 0 Real.pi + parameterArcLength K Real.pi (2 * Real.pi) := by
  rw [totalArcLength, parameterArcLength_eq_integral K Real.two_pi_pos.le,
    parameterArcLength_eq_integral K Real.pi_pos.le,
    parameterArcLength_eq_integral K (by linarith [Real.pi_pos])]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_speed K 0 Real.pi)
    (intervalIntegrable_speed K Real.pi (2 * Real.pi))).symm

/-- Every smooth knot has distortion at least one. -/
theorem one_le_distortion (K : Knot) : (1 : ℝ≥0∞) ≤ distortion K := by
  have hzero_mem : (0 : ℝ) ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    exact ⟨le_rfl, Real.two_pi_pos⟩
  have hpi_mem : Real.pi ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    exact ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have hne : (0 : ℝ) ≠ Real.pi := ne_of_lt Real.pi_pos
  have hcurve_ne : K.curve 0 ≠ K.curve Real.pi :=
    K.injOn.ne hzero_mem hpi_mem hne
  have hdist_pos : 0 < dist (K.curve 0) (K.curve Real.pi) :=
    dist_pos.mpr hcurve_ne
  have hfirst : dist (K.curve 0) (K.curve Real.pi) ≤
      parameterArcLength K 0 Real.pi :=
    dist_curve_le_parameterArcLength K Real.pi_pos.le
  have hsecond : dist (K.curve 0) (K.curve Real.pi) ≤
      parameterArcLength K Real.pi (2 * Real.pi) := by
    have h := dist_curve_le_parameterArcLength K
      (a := Real.pi) (b := 2 * Real.pi) (by linarith [Real.pi_pos])
    rw [show K.curve (2 * Real.pi) = K.curve 0 by simpa using K.periodic 0] at h
    simpa [dist_comm] using h
  have hintrinsic : dist (K.curve 0) (K.curve Real.pi) ≤
      intrinsicDistance K 0 Real.pi := by
    rw [intrinsicDistance, totalArcLength_eq_half_add_half]
    simpa using min_le_min hfirst hsecond
  have hratio : 1 ≤ distortionRatio K 0 Real.pi := by
    rw [distortionRatio, one_le_div₀ hdist_pos]
    exact hintrinsic
  apply (ENNReal.one_le_ofReal.mpr hratio).trans
  apply le_sSup
  exact ⟨0, hzero_mem, Real.pi, hpi_mem, hne, rfl⟩

end PardonDistortion
end Submission
