import Submission.ArcLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

/-- Arclength accumulated from parameter zero. -/
noncomputable def arcCoordinate (K : Knot) (t : ℝ) : ℝ :=
  ∫ u in 0..t, speed K u

lemma speed_pos (K : Knot) (t : ℝ) : 0 < speed K t := by
  exact norm_pos_iff.mpr (K.immersion t)

lemma arcCoordinate_zero (K : Knot) : arcCoordinate K 0 = 0 := by
  simp [arcCoordinate]

/-- Difference of accumulated arclengths is the integral of speed over the
intervening parameter interval. -/
lemma arcCoordinate_sub (K : Knot) (s t : ℝ) :
    arcCoordinate K t - arcCoordinate K s = ∫ u in s..t, speed K u := by
  exact intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_speed K 0 t) (intervalIntegrable_speed K 0 s)

lemma integral_speed_pos (K : Knot) {s t : ℝ} (hst : s < t) :
    0 < ∫ u in s..t, speed K u := by
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (intervalIntegrable_speed K s t) (speed_pos K) hst

/-- Immersion makes accumulated arclength a strictly increasing coordinate. -/
lemma strictMono_arcCoordinate (K : Knot) : StrictMono (arcCoordinate K) := by
  intro s t hst
  rw [← sub_pos, arcCoordinate_sub]
  exact integral_speed_pos K hst

lemma arcCoordinate_injective (K : Knot) : Function.Injective (arcCoordinate K) :=
  (strictMono_arcCoordinate K).injective

/-- On an increasing parameter interval, parameter arclength is ordinary
difference in arclength coordinates. -/
lemma parameterArcLength_eq_arcCoordinate_sub
    (K : Knot) {s t : ℝ} (hst : s ≤ t) :
    parameterArcLength K s t = arcCoordinate K t - arcCoordinate K s := by
  rw [parameterArcLength_eq_integral K hst, arcCoordinate_sub]

lemma totalArcLength_eq_arcCoordinate (K : Knot) :
    totalArcLength K = arcCoordinate K (2 * Real.pi) := by
  rw [totalArcLength, parameterArcLength_eq_arcCoordinate_sub K Real.two_pi_pos.le,
    arcCoordinate_zero, sub_zero]

lemma totalArcLength_pos (K : Knot) : 0 < totalArcLength K := by
  rw [totalArcLength_eq_arcCoordinate, ← arcCoordinate_zero K]
  exact strictMono_arcCoordinate K Real.two_pi_pos

/-- The derivative of a smooth periodic knot is periodic with the same
period. -/
lemma deriv_periodic (K : Knot) (t : ℝ) :
    deriv K.curve (t + 2 * Real.pi) = deriv K.curve t := by
  have heq : (fun u ↦ K.curve (u + 2 * Real.pi)) = K.curve :=
    funext K.periodic
  have hderiv := congrArg (fun f : ℝ → R3 ↦ deriv f t) heq
  rwa [deriv_comp_add_const] at hderiv

lemma speed_periodic (K : Knot) (t : ℝ) :
    speed K (t + 2 * Real.pi) = speed K t := by
  rw [speed, speed, deriv_periodic]

lemma periodic_speed (K : Knot) :
    Function.Periodic (speed K) (2 * Real.pi) :=
  speed_periodic K

/-- Every parameter interval of one period has the total arclength. -/
lemma integral_speed_add_period (K : Knot) (t : ℝ) :
    ∫ u in t..t + 2 * Real.pi, speed K u = totalArcLength K := by
  calc
    (∫ u in t..t + 2 * Real.pi, speed K u) =
        ∫ u in 0..0 + 2 * Real.pi, speed K u :=
      (periodic_speed K).intervalIntegral_add_eq t 0
    _ = totalArcLength K := by
      rw [zero_add, ← parameterArcLength_eq_integral K Real.two_pi_pos.le]
      rfl

/-- Accumulated arclength intertwines one parameter period with translation by
the total length. -/
lemma arcCoordinate_add_period (K : Knot) (t : ℝ) :
    arcCoordinate K (t + 2 * Real.pi) = arcCoordinate K t + totalArcLength K := by
  have h := arcCoordinate_sub K t (t + 2 * Real.pi)
  rw [integral_speed_add_period] at h
  linarith

lemma parameterArcLength_lt_total_of_mem_Ico
    (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hst : s < t) :
    parameterArcLength K s t < totalArcLength K := by
  rw [parameterArcLength_eq_arcCoordinate_sub K hst.le,
    totalArcLength_eq_arcCoordinate]
  have h0s : arcCoordinate K 0 ≤ arcCoordinate K s :=
    (strictMono_arcCoordinate K).monotone hs.1
  have htT : arcCoordinate K t < arcCoordinate K (2 * Real.pi) :=
    strictMono_arcCoordinate K ht.2
  rw [arcCoordinate_zero] at h0s
  linarith

lemma intrinsicDistance_eq_min_arcCoordinate
    (K : Knot) {s t : ℝ} (hst : s ≤ t) :
    intrinsicDistance K s t =
      min (arcCoordinate K t - arcCoordinate K s)
        (totalArcLength K - (arcCoordinate K t - arcCoordinate K s)) := by
  rw [intrinsicDistance, parameterArcLength_eq_arcCoordinate_sub K hst]

lemma intrinsicDistance_pos_of_mem_Ico
    (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hst : s < t) :
    0 < intrinsicDistance K s t := by
  rw [intrinsicDistance_eq_min_arcCoordinate K hst.le, lt_min_iff]
  constructor
  · exact sub_pos.mpr (strictMono_arcCoordinate K hst)
  · rw [sub_pos]
    simpa [parameterArcLength_eq_arcCoordinate_sub K hst.le] using
      parameterArcLength_lt_total_of_mem_Ico K hs ht hst

end PardonDistortion
end Submission
