import Submission.ArcLength

open Set
open scoped ENNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

/-- Convert the benchmark's `ENNReal` normalization into ordinary real division. -/
lemma ennreal_one_div_nat_mul_natCast_eq_ofReal_div (c n : ℕ) (hc : 0 < c) :
    (1 / (c : ℝ≥0∞)) * (n : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) / (c : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hc), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  simp [div_eq_mul_inv, mul_comm]

/-- Distinct parameters in the fundamental interval give distinct points of the knot. -/
lemma curve_ne_of_mem_Ico (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t) :
    K.curve s ≠ K.curve t :=
  K.injOn.ne hs ht hst

/-- Distinct parameters in the fundamental interval have positive chord length. -/
lemma dist_curve_pos_of_mem_Ico (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t) :
    0 < dist (K.curve s) (K.curve t) :=
  dist_pos.mpr (curve_ne_of_mem_Ico K hs ht hst)

/-- Every admissible pairwise distortion ratio is bounded by the defining supremum. -/
lemma ofReal_distortionRatio_le_distortion (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t) :
    ENNReal.ofReal (distortionRatio K s t) ≤ distortion K := by
  apply le_sSup
  exact ⟨s, hs, t, ht, hst, rfl⟩

/-- A real lower bound for one pairwise ratio gives an extended-real lower bound for distortion. -/
lemma ofReal_le_distortion_of_le_distortionRatio (K : Knot) {s t r : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (hr : r ≤ distortionRatio K s t) :
    ENNReal.ofReal r ≤ distortion K :=
  (ENNReal.ofReal_le_ofReal hr).trans
    (ofReal_distortionRatio_le_distortion K hs ht hst)

/-- A pairwise real bound at the benchmark's normalization proves the stated target. -/
lemma pardonTarget_le_distortion_of_le_distortionRatio
    (p q : ℕ) (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (hr : ((Nat.min p q : ℕ) : ℝ) / 160 ≤ distortionRatio K s t) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  calc
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) =
        ENNReal.ofReal (((Nat.min p q : ℕ) : ℝ) / (160 : ℝ)) :=
      ennreal_one_div_nat_mul_natCast_eq_ofReal_div 160 (Nat.min p q) (by norm_num)
    _ ≤ distortion K := ofReal_le_distortion_of_le_distortionRatio K hs ht hst hr

/-- If the total distortion is finite, each real pairwise ratio is bounded by its real value. -/
lemma distortionRatio_le_toReal_distortion (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (hfinite : distortion K ≠ ⊤) :
    distortionRatio K s t ≤ (distortion K).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    (ofReal_distortionRatio_le_distortion K hs ht hst)

/-- Finite distortion is at least one after conversion to a real number. -/
lemma one_le_toReal_distortion (K : Knot) (hfinite : distortion K ≠ ⊤) :
    (1 : ℝ) ≤ (distortion K).toReal := by
  have h := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hfinite).mpr
    (one_le_distortion K)
  simpa using h

/--
For a finite-distortion knot, intrinsic arclength between an admissible pair is at most
the distortion times the Euclidean chord length.
-/
lemma intrinsicDistance_le_toReal_distortion_mul_dist (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (hfinite : distortion K ≠ ⊤) :
    intrinsicDistance K s t ≤
      (distortion K).toReal * dist (K.curve s) (K.curve t) := by
  have hdist_ne : dist (K.curve s) (K.curve t) ≠ 0 :=
    (dist_curve_pos_of_mem_Ico K hs ht hst).ne'
  calc
    intrinsicDistance K s t =
        distortionRatio K s t * dist (K.curve s) (K.curve t) := by
      rw [distortionRatio, div_mul_cancel₀ _ hdist_ne]
    _ ≤ (distortion K).toReal * dist (K.curve s) (K.curve t) :=
      mul_le_mul_of_nonneg_right
        (distortionRatio_le_toReal_distortion K hs ht hst hfinite) dist_nonneg

/--
The preceding local estimate has an unconditional extended-real form: it remains true
when the knot has infinite distortion.
-/
lemma ofReal_intrinsicDistance_le_distortion_mul_ofReal_dist (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t) :
    ENNReal.ofReal (intrinsicDistance K s t) ≤
      distortion K * ENNReal.ofReal (dist (K.curve s) (K.curve t)) := by
  by_cases hfinite : distortion K = ⊤
  · rw [hfinite, ENNReal.top_mul (ENNReal.ofReal_pos.mpr
      (dist_curve_pos_of_mem_Ico K hs ht hst)).ne']
    exact le_top
  · calc
      ENNReal.ofReal (intrinsicDistance K s t) ≤
          ENNReal.ofReal
            ((distortion K).toReal * dist (K.curve s) (K.curve t)) :=
        ENNReal.ofReal_le_ofReal
          (intrinsicDistance_le_toReal_distortion_mul_dist K hs ht hst hfinite)
      _ = ENNReal.ofReal (distortion K).toReal *
          ENNReal.ofReal (dist (K.curve s) (K.curve t)) :=
        ENNReal.ofReal_mul ENNReal.toReal_nonneg
      _ = distortion K * ENNReal.ofReal (dist (K.curve s) (K.curve t)) := by
        rw [ENNReal.ofReal_toReal hfinite]

/-- On an increasing parameter interval, replace the chord by the (larger) arc length. -/
lemma intrinsicDistance_le_toReal_distortion_mul_parameterArcLength
    (K : Knot) {s t : ℝ} (hst_order : s ≤ t)
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (hfinite : distortion K ≠ ⊤) :
    intrinsicDistance K s t ≤
      (distortion K).toReal * parameterArcLength K s t := by
  refine (intrinsicDistance_le_toReal_distortion_mul_dist K hs ht hst hfinite).trans ?_
  exact mul_le_mul_of_nonneg_left
    (dist_curve_le_parameterArcLength K hst_order) ENNReal.toReal_nonneg

end PardonDistortion
end Submission
