import Submission.LocalArc

open MeasureTheory Set
open scoped ENNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

lemma arcCoordinate_hasDerivAt (K : Knot) (t : ℝ) :
    HasDerivAt (arcCoordinate K) (speed K t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_speed K 0 t)
  · exact (continuous_speed K).stronglyMeasurableAtFilter volume (nhds t)
  · exact (continuous_speed K).continuousAt

lemma arcCoordinate_mem_Ico_of_mem_Ico (K : Knot) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    arcCoordinate K t ∈ Ico 0 (totalArcLength K) := by
  constructor
  · rw [← arcCoordinate_zero K]
    exact (strictMono_arcCoordinate K).monotone ht.1
  · rw [totalArcLength_eq_arcCoordinate]
    exact strictMono_arcCoordinate K ht.2

/-- Change variables from the knot parameter to arclength on any measurable
parameter set. -/
lemma lintegral_speed_eq_volume_arcCoordinate_image
    (K : Knot) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ t in A, ENNReal.ofReal (speed K t)) =
      volume (arcCoordinate K '' A) := by
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun t _ht ↦ (arcCoordinate_hasDerivAt K t).hasDerivWithinAt)
    (arcCoordinate_injective K).injOn (fun _ : ℝ ↦ (1 : ℝ≥0∞))
  simpa [abs_of_pos (speed_pos K _)] using hchange.symm

/-- A parameter set intrinsically contained in a radius-`R` ball on the knot
has arclength integral at most `2R`. -/
lemma lintegral_speed_le_two_mul_of_intrinsic
    (K : Knot) {A : Set ℝ} {s R : ℝ}
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ Ico (0 : ℝ) (2 * Real.pi)) (hs : s ∈ A)
    (hpair : ∀ t ∈ A, intrinsicDistance K s t ≤ R) :
    (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤ ENNReal.ofReal (2 * R) := by
  let _ : Fact (0 < totalArcLength K) := ⟨totalArcLength_pos K⟩
  let U : Set (AddCircle (totalArcLength K)) :=
    Metric.closedBall (arcCirclePoint K s) R
  have hsubset : arcCoordinate K '' A \ {0} ⊆
      ((fun y : ℝ ↦ (y : AddCircle (totalArcLength K))) ⁻¹' U) ∩
        Ioc 0 (totalArcLength K) := by
    rintro y ⟨⟨t, ht, rfl⟩, hy0⟩
    have htarc := arcCoordinate_mem_Ico_of_mem_Ico K (hA ht)
    constructor
    · exact arcCirclePoint_image_subset_closedBall K hA hs hpair ⟨t, ht, rfl⟩
    · exact ⟨lt_of_le_of_ne htarc.1 (Ne.symm hy0), htarc.2.le⟩
  rw [lintegral_speed_eq_volume_arcCoordinate_image K hAmeas]
  calc
    volume (arcCoordinate K '' A) =
        volume (arcCoordinate K '' A \ {0}) :=
      (measure_sdiff_null (measure_singleton (0 : ℝ))).symm
    _ ≤ volume
        (((fun y : ℝ ↦ (y : AddCircle (totalArcLength K))) ⁻¹' U) ∩
          Ioc 0 (totalArcLength K)) := measure_mono hsubset
    _ = volume U :=
      by
        simpa [U] using
          (AddCircle.add_projection_respects_measure (totalArcLength K) 0
            (U := U) measurableSet_closedBall).symm
    _ = ENNReal.ofReal (min (totalArcLength K) (2 * R)) :=
      AddCircle.volume_closedBall (totalArcLength K) R
    _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- Measurable parameters whose knot points lie in one positive rational box
have speed integral at most `10*r*D`. -/
lemma lintegral_speed_preimage_rationalBox_le
    (K : Knot) {c : R3} {r : ℝ} (hr : 0 < r)
    (hfinite : distortion K ≠ ⊤)
    {A : Set ℝ} (hAmeas : MeasurableSet A)
    (hA : A = Ico (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' rationalBox c r)
    (hne : A.Nonempty) :
    (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  subst A
  obtain ⟨s, hsI, hsB⟩ := hne
  calc
    (∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' rationalBox c r,
        ENNReal.ofReal (speed K t)) ≤
        ENNReal.ofReal (2 * (5 * r * (distortion K).toReal)) := by
      apply lintegral_speed_le_two_mul_of_intrinsic K hAmeas inter_subset_left ⟨hsI, hsB⟩
      intro t ht
      by_cases hst : s = t
      · subst t
        have hR : 0 ≤ 5 * r * (distortion K).toReal := by positivity
        simpa [intrinsicDistance, parameterArcLength, totalArcLength_pos K |>.le] using hR
      · calc
          intrinsicDistance K s t ≤
              (distortion K).toReal * dist (K.curve s) (K.curve t) :=
            intrinsicDistance_le_toReal_distortion_mul_dist K hsI ht.1 hst hfinite
          _ ≤ (distortion K).toReal * (5 * r) :=
            mul_le_mul_of_nonneg_left
              (dist_lt_five_mul_scale hr hsB ht.2).le ENNReal.toReal_nonneg
          _ = 5 * r * (distortion K).toReal := by ring
    _ = ENNReal.ofReal (10 * r * (distortion K).toReal) := by
      congr 1
      ring

end

end PardonDistortion
end Submission
