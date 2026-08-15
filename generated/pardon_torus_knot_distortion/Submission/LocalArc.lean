import Submission.ArcCoordinate
import Submission.BoxGeometry
import Submission.Distortion

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

private theorem knotTotalLengthPositive (K : Knot) : Fact (0 < totalArcLength K) :=
  ⟨totalArcLength_pos K⟩

/-- The arclength coordinate of a knot, regarded modulo its total length. -/
noncomputable def arcCirclePoint (K : Knot) (t : ℝ) : AddCircle (totalArcLength K) :=
  arcCoordinate K t

@[simp] lemma arcCirclePoint_add_period (K : Knot) (t : ℝ) :
    arcCirclePoint K (t + 2 * Real.pi) = arcCirclePoint K t := by
  rw [arcCirclePoint, arcCirclePoint, arcCoordinate_add_period]
  exact AddCircle.coe_add_period (p := totalArcLength K) (arcCoordinate K t)

lemma parameterArcLength_comm (K : Knot) (s t : ℝ) :
    parameterArcLength K s t = parameterArcLength K t s := by
  rw [parameterArcLength, parameterArcLength, intervalIntegral.integral_symm]
  exact abs_neg _

lemma intrinsicDistance_comm (K : Knot) (s t : ℝ) :
    intrinsicDistance K s t = intrinsicDistance K t s := by
  simp only [intrinsicDistance, parameterArcLength_comm K s t]

/-- On one parameter period, the quotient-circle distance between arclength
coordinates is at most intrinsic knot distance.  (It is in fact equal, but
the one-sided statement is exactly what the local-length argument needs.) -/
lemma dist_arcCirclePoint_le_intrinsicDistance
    (K : Knot) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    dist (arcCirclePoint K s) (arcCirclePoint K t) ≤ intrinsicDistance K s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, intrinsicDistance_comm]
    exact this ht hs (le_of_not_ge hst)
  rw [intrinsicDistance_eq_min_arcCoordinate K hst, le_min_iff]
  have hdelta_nonneg :
      0 ≤ arcCoordinate K t - arcCoordinate K s :=
    sub_nonneg.mpr ((strictMono_arcCoordinate K).monotone hst)
  have hdelta_le :
      arcCoordinate K t - arcCoordinate K s ≤ totalArcLength K := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · simp [totalArcLength_pos K |>.le]
    · rw [← parameterArcLength_eq_arcCoordinate_sub K hst]
      exact (parameterArcLength_lt_total_of_mem_Ico K hs ht hst').le
  constructor
  · calc
      dist (arcCirclePoint K s) (arcCirclePoint K t) =
          ‖((arcCoordinate K s - arcCoordinate K t : ℝ) :
            AddCircle (totalArcLength K))‖ := by
        rw [dist_eq_norm, arcCirclePoint, arcCirclePoint, ← AddCircle.coe_sub]
      _ ≤ |arcCoordinate K s - arcCoordinate K t| :=
        QuotientAddGroup.norm_mk_le_norm
      _ = arcCoordinate K t - arcCoordinate K s := by
        rw [abs_sub_comm, abs_of_nonneg hdelta_nonneg]
  · let x := arcCoordinate K s - arcCoordinate K t
    have hcoe :
        ((x : ℝ) : AddCircle (totalArcLength K)) =
          ((x + totalArcLength K : ℝ) : AddCircle (totalArcLength K)) := by
      exact (AddCircle.coe_add_period (p := totalArcLength K) x).symm
    calc
      dist (arcCirclePoint K s) (arcCirclePoint K t) =
          ‖((x : ℝ) : AddCircle (totalArcLength K))‖ := by
        rw [dist_eq_norm, arcCirclePoint, arcCirclePoint, ← AddCircle.coe_sub]
      _ = ‖((x + totalArcLength K : ℝ) : AddCircle (totalArcLength K))‖ :=
        congrArg norm hcoe
      _ ≤ |x + totalArcLength K| := QuotientAddGroup.norm_mk_le_norm
      _ = totalArcLength K -
          (arcCoordinate K t - arcCoordinate K s) := by
        rw [abs_of_nonneg]
        · dsimp [x]
          ring
        · dsimp [x]
          linarith

/-- The arclength content of a parameter set, measured after passing to the
arclength circle.  This avoids double-counting the period endpoints. -/
noncomputable def arcContent (K : Knot) (A : Set ℝ) : ℝ≥0∞ :=
  let _ := knotTotalLengthPositive K
  MeasureTheory.volume (arcCirclePoint K '' A)

lemma arcCirclePoint_image_subset_closedBall
    (K : Knot) {A : Set ℝ} {s R : ℝ}
    (hA : A ⊆ Ico (0 : ℝ) (2 * Real.pi)) (hs : s ∈ A)
    (hpair : ∀ t ∈ A, intrinsicDistance K s t ≤ R) :
    arcCirclePoint K '' A ⊆ Metric.closedBall (arcCirclePoint K s) R := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact (dist_arcCirclePoint_le_intrinsicDistance K (hA hs) (hA ht)).trans (hpair t ht)

/-- If every point of a parameter set is intrinsically within `R` of one
chosen point, its total arclength content is at most `2R`. -/
lemma arcContent_le_two_mul
    (K : Knot) {A : Set ℝ} {s R : ℝ}
    (hA : A ⊆ Ico (0 : ℝ) (2 * Real.pi)) (hs : s ∈ A)
    (hpair : ∀ t ∈ A, intrinsicDistance K s t ≤ R) :
    arcContent K A ≤ ENNReal.ofReal (2 * R) := by
  let _ := knotTotalLengthPositive K
  calc
    arcContent K A ≤ MeasureTheory.volume (Metric.closedBall (arcCirclePoint K s) R) :=
      MeasureTheory.measure_mono (arcCirclePoint_image_subset_closedBall K hA hs hpair)
    _ = ENNReal.ofReal (min (totalArcLength K) (2 * R)) :=
      AddCircle.volume_closedBall (totalArcLength K) R
    _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- A subset of a positive-scale rational box occupies at most `10*r*D` of
the arclength circle, where `D` is the finite distortion. -/
lemma arcContent_preimage_rationalBox_le
    (K : Knot) {c : R3} {r : ℝ} (hr : 0 < r)
    (hfinite : distortion K ≠ ⊤)
    {A : Set ℝ} (hA : A = Ico (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' rationalBox c r)
    (hne : A.Nonempty) :
    arcContent K A ≤ ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  subst A
  obtain ⟨s, hsI, hsB⟩ := hne
  calc
    arcContent K (Ico (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' rationalBox c r) ≤
        ENNReal.ofReal (2 * (5 * r * (distortion K).toReal)) := by
      apply arcContent_le_two_mul K inter_subset_left ⟨hsI, hsB⟩
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

end PardonDistortion
end Submission
