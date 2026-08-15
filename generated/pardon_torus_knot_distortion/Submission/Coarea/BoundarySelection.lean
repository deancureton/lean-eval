import Submission.ArcMeasure
import Submission.Coarea.Lipschitz

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Branch-free selection of a rational-box boundary

This file combines the Lipschitz coarea theorem with the local arclength
estimate.  A closed box is used to obtain a compact parameter set; its extra
period endpoint is measure-null, while the strict coefficient in the box
diameter calculation preserves the same `5r` geometric bound.
-/

/-- The closed rational box, expressed as a sublevel set of the weighted
sup-norm gauge. -/
def closedRationalBox (c : R3) (r : ℝ) : Set R3 :=
  {x | rationalBoxGauge c x ≤ r}

lemma isClosed_closedRationalBox (c : R3) (r : ℝ) :
    IsClosed (closedRationalBox c r) :=
  isClosed_Iic.preimage (continuous_rationalBoxGauge c)

lemma measurableSet_closedRationalBox (c : R3) (r : ℝ) :
    MeasurableSet (closedRationalBox c r) :=
  (isClosed_closedRationalBox c r).measurableSet

lemma mem_closedRationalBox_iff {c x : R3} {r : ℝ} :
    x ∈ closedRationalBox c r ↔ rationalBoxGauge c x ≤ r :=
  Iff.rfl

lemma abs_coord_sub_center_le {c x : R3} {r : ℝ}
    (hx : x ∈ closedRationalBox c r) (i : Fin 3) :
    |x.ofLp i - c.ofLp i| ≤ axisWeight i * r := by
  have hi : ‖normalizedBoxCoordinates c x i‖ ≤ rationalBoxGauge c x :=
    norm_le_pi_norm (normalizedBoxCoordinates c x) i
  have hir : ‖normalizedBoxCoordinates c x i‖ ≤ r := hi.trans hx
  rw [normalizedBoxCoordinates, Real.norm_eq_abs, abs_div,
    abs_of_pos (axisWeight_pos i), div_le_iff₀ (axisWeight_pos i)] at hir
  simpa [mul_comm] using hir

lemma abs_coord_sub_coord_le_two_mul {c x y : R3} {r : ℝ}
    (hx : x ∈ closedRationalBox c r) (hy : y ∈ closedRationalBox c r)
    (i : Fin 3) :
    |x.ofLp i - y.ofLp i| ≤ 2 * axisWeight i * r := by
  calc
    |x.ofLp i - y.ofLp i| =
        |(x.ofLp i - c.ofLp i) + (c.ofLp i - y.ofLp i)| := by ring_nf
    _ ≤ |x.ofLp i - c.ofLp i| + |c.ofLp i - y.ofLp i| := abs_add_le _ _
    _ ≤ axisWeight i * r + axisWeight i * r :=
      add_le_add (abs_coord_sub_center_le hx i) (by
        simpa [abs_sub_comm] using abs_coord_sub_center_le hy i)
    _ = 2 * axisWeight i * r := by ring

/-- The same strict `5r` diameter estimate holds for the closed rational box. -/
lemma dist_lt_five_mul_scale_of_mem_closed {c x y : R3} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ closedRationalBox c r)
    (hy : y ∈ closedRationalBox c r) :
    dist x y < 5 * r := by
  have hcoord (i : Fin 3) :
      dist (x.ofLp i) (y.ofLp i) ≤ 2 * axisWeight i * r := by
    simpa [Real.dist_eq] using abs_coord_sub_coord_le_two_mul hx hy i
  have hcoord_nonneg (i : Fin 3) : 0 ≤ 2 * axisWeight i * r := by
    exact mul_nonneg (mul_nonneg (by norm_num) (axisWeight_pos i).le) hr.le
  have hsq (i : Fin 3) :
      dist (x.ofLp i) (y.ofLp i) ^ 2 ≤ (2 * axisWeight i * r) ^ 2 := by
    exact sq_le_sq₀ dist_nonneg (hcoord_nonneg i) |>.2 (hcoord i)
  have hsum :
      ∑ i : Fin 3, dist (x.ofLp i) (y.ofLp i) ^ 2 ≤
        ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ hsq i
  rw [← PiLp.dist_sq_eq_of_L2] at hsum
  have hsum_rhs :
      ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 =
        4 * (∑ i : Fin 3, axisWeight i ^ 2) * r ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three, axisWeight_zero,
      axisWeight_one, axisWeight_two]
    ring
  rw [hsum_rhs, sum_axisWeight_sq] at hsum
  have hweight := four_mul_weight_sq_sum_lt_twenty_five
  have hfive_pos : 0 < 5 * r := mul_pos (by norm_num) hr
  have hstrict : dist x y ^ 2 < 25 * r ^ 2 := by
    exact hsum.trans_lt (by
      nlinarith [mul_lt_mul_of_pos_right hweight (sq_pos_of_pos hr)])
  have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- The shell derivative is bounded by knot speed wherever the shell
coordinate is differentiable.  No differentiability of the ambient sup norm
is required. -/
lemma abs_deriv_boxShellParameter_le_speed_of_differentiableAt
    (K : Knot) (c : R3) (t : ℝ)
    (hshell : DifferentiableAt ℝ (boxShellParameter K c) t) :
    |deriv (boxShellParameter K c) t| ≤ speed K t := by
  have hcurve : HasDerivAt K.curve (deriv K.curve t) t :=
    (K.smooth.differentiable (by simp) t).hasDerivAt
  have hslope : ∀ y : ℝ,
      ‖slope (boxShellParameter K c) t y‖ ≤ ‖slope K.curve t y‖ := by
    intro y
    rw [slope, slope, norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    change ‖rationalBoxGauge c (K.curve y) - rationalBoxGauge c (K.curve t)‖ ≤
      ‖K.curve y - K.curve t‖
    simpa only [NNReal.coe_one, one_mul] using
      (lipschitzWith_rationalBoxGauge c).norm_sub_le (K.curve y) (K.curve t)
  have hlimShell := hshell.hasDerivAt.tendsto_slope.norm
  have hlimCurve := hcurve.tendsto_slope.norm
  rw [← Real.norm_eq_abs, speed]
  exact le_of_tendsto_of_tendsto hlimShell hlimCurve
    (Filter.Eventually.of_forall hslope)

lemma abs_deriv_boxShellParameter_le_speed (K : Knot) (c : R3) (t : ℝ) :
    |deriv (boxShellParameter K c) t| ≤ speed K t := by
  by_cases hdiff : DifferentiableAt ℝ (boxShellParameter K c) t
  · exact abs_deriv_boxShellParameter_le_speed_of_differentiableAt K c t hdiff
  · rw [deriv_zero_of_not_differentiableAt hdiff, abs_zero]
    exact (speed_pos K t).le

/-- Speed integral inside a closed rational box.  The bound is identical to
the open-box result because the closed box still has diameter strictly below
`5r`. -/
lemma lintegral_speed_preimage_closedRationalBox_le
    (K : Knot) {c : R3} {r : ℝ} (hr : 0 < r)
    (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedRationalBox c r,
        ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  let A : Set ℝ := Ico (0 : ℝ) (2 * Real.pi) ∩
    K.curve ⁻¹' closedRationalBox c r
  have hAmeas : MeasurableSet A := measurableSet_Ico.inter
    ((measurableSet_closedRationalBox c r).preimage K.smooth.continuous.measurable)
  by_cases hne : A.Nonempty
  · obtain ⟨s, hsI, hsB⟩ := hne
    calc
      (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤
          ENNReal.ofReal (2 * (5 * r * (distortion K).toReal)) := by
        apply lintegral_speed_le_two_mul_of_intrinsic K hAmeas inter_subset_left
          ⟨hsI, hsB⟩
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
                (dist_lt_five_mul_scale_of_mem_closed hr hsB ht.2).le
                ENNReal.toReal_nonneg
            _ = 5 * r * (distortion K).toReal := by ring
      _ = ENNReal.ofReal (10 * r * (distortion K).toReal) := by
        congr 1
        ring
  · have hA : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    change (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤ _
    rw [hA]
    simp

/-- The compact parameter set obtained by retaining one closed fundamental
interval and the part of the knot lying in a closed rational box. -/
def closedBoxParameters (K : Knot) (c : R3) (r : ℝ) : Set ℝ :=
  Icc (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' closedRationalBox c r

lemma isCompact_closedBoxParameters (K : Knot) (c : R3) (r : ℝ) :
    IsCompact (closedBoxParameters K c r) := by
  exact isCompact_Icc.inter_right
    ((isClosed_closedRationalBox c r).preimage K.smooth.continuous)

/-- Adding the right endpoint of the fundamental interval does not change a
local speed integral. -/
lemma lintegral_closedBoxParameters_speed_eq_halfOpen
    (K : Knot) (c : R3) (r : ℝ) :
    (∫⁻ t in closedBoxParameters K c r, ENNReal.ofReal (speed K t)) =
      ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedRationalBox c r, ENNReal.ofReal (speed K t) := by
  have hsets :
      closedBoxParameters K c r =ᵐ[volume]
        ((Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedRationalBox c r) : Set ℝ) := by
    filter_upwards [MeasureTheory.Ico_ae_eq_Icc (μ := volume)
      (a := (0 : ℝ)) (b := 2 * Real.pi)] with t ht
    exact congrArg (fun p : Prop ↦ p ∧ K.curve t ∈ closedRationalBox c r) ht.symm
  rw [Measure.restrict_congr_set hsets]

/-- The shell-coordinate Jacobian on the compact closed-box parameter set is
bounded by the same local arclength estimate as on the half-open fundamental
interval. -/
lemma lintegral_abs_deriv_boxShellParameter_closedBoxParameters_le
    (K : Knot) {c : R3} {r : ℝ} (hr : 0 < r)
    (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in closedBoxParameters K c r,
        ENNReal.ofReal |deriv (boxShellParameter K c) t|) ≤
      ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  calc
    (∫⁻ t in closedBoxParameters K c r,
        ENNReal.ofReal |deriv (boxShellParameter K c) t|) ≤
        ∫⁻ t in closedBoxParameters K c r, ENNReal.ofReal (speed K t) := by
      exact lintegral_mono fun t ↦
        ENNReal.ofReal_le_ofReal (abs_deriv_boxShellParameter_le_speed K c t)
    _ = ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedRationalBox c r,
          ENNReal.ofReal (speed K t) :=
      lintegral_closedBoxParameters_speed_eq_halfOpen K c r
    _ ≤ ENNReal.ofReal (10 * r * (distortion K).toReal) :=
      lintegral_speed_preimage_closedRationalBox_le K hr hfinite

/-- Branch-free outer-boundary selection.  The compact closed-box parameter
set is used only to invoke coarea; because the selected level is no larger
than the outer radius, every occurrence of that level on the half-open
fundamental interval already lies in that compact set. -/
theorem exists_outerBoundary_count_le_distortion
    (K : Knot) (c : R3) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hfinite : distortion K ≠ ⊤) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      y ∉ (boxShellParameter K c) ''
        Submission.Coarea.lipschitzExceptionalSet (boxShellParameter K c) ∧
      (Submission.Coarea.fiberSet (boxShellParameter K c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite ∧
      (boxBoundaryCount K c (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
        ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
  have houter : 0 < (1 + ε) * r := mul_pos (by linarith) hr
  have hwidth : (1 + ε) * r - r = ε * r := by ring
  obtain ⟨y, hy, hyExceptional, hfiniteCompact, hybound⟩ :=
    Submission.Coarea.PardonApplication.exists_boxShellRegularValue_fiberCount_le_integral_of_isCompact
        K c (isCompact_closedBoxParameters K c ((1 + ε) * r))
          (show r < (1 + ε) * r by nlinarith)
  have hsub :
      Submission.Coarea.fiberSet (boxShellParameter K c)
          (Ico (0 : ℝ) (2 * Real.pi)) y ⊆
        Submission.Coarea.fiberSet (boxShellParameter K c)
          (closedBoxParameters K c ((1 + ε) * r)) y := by
    intro t ht
    rw [Submission.Coarea.fiberSet] at ht ⊢
    rcases ht with ⟨htIco, htlevel⟩
    refine ⟨⟨⟨htIco.1, htIco.2.le⟩, ?_⟩, htlevel⟩
    change rationalBoxGauge c (K.curve t) ≤ (1 + ε) * r
    change rationalBoxGauge c (K.curve t) = y at htlevel
    rw [htlevel]
    exact hy.2
  have hfiniteHalfOpen :
      (Submission.Coarea.fiberSet (boxShellParameter K c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite :=
    hfiniteCompact.subset hsub
  refine ⟨y, hy, hyExceptional, hfiniteHalfOpen, ?_⟩
  have hcount :
      (boxBoundaryCount K c (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
        (Submission.Coarea.fiberCount (boxShellParameter K c)
          (closedBoxParameters K c ((1 + ε) * r)) y : ℝ≥0∞) := by
    change ((Submission.Coarea.fiberSet (boxShellParameter K c)
      (Ico (0 : ℝ) (2 * Real.pi)) y).ncard : ℝ≥0∞) ≤
        ((Submission.Coarea.fiberSet (boxShellParameter K c)
          (closedBoxParameters K c ((1 + ε) * r)) y).ncard : ℝ≥0∞)
    exact_mod_cast Set.ncard_le_ncard hsub hfiniteCompact
  refine hcount.trans (hybound.trans ?_)
  calc
    (∫⁻ t in closedBoxParameters K c ((1 + ε) * r),
        ENNReal.ofReal |deriv (boxShellParameter K c) t|) /
          ENNReal.ofReal ((1 + ε) * r - r) ≤
        ENNReal.ofReal (10 * ((1 + ε) * r) * (distortion K).toReal) /
          ENNReal.ofReal ((1 + ε) * r - r) := by
      exact ENNReal.div_le_div
        (lintegral_abs_deriv_boxShellParameter_closedBoxParameters_le
          K houter hfinite) le_rfl
    _ = ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
      rw [hwidth]
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hε hr)]
      congr 1
      field_simp [ne_of_gt hε, ne_of_gt hr]
      ring

/-- At the shell width used in Pardon's argument, `ε = 1/7`, the branch-free
selector gives the exact constant `80 D`. -/
theorem exists_outerBoundary_count_le_eighty_mul_distortion
    (K : Knot) (c : R3) {r : ℝ} (hr : 0 < r)
    (hfinite : distortion K ≠ ⊤) :
    ∃ y ∈ Ioc r ((8 / 7) * r),
      y ∉ (boxShellParameter K c) ''
        Submission.Coarea.lipschitzExceptionalSet (boxShellParameter K c) ∧
      (Submission.Coarea.fiberSet (boxShellParameter K c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite ∧
      (boxBoundaryCount K c (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
        ENNReal.ofReal (80 * (distortion K).toReal) := by
  obtain ⟨y, hy, hyExceptional, hfiniteFiber, hybound⟩ :=
    exists_outerBoundary_count_le_distortion K c hr
      (show (0 : ℝ) < 1 / 7 by norm_num) hfinite
  refine ⟨y, ?_, hyExceptional, hfiniteFiber, ?_⟩
  · have hscale : (8 / 7 : ℝ) = 1 + 1 / 7 := by norm_num
    rw [hscale]
    exact hy
  · have hconstant : (10 * (1 + 1 / ((1 : ℝ) / 7)) : ℝ) = 80 := by norm_num
    rw [hconstant] at hybound
    exact hybound

end


end PardonDistortion
end Submission
