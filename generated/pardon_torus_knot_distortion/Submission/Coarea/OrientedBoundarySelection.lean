import Submission.Coarea.BoundarySelection
import Submission.Coarea.OrientedShell

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Branch-free boundary selection in an oriented rational box

The argument is uniform in the permuted coordinate frame.  A compact closed
box supplies the parameter set required by Lipschitz coarea, and its additional
period endpoint is null for the local speed integral.
-/

/-- The closed sublevel set of the oriented weighted sup gauge. -/
def closedOrientedBox
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Set R3 :=
  {x | orientedBoxGauge frame c x ≤ r}

lemma isClosed_closedOrientedBox
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) :
    IsClosed (closedOrientedBox frame c r) :=
  isClosed_Iic.preimage (continuous_orientedBoxGauge frame c)

lemma measurableSet_closedOrientedBox
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) :
    MeasurableSet (closedOrientedBox frame c r) :=
  (isClosed_closedOrientedBox frame c r).measurableSet

lemma abs_orientedCoord_sub_center_le
    {frame : Equiv.Perm (Fin 3)} {c x : R3} {r : ℝ}
    (hx : x ∈ closedOrientedBox frame c r) (i : Fin 3) :
    |x.ofLp (frame i) - c.ofLp (frame i)| ≤ axisWeight i * r := by
  have hi : ‖normalizedOrientedBoxCoordinates frame c x i‖ ≤
      orientedBoxGauge frame c x :=
    norm_le_pi_norm (normalizedOrientedBoxCoordinates frame c x) i
  have hir : ‖normalizedOrientedBoxCoordinates frame c x i‖ ≤ r := hi.trans hx
  rw [normalizedOrientedBoxCoordinates, Real.norm_eq_abs, abs_div,
    abs_of_pos (axisWeight_pos i), div_le_iff₀ (axisWeight_pos i)] at hir
  simpa [sub_eq_add_neg, mul_comm] using hir

lemma abs_orientedCoord_sub_coord_le_two_mul
    {frame : Equiv.Perm (Fin 3)} {c x y : R3} {r : ℝ}
    (hx : x ∈ closedOrientedBox frame c r)
    (hy : y ∈ closedOrientedBox frame c r) (i : Fin 3) :
    |x.ofLp (frame i) - y.ofLp (frame i)| ≤ 2 * axisWeight i * r := by
  calc
    |x.ofLp (frame i) - y.ofLp (frame i)| =
        |(x.ofLp (frame i) - c.ofLp (frame i)) +
          (c.ofLp (frame i) - y.ofLp (frame i))| := by ring_nf
    _ ≤ |x.ofLp (frame i) - c.ofLp (frame i)| +
        |c.ofLp (frame i) - y.ofLp (frame i)| := abs_add_le _ _
    _ ≤ axisWeight i * r + axisWeight i * r :=
      add_le_add (abs_orientedCoord_sub_center_le hx i) (by
        simpa [abs_sub_comm] using abs_orientedCoord_sub_center_le hy i)
    _ = 2 * axisWeight i * r := by ring

/-- Permuting the box axes leaves the strict `5r` diameter estimate
unchanged. -/
lemma dist_lt_five_mul_scale_of_mem_closedOrientedBox
    {frame : Equiv.Perm (Fin 3)} {c x y : R3} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ closedOrientedBox frame c r)
    (hy : y ∈ closedOrientedBox frame c r) :
    dist x y < 5 * r := by
  have hcoord (i : Fin 3) :
      dist (x.ofLp (frame i)) (y.ofLp (frame i)) ≤
        2 * axisWeight i * r := by
    simpa [Real.dist_eq] using abs_orientedCoord_sub_coord_le_two_mul hx hy i
  have hcoord_nonneg (i : Fin 3) : 0 ≤ 2 * axisWeight i * r := by
    exact mul_nonneg (mul_nonneg (by norm_num) (axisWeight_pos i).le) hr.le
  have hsq (i : Fin 3) :
      dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2 ≤
        (2 * axisWeight i * r) ^ 2 :=
    sq_le_sq₀ dist_nonneg (hcoord_nonneg i) |>.2 (hcoord i)
  have hsum :
      ∑ i : Fin 3, dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2 ≤
        ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ hsq i
  have hperm :
      (∑ i : Fin 3, dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2) =
        ∑ i : Fin 3, dist (x.ofLp i) (y.ofLp i) ^ 2 :=
    Equiv.sum_comp frame
      (fun i : Fin 3 ↦ dist (x.ofLp i) (y.ofLp i) ^ 2)
  rw [hperm, ← PiLp.dist_sq_eq_of_L2] at hsum
  have hsum_rhs :
      ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 =
        4 * (∑ i : Fin 3, axisWeight i ^ 2) * r ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three, axisWeight_zero,
      axisWeight_one, axisWeight_two]
    ring
  rw [hsum_rhs, sum_axisWeight_sq] at hsum
  have hweight := four_mul_weight_sq_sum_lt_twenty_five
  have hstrict : dist x y ^ 2 < 25 * r ^ 2 := by
    exact hsum.trans_lt (by
      nlinarith [mul_lt_mul_of_pos_right hweight (sq_pos_of_pos hr)])
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- The oriented shell derivative is bounded by speed at every parameter,
with the nondifferentiable case supplied by the definition of `deriv`. -/
lemma abs_deriv_orientedShellParameter_le_speed
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (t : ℝ) :
    |deriv (orientedShellParameter K frame c) t| ≤ speed K t := by
  by_cases hdiff : DifferentiableAt ℝ (orientedShellParameter K frame c) t
  · exact abs_deriv_orientedShellParameter_le_speed_of_differentiableAt
      K frame c t hdiff
  · rw [deriv_zero_of_not_differentiableAt hdiff, abs_zero]
    exact (speed_pos K t).le

/-- Local arclength inside a closed oriented rational box. -/
lemma lintegral_speed_preimage_closedOrientedBox_le
    (K : Knot) {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedOrientedBox frame c r,
        ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  let A : Set ℝ := Ico (0 : ℝ) (2 * Real.pi) ∩
    K.curve ⁻¹' closedOrientedBox frame c r
  have hAmeas : MeasurableSet A := measurableSet_Ico.inter
    ((measurableSet_closedOrientedBox frame c r).preimage
      K.smooth.continuous.measurable)
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
          simpa [intrinsicDistance, parameterArcLength,
            totalArcLength_pos K |>.le] using hR
        · calc
            intrinsicDistance K s t ≤
                (distortion K).toReal * dist (K.curve s) (K.curve t) :=
              intrinsicDistance_le_toReal_distortion_mul_dist K hsI ht.1 hst hfinite
            _ ≤ (distortion K).toReal * (5 * r) :=
              mul_le_mul_of_nonneg_left
                (dist_lt_five_mul_scale_of_mem_closedOrientedBox hr hsB ht.2).le
                ENNReal.toReal_nonneg
            _ = 5 * r * (distortion K).toReal := by ring
      _ = ENNReal.ofReal (10 * r * (distortion K).toReal) := by
        congr 1
        ring
  · have hA : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    change (∫⁻ t in A, ENNReal.ofReal (speed K t)) ≤ _
    rw [hA]
    simp

/-- The compact part of one closed fundamental interval whose image lies in
the closed oriented box. -/
def closedOrientedBoxParameters
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Set ℝ :=
  Icc (0 : ℝ) (2 * Real.pi) ∩
    K.curve ⁻¹' closedOrientedBox frame c r

lemma isCompact_closedOrientedBoxParameters
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) :
    IsCompact (closedOrientedBoxParameters K frame c r) := by
  exact isCompact_Icc.inter_right
    ((isClosed_closedOrientedBox frame c r).preimage K.smooth.continuous)

/-- The right endpoint added for compactness is measure-null. -/
lemma lintegral_closedOrientedBoxParameters_speed_eq_halfOpen
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) :
    (∫⁻ t in closedOrientedBoxParameters K frame c r,
        ENNReal.ofReal (speed K t)) =
      ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
        K.curve ⁻¹' closedOrientedBox frame c r,
        ENNReal.ofReal (speed K t) := by
  have hsets :
      closedOrientedBoxParameters K frame c r =ᵐ[volume]
        ((Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedOrientedBox frame c r) : Set ℝ) := by
    filter_upwards [MeasureTheory.Ico_ae_eq_Icc (μ := volume)
      (a := (0 : ℝ)) (b := 2 * Real.pi)] with t ht
    exact congrArg
      (fun p : Prop ↦ p ∧ K.curve t ∈ closedOrientedBox frame c r) ht.symm
  rw [Measure.restrict_congr_set hsets]

/-- Oriented shell-coordinate variation on the compact parameter set is
bounded by the local arclength estimate. -/
lemma lintegral_abs_deriv_orientedShellParameter_closedParameters_le
    (K : Knot) {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in closedOrientedBoxParameters K frame c r,
        ENNReal.ofReal |deriv (orientedShellParameter K frame c) t|) ≤
      ENNReal.ofReal (10 * r * (distortion K).toReal) := by
  calc
    (∫⁻ t in closedOrientedBoxParameters K frame c r,
        ENNReal.ofReal |deriv (orientedShellParameter K frame c) t|) ≤
        ∫⁻ t in closedOrientedBoxParameters K frame c r,
          ENNReal.ofReal (speed K t) := by
      exact lintegral_mono fun t ↦ ENNReal.ofReal_le_ofReal
        (abs_deriv_orientedShellParameter_le_speed K frame c t)
    _ = ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedOrientedBox frame c r,
          ENNReal.ofReal (speed K t) :=
      lintegral_closedOrientedBoxParameters_speed_eq_halfOpen K frame c r
    _ ≤ ENNReal.ofReal (10 * r * (distortion K).toReal) :=
      lintegral_speed_preimage_closedOrientedBox_le K hr hfinite

/-- The level boundary of an oriented rational box. -/
def orientedBoxBoundary
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Set R3 :=
  {x | orientedBoxGauge frame c x = r}

/-- Number of oriented-box boundary intersections on a parameter set. -/
noncomputable def orientedBoundaryCount
    (K : Knot) (frame : Equiv.Perm (Fin 3))
    (c : R3) (s : Set ℝ) (r : ℝ) : ℕ :=
  Submission.Coarea.fiberCount (orientedShellParameter K frame c) s r

lemma orientedBoundaryCount_eq_ncard
    (K : Knot) (frame : Equiv.Perm (Fin 3))
    (c : R3) (s : Set ℝ) (r : ℝ) :
    orientedBoundaryCount K frame c s r =
      (s ∩ K.curve ⁻¹' orientedBoxBoundary frame c r).ncard := by
  rfl

/-- Branch-free outer-boundary selection, uniformly in the oriented frame. -/
theorem exists_orientedOuterBoundary_count_le_distortion
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hfinite : distortion K ≠ ⊤) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      y ∉ (orientedShellParameter K frame c) ''
        Submission.Coarea.lipschitzExceptionalSet
          (orientedShellParameter K frame c) ∧
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite ∧
      (orientedBoundaryCount K frame c
        (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
          ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
  have houter : 0 < (1 + ε) * r := mul_pos (by linarith) hr
  have hwidth : (1 + ε) * r - r = ε * r := by ring
  obtain ⟨y, hy, hyExceptional, hfiniteCompact, hybound⟩ :=
    exists_orientedShellRegularValue_fiberCount_le_integral_of_isCompact
      K frame c
        (isCompact_closedOrientedBoxParameters K frame c ((1 + ε) * r))
        (show r < (1 + ε) * r by nlinarith)
  have hsub :
      Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (Ico (0 : ℝ) (2 * Real.pi)) y ⊆
        Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y := by
    intro t ht
    rw [Submission.Coarea.fiberSet] at ht ⊢
    rcases ht with ⟨htIco, htlevel⟩
    refine ⟨⟨⟨htIco.1, htIco.2.le⟩, ?_⟩, htlevel⟩
    change orientedBoxGauge frame c (K.curve t) ≤ (1 + ε) * r
    change orientedBoxGauge frame c (K.curve t) = y at htlevel
    rw [htlevel]
    exact hy.2
  have hfiniteHalfOpen :
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite :=
    hfiniteCompact.subset hsub
  refine ⟨y, hy, hyExceptional, hfiniteHalfOpen, ?_⟩
  have hcount :
      (orientedBoundaryCount K frame c
          (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
        (Submission.Coarea.fiberCount (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y : ℝ≥0∞) := by
    change ((Submission.Coarea.fiberSet (orientedShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) y).ncard : ℝ≥0∞) ≤
        ((Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y).ncard : ℝ≥0∞)
    exact_mod_cast Set.ncard_le_ncard hsub hfiniteCompact
  refine hcount.trans (hybound.trans ?_)
  calc
    (∫⁻ t in closedOrientedBoxParameters K frame c ((1 + ε) * r),
        ENNReal.ofReal |deriv (orientedShellParameter K frame c) t|) /
          ENNReal.ofReal ((1 + ε) * r - r) ≤
        ENNReal.ofReal (10 * ((1 + ε) * r) * (distortion K).toReal) /
          ENNReal.ofReal ((1 + ε) * r - r) := by
      exact ENNReal.div_le_div
        (lintegral_abs_deriv_orientedShellParameter_closedParameters_le
          K houter hfinite) le_rfl
    _ = ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
      rw [hwidth]
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hε hr)]
      congr 1
      field_simp [ne_of_gt hε, ne_of_gt hr]
      ring

/-- The exact `80D` oriented-boundary selector at `ε = 1/7`.  This theorem
can be applied directly at every frame and center arising in the nested-box
construction. -/
theorem exists_orientedOuterBoundary_count_le_eighty_mul_distortion
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    ∃ y ∈ Ioc r ((8 / 7) * r),
      y ∉ (orientedShellParameter K frame c) ''
        Submission.Coarea.lipschitzExceptionalSet
          (orientedShellParameter K frame c) ∧
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite ∧
      (orientedBoundaryCount K frame c
        (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
          ENNReal.ofReal (80 * (distortion K).toReal) := by
  obtain ⟨y, hy, hyExceptional, hfiniteFiber, hybound⟩ :=
    exists_orientedOuterBoundary_count_le_distortion K frame c hr
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
