import Submission.Coarea.OrientedShell

/-!
# Smooth superellipsoid geometry for the double-bubble step

The outer polyhedral box is replaced by a very high even-power superellipsoid.  Its gauge is the
weighted `PiLp 256` norm of the three oriented box coordinates.  The same surface is cut out by
an honest polynomial, which is the form used for planar Sard and transverse-intersection
arguments.  The rational factors `193 / 192` and `8 / 7` leave enough room for all containment
and coarea estimates while keeping the final constant below `160`.
-/

open Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

/-- The exponent of the smooth norm approximation to the box gauge. -/
def superellipsoidExponent : ℕ := 256

/-- The slight enlargement which contains the original open rational box. -/
def superellipsoidInnerFactor : ℝ := 193 / 192

/-- The outer scale factor used in the coarea sweep. -/
def superellipsoidOuterFactor : ℝ := 8 / 7

lemma superellipsoidInnerFactor_pos : 0 < superellipsoidInnerFactor := by
  norm_num [superellipsoidInnerFactor]

lemma one_lt_superellipsoidInnerFactor : 1 < superellipsoidInnerFactor := by
  norm_num [superellipsoidInnerFactor]

lemma superellipsoidOuterFactor_pos : 0 < superellipsoidOuterFactor := by
  norm_num [superellipsoidOuterFactor]

lemma superellipsoidInnerFactor_lt_outerFactor :
    superellipsoidInnerFactor < superellipsoidOuterFactor := by
  norm_num [superellipsoidInnerFactor, superellipsoidOuterFactor]

/-- The normalized coordinates, regarded as the finite-dimensional `L^256` space. -/
def superellipsoidCoordinates
    (frame : Equiv.Perm (Fin 3)) (c x : R3) : PiLp 256 (fun _ : Fin 3 ↦ ℝ) :=
  WithLp.toLp 256 (normalizedOrientedBoxCoordinates frame c x)

/-- Weighted `L^256` gauge.  This is a norm after translating by `c`. -/
def superellipsoidGauge (frame : Equiv.Perm (Fin 3)) (c x : R3) : ℝ :=
  ‖superellipsoidCoordinates frame c x‖

/-- The polynomial whose positive level sets are the superellipsoid boundaries. -/
def superellipsoidPolynomial (frame : Equiv.Perm (Fin 3)) (c x : R3) : ℝ :=
  ∑ i : Fin 3, (normalizedOrientedBoxCoordinates frame c x i) ^ 256

/-- The open superellipsoid of scale `R`. -/
def superellipsoidBody (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set R3 :=
  {x | superellipsoidGauge frame c x < R}

/-- Its closed body. -/
def closedSuperellipsoidBody (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set R3 :=
  {x | superellipsoidGauge frame c x ≤ R}

/-- Its smooth outer boundary. -/
def superellipsoidBoundary (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set R3 :=
  {x | superellipsoidGauge frame c x = R}

lemma superellipsoidBody_mono
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R S : ℝ} (hRS : R ≤ S) :
    superellipsoidBody frame c R ⊆ superellipsoidBody frame c S := by
  intro x hx
  exact hx.trans_le hRS

lemma superellipsoidGauge_nonneg (frame : Equiv.Perm (Fin 3)) (c x : R3) :
    0 ≤ superellipsoidGauge frame c x :=
  by
    let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
    exact norm_nonneg (superellipsoidCoordinates frame c x)

lemma superellipsoidPolynomial_nonneg (frame : Equiv.Perm (Fin 3)) (c x : R3) :
    0 ≤ superellipsoidPolynomial frame c x := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- The norm formula which connects the metric gauge to the polynomial equation. -/
lemma superellipsoidGauge_eq_polynomial_rpow
    (frame : Equiv.Perm (Fin 3)) (c x : R3) :
    superellipsoidGauge frame c x =
      (superellipsoidPolynomial frame c x) ^ (1 / (256 : ℝ)) := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [superellipsoidGauge, PiLp.norm_eq_of_nat 256 rfl, superellipsoidPolynomial]
  apply congrArg (fun z : ℝ ↦ z ^ (1 / (256 : ℝ)))
  apply Finset.sum_congr rfl
  intro i _
  change ‖normalizedOrientedBoxCoordinates frame c x i‖ ^ 256 =
    normalizedOrientedBoxCoordinates frame c x i ^ 256
  rw [Real.norm_eq_abs, (by norm_num : Even 256).pow_abs]

/-- On a positive scale, the metric boundary and polynomial level are exactly the same set. -/
lemma mem_superellipsoidBoundary_iff_polynomial_eq_pow
    (frame : Equiv.Perm (Fin 3)) (c x : R3) {R : ℝ} (hR : 0 ≤ R) :
    x ∈ superellipsoidBoundary frame c R ↔
      superellipsoidPolynomial frame c x = R ^ 256 := by
  rw [superellipsoidBoundary, mem_ofPred_eq,
    superellipsoidGauge_eq_polynomial_rpow]
  constructor
  · intro h
    have hroot :
        ((superellipsoidPolynomial frame c x) ^ (1 / (256 : ℝ))) ^ 256 =
          superellipsoidPolynomial frame c x := by
      simpa [one_div] using Real.rpow_inv_natCast_pow
        (superellipsoidPolynomial_nonneg frame c x) (n := 256) (by norm_num)
    calc
      superellipsoidPolynomial frame c x =
          ((superellipsoidPolynomial frame c x) ^ (1 / (256 : ℝ))) ^ 256 := hroot.symm
      _ = R ^ 256 := congrArg (fun z : ℝ ↦ z ^ 256) h
  · intro h
    rw [h]
    simpa [one_div] using Real.pow_rpow_inv_natCast hR (n := 256) (by norm_num)

/-- The polynomial is smooth to every order. -/
lemma contDiff_superellipsoidPolynomial (frame : Equiv.Perm (Fin 3)) (c : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (superellipsoidPolynomial frame c) := by
  unfold superellipsoidPolynomial normalizedOrientedBoxCoordinates
  fun_prop

/-- Each normalized coordinate is bounded by the `L^256` gauge. -/
lemma abs_normalizedCoordinate_le_superellipsoidGauge
    (frame : Equiv.Perm (Fin 3)) (c x : R3) (i : Fin 3) :
    |normalizedOrientedBoxCoordinates frame c x i| ≤
      superellipsoidGauge frame c x := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (superellipsoidCoordinates frame c x) i

/-- A superellipsoid lies inside the rational box at the same scale. -/
lemma superellipsoidBody_subset_orientedBox
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    superellipsoidBody frame c R ⊆ orientedBox frame c R := by
  intro x hx
  rw [mem_orientedBox_iff_gauge_lt hR]
  rw [superellipsoidBody, mem_ofPred_eq] at hx
  rw [orientedBoxGauge, pi_norm_lt_iff hR]
  intro i
  exact (abs_normalizedCoordinate_le_superellipsoidGauge frame c x i).trans_lt hx

/-- Closed-body version of the preceding containment. -/
lemma closedSuperellipsoidBody_subset_closedOrientedBox
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} :
    closedSuperellipsoidBody frame c R ⊆
      {x | orientedBoxGauge frame c x ≤ R} := by
  intro x hx
  rw [closedSuperellipsoidBody, mem_ofPred_eq] at hx
  change ‖normalizedOrientedBoxCoordinates frame c x‖ ≤ R
  have hR : 0 ≤ R := (superellipsoidGauge_nonneg frame c x).trans hx
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  exact (abs_normalizedCoordinate_le_superellipsoidGauge frame c x i).trans hx

/-- Numerical margin behind the inclusion of the box in the smoothed body. -/
lemma three_lt_superellipsoidInnerFactor_pow :
    (3 : ℝ) < superellipsoidInnerFactor ^ 256 := by
  norm_num [superellipsoidInnerFactor]

/-- Equivalently, the `L^256` distortion of a three-coordinate sup norm is below `193/192`. -/
lemma three_rpow_inv_exponent_lt_innerFactor :
    (3 : ℝ) ^ (1 / (256 : ℝ)) < superellipsoidInnerFactor := by
  apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    superellipsoidInnerFactor_pos.le (by norm_num : (256 : ℕ) ≠ 0)).mp
  calc
    ((3 : ℝ) ^ (1 / (256 : ℝ))) ^ 256 = 3 := by
      simpa [one_div] using Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 3)
        (n := 256) (by norm_num)
    _ < superellipsoidInnerFactor ^ 256 := three_lt_superellipsoidInnerFactor_pow

/-- Generic finite-dimensional comparison between the `L^256` and sup gauges. -/
lemma superellipsoidGauge_le_three_rpow_mul_orientedBoxGauge
    (frame : Equiv.Perm (Fin 3)) (c x : R3) :
    superellipsoidGauge frame c x ≤
      (3 : ℝ) ^ (1 / (256 : ℝ)) * orientedBoxGauge frame c x := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  have h := (PiLp.lipschitzWith_toLp (p := (256 : ℝ≥0∞))
    (fun _ : Fin 3 ↦ ℝ)).dist_le_mul
      (normalizedOrientedBoxCoordinates frame c x) 0
  simpa [superellipsoidGauge, superellipsoidCoordinates, orientedBoxGauge,
    ENNReal.toReal_natCast, Fintype.card_fin, dist_zero_right] using h

/-- The original rational box is strictly contained in the body at scale `(193/192)r`. -/
lemma orientedBox_subset_superellipsoidBody_innerFactor
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r) :
    orientedBox frame c r ⊆
      superellipsoidBody frame c (superellipsoidInnerFactor * r) := by
  intro x hx
  rw [superellipsoidBody, mem_ofPred_eq]
  have hbox : orientedBoxGauge frame c x < r :=
    (mem_orientedBox_iff_gauge_lt hr).mp hx
  calc
    superellipsoidGauge frame c x ≤
        (3 : ℝ) ^ (1 / (256 : ℝ)) * orientedBoxGauge frame c x :=
      superellipsoidGauge_le_three_rpow_mul_orientedBoxGauge frame c x
    _ < (3 : ℝ) ^ (1 / (256 : ℝ)) * r := by
      exact mul_lt_mul_of_pos_left hbox (Real.rpow_pos_of_pos (by norm_num) _)
    _ < superellipsoidInnerFactor * r := by
      exact mul_lt_mul_of_pos_right three_rpow_inv_exponent_lt_innerFactor hr

/-- Sharpened rational-box diameter arithmetic. -/
lemma four_mul_weight_sq_sum_lt_nine_halves_sq :
    4 * (1 + aspect ^ 2 + aspect ^ 4) < (9 / 2 : ℝ) ^ 2 := by
  norm_num [aspect]

/-- Any two points in the closed oriented box of positive scale are strictly less than
`(9/2)R` apart.  Strictness comes from the rational coefficient inequality, not from the box. -/
lemma dist_lt_nine_halves_mul_scale_of_gauge_le
    (frame : Equiv.Perm (Fin 3)) (c : R3) {x y : R3} {R : ℝ} (hR : 0 < R)
    (hx : orientedBoxGauge frame c x ≤ R) (hy : orientedBoxGauge frame c y ≤ R) :
    dist x y < (9 / 2 : ℝ) * R := by
  have hcoord (i : Fin 3) :
      dist (x.ofLp (frame i)) (y.ofLp (frame i)) ≤ 2 * axisWeight i * R := by
    rw [Real.dist_eq]
    calc
      |x.ofLp (frame i) - y.ofLp (frame i)| =
          |(x.ofLp (frame i) - c.ofLp (frame i)) +
            (c.ofLp (frame i) - y.ofLp (frame i))| := by ring_nf
      _ ≤
          |x.ofLp (frame i) - c.ofLp (frame i)| +
            |c.ofLp (frame i) - y.ofLp (frame i)| := abs_add_le _ _
      _ ≤ axisWeight i * R + axisWeight i * R := by
        gcongr
        · have hi := (pi_norm_le_iff_of_nonneg hR.le).mp hx i
          rw [normalizedOrientedBoxCoordinates, Real.norm_eq_abs, abs_div,
            abs_of_pos (axisWeight_pos i), div_le_iff₀ (axisWeight_pos i)] at hi
          simpa [mul_comm] using hi
        · have hi := (pi_norm_le_iff_of_nonneg hR.le).mp hy i
          rw [normalizedOrientedBoxCoordinates, Real.norm_eq_abs, abs_div,
            abs_of_pos (axisWeight_pos i), div_le_iff₀ (axisWeight_pos i)] at hi
          simpa [abs_sub_comm, mul_comm] using hi
      _ = 2 * axisWeight i * R := by ring
  have hsq (i : Fin 3) :
      dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2 ≤
        (2 * axisWeight i * R) ^ 2 := by
    exact sq_le_sq₀ dist_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (axisWeight_pos i).le) hR.le) |>.2 (hcoord i)
  have hsum :
      ∑ i : Fin 3, dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2 ≤
        ∑ i : Fin 3, (2 * axisWeight i * R) ^ 2 := by
    exact Finset.sum_le_sum fun i _ ↦ hsq i
  have hperm :
      (∑ i : Fin 3, dist (x.ofLp (frame i)) (y.ofLp (frame i)) ^ 2) =
        ∑ i : Fin 3, dist (x.ofLp i) (y.ofLp i) ^ 2 :=
    Equiv.sum_comp frame
      (fun i : Fin 3 ↦ dist (x.ofLp i) (y.ofLp i) ^ 2)
  rw [hperm, ← PiLp.dist_sq_eq_of_L2] at hsum
  have hsum_rhs :
      ∑ i : Fin 3, (2 * axisWeight i * R) ^ 2 =
        4 * (1 + aspect ^ 2 + aspect ^ 4) * R ^ 2 := by
    rw [Fin.sum_univ_three, axisWeight_zero, axisWeight_one, axisWeight_two]
    ring
  rw [hsum_rhs] at hsum
  have hconstant := four_mul_weight_sq_sum_lt_nine_halves_sq
  have hbound : dist x y ^ 2 < ((9 / 2 : ℝ) * R) ^ 2 := by
    calc
      dist x y ^ 2 ≤ 4 * (1 + aspect ^ 2 + aspect ^ 4) * R ^ 2 := hsum
      _ < (9 / 2 : ℝ) ^ 2 * R ^ 2 :=
        mul_lt_mul_of_pos_right hconstant (sq_pos_of_pos hR)
      _ = ((9 / 2 : ℝ) * R) ^ 2 := by ring
  exact (sq_lt_sq₀ dist_nonneg
    (mul_pos (by norm_num : (0 : ℝ) < 9 / 2) hR).le).mp hbound

/-- The same sharp diameter estimate for the closed smooth body. -/
lemma dist_lt_nine_halves_mul_scale_of_mem_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) {x y : R3} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ closedSuperellipsoidBody frame c R)
    (hy : y ∈ closedSuperellipsoidBody frame c R) :
    dist x y < (9 / 2 : ℝ) * R := by
  exact dist_lt_nine_halves_mul_scale_of_gauge_le frame c hR
    (closedSuperellipsoidBody_subset_closedOrientedBox frame c hx)
    (closedSuperellipsoidBody_subset_closedOrientedBox frame c hy)

/-- A lower half of the smooth body fits in the same successor box as the corresponding
polyhedral half. -/
lemma lowerSuperellipsoidHalf_subset_successor
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R r d : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d} ⊆
      orientedBox (axisCycle.trans frame) (lowerHalfCenter frame c R d)
        (successorScale R r) := by
  intro x hx
  exact lowerHalf_subset_successor frame c hR hr hd
    ⟨superellipsoidBody_subset_orientedBox frame c hR hx.1, hx.2⟩

/-- Upper-half version. -/
lemma upperSuperellipsoidHalf_subset_successor
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R r d : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    superellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame) (upperHalfCenter frame c R d)
        (successorScale R r) := by
  intro x hx
  exact upperHalf_subset_successor frame c hR hr hd
    ⟨superellipsoidBody_subset_orientedBox frame c hR hx.1, hx.2⟩

/-- Exact outer-shell arithmetic: the sharp diameter constant and shell width cost less than
`75`, leaving five units of slack in the final `160D` budget. -/
lemma nine_mul_outerFactor_div_shellWidth_lt_seventyFive :
    9 * superellipsoidOuterFactor /
      (superellipsoidOuterFactor - superellipsoidInnerFactor) < 75 := by
  norm_num [superellipsoidOuterFactor, superellipsoidInnerFactor]

/-- Even the elementary `PiLp` Lipschitz comparison, which costs an extra factor `193/192`,
stays below `76`.  A sharp `L^256 ≤ L^2` comparison removes this factor and recovers `75`. -/
lemma innerFactor_mul_nine_mul_outerFactor_div_shellWidth_lt_seventySix :
    superellipsoidInnerFactor * 9 * superellipsoidOuterFactor /
      (superellipsoidOuterFactor - superellipsoidInnerFactor) < 76 := by
  norm_num [superellipsoidOuterFactor, superellipsoidInnerFactor]

end Submission.PardonDistortion
