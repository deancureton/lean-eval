import ChallengeDeps

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The rational aspect ratio used for Pardon's nested boxes. -/
noncomputable def aspect : ℝ := 5 / 4

/-- Coordinate half-widths for a box of scale one. -/
noncomputable def axisWeight (i : Fin 3) : ℝ :=
  if i = 0 then 1 else if i = 1 then aspect else aspect ^ 2

/-- The open rational box with center `c` and scale `r`. -/
noncomputable def rationalBox (c : R3) (r : ℝ) : Set R3 :=
  {x | ∀ i, |(x - c).ofLp i| < axisWeight i * r}

lemma aspect_pos : 0 < aspect := by
  norm_num [aspect]

lemma aspect_one_lt : 1 < aspect := by
  norm_num [aspect]

lemma axisWeight_zero : axisWeight 0 = 1 := by
  simp [axisWeight]

lemma axisWeight_one : axisWeight 1 = aspect := by
  norm_num [axisWeight]

lemma axisWeight_two : axisWeight 2 = aspect ^ 2 := by
  norm_num [axisWeight, Fin.ext_iff]

lemma axisWeight_pos (i : Fin 3) : 0 < axisWeight i := by
  fin_cases i <;> norm_num [axisWeight, aspect, Fin.ext_iff]

lemma one_le_axisWeight (i : Fin 3) : 1 ≤ axisWeight i := by
  fin_cases i <;> norm_num [axisWeight, aspect]

lemma axisWeight_le_sq (i : Fin 3) : axisWeight i ≤ aspect ^ 2 := by
  fin_cases i <;> norm_num [axisWeight, aspect]

lemma mem_rationalBox_iff {c x : R3} {r : ℝ} :
    x ∈ rationalBox c r ↔ ∀ i, |(x - c).ofLp i| < axisWeight i * r :=
  Iff.rfl

lemma abs_coord_sub_center_lt {c x : R3} {r : ℝ}
    (hx : x ∈ rationalBox c r) (i : Fin 3) :
    |x.ofLp i - c.ofLp i| < axisWeight i * r := by
  simpa using hx i

/-- Two points in the same rational box differ in coordinate `i` by less than
twice that coordinate's half-width. -/
lemma abs_coord_sub_coord_lt_two_mul {c x y : R3} {r : ℝ}
    (hx : x ∈ rationalBox c r) (hy : y ∈ rationalBox c r) (i : Fin 3) :
    |x.ofLp i - y.ofLp i| < 2 * axisWeight i * r := by
  calc
    |x.ofLp i - y.ofLp i| =
        |(x.ofLp i - c.ofLp i) + (c.ofLp i - y.ofLp i)| := by ring_nf
    _ ≤ |x.ofLp i - c.ofLp i| + |c.ofLp i - y.ofLp i| := abs_add_le _ _
    _ < axisWeight i * r + axisWeight i * r :=
      add_lt_add (abs_coord_sub_center_lt hx i) (by
        simpa [abs_sub_comm] using abs_coord_sub_center_lt hy i)
    _ = 2 * axisWeight i * r := by ring

/-- The longest half-width can be halved and then used as the shortest
half-width after cyclically permuting the coordinates. -/
lemma aspect_cube_lt_two : aspect ^ 3 < 2 := by
  norm_num [aspect]

/-- The halved longest side of a box is shorter than the shortest side after
rescaling by `1 / aspect`. This is the only strict inequality needed when the
three axes are cyclically permuted after a bisection. -/
lemma half_longest_weight_lt_rescaled_shortest :
    aspect ^ 2 / 2 < 1 / aspect := by
  norm_num [aspect]

/-- Arithmetic form of the cyclic half-box containment. At positive scale
`r`, the half-widths `aspect²*r/2`, `r`, and `aspect*r` fit respectively in
the half-widths of a rational box at scale `r/aspect`. -/
lemma half_box_axis_bounds (r : ℝ) (hr : 0 < r) :
    aspect ^ 2 * r / 2 < r / aspect ∧
      r = aspect * (r / aspect) ∧
      aspect * r = aspect ^ 2 * (r / aspect) := by
  constructor
  · calc
      aspect ^ 2 * r / 2 = (aspect ^ 2 / 2) * r := by ring
      _ < (1 / aspect) * r :=
        mul_lt_mul_of_pos_right half_longest_weight_lt_rescaled_shortest hr
      _ = r / aspect := by ring
  constructor <;> field_simp [aspect, ne_of_gt hr]

/-- The squared diameter of a scale-`r` rational box is strictly less than
`(5 * r) ^ 2` after factoring out `r ^ 2`. -/
lemma four_mul_weight_sq_sum_lt_twenty_five :
    4 * (1 + aspect ^ 2 + aspect ^ 4) < 25 := by
  norm_num [aspect]

lemma sum_axisWeight_sq :
    ∑ i : Fin 3, axisWeight i ^ 2 = 1 + aspect ^ 2 + aspect ^ 4 := by
  rw [Fin.sum_univ_three, axisWeight_zero, axisWeight_one, axisWeight_two]
  ring

/-- Any two points in a positive-scale rational box are less than `5*r`
apart. Thus `5*r` is a convenient strict diameter bound. -/
lemma dist_lt_five_mul_scale {c x y : R3} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ rationalBox c r) (hy : y ∈ rationalBox c r) :
    dist x y < 5 * r := by
  have hcoord (i : Fin 3) :
      dist (x.ofLp i) (y.ofLp i) < 2 * axisWeight i * r := by
    simpa [Real.dist_eq] using abs_coord_sub_coord_lt_two_mul hx hy i
  have hcoord_nonneg (i : Fin 3) : 0 ≤ 2 * axisWeight i * r := by
    exact mul_nonneg (mul_nonneg (by norm_num) (axisWeight_pos i).le) hr.le
  have hsq (i : Fin 3) :
      dist (x.ofLp i) (y.ofLp i) ^ 2 < (2 * axisWeight i * r) ^ 2 := by
    exact (sq_lt_sq₀ dist_nonneg (hcoord_nonneg i)).2 (hcoord i)
  have hsum :
      ∑ i : Fin 3, dist (x.ofLp i) (y.ofLp i) ^ 2 <
        ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 :=
    Finset.sum_lt_sum (fun i _ ↦ le_of_lt (hsq i))
      ⟨0, Finset.mem_univ 0, hsq 0⟩
  rw [← PiLp.dist_sq_eq_of_L2] at hsum
  have hsum_rhs :
      ∑ i : Fin 3, (2 * axisWeight i * r) ^ 2 =
        4 * (∑ i : Fin 3, axisWeight i ^ 2) * r ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three, axisWeight_zero,
      axisWeight_one, axisWeight_two]
    ring
  rw [hsum_rhs, sum_axisWeight_sq] at hsum
  have hweight := four_mul_weight_sq_sum_lt_twenty_five
  have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
  have hfive_pos : 0 < 5 * r := mul_pos (by norm_num) hr
  have hsum_simplified : dist x y ^ 2 <
      4 * (1 + aspect ^ 2 + aspect ^ 4) * r ^ 2 := by
    nlinarith
  nlinarith [mul_lt_mul_of_pos_right hweight (sq_pos_of_pos hr)]

/-- The limiting scale factor after cutting a slightly enlarged rational box
in half, for Pardon's choice `ε = 1/7`. -/
noncomputable def shrinkFactor : ℝ :=
  (1 + (1 / 7 : ℝ)) / aspect + (1 / 7 : ℝ) / 2

lemma shrinkFactor_eq : shrinkFactor = 69 / 70 := by
  norm_num [shrinkFactor, aspect]

lemma shrinkFactor_pos : 0 < shrinkFactor := by
  rw [shrinkFactor_eq]
  norm_num

lemma shrinkFactor_lt_one : shrinkFactor < 1 := by
  rw [shrinkFactor_eq]
  norm_num

lemma one_sub_shrinkFactor_eq : 1 - shrinkFactor = 1 / 70 := by
  rw [shrinkFactor_eq]
  norm_num

lemma shrinkFactor_mul_lt (r : ℝ) (hr : 0 < r) :
    shrinkFactor * r < r := by
  nlinarith [mul_lt_mul_of_pos_right shrinkFactor_lt_one hr]

end PardonDistortion
end Submission
