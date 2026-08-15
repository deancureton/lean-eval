import Submission.PardonReduction

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- Cyclically relabel the new short, medium, and long axes by the old long,
short, and medium axes. -/
def axisCycle : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] lemma axisCycle_zero : axisCycle 0 = 2 := rfl
@[simp] lemma axisCycle_one : axisCycle 1 = 0 := rfl
@[simp] lemma axisCycle_two : axisCycle 2 = 1 := rfl

/-- A rational box with a freely permuted orthonormal coordinate frame. -/
def orientedBox (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Set R3 :=
  {x | ∀ i, |(x - c).ofLp (frame i)| < axisWeight i * r}

lemma mem_orientedBox_iff {frame : Equiv.Perm (Fin 3)} {c x : R3} {r : ℝ} :
    x ∈ orientedBox frame c r ↔
      ∀ i, |x.ofLp (frame i) - c.ofLp (frame i)| < axisWeight i * r := by
  simp only [orientedBox, mem_ofPred_eq]
  constructor
  · intro h i
    simpa using h i
  · intro h i
    simpa using h i

/-- Replace one Euclidean coordinate, leaving the other two fixed. -/
def replaceCoord (c : R3) (j : Fin 3) (z : ℝ) : R3 :=
  WithLp.toLp 2 (Function.update c.ofLp j z)

@[simp] lemma replaceCoord_same (c : R3) (j : Fin 3) (z : ℝ) :
    (replaceCoord c j z).ofLp j = z := by
  simp [replaceCoord]

lemma replaceCoord_of_ne (c : R3) {i j : Fin 3} (hij : i ≠ j) (z : ℝ) :
    (replaceCoord c j z).ofLp i = c.ofLp i := by
  simp [replaceCoord, hij]

/-- The scale of a successor box obtained from an outer scale `R` by cutting
within `shellEpsilon * r` of its center. -/
def successorScale (R r : ℝ) : ℝ :=
  R / aspect + shellEpsilon * r / 2

lemma successorScale_pos {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    0 < successorScale R r := by
  rw [successorScale]
  exact add_pos (div_pos hR aspect_pos)
    (div_pos (mul_pos shellEpsilon_pos hr) (by norm_num))

lemma successorScale_le_shrinkFactor_mul {R r : ℝ}
    (_hr : 0 ≤ r) (hR : R ≤ (1 + shellEpsilon) * r) :
    successorScale R r ≤ shrinkFactor * r := by
  rw [shrinkFactor_eq_shell_expression]
  dsimp [successorScale]
  have ha : 0 < aspect := aspect_pos
  calc
    R / aspect + shellEpsilon * r / 2 ≤
        ((1 + shellEpsilon) * r) / aspect + shellEpsilon * r / 2 := by
      gcongr
    _ = ((1 + shellEpsilon) / aspect + shellEpsilon / 2) * r := by ring

/-- Center of the part below the cutting plane perpendicular to the old long
axis. -/
def lowerHalfCenter (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : R3 :=
  replaceCoord c (frame 2) ((c.ofLp (frame 2) - aspect ^ 2 * R + d) / 2)

/-- Center of the part above the cutting plane perpendicular to the old long
axis. -/
def upperHalfCenter (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : R3 :=
  replaceCoord c (frame 2) ((d + c.ofLp (frame 2) + aspect ^ 2 * R) / 2)

lemma lowerHalf_subset_successor
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R r d : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    orientedBox frame c R ∩ {x | x.ofLp (frame 2) ≤ d} ⊆
      orientedBox (axisCycle.trans frame) (lowerHalfCenter frame c R d)
        (successorScale R r) := by
  intro x hx
  rcases hx with ⟨hx, hcut⟩
  change x.ofLp (frame 2) ≤ d at hcut
  rw [mem_orientedBox_iff] at hx ⊢
  intro i
  fin_cases i
  · change |x.ofLp (frame 2) - (lowerHalfCenter frame c R d).ofLp (frame 2)| <
      1 * successorScale R r
    have hout := hx 2
    rw [axisWeight_two] at hout
    have hlower : c.ofLp (frame 2) - aspect ^ 2 * R < x.ofLp (frame 2) := by
      rw [abs_lt] at hout
      linarith
    have hcoord :
        (lowerHalfCenter frame c R d).ofLp (frame 2) =
          (c.ofLp (frame 2) - aspect ^ 2 * R + d) / 2 := by
      simp [lowerHalfCenter]
    rw [hcoord, one_mul, abs_lt]
    have haspect : aspect ^ 2 * R / 2 < R / aspect := by
      calc
        aspect ^ 2 * R / 2 = (aspect ^ 2 / 2) * R := by ring
        _ < (1 / aspect) * R :=
          mul_lt_mul_of_pos_right half_longest_weight_lt_rescaled_shortest hR
        _ = R / aspect := by ring
    have hd' : d - c.ofLp (frame 2) ≤ shellEpsilon * r :=
      (le_abs_self _).trans hd
    constructor <;> dsimp [successorScale] <;> linarith
  · change |x.ofLp (frame 0) - (lowerHalfCenter frame c R d).ofLp (frame 0)| <
      aspect * successorScale R r
    have hout := hx 0
    rw [axisWeight_zero] at hout
    have hne : frame 0 ≠ frame 2 := by
      exact fun h ↦ by simpa using frame.injective h
    rw [lowerHalfCenter, replaceCoord_of_ne c hne]
    have hpos : 0 < shellEpsilon * r / 2 :=
      div_pos (mul_pos shellEpsilon_pos hr) (by norm_num)
    have ha : 0 < aspect := aspect_pos
    dsimp [successorScale]
    have heq : aspect * (R / aspect) = R := by field_simp
    nlinarith [aspect_pos]
  · change |x.ofLp (frame 1) - (lowerHalfCenter frame c R d).ofLp (frame 1)| <
      aspect ^ 2 * successorScale R r
    have hout := hx 1
    rw [axisWeight_one] at hout
    have hne : frame 1 ≠ frame 2 := by
      exact fun h ↦ by simpa using frame.injective h
    rw [lowerHalfCenter, replaceCoord_of_ne c hne]
    have hpos : 0 < shellEpsilon * r / 2 :=
      div_pos (mul_pos shellEpsilon_pos hr) (by norm_num)
    have ha : 0 < aspect := aspect_pos
    dsimp [successorScale]
    have heq : aspect ^ 2 * (R / aspect) = aspect * R := by
      field_simp
    nlinarith [sq_pos_of_pos aspect_pos]

lemma upperHalf_subset_successor
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R r d : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r) :
    orientedBox frame c R ∩ {x | d ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame) (upperHalfCenter frame c R d)
        (successorScale R r) := by
  intro x hx
  rcases hx with ⟨hx, hcut⟩
  change d ≤ x.ofLp (frame 2) at hcut
  rw [mem_orientedBox_iff] at hx ⊢
  intro i
  fin_cases i
  · change |x.ofLp (frame 2) - (upperHalfCenter frame c R d).ofLp (frame 2)| <
      1 * successorScale R r
    have hout := hx 2
    rw [axisWeight_two] at hout
    have hupper : x.ofLp (frame 2) < c.ofLp (frame 2) + aspect ^ 2 * R := by
      rw [abs_lt] at hout
      linarith
    have hcoord :
        (upperHalfCenter frame c R d).ofLp (frame 2) =
          (d + c.ofLp (frame 2) + aspect ^ 2 * R) / 2 := by
      simp [upperHalfCenter]
    rw [hcoord, one_mul, abs_lt]
    have haspect : aspect ^ 2 * R / 2 < R / aspect := by
      calc
        aspect ^ 2 * R / 2 = (aspect ^ 2 / 2) * R := by ring
        _ < (1 / aspect) * R :=
          mul_lt_mul_of_pos_right half_longest_weight_lt_rescaled_shortest hR
        _ = R / aspect := by ring
    have hd' : c.ofLp (frame 2) - d ≤ shellEpsilon * r := by
      calc
        c.ofLp (frame 2) - d = -(d - c.ofLp (frame 2)) := by ring
        _ ≤ |d - c.ofLp (frame 2)| := neg_le_abs _
        _ ≤ shellEpsilon * r := hd
    constructor <;> dsimp [successorScale] <;> linarith
  · change |x.ofLp (frame 0) - (upperHalfCenter frame c R d).ofLp (frame 0)| <
      aspect * successorScale R r
    have hout := hx 0
    rw [axisWeight_zero] at hout
    have hne : frame 0 ≠ frame 2 := by
      exact fun h ↦ by simpa using frame.injective h
    rw [upperHalfCenter, replaceCoord_of_ne c hne]
    have hpos : 0 < shellEpsilon * r / 2 :=
      div_pos (mul_pos shellEpsilon_pos hr) (by norm_num)
    have ha : 0 < aspect := aspect_pos
    dsimp [successorScale]
    have heq : aspect * (R / aspect) = R := by field_simp
    nlinarith [aspect_pos]
  · change |x.ofLp (frame 1) - (upperHalfCenter frame c R d).ofLp (frame 1)| <
      aspect ^ 2 * successorScale R r
    have hout := hx 1
    rw [axisWeight_one] at hout
    have hne : frame 1 ≠ frame 2 := by
      exact fun h ↦ by simpa using frame.injective h
    rw [upperHalfCenter, replaceCoord_of_ne c hne]
    have hpos : 0 < shellEpsilon * r / 2 :=
      div_pos (mul_pos shellEpsilon_pos hr) (by norm_num)
    have ha : 0 < aspect := aspect_pos
    dsimp [successorScale]
    have heq : aspect ^ 2 * (R / aspect) = aspect * R := by
      field_simp
    nlinarith [sq_pos_of_pos aspect_pos]

end

end PardonDistortion
end Submission
