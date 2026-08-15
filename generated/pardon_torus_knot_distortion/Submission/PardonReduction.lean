import Submission.BoxGeometry
import Submission.Distortion

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

/-- Pardon's shell-thickness parameter.  The rational choice `1/7` makes both
the count constant and the geometric shrink factor exact. -/
noncomputable def shellEpsilon : ℝ := 1 / 7

lemma shellEpsilon_pos : 0 < shellEpsilon := by
  norm_num [shellEpsilon]

lemma shellEpsilon_lt_one : shellEpsilon < 1 := by
  norm_num [shellEpsilon]

lemma ten_mul_one_add_inv_shellEpsilon :
    10 * (1 + shellEpsilon⁻¹) = 80 := by
  norm_num [shellEpsilon]

lemma five_mul_one_add_inv_shellEpsilon :
    5 * (1 + shellEpsilon⁻¹) = 40 := by
  norm_num [shellEpsilon]

/-- The boundary sphere and cutting disk estimates combine to the published
constant `160`. -/
lemma twenty_mul_one_add_inv_shellEpsilon :
    20 * (1 + shellEpsilon⁻¹) = 160 := by
  norm_num [shellEpsilon]

/-- The geometric constant used in `BoxGeometry` is exactly the scale obtained
from an `ε = 1/7` enlargement followed by cyclic bisection. -/
lemma shrinkFactor_eq_shell_expression :
    shrinkFactor = (1 + shellEpsilon) / aspect + shellEpsilon / 2 := by
  rfl

/-- Reduce the benchmark's extended-real conclusion to Pardon's ordinary-real
inequality in the finite-distortion case.  Infinite distortion is discharged
automatically. -/
lemma pardonTarget_le_of_real_bound
    (p q : ℕ) (K : Knot)
    (hbound : distortion K ≠ ⊤ →
      ((Nat.min p q : ℕ) : ℝ) ≤ 160 * (distortion K).toReal) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  by_cases hfinite : distortion K = ⊤
  · simp [hfinite]
  · calc
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) =
          ENNReal.ofReal (((Nat.min p q : ℕ) : ℝ) / (160 : ℝ)) :=
        ennreal_one_div_nat_mul_natCast_eq_ofReal_div 160 (Nat.min p q) (by norm_num)
      _ ≤
          ENNReal.ofReal (distortion K).toReal := by
        apply ENNReal.ofReal_le_ofReal
        have h := hbound hfinite
        nlinarith
      _ = distortion K := ENNReal.ofReal_toReal hfinite

/-- Contradiction form of the real reduction, convenient for the nested-box
argument. -/
lemma real_bound_of_not_lt
    (p q : ℕ) (K : Knot)
    (hcontra : ¬ 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    ((Nat.min p q : ℕ) : ℝ) ≤ 160 * (distortion K).toReal := by
  exact le_of_not_gt hcontra

end PardonDistortion
end Submission
