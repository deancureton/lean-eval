import Submission.LoopNested
import Submission.PardonReduction

/-!
# Final reduction to the one-step double-bubble theorem

All extended-real arithmetic and the infinite nested-box contradiction are
closed here.  The remaining geometric theorem has one precise output: under
the strict contrary inequality, every loop-carrying oriented box has a
loop-carrying successor whose scale is at most `69/70` of the old scale.
-/

open Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The exact one-step geometric assertion needed by the capstone. -/
def HasPardonShrinkingStep (p q : ℕ) (K : Knot)
    (Phi : AmbientIsotopy) : Prop :=
  distortion K ≠ ⊤ →
  160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ) →
  ∀ frame c r, 0 < r → OrientedLoopCarrier Phi frame c r →
    ∃ frame' c' r', 0 < r' ∧
      OrientedLoopCarrier Phi frame' c' r' ∧
      r' ≤ shrinkFactor * r

/-- Once the one-step geometric assertion is available, the nested boxes
give the real inequality `min p q ≤ 160D`. -/
theorem real_bound_of_hasPardonShrinkingStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hstep : HasPardonShrinkingStep p q K Phi)
    (hfinite : distortion K ≠ ⊤) :
    ((Nat.min p q : ℕ) : ℝ) ≤ 160 * (distortion K).toReal := by
  apply invariant_le_one_sixty_of_orientedLoopCarrier Phi
  intro hcontra frame c r hr hcarrier
  exact hstep hfinite hcontra frame c r hr hcarrier

/-- Final ENNReal benchmark conclusion from the one-step theorem. -/
theorem pardonTarget_of_hasPardonShrinkingStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hstep : HasPardonShrinkingStep p q K Phi) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_le_of_real_bound p q K
  intro hfinite
  exact real_bound_of_hasPardonShrinkingStep p q K Phi hstep hfinite

end

end Submission.PardonDistortion
