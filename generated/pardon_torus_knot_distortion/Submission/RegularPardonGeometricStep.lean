import Submission.PardonGeometricStep
import Submission.RegularDoubleBubbleSelection

/-!
# The regular geometric interface for Pardon's shrinking step

The coarea argument selects more than the numerical `DoubleBubbleSelection`:
the outer box is transverse to the transported torus on all six faces, and
the cutting plane is transverse to the knot and to two smooth independent
carrier loops.  This file makes those hypotheses available to the sole
remaining topological cut theorem, while reusing the already verified
compression charging and nested-box arithmetic.
-/

open Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

noncomputable section

/-- A resolution of the *regular* double bubble selected by coarea.  The
third branch is the particular charged compression produced by the geometric
cut construction. -/
structure RegularResolvedDoubleBubbleStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (S : RegularDoubleBubbleSelection K Phi frame c r) where
  cutAlternative : CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          lowerClosedHalfspace frame S.cut.height) ∨
      CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          upperClosedHalfspace frame S.cut.height) ∨
      Nonempty (ChargedCompression (Phi := Phi) p q S.toDoubleBubbleSelection)

/-- Exact remaining theorem after all analytic genericity and counting choices
have been made. -/
def HasRegularResolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c r, 0 < r → OrientedLoopCarrier Phi frame c r →
    ∀ S : RegularDoubleBubbleSelection K Phi frame c r,
      Nonempty (RegularResolvedDoubleBubbleStep p q K Phi frame c r S)

/-- Resolving every regular selected cut supplies the exact successor required
by the nested oriented-box contradiction. -/
theorem hasPardonShrinkingStep_of_regularResolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hresolved : HasRegularResolvedDoubleBubbleSteps p q K Phi) :
    HasPardonShrinkingStep p q K Phi := by
  intro hfinite hcontra frame c r hr hcarrier
  obtain ⟨S⟩ := exists_regularDoubleBubbleSelection
    K Phi frame c hr hcarrier hfinite
  obtain ⟨G⟩ := hresolved frame c r hr hcarrier S
  have hsides : CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          lowerClosedHalfspace frame S.cut.height) ∨
      CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          upperClosedHalfspace frame S.cut.height) := by
    rcases G.cutAlternative with hleft | hright | hcharged
    · exact Or.inl hleft
    · exact Or.inr hright
    · obtain ⟨charged⟩ := hcharged
      exact False.elim <|
        (S.toDoubleBubbleSelection.no_compressionCharging_of_distortion_lt
          charged.disk p q charged.certificate hcontra) charged.charging
  rcases hsides with hlower | hupper
  · refine ⟨axisCycle.trans frame,
      lowerHalfCenter frame c S.outer.level S.cut.height,
      successorScale S.outer.level r, S.selectedSuccessorScale_pos hr, ?_,
      S.selectedSuccessorScale_le hr⟩
    apply CarriesTransportedLoopGenus.mono ?_ hlower
    simpa only [lowerClosedHalfspace] using S.selectedLowerHalf_subset_successor hr
  · refine ⟨axisCycle.trans frame,
      upperHalfCenter frame c S.outer.level S.cut.height,
      successorScale S.outer.level r, S.selectedSuccessorScale_pos hr, ?_,
      S.selectedSuccessorScale_le hr⟩
    apply CarriesTransportedLoopGenus.mono ?_ hupper
    simpa only [upperClosedHalfspace] using S.selectedUpperHalf_subset_successor hr

/-- The extended-real benchmark target follows immediately from the regular
topological cut theorem. -/
theorem pardonTarget_of_regularResolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hresolved : HasRegularResolvedDoubleBubbleSteps p q K Phi) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K :=
  pardonTarget_of_hasPardonShrinkingStep p q K Phi
    (hasPardonShrinkingStep_of_regularResolvedDoubleBubbleSteps
      p q K Phi hresolved)

end

end Submission.PardonDistortion
