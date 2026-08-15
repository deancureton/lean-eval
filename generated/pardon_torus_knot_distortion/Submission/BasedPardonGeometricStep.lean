import Submission.BasedRegularDoubleBubbleSelection
import Submission.PardonGeometricStep

/-!
# Connected regular cuts imply Pardon's bound

This is the final numerical and compactness hand-off for the connectivity-safe
carrier predicate.  Both smooth carrier loops pass through one exact common
basepoint.  Consequently the remaining geometric theorem may use that point
when converting a mixed lower/upper winding decomposition into the particular
compressing disk charged to the selected boundary events.
-/

open Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

noncomputable section

/-- A resolution of one regular based cut.  The third alternative is the
specific compression supplied by the cut, already equipped with its signed
intersection certificate and injective event charging. -/
structure BasedRegularResolvedDoubleBubbleStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) where
  cutAlternative : CarriesTransportedBasedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          lowerClosedHalfspace frame S.cut.height) ∨
      CarriesTransportedBasedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          upperClosedHalfspace frame S.cut.height) ∨
      Nonempty (ChargedCompression (Phi := Phi) p q S.toDoubleBubbleSelection)

/-- The sole remaining geometric theorem in its connectivity-safe form. -/
def HasBasedRegularResolvedDoubleBubbleSteps
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) : Prop :=
  ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
    ∀ S : BasedRegularDoubleBubbleSelection K Phi frame c r,
      Nonempty (BasedRegularResolvedDoubleBubbleStep p q K Phi frame c r S)

/-- A contrary strict distortion inequality would shrink every based carrier
box by the uniform factor `69/70`, contradicting local flatness and compactness
of the transported torus. -/
theorem real_bound_of_basedRegularResolvedDoubleBubbleSteps
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (hresolved : HasBasedRegularResolvedDoubleBubbleSteps
      p q hp hq hc K Phi sigma hclass)
    (hfinite : distortion K ≠ ⊤) :
    ((Nat.min p q : ℕ) : ℝ) ≤ 160 * (distortion K).toReal := by
  by_contra hnot
  have hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ) :=
    lt_of_not_ge hnot
  apply not_exists_shrinking_orientedBasedLoopCarrier Phi
  intro frame c r hr hcarrier
  obtain ⟨S⟩ := exists_basedRegularDoubleBubbleSelection
    K Phi frame c hr hcarrier hfinite
  obtain ⟨G⟩ := hresolved frame c r hr hcarrier S
  have hsides : CarriesTransportedBasedLoopGenus Phi
        (orientedBox frame c S.outer.level ∩
          lowerClosedHalfspace frame S.cut.height) ∨
      CarriesTransportedBasedLoopGenus Phi
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
    apply CarriesTransportedBasedLoopGenus.mono ?_ hlower
    simpa only [lowerClosedHalfspace] using S.selectedLowerHalf_subset_successor hr
  · refine ⟨axisCycle.trans frame,
      upperHalfCenter frame c S.outer.level S.cut.height,
      successorScale S.outer.level r, S.selectedSuccessorScale_pos hr, ?_,
      S.selectedSuccessorScale_le hr⟩
    apply CarriesTransportedBasedLoopGenus.mono ?_ hupper
    simpa only [upperClosedHalfspace] using S.selectedUpperHalf_subset_successor hr

/-- Final extended-real benchmark target from the based regular geometric cut
theorem. -/
theorem pardonTarget_of_basedRegularResolvedDoubleBubbleSteps
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (hresolved : HasBasedRegularResolvedDoubleBubbleSteps
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_le_of_real_bound p q K
  intro hfinite
  exact real_bound_of_basedRegularResolvedDoubleBubbleSteps
    p q hp hq hc K Phi sigma hclass hresolved hfinite

end

end Submission.PardonDistortion
