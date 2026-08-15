import Submission.SuperellipsoidPardonGeometricStep
import Submission.Topology.HalfSphereSurgeryDichotomy
import Submission.Topology.SuperellipsoidTwoSurgeryCells

/-!
# Superellipsoid adapter for the half-sphere surgery dichotomy

This file identifies the abstract parent and child cells of
`HalfSphereSurgeryDichotomy` with the smooth body and the two closed half-bodies selected by
superellipsoid coarea.  It produces exactly `SuperellipsoidResolvedDoubleBubbleStep`, the final
topological input consumed by the shrinking argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-- An abstract elementary sphere-surgery resolution, after identifying its three relevant
surface cells with the selected smooth parent and children, gives the exact high-level resolved
double-bubble step. -/
def SuperellipsoidResolvedDoubleBubbleStep.ofHalfSphereSurgery
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (stage : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (event : ElementaryHalfSphereSurgeryEvent stage)
    (parentPart_eq : event.parentPart = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale))
    (lowerPart_subset : event.lowerPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upperPart_subset : event.upperPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ i, (stage.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData stage i))
    (inessentialData : ∀ hzero : stage.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily stage hzero,
        Nonempty M.ConnectedPushoutData)
    (charge : EventCoveredCompressingDisk (Phi := Phi) stage.eventRegion →
      SuperellipsoidChargedCompression (Phi := Phi) p q selection)
    (parentCarrier : CarriesTransportedBasedLoopGenus Phi
      (superellipsoidBody frame c selection.outer.scale)) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection where
  cutAlternative := by
    have hparent : CarriesBasedLoopTorusGenus Phi event.parentPart := by
      rw [parentPart_eq]
      exact parentCarrier
    rcases chargedCompression_or_carries_child stage event essentialSurgery
        inessentialData charge hparent with hcharged | hlower | hupper
    · exact Or.inr (Or.inr hcharged)
    · exact Or.inl (hlower.mono lowerPart_subset)
    · exact Or.inr (Or.inl (hupper.mono upperPart_subset))

/-- The original smooth based carrier supplies the parent carrier because the selected outer
superellipsoid contains the original oriented box. -/
def SuperellipsoidResolvedDoubleBubbleStep.ofHalfSphereSurgeryFromOriginalBox
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (stage : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (event : ElementaryHalfSphereSurgeryEvent stage)
    (parentPart_eq : event.parentPart = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale))
    (lowerPart_subset : event.lowerPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upperPart_subset : event.upperPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ i, (stage.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData stage i))
    (inessentialData : ∀ hzero : stage.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily stage hzero,
        Nonempty M.ConnectedPushoutData)
    (charge : EventCoveredCompressingDisk (Phi := Phi) stage.eventRegion →
      SuperellipsoidChargedCompression (Phi := Phi) p q selection) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection := by
  apply SuperellipsoidResolvedDoubleBubbleStep.ofHalfSphereSurgery
    p q K Phi frame c r WB selection stage event parentPart_eq
      lowerPart_subset upperPart_subset essentialSurgery inessentialData charge
  exact (⟨WB.toBasedLoopCarrierWitness⟩ : CarriesTransportedBasedLoopGenus Phi
    (orientedBox frame c r)).mono (selection.originalBox_subset_outerBody hr)

/-- Specialized final adapter using the analytic strict-cell partition.  The only remaining
topological inputs are the finite barrier-circle identification, essential surgery data,
inessential maximal-disk pushouts, and the concrete compression charge. -/
def SuperellipsoidResolvedDoubleBubbleStep.ofAnalyticTwoSurgeryCells
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (stage : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hbarrier : ⋃ i, Set.range (fun t ↦ (stage.circle i).windingLoop.curve t) =
      superellipsoidOuterCutBarrierPart Phi frame c selection.outer.scale
        selection.cut.height)
    (essentialSurgery : ∀ i, (stage.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData stage i))
    (inessentialData : ∀ hzero : stage.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily stage hzero,
        Nonempty M.ConnectedPushoutData)
    (charge : EventCoveredCompressingDisk (Phi := Phi) stage.eventRegion →
      SuperellipsoidChargedCompression (Phi := Phi) p q selection) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection := by
  let event := elementaryHalfSphereSurgeryEvent_of_superellipsoidBarrier stage
    frame c selection.outer.scale selection.cut.height hbarrier
  apply SuperellipsoidResolvedDoubleBubbleStep.ofHalfSphereSurgeryFromOriginalBox
    p q K Phi frame c hr WB selection stage event rfl
      (superellipsoidStrictLowerPart_subset_closedLowerBody Phi frame c
        selection.outer.scale selection.cut.height)
      (superellipsoidStrictUpperPart_subset_closedUpperBody Phi frame c
        selection.outer.scale selection.cut.height)
      essentialSurgery inessentialData charge

end Submission.PardonDistortion
