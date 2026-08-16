import Submission.Topology.RegularBandTwoLevelDichotomy
import Submission.Topology.SuperellipsoidFiniteStageTransportCharging

/-!
# Direct resolved step from two separated regular endpoint spheres

This adapter bypasses an intermediate moving-sphere sequence.  An essential circle on either
endpoint sphere gives the already constructed charged compression.  If every endpoint circle is
inessential, the regular-band cyclic retraction and exact four-cell partition put the canonical
rank-two complement core in the lower or upper child.

The file is purely logical: the endpoint sphere system, its four-cell partition, its essential
sphere-side surgery data, and charging continuation remain explicit geometric inputs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus

/-- The two-level alternative before translating transported-torus carriers back to ambient
subsets. -/
theorem twoLevel_transportChargedCompression_or_carries_child
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (system : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (B : OrientedCoordinateRegularBandData Phi frame selection.cut.height)
    (L : RegularBandTwoLevelLocalizationData system B)
    (G : OrientedCoordinateRegularBandCyclicRetractionData B)
    (essentialSurgery : ∀ i, (system.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData system i))
    (chargingTransport : ∀ i, (system.circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi (system.circle i).windingLoop.curve)
        (system.circle i).windingLoop.lift.first.winding
        (system.circle i).windingLoop.lift.second.winding)
    (hparent : CarriesBasedLoopTorusGenus Phi L.cells.parentPart) :
    Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q selection) ∨
      CarriesBasedLoopTorusGenus Phi L.cells.lowerPart ∨
        CarriesBasedLoopTorusGenus Phi L.cells.upperPart := by
  classical
  by_cases hessential : ∃ i, (system.circle i).Essential
  · obtain ⟨i, hi⟩ := hessential
    obtain ⟨D⟩ := essentialSurgery i hi
    exact Or.inl <|
      SuperellipsoidDoubleBubbleSelection.chargedCompressionOfEssentialSphereCircleTransport
        selection D p q (chargingTransport i hi)
  · have hzero : system.AllInessential := by
      intro i
      have hi : ¬ (system.circle i).Essential := fun hi ↦ hessential ⟨i, hi⟩
      exact not_ne_iff.mp (show ¬ (system.circle i).windingLoop.windingPair ≠ (0, 0) from hi)
    exact Or.inr (L.carries_lower_or_upper_of_cyclicRetraction hzero G hparent)

/-- One exact two-level sphere system supplies the resolved superellipsoid double-bubble step. -/
theorem SuperellipsoidResolvedDoubleBubbleStep.ofTwoLevelRegularBand
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (system : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (B : OrientedCoordinateRegularBandData Phi frame selection.cut.height)
    (L : RegularBandTwoLevelLocalizationData system B)
    (G : OrientedCoordinateRegularBandCyclicRetractionData B)
    (originalBox_subset_parent : transportedTorusPart Phi (orientedBox frame c r) ⊆
      L.cells.parentPart)
    (lower_subset : L.cells.lowerPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upper_subset : L.cells.upperPart ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ i, (system.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData system i))
    (chargingTransport : ∀ i, (system.circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi (system.circle i).windingLoop.curve)
        (system.circle i).windingLoop.lift.first.winding
        (system.circle i).windingLoop.lift.second.winding) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection where
  cutAlternative := by
    have hparent : CarriesBasedLoopTorusGenus Phi L.cells.parentPart :=
      CarriesBasedLoopTorusGenus.mono originalBox_subset_parent
        (⟨WB.toBasedLoopCarrierWitness⟩ : CarriesTransportedBasedLoopGenus Phi
          (orientedBox frame c r))
    rcases twoLevel_transportChargedCompression_or_carries_child
        p q K Phi frame c selection system B L G essentialSurgery chargingTransport
        hparent with hcharged | hlower | hupper
    · exact Or.inr (Or.inr hcharged)
    · exact Or.inl (hlower.mono lower_subset)
    · exact Or.inr (Or.inl (hupper.mono upper_subset))

end Submission.PardonDistortion
