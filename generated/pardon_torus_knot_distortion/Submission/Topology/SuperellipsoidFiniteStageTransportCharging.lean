import Submission.Topology.SuperellipsoidFiniteStageAdapter
import Submission.Topology.SuperellipsoidSmoothedChargingTransport

/-!
# Finite-stage charging transported from original barrier loops

This module replaces ambient containment of every smoothed stage circle in the original
outer/cutting-disk event region.  At an essential stage circle, an original charged barrier loop
is joined to the smoothed circle by a regular transverse continuation.  Endpoint matching
transports both the transverse certificate and its injective charge.

The all-inessential branch is unchanged: finite pushout parity propagation still places the
terminal rank-two carrier in one of the two child cells.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Torus

namespace SuperellipsoidDoubleBubbleSelection

/-- Exact equality of the surgery boundary loop transports the complete smoothed-loop charging
package to the constructed compressing disk. -/
theorem chargedCompressionOfEssentialSphereCircleTransport
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
    {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {stage : FiniteSphereSurgeryIntersectionSystem Phi iota} {i : iota}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : EssentialSphereCircleSurgeryData stage i)
    (p q : ℕ)
    (T : SmoothedLoopChargingTransport selection p q
      (transportedLoopCoordinates Phi (stage.circle i).windingLoop.curve)
      (stage.circle i).windingLoop.lift.first.winding
      (stage.circle i).windingLoop.lift.second.winding) :
    Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q selection) := by
  obtain ⟨disk, hboundary⟩ :=
    D.surgery.exists_generalCompressingDiskWitness_with_boundary i D.innermost
  have hloop : disk.boundaryLoop = (stage.circle i).windingLoop :=
    hboundary.trans D.boundary_eq
  let T' : SmoothedLoopChargingTransport selection p q
      (transportedLoopCoordinates Phi disk.boundaryLoop.curve)
      disk.boundaryLoop.lift.first.winding disk.boundaryLoop.lift.second.winding := by
    rw [hloop]
    exact T
  exact ⟨T'.toChargedCompression disk⟩

end SuperellipsoidDoubleBubbleSelection

/-- The finite-stage Pardon alternative whose essential branch is charged by continuation from
an original barrier loop.  No smoothed event-region containment or target raw-regular premise is
used. -/
theorem finiteRegularSphereSurgery_transportChargedCompression_or_carries_terminalChild
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (chargingTransport : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi ((F.system k).circle i).windingLoop.curve)
          ((F.system k).circle i).windingLoop.lift.first.winding
          ((F.system k).circle i).windingLoop.lift.second.winding)
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (hparent : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside) :
    Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q selection) ∨
      CarriesBasedLoopTorusGenus Phi lower ∨
        CarriesBasedLoopTorusGenus Phi upper := by
  classical
  by_cases hessential : ∃ k, k ≤ F.length ∧
      ∃ i, ((F.system k).circle i).Essential
  · obtain ⟨k, hk, i, hi⟩ := hessential
    obtain ⟨D⟩ := essentialSurgery k hk i hi
    exact Or.inl <|
      SuperellipsoidDoubleBubbleSelection.chargedCompressionOfEssentialSphereCircleTransport
        selection D p q (chargingTransport k hk i hi)
  · have hzero : F.AllInessential := by
      intro k hk i
      have hi : ¬ ((F.system k).circle i).Essential := fun hi ↦
        hessential ⟨k, hk, i, hi⟩
      exact not_ne_iff.mp (show
        ¬ ((F.system k).circle i).windingLoop.windingPair ≠ (0, 0) from hi)
    obtain ⟨D⟩ := inessentialResolution hzero
    have hInitial : CarriesBasedLoopTorusGenus Phi
        (D.paritySequence.stage 0).inside := by
      rw [D.stage_eq 0 (Nat.zero_le F.length)]
      exact hparent
    have hterminal := D.paritySequence.carries_terminal hInitial
    have hchildren := D.terminal.toTerminalTwoSphereCoreCells
      |>.carries_lower_or_upper_of_carries_inside hterminal
    rw [D.terminal_lower_eq, D.terminal_upper_eq] at hchildren
    exact Or.inr hchildren

/-- A finite regular sphere-surgery sequence with per-essential-circle charging transport gives
the resolved superellipsoid step. -/
theorem SuperellipsoidResolvedDoubleBubbleStep.ofFiniteRegularSphereSurgeryTransportCharging
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (initialInside_eq : (F.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale))
    (lower_subset : lower ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upper_subset : upper ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (chargingTransport : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi ((F.system k).circle i).windingLoop.curve)
          ((F.system k).circle i).windingLoop.lift.first.winding
          ((F.system k).circle i).windingLoop.lift.second.winding)
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper)) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection where
  cutAlternative := by
    have hInitial : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside := by
      rw [initialInside_eq]
      exact CarriesTransportedBasedLoopGenus.mono
        (selection.originalBox_subset_outerBody hr)
        (⟨WB.toBasedLoopCarrierWitness⟩ : CarriesTransportedBasedLoopGenus Phi
          (orientedBox frame c r))
    rcases finiteRegularSphereSurgery_transportChargedCompression_or_carries_terminalChild
        p q K Phi frame c selection F lower upper essentialSurgery chargingTransport
        inessentialResolution hInitial with hcharged | hlower | hupper
    · exact Or.inr (Or.inr hcharged)
    · exact Or.inl (hlower.mono lower_subset)
    · exact Or.inr (Or.inl (hupper.mono upper_subset))

/-- The complete finite-stage geometry package with original-barrier charging retained for every
essential smoothed stage circle. -/
structure SuperellipsoidFiniteStageTransportResolutionData
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness) where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialInside_eq :
    (stageSequence.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale)
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  essentialSurgery : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData (stageSequence.system k) i)
  chargingTransport : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi
          ((stageSequence.system k).circle i).windingLoop.curve)
        ((stageSequence.system k).circle i).windingLoop.lift.first.winding
        ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  inessentialResolution : stageSequence.AllInessential →
    Nonempty (AllInessentialFiniteBandResolution stageSequence lower upper)

namespace SuperellipsoidFiniteStageTransportResolutionData

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Transport-charged finite-stage data constructs the resolved double-bubble step. -/
theorem toResolvedDoubleBubbleStep
    (D : SuperellipsoidFiniteStageTransportResolutionData
      p q K Phi frame c r WB selection)
    (hr : 0 < r) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection :=
  SuperellipsoidResolvedDoubleBubbleStep.ofFiniteRegularSphereSurgeryTransportCharging
    p q K Phi frame c hr WB selection D.stageSequence D.lower D.upper
      D.initialInside_eq D.lower_subset D.upper_subset D.essentialSurgery
      D.chargingTransport D.inessentialResolution

end SuperellipsoidFiniteStageTransportResolutionData

/-- Pointwise transport-charged finite-stage geometry supplies the global resolved-step
hypothesis consumed by the quantitative shrinking argument. -/
theorem hasSuperellipsoidResolvedDoubleBubbleSteps_of_finiteStageTransportResolution
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (resolution : ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
      ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
      ∀ selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
        WB.toSmoothLoopCarrierWitness,
        Nonempty (SuperellipsoidFiniteStageTransportResolutionData
          p q K Phi frame c r WB selection)) :
    HasSuperellipsoidResolvedDoubleBubbleSteps p q hp hq hc K Phi sigma hclass := by
  intro frame c r hr hcarrier WB selection
  obtain ⟨D⟩ := resolution frame c r hr hcarrier WB selection
  exact ⟨D.toResolvedDoubleBubbleStep hr⟩

end Submission.PardonDistortion
