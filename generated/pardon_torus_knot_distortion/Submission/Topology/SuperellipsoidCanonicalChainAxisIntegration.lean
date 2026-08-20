import Submission.Topology.SuperellipsoidCanonicalStageChain
import Submission.Topology.SuperellipsoidFiniteQuadraticAxisIntegration

/-!
# Canonical stage-chain integration for the axis route

The canonical chain fixes the initial outer sphere and the separated terminal children.  This
module derives every endpoint and component-containment field of the finite-stage axis package.
The retained inputs are exactly stagewise charging transport and a quadratic four-port package at
each adjacent transition.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Topology.FiniteSuperellipsoidBarrierGraph
open Submission.Topology.FiniteSuperellipsoidBarrierGraph.TruncatedSphereAlternatingCycles

universe u

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r ε : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}
  (hr : 0 < r)
  (initialFamily : FiniteSuperellipsoidOuterTorusSmoothCircleFamily
    Phi frame c selection.outer.scale selection.cut.height)
  [Fintype initialFamily.index]
  {lowerOuterIndex lowerCutIndex upperOuterIndex upperCutIndex : Type u}
  [Fintype lowerOuterIndex] [Fintype lowerCutIndex]
  [Fintype upperOuterIndex] [Fintype upperCutIndex]
  {lowerGraph : FiniteSuperellipsoidBarrierGraph Phi frame c selection.outer.scale
    (selection.cut.height - ε) lowerOuterIndex lowerCutIndex}
  {upperGraph : FiniteSuperellipsoidBarrierGraph Phi frame c selection.outer.scale
    (selection.cut.height + ε) upperOuterIndex upperCutIndex}
  (lowerOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily lowerGraph)
  (lowerCutOrder : CutCircleTransverseCyclicOrderFamily lowerGraph)
  (upperOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily upperGraph)
  (upperCutOrder : CutCircleTransverseCyclicOrderFamily upperGraph)
  [Fintype (SuperellipsoidSeamVertex Phi frame c selection.outer.scale
    (selection.cut.height - ε))]
  [Fintype (SuperellipsoidSeamVertex Phi frame c selection.outer.scale
    (selection.cut.height + ε))]
  (hε : 0 < ε)
  (hlower : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    x.ofLp (frame 2) < selection.cut.height - ε)
  (hupper : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    selection.cut.height + ε < x.ofLp (frame 2))

/-- The remaining inputs after the canonical endpoint geometry and essential fillings have been
derived. -/
structure SuperellipsoidCanonicalChainAxisData where
  middleCount : ℕ
  middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi
  chargingTransport :
    let chain := canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder (selection.outer.scale_pos hr) hε hlower hupper
      middleCount middle
    let stageSequence := chain.toFiniteRegularSphereSurgeryStageSequence
    ∀ k, k ≤ stageSequence.length → ∀ i,
      ((stageSequence.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi
            ((stageSequence.system k).circle i).windingLoop.curve)
          ((stageSequence.system k).circle i).windingLoop.lift.first.winding
          ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  quadraticStageSideCovers :
    let chain := canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder (selection.outer.scale_pos hr) hε hlower hupper
      middleCount middle
    let stageSequence := chain.toFiniteRegularSphereSurgeryStageSequence
    ∀ hzero : stageSequence.AllInessential,
      Nonempty (FiniteQuadraticFourPortStageSideCoverData stageSequence hzero)

namespace SuperellipsoidCanonicalChainAxisData

/-- The canonical chain and its local transition packages construct the reduced finite-stage axis
data. -/
def toFiniteQuadraticStageAxisData
    (D : SuperellipsoidCanonicalChainAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) hr initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hε hlower hupper) :
    SuperellipsoidFiniteQuadraticStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) := by
  let chain := canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder (selection.outer.scale_pos hr) hε hlower hupper
    D.middleCount D.middle
  let stageSequence := chain.toFiniteRegularSphereSurgeryStageSequence
  let rounding := canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
    hlower hupper
  have hstage : stageSequence.parityStage stageSequence.length =
      canonicalSeparatedTerminalParityStage (Phi := Phi)
        (selection.outer.scale_pos hr) hε hlower hupper := by
    change stageSequence.parityStage (D.middleCount + 1) = _
    exact canonicalSuperellipsoidStageChain_terminalParityStage initialFamily
      lowerOuterOrder lowerCutOrder upperOuterOrder upperCutOrder
      (selection.outer.scale_pos hr) hε hlower hupper D.middleCount D.middle
  let canonicalTerminal := canonicalSeparatedTerminalTwoComponentStage (Phi := Phi)
    (selection.outer.scale_pos hr) hε hlower hupper
  let terminal : TerminalTwoComponentSphereStage
      (stageSequence.parityStage stageSequence.length) := {
    lower := canonicalTerminal.lower
    upper := canonicalTerminal.upper
    isOpen_lower := canonicalTerminal.isOpen_lower
    isOpen_upper := canonicalTerminal.isOpen_upper
    lower_disjoint_upper := canonicalTerminal.lower_disjoint_upper
    inside_eq := by
      rw [hstage]
      exact canonicalTerminal.inside_eq
    sphere_count := by
      rw [hstage]
      exact canonicalTerminal.sphere_count }
  have hterminalLower : terminal.lower = transportedTorusPart Phi rounding.lowerInside := by
    rfl
  have hterminalUpper : terminal.upper = transportedTorusPart Phi rounding.upperInside := by
    rfl
  exact {
    stageSequence := stageSequence
    lower := transportedTorusPart Phi rounding.lowerInside
    upper := transportedTorusPart Phi rounding.upperInside
    initialBody_subset := by
      rw [show stageSequence.parityStage 0 =
        initialOuterSuperellipsoidParityStage Phi frame c (selection.outer.scale_pos hr) by
          exact canonicalSuperellipsoidStageChain_initialParityStage initialFamily
            lowerOuterOrder lowerCutOrder upperOuterOrder upperCutOrder
            (selection.outer.scale_pos hr) hε hlower hupper D.middleCount D.middle]
      intro x hx
      exact superellipsoidBody_subset_interior_closedSuperellipsoidBody
        frame c selection.outer.scale hx
    lower_subset := by
      intro x hx
      exact rounding.lowerInside_subset_halfBody hx
    upper_subset := by
      intro x hx
      exact rounding.upperInside_subset_halfBody hx
    chargingTransport := D.chargingTransport
    terminal := terminal
    terminal_lower_eq := hterminalLower
    terminal_upper_eq := hterminalUpper
    quadraticStageSideCovers := D.quadraticStageSideCovers }

end SuperellipsoidCanonicalChainAxisData
end Submission.PardonDistortion
