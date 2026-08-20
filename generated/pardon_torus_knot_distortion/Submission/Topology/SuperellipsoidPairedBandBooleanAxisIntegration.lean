import Submission.Topology.PairedBandBooleanRegularStageFamily
import Submission.Topology.FourPortSixEdgeEndpointSystemAttachment
import Submission.Topology.SuperellipsoidBooleanStageAxisIntegration

/-!
# Paired-band Boolean integration for the superellipsoid axis route

This module connects the geometric paired-band stage family to the Boolean axis adapter.  It
removes the abstract choice-indexed stage constructor: the retained data are the actual collars,
circle decompositions, endpoint parity identifications, charging transports, and one quadratic
package for every consecutive flip.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Topology.FiniteSuperellipsoidBarrierGraph.TruncatedSphereAlternatingCycles

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r ε : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}
  {outerIndex cutIndex vertex edge : Type}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c selection.outer.scale
    selection.cut.height outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}
  (hr : 0 < r)
  (hε : 0 < ε)
  (hlower : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    x.ofLp (frame 2) < selection.cut.height - ε)
  (hupper : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    selection.cut.height + ε < x.ofLp (frame 2))

/-- The remaining inputs after every Boolean stage has been realized by honest paired-band
moving-sphere geometry. -/
structure SuperellipsoidPairedBandBooleanAxisData where
  stages : BooleanChoicePairedBandRegularStageData (C := C)
  initialInside_eq :
    (stages.stageEntry (fun _ ↦ false)).parityStage.inside =
      transportedTorusPart Phi (interior
        (closedSuperellipsoidBody frame c selection.outer.scale))
  terminal : TerminalTwoComponentSphereStage
    ((stages.stageEntry (fun _ ↦ true)).parityStage)
  terminal_lower_eq : terminal.lower = transportedTorusPart Phi
    (canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
      hlower hupper).lowerInside
  terminal_upper_eq : terminal.upper = transportedTorusPart Phi
    (canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
      hlower hupper).upperInside
  chargingTransport :
    let stageSequence := stages.toBooleanChoiceRegularStageData
      |>.toFiniteRegularSphereSurgeryStageFamily
      |>.toFiniteRegularSphereSurgeryStageSequence
    ∀ k, k ≤ stageSequence.length → ∀ i,
      ((stageSequence.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi
            ((stageSequence.system k).circle i).windingLoop.curve)
          ((stageSequence.system k).circle i).windingLoop.lift.first.winding
          ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  indexedQuadraticStageSideCovers :
    let stageSequence := stages.toBooleanChoiceRegularStageData
      |>.toFiniteRegularSphereSurgeryStageFamily
      |>.toFiniteRegularSphereSurgeryStageSequence
    ∀ hzero : stageSequence.AllInessential,
      Nonempty
        (BooleanChoicePairedBandRegularStageData.FiniteBooleanFlipIndexedQuadraticStageSideCoverData
          stages hzero)

namespace SuperellipsoidPairedBandBooleanAxisData

/-- Forget only the paired-band presentation, retaining its constructed regular stages. -/
def toSuperellipsoidBooleanStageAxisData
    (D : SuperellipsoidPairedBandBooleanAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) (C := C) hr hε hlower hupper) :
    SuperellipsoidBooleanStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) hr hε hlower hupper where
  bandCount := P.bandCount
  stages := D.stages.toBooleanChoiceRegularStageData
  initialInside_eq := D.initialInside_eq
  terminal := D.terminal
  terminal_lower_eq := D.terminal_lower_eq
  terminal_upper_eq := D.terminal_upper_eq
  chargingTransport := D.chargingTransport
  quadraticStageSideCovers hzero :=
    (D.indexedQuadraticStageSideCovers hzero).map fun M ↦
      M.toFiniteQuadraticFourPortStageSideCoverData

/-- Paired-band Boolean geometry constructs the reduced quadratic axis package. -/
def toFiniteQuadraticStageAxisData
    (D : SuperellipsoidPairedBandBooleanAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) (C := C) hr hε hlower hupper) :
    SuperellipsoidFiniteQuadraticStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) :=
  D.toSuperellipsoidBooleanStageAxisData.toFiniteQuadraticStageAxisData

end SuperellipsoidPairedBandBooleanAxisData
end Submission.PardonDistortion
