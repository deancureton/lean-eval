import Submission.Topology.FiniteBooleanFlipStageFamily
import Submission.Topology.SuperellipsoidCanonicalStageEntries
import Submission.Topology.SuperellipsoidFiniteQuadraticAxisIntegration

/-!
# Boolean-stage integration for the superellipsoid axis route

A finite family obtained by flipping one local band at a time already has the correct number of
audited transitions.  This module uses that family directly, avoiding duplicate fixed endpoint
stages.  The retained endpoint inputs identify only the parity sides of the all-false and all-true
resolutions with the canonical outer and separated-terminal sides.
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
  (hr : 0 < r)
  (hε : 0 < ε)
  (hlower : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    x.ofLp (frame 2) < selection.cut.height - ε)
  (hupper : ∃ x, x ∈ superellipsoidBody frame c selection.outer.scale ∧
    selection.cut.height + ε < x.ofLp (frame 2))

/-- The remaining inputs for an axis construction whose regular stages are indexed by Boolean
band choices. -/
structure SuperellipsoidBooleanStageAxisData where
  bandCount : ℕ
  stages : BooleanChoiceRegularStageData Phi bandCount
  initialInside_eq :
    (stages.stage (fun _ ↦ false)).parityStage.inside =
      transportedTorusPart Phi (interior
        (closedSuperellipsoidBody frame c selection.outer.scale))
  terminal : TerminalTwoComponentSphereStage
    ((stages.stage (fun _ ↦ true)).parityStage)
  terminal_lower_eq : terminal.lower = transportedTorusPart Phi
    (canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
      hlower hupper).lowerInside
  terminal_upper_eq : terminal.upper = transportedTorusPart Phi
    (canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
      hlower hupper).upperInside
  chargingTransport :
    let stageSequence := stages.toFiniteRegularSphereSurgeryStageFamily
      |>.toFiniteRegularSphereSurgeryStageSequence
    ∀ k, k ≤ stageSequence.length → ∀ i,
      ((stageSequence.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi
            ((stageSequence.system k).circle i).windingLoop.curve)
          ((stageSequence.system k).circle i).windingLoop.lift.first.winding
          ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  quadraticStageSideCovers :
    let stageSequence := stages.toFiniteRegularSphereSurgeryStageFamily
      |>.toFiniteRegularSphereSurgeryStageSequence
    ∀ hzero : stageSequence.AllInessential,
      Nonempty (FiniteQuadraticFourPortStageSideCoverData stageSequence hzero)

namespace SuperellipsoidBooleanStageAxisData

/-- The Boolean stage family and its local transition packages construct the reduced finite-stage
axis data without inserting duplicate endpoint stages. -/
def toFiniteQuadraticStageAxisData
    (D : SuperellipsoidBooleanStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) hr hε hlower hupper) :
    SuperellipsoidFiniteQuadraticStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) := by
  let stageFamily := D.stages.toFiniteRegularSphereSurgeryStageFamily
  let stageSequence := stageFamily.toFiniteRegularSphereSurgeryStageSequence
  let rounding := canonicalSeparatedTerminalRoundingData (selection.outer.scale_pos hr) hε
    hlower hupper
  have hinitial : stageSequence.parityStage 0 =
      (D.stages.stage (fun _ ↦ false)).parityStage := by
    calc
      stageSequence.parityStage 0 = stageFamily.parityStage 0 :=
        stageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage (Nat.zero_le _)
      _ = (D.stages.stage (fun _ ↦ false)).parityStage :=
        D.stages.toFiniteRegularSphereSurgeryStageFamily_initialParityStage
  have hterminal : stageSequence.parityStage stageSequence.length =
      (D.stages.stage (fun _ ↦ true)).parityStage := by
    calc
      stageSequence.parityStage stageSequence.length =
          stageFamily.parityStage (Fin.last D.bandCount) := by
        exact stageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage (le_refl _)
      _ = (D.stages.stage (fun _ ↦ true)).parityStage :=
        D.stages.toFiniteRegularSphereSurgeryStageFamily_terminalParityStage
  let terminal : TerminalTwoComponentSphereStage
      (stageSequence.parityStage stageSequence.length) := {
    lower := D.terminal.lower
    upper := D.terminal.upper
    isOpen_lower := D.terminal.isOpen_lower
    isOpen_upper := D.terminal.isOpen_upper
    lower_disjoint_upper := D.terminal.lower_disjoint_upper
    inside_eq := by
      rw [hterminal]
      exact D.terminal.inside_eq
    sphere_count := by
      rw [hterminal]
      exact D.terminal.sphere_count }
  exact {
    stageSequence := stageSequence
    lower := transportedTorusPart Phi rounding.lowerInside
    upper := transportedTorusPart Phi rounding.upperInside
    initialBody_subset := by
      rw [hinitial, D.initialInside_eq]
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
    terminal_lower_eq := D.terminal_lower_eq
    terminal_upper_eq := D.terminal_upper_eq
    quadraticStageSideCovers := D.quadraticStageSideCovers }

end SuperellipsoidBooleanStageAxisData
end Submission.PardonDistortion
