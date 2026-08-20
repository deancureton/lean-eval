import Submission.Topology.SphereCircleFiniteStageEssentialFilling
import Submission.Topology.SuperellipsoidFiniteQuadraticStageSideCovers
import Submission.Topology.SuperellipsoidFiniteStageAxisIntegration

/-!
# Quadratic finite-stage integration for the axis-circle route

The componentwise planar filling theorem makes the essential branch automatic for every finite
sphere stage.  In the all-inessential branch, a quadratic four-port package at each transition
constructs the required forward- or reverse-sided canonical disk cover.  This module combines
those two reductions into the finite-stage axis interface.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {p q : ℕ} {K : Knot}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Finite-stage geometric data whose essential branch is discharged componentwise and whose
all-inessential branch is described by explicit quadratic four-port moves. -/
structure SuperellipsoidFiniteQuadraticStageAxisData where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialBody_subset : transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale) ⊆
      (stageSequence.parityStage 0).inside
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  chargingTransport : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi
          ((stageSequence.system k).circle i).windingLoop.curve)
        ((stageSequence.system k).circle i).windingLoop.lift.first.winding
        ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  terminal : TerminalTwoComponentSphereStage
    (stageSequence.parityStage stageSequence.length)
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper
  quadraticStageSideCovers : ∀ hzero : stageSequence.AllInessential,
    Nonempty (FiniteQuadraticFourPortStageSideCoverData stageSequence hzero)

namespace SuperellipsoidFiniteQuadraticStageAxisData

/-- Componentwise planar fillings and the local quadratic moves construct the reduced finite-stage
axis package. -/
def toFiniteStageSideCoverAxisData
    (D : SuperellipsoidFiniteQuadraticStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection)) :
    SuperellipsoidFiniteStageSideCoverAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) where
  stageSequence := D.stageSequence
  lower := D.lower
  upper := D.upper
  initialBody_subset := D.initialBody_subset
  lower_subset := D.lower_subset
  upper_subset := D.upper_subset
  coordinateFillings k _ :=
    (D.stageSequence.system k).hasEssentialDoubledCoordinateFilling_of_sphereComponents
  chargingTransport := D.chargingTransport
  terminal := D.terminal
  terminal_lower_eq := D.terminal_lower_eq
  terminal_upper_eq := D.terminal_upper_eq
  stageSideCovers hzero := by
    obtain ⟨covers⟩ := D.quadraticStageSideCovers hzero
    exact ⟨covers.toFiniteStageSideDiskCoverData⟩

/-- The quadratic finite-stage geometry constructs the exact axis-resolution record consumed by
the quantitative estimate. -/
def toFiniteStageAxisResolutionData
    (D : SuperellipsoidFiniteQuadraticStageAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection)) :
    SuperellipsoidFiniteStageAxisResolutionData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) :=
  D.toFiniteStageSideCoverAxisData.toFiniteStageAxisResolutionData

end SuperellipsoidFiniteQuadraticStageAxisData
end Submission.PardonDistortion
