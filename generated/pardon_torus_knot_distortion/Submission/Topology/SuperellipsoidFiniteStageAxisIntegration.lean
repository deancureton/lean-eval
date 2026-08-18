import Submission.Topology.SphereCircleAxisFilling
import Submission.Topology.SuperellipsoidCanonicalFiniteStageIntegration

/-!
# Finite-stage side-cover integration for the axis-circle route

This module combines the reduced essential branch with the heterogeneous all-inessential
transition sequence.  Honest coordinate fillings produce the required axis circle, while one
stage-sided disk cover at every move produces the parity resolution.  The initial stage is the
outer superellipsoid, matching the canonical initial sphere construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {p q : ℕ} {K : Knot}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Geometric finite-stage inputs with both logical branches reduced to their local data.

The essential branch retains only a coordinate filling for a suitable essential circle.  The
all-inessential branch retains only a pre- or post-sided canonical disk cover at each move. -/
structure SuperellipsoidFiniteStageSideCoverAxisData where
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
  coordinateFillings : ∀ k, k ≤ stageSequence.length →
    (stageSequence.system k).HasEssentialDoubledCoordinateFilling
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
  stageSideCovers : ∀ hzero : stageSequence.AllInessential,
    Nonempty (FiniteStageSideDiskCoverData stageSequence hzero)

namespace SuperellipsoidFiniteStageSideCoverAxisData

/-- The local coordinate-filling and stage-side-cover inputs construct the exact reduced
resolution record consumed by the quantitative axis argument. -/
def toFiniteStageAxisResolutionData
    (D : SuperellipsoidFiniteStageSideCoverAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection)) :
    SuperellipsoidFiniteStageAxisResolutionData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) where
  stageSequence := D.stageSequence
  lower := D.lower
  upper := D.upper
  initialBody_subset := D.initialBody_subset
  lower_subset := D.lower_subset
  upper_subset := D.upper_subset
  axisCircle := D.stageSequence.hasAxisCircleIfEssential_of_doubledCoordinateFillings
    D.coordinateFillings
  chargingTransport := D.chargingTransport
  inessentialResolution := by
    intro hzero
    obtain ⟨covers⟩ := D.stageSideCovers hzero
    exact ⟨D.stageSequence.allInessentialResolutionOfStageSideDiskCovers hzero covers
      D.terminal D.lower D.upper D.terminal_lower_eq D.terminal_upper_eq⟩

end SuperellipsoidFiniteStageSideCoverAxisData

/-- Uniform existence of the local finite-stage axis data. -/
def HasSuperellipsoidFiniteStageSideCoverAxisData
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) : Prop :=
  ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
    ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
    ∀ S : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness,
      Nonempty (SuperellipsoidFiniteStageSideCoverAxisData
        (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
        (WB := WB) (selection := S))

/-- The fully local finite-stage axis package implies Pardon's benchmark bound. -/
theorem pardonTarget_of_superellipsoidFiniteStageSideCoverAxisData
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hresolved : HasSuperellipsoidFiniteStageSideCoverAxisData
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_of_superellipsoidFiniteStageAxisResolutions
    p q hp hq hc K Phi sigma hclass
  intro frame c r hr hcarrier WB selection
  obtain ⟨D⟩ := hresolved frame c r hr hcarrier WB selection
  exact ⟨D.toFiniteStageAxisResolutionData⟩

end Submission.PardonDistortion
