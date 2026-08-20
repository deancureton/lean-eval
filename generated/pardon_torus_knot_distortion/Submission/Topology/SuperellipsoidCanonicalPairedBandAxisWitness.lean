import Submission.Topology.SuperellipsoidCanonicalBarrierArcPresentation
import Submission.Topology.SuperellipsoidPairedBandBooleanAxisIntegration

/-!
# Canonical paired-band witness for the Pardon axis route

This file removes the arbitrary middle-stage family from the final witness.  Once the canonical
central barrier charts are exact, an honest Boolean paired-band stage family feeds the finite
quadratic axis argument directly.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Topology.FiniteSuperellipsoidBarrierGraph

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Boolean moving-sphere data over the canonical central chart realization. -/
def SuperellipsoidCanonicalPairedBandStageData
    (hr : 0 < r)
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection)
    (X : CanonicalCentralBarrierChartData.ArcExactness D) : Type 1 := by
  letI := D.centralSeamVertexFintype
  exact SuperellipsoidPairedBandBooleanAxisData
    (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
    (WB := WB) (selection := selection)
    (C := CanonicalCentralBarrierChartData.realization D X)
    hr D.heightData.band.ε_pos D.heightData.lowerPoint D.heightData.upperPoint

/-- The exact central chart equation together with its Boolean moving-sphere realization. -/
structure SuperellipsoidCanonicalPairedBandWitnessData
    (hr : 0 < r)
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection) :
    Type 1 where
  exactness : CanonicalCentralBarrierChartData.ArcExactness D
  stages : SuperellipsoidCanonicalPairedBandStageData
    (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
    (WB := WB) (selection := selection) hr D exactness

/-- The canonical endpoint and chart choices followed by the remaining honest Boolean
moving-sphere geometry. -/
def SuperellipsoidCanonicalPairedBandAxisWitness (hr : 0 < r) : Type 1 :=
  SuperellipsoidCanonicalPairedBandWitnessData
    (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
    (WB := WB) (selection := selection) hr
    (SuperellipsoidDoubleBubbleSelection.canonicalEndpointRegularityData selection hr)

namespace SuperellipsoidCanonicalPairedBandAxisWitness

/-- The canonical paired-band witness constructs the reduced side-cover axis package. -/
def toFiniteStageSideCoverAxisData
    (W : SuperellipsoidCanonicalPairedBandAxisWitness
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) hr) :
    SuperellipsoidFiniteStageSideCoverAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) := by
  dsimp only [SuperellipsoidCanonicalPairedBandAxisWitness] at W
  let D := SuperellipsoidDoubleBubbleSelection.canonicalEndpointRegularityData selection hr
  letI := D.centralSeamVertexFintype
  exact W.stages.toFiniteQuadraticStageAxisData.toFiniteStageSideCoverAxisData

end SuperellipsoidCanonicalPairedBandAxisWitness

/-- Uniform existence of the canonical paired-band witness for every selected double bubble. -/
def HasSuperellipsoidCanonicalPairedBandAxisWitness
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (_sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (_sigma.f t)) : Prop :=
  ∀ frame c r, ∀ hr : 0 < r, OrientedBasedLoopCarrier Phi frame c r →
    ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
    ∀ selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness,
      Nonempty (SuperellipsoidCanonicalPairedBandAxisWitness
        (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
        (WB := WB) (selection := selection) hr)

/-- Uniform canonical paired-band geometry implies Pardon's benchmark bound. -/
theorem pardonTarget_of_superellipsoidCanonicalPairedBandAxisWitness
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hresolved : HasSuperellipsoidCanonicalPairedBandAxisWitness
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_of_superellipsoidFiniteStageSideCoverAxisData
    p q hp hq hc K Phi sigma hclass
  intro frame c r hr hcarrier WB selection
  obtain ⟨W⟩ := hresolved frame c r hr hcarrier WB selection
  exact ⟨W.toFiniteStageSideCoverAxisData⟩

end Submission.PardonDistortion
