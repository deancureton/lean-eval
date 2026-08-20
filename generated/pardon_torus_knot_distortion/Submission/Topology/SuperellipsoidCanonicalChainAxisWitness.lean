import Submission.Topology.SuperellipsoidCanonicalChainAxisIntegration
import Submission.Topology.SuperellipsoidCanonicalEndpointGraphs

/-!
# Uniform witness for the canonical finite-stage axis construction

This structure packages every remaining geometric choice for one selected superellipsoid: the
regular initial and terminal sections, finite seam orders, truncation witnesses, intermediate
stages, charging continuations, and adjacent quadratic moves.  Uniform existence of this package
is exactly sufficient for Pardon's quantitative bound.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open Submission.Topology.FiniteSuperellipsoidBarrierGraph

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- The selected regular outer level and transverse cut canonically determine the initial smooth
circle family. -/
def canonicalInitialSmoothCircleFamily
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection) :
    FiniteSuperellipsoidOuterTorusSmoothCircleFamily
      Phi frame c selection.outer.scale selection.cut.height :=
  FiniteSuperellipsoidOuterTorusSmoothCircleFamily.ofRegularValue
    D.scale_pos.le selection.outer.surfaceRegular selection.cut.seamRegular

noncomputable instance canonicalInitialSmoothCircleFamilyIndexFintype
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection) :
    Fintype (canonicalInitialSmoothCircleFamily D).index := by
  letI := (canonicalInitialSmoothCircleFamily D).finite_index
  exact Fintype.ofFinite _

/-- The remaining stagewise geometry after all endpoint data have been constructed canonically. -/
def SuperellipsoidCanonicalEndpointAxisData
    (hr : 0 < r)
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection) : Type :=
  SuperellipsoidCanonicalChainAxisData
    (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
    (WB := WB) (selection := selection) hr (canonicalInitialSmoothCircleFamily D)
    D.lowerOuterOrder D.lowerCutOrder D.upperOuterOrder D.upperCutOrder
    D.heightData.band.ε_pos D.heightData.lowerPoint D.heightData.upperPoint

/-- The endpoint regularity package chosen canonically for this selected double bubble. -/
def canonicalEndpointRegularityData (hr : 0 < r) :
    SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData selection :=
  Submission.Topology.SuperellipsoidDoubleBubbleSelection.canonicalEndpointRegularityData
    selection hr

/-- All remaining geometric data for one canonical finite-stage construction.  Every endpoint
choice has already been made; this type is exactly the unresolved stagewise axis data. -/
def SuperellipsoidCanonicalChainAxisWitness (hr : 0 < r) : Type :=
  SuperellipsoidCanonicalEndpointAxisData
    (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
    (WB := WB) (selection := selection) hr (canonicalEndpointRegularityData hr)

namespace SuperellipsoidCanonicalChainAxisWitness

/-- A canonical witness constructs the reduced side-cover axis package. -/
def toFiniteStageSideCoverAxisData
    (W : SuperellipsoidCanonicalChainAxisWitness
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) hr) :
    SuperellipsoidFiniteStageSideCoverAxisData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection) := by
  unfold SuperellipsoidCanonicalChainAxisWitness at W
  unfold SuperellipsoidCanonicalEndpointAxisData at W
  exact W.toFiniteQuadraticStageAxisData.toFiniteStageSideCoverAxisData

end SuperellipsoidCanonicalChainAxisWitness

/-- Uniform existence of the canonical chain witness for every selected double bubble. -/
def HasSuperellipsoidCanonicalChainAxisWitness
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (_sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (_sigma.f t)) : Prop :=
  ∀ frame c r, ∀ hr : 0 < r, OrientedBasedLoopCarrier Phi frame c r →
    ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
    ∀ selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness,
      Nonempty (SuperellipsoidCanonicalChainAxisWitness
        (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
        (WB := WB) (selection := selection) hr)

/-- Uniform canonical-chain geometry implies Pardon's benchmark bound. -/
theorem pardonTarget_of_superellipsoidCanonicalChainAxisWitness
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hresolved : HasSuperellipsoidCanonicalChainAxisWitness
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_of_superellipsoidFiniteStageSideCoverAxisData
    p q hp hq hc K Phi sigma hclass
  intro frame c r hr hcarrier WB selection
  obtain ⟨W⟩ := hresolved frame c r hr hcarrier WB selection
  exact ⟨W.toFiniteStageSideCoverAxisData⟩

end Submission.PardonDistortion
