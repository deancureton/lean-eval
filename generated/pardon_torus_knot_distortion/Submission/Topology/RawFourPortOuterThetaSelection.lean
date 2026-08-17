import Submission.Topology.CoherentThetaOuterCycle
import Submission.Topology.RawFourPortThetaDiskSide

/-!
# Selecting the outer raw four-port theta cycle

A planar theta presentation identifies the three canonical two-edge Jordan circles with the
three raw zero-winding circles, but does not choose an outer circle.  The generic planar theta
theorem makes that choice.  This module transports its three cases into the reordered raw
four-port package used by the disk-side argument.

The label-change lens remains separate: its containment in the two bounded faces is geometric
information and is not implied by the carrier presentation.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

/-- Identification of the three raw zero-winding circles with the three cycles of one planar
theta graph.  The indices exhaust the raw `Fin 3` family; no one of them is declared outer. -/
structure RawFourPortPlanarThetaPresentation (R : FourPortRawCircleData raw) where
  theta : PlanarJordanThetaData
  index01 : Fin 3
  index02 : Fin 3
  index12 : Fin 3
  indices_exhaust : ∀ i, i = index01 ∨ i = index02 ∨ i = index12
  circle01_eq :
    (R.circle index01).zeroWindingJordanCircle (R.zeroWinding index01) = theta.circle01
  circle02_eq :
    (R.circle index02).zeroWindingJordanCircle (R.zeroWinding index02) = theta.circle02
  circle12_eq :
    (R.circle index12).zeroWindingJordanCircle (R.zeroWinding index12) = theta.circle12

namespace RawFourPortPlanarThetaPresentation

variable (P : RawFourPortPlanarThetaPresentation R)

private theorem circle02_subset_circle01_closed
    (h : closure P.theta.circle01.inside =
      closure P.theta.circle02.inside ∪ closure P.theta.circle12.inside) :
    P.theta.circle02.carrier ⊆
      P.theta.circle01.inside ∪ P.theta.circle01.carrier := by
  rw [← P.theta.circle01.closure_inside, h]
  intro x hx
  left
  rw [P.theta.circle02.closure_inside]
  exact Or.inr hx

private theorem circle12_subset_circle01_closed
    (h : closure P.theta.circle01.inside =
      closure P.theta.circle02.inside ∪ closure P.theta.circle12.inside) :
    P.theta.circle12.carrier ⊆
      P.theta.circle01.inside ∪ P.theta.circle01.carrier := by
  rw [← P.theta.circle01.closure_inside, h]
  intro x hx
  right
  rw [P.theta.circle12.closure_inside]
  exact Or.inr hx

private theorem circle01_subset_circle02_closed
    (h : closure P.theta.circle02.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle12.inside) :
    P.theta.circle01.carrier ⊆
      P.theta.circle02.inside ∪ P.theta.circle02.carrier := by
  rw [← P.theta.circle02.closure_inside, h]
  intro x hx
  left
  rw [P.theta.circle01.closure_inside]
  exact Or.inr hx

private theorem circle12_subset_circle02_closed
    (h : closure P.theta.circle02.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle12.inside) :
    P.theta.circle12.carrier ⊆
      P.theta.circle02.inside ∪ P.theta.circle02.carrier := by
  rw [← P.theta.circle02.closure_inside, h]
  intro x hx
  right
  rw [P.theta.circle12.closure_inside]
  exact Or.inr hx

private theorem circle01_subset_circle12_closed
    (h : closure P.theta.circle12.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle02.inside) :
    P.theta.circle01.carrier ⊆
      P.theta.circle12.inside ∪ P.theta.circle12.carrier := by
  rw [← P.theta.circle12.closure_inside, h]
  intro x hx
  left
  rw [P.theta.circle01.closure_inside]
  exact Or.inr hx

private theorem circle02_subset_circle12_closed
    (h : closure P.theta.circle12.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle02.inside) :
    P.theta.circle02.carrier ⊆
      P.theta.circle12.inside ∪ P.theta.circle12.carrier := by
  rw [← P.theta.circle12.closure_inside, h]
  intro x hx
  right
  rw [P.theta.circle02.closure_inside]
  exact Or.inr hx

private def outer01
    (h : closure P.theta.circle01.inside =
      closure P.theta.circle02.inside ∪ closure P.theta.circle12.inside) :
    RawFourPortOuterPlaneThetaData R where
  outerIndex := P.index01
  childOneIndex := P.index02
  childTwoIndex := P.index12
  indices_exhaust := P.indices_exhaust
  commonArc := P.theta.edge2
  outerArcOne := P.theta.edge0
  outerArcTwo := P.theta.edge1
  exceptional := P.theta.exceptional
  outer_carrier := by rw [P.circle01_eq, P.theta.carrier01]
  childOne_carrier := by
    rw [P.circle02_eq, P.theta.carrier02, Set.union_comm]
  childTwo_carrier := by
    rw [P.circle12_eq, P.theta.carrier12, Set.union_comm]
  childOne_subset_outerClosed := by
    rw [P.circle02_eq, P.circle01_eq]
    exact P.circle02_subset_circle01_closed h
  childTwo_subset_outerClosed := by
    rw [P.circle12_eq, P.circle01_eq]
    exact P.circle12_subset_circle01_closed h
  outerArcOne_has_private_point := by
    rw [P.circle12_eq, P.theta.carrier12]
    exact P.theta.private0_nonempty
  outerArcTwo_has_private_point := by
    rw [P.circle02_eq, P.theta.carrier02]
    exact P.theta.private1_nonempty
  exceptional_finite := P.theta.exceptional_finite
  common_local_line := by
    intro p hp
    obtain ⟨d, r, hr, h02, h12⟩ := P.theta.local2 p hp
    refine ⟨d, r, hr, ?_, ?_⟩
    · simpa only [P.circle02_eq] using h02
    · simpa only [P.circle12_eq] using h12

private def outer02
    (h : closure P.theta.circle02.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle12.inside) :
    RawFourPortOuterPlaneThetaData R where
  outerIndex := P.index02
  childOneIndex := P.index01
  childTwoIndex := P.index12
  indices_exhaust := fun i ↦ by
    rcases P.indices_exhaust i with hi | hi | hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inl hi
    · exact Or.inr (Or.inr hi)
  commonArc := P.theta.edge1
  outerArcOne := P.theta.edge0
  outerArcTwo := P.theta.edge2
  exceptional := P.theta.exceptional
  outer_carrier := by rw [P.circle02_eq, P.theta.carrier02]
  childOne_carrier := by
    rw [P.circle01_eq, P.theta.carrier01, Set.union_comm]
  childTwo_carrier := by rw [P.circle12_eq, P.theta.carrier12]
  childOne_subset_outerClosed := by
    rw [P.circle01_eq, P.circle02_eq]
    exact P.circle01_subset_circle02_closed h
  childTwo_subset_outerClosed := by
    rw [P.circle12_eq, P.circle02_eq]
    exact P.circle12_subset_circle02_closed h
  outerArcOne_has_private_point := by
    rw [P.circle12_eq, P.theta.carrier12]
    exact P.theta.private0_nonempty
  outerArcTwo_has_private_point := by
    rw [P.circle01_eq, P.theta.carrier01]
    exact P.theta.private2_nonempty
  exceptional_finite := P.theta.exceptional_finite
  common_local_line := by
    intro p hp
    obtain ⟨d, r, hr, h01, h12⟩ := P.theta.local1 p hp
    refine ⟨d, r, hr, ?_, ?_⟩
    · simpa only [P.circle01_eq] using h01
    · simpa only [P.circle12_eq] using h12

private def outer12
    (h : closure P.theta.circle12.inside =
      closure P.theta.circle01.inside ∪ closure P.theta.circle02.inside) :
    RawFourPortOuterPlaneThetaData R where
  outerIndex := P.index12
  childOneIndex := P.index01
  childTwoIndex := P.index02
  indices_exhaust := fun i ↦ by
    rcases P.indices_exhaust i with hi | hi | hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
    · exact Or.inl hi
  commonArc := P.theta.edge0
  outerArcOne := P.theta.edge1
  outerArcTwo := P.theta.edge2
  exceptional := P.theta.exceptional
  outer_carrier := by rw [P.circle12_eq, P.theta.carrier12]
  childOne_carrier := by rw [P.circle01_eq, P.theta.carrier01]
  childTwo_carrier := by rw [P.circle02_eq, P.theta.carrier02]
  childOne_subset_outerClosed := by
    rw [P.circle01_eq, P.circle12_eq]
    exact P.circle01_subset_circle12_closed h
  childTwo_subset_outerClosed := by
    rw [P.circle02_eq, P.circle12_eq]
    exact P.circle02_subset_circle12_closed h
  outerArcOne_has_private_point := by
    rw [P.circle02_eq, P.theta.carrier02]
    exact P.theta.private1_nonempty
  outerArcTwo_has_private_point := by
    rw [P.circle01_eq, P.theta.carrier01]
    exact P.theta.private2_nonempty
  exceptional_finite := P.theta.exceptional_finite
  common_local_line := by
    intro p hp
    obtain ⟨d, r, hr, h01, h02⟩ := P.theta.local0 p hp
    refine ⟨d, r, hr, ?_, ?_⟩
    · simpa only [P.circle01_eq] using h01
    · simpa only [P.circle02_eq] using h02

/-- The generic planar theorem selects and orders the outer raw theta cycle. -/
theorem nonempty_outerPlaneThetaData
    (P : RawFourPortPlanarThetaPresentation R) :
    Nonempty (RawFourPortOuterPlaneThetaData R) := by
  rcases PlanarJordanThetaData.exists_outer_cycle_decomposition P.theta with
    h01 | h02 | h12
  · exact ⟨P.outer01 h01⟩
  · exact ⟨P.outer02 h02⟩
  · exact ⟨P.outer12 h12⟩

end RawFourPortPlanarThetaPresentation
end Submission.Topology
