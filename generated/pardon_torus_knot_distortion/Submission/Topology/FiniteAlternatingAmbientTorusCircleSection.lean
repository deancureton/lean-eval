import Submission.Topology.FiniteAlternatingTorusCircleSection

/-!
# Torus-circle sections from ambient alternating paths

An alternating path system is often easiest to construct in `R3`.  If every constituent path
lies on the transported torus, its canonical embedded cycles lift to the torus subtype and give
the same exact finite circle section as a subtype-valued construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

namespace FiniteAlternatingEndpointSystem.ClosedArcIncidenceData

universe u

variable {Phi : AmbientIsotopy} {vertex : Type u} [Fintype vertex]
  {A : FiniteAlternatingEndpointSystem vertex}
  {point : vertex → R3}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- Constituent paths on the transported torus force every canonical cycle onto it. -/
theorem range_circleMap_subset_transportedTorus
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi)
    (q : A.CycleIndex) :
    Set.range ((orientedFamily firstPaths secondPaths).circleMap q) ⊆
      transportedTorus Phi := by
  rw [H.range_circleMap_eq_cycleEdgeCarrier]
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    by_cases hcycle : A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q
    · rw [if_pos hcycle] at he
      exact hfirst e he
    · rw [if_neg hcycle] at he
      exact he.elim
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    by_cases hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
    · rw [if_pos hcycle] at he
      exact hsecond e he
    · rw [if_neg hcycle] at he
      exact he.elim

/-- Lift one canonical ambient cycle to an embedded transported-torus circle. -/
noncomputable def embeddedTorusCircleOfAmbient
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi)
    (q : A.CycleIndex) : EmbeddedTorusIntersectionCircle Phi := by
  let beta : Circle → transportedTorus Phi := fun z ↦
    ⟨(orientedFamily firstPaths secondPaths).circleMap q z,
      H.range_circleMap_subset_transportedTorus hfirst hsecond q ⟨z, rfl⟩⟩
  have hbeta : IsEmbedding beta := by
    apply IsEmbedding.codRestrict
    exact (H.twoArcData q).data.isEmbedding
  exact EmbeddedTorusIntersectionCircle.ofTorusEmbedding beta hbeta

@[simp] theorem embeddedTorusCircleOfAmbient_apply
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi)
    (q : A.CycleIndex) (z : Circle) :
    (H.embeddedTorusCircleOfAmbient hfirst hsecond q).circle z =
      (orientedFamily firstPaths secondPaths).circleMap q z :=
  rfl

/-- The ambient carrier of the lifted quotient cycles. -/
noncomputable def ambientCycleCarrierOfAmbient
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi) : Set R3 :=
  ⋃ q : A.CycleIndex,
    Set.range (H.embeddedTorusCircleOfAmbient hfirst hsecond q).circle

/-- The quotient cycles collectively use every constituent edge exactly as a carrier. -/
theorem iUnion_cycleEdgeCarrier_eq
    (_H : ClosedArcIncidenceData A point firstPaths secondPaths) :
    (⋃ q : A.CycleIndex, cycleEdgeCarrier A point firstPaths secondPaths q) =
      (⋃ e : A.first.edge, Set.range (firstPaths.path e)) ∪
        ⋃ e : A.second.edge, Set.range (secondPaths.path e) := by
  classical
  ext x
  simp only [cycleEdgeCarrier, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨q, ⟨e, he⟩ | ⟨e, he⟩⟩
    · left
      refine ⟨e, ?_⟩
      split at he
      · exact he
      · exact he.elim
    · right
      refine ⟨e, ?_⟩
      split at he
      · exact he
      · exact he.elim
  · rintro (⟨e, he⟩ | ⟨e, he⟩)
    · let q := A.cycleOfVertex (A.first.endpointEquiv (e, 0))
      refine ⟨q, Or.inl ⟨e, ?_⟩⟩
      exact if_pos rfl ▸ he
    · let q := A.cycleOfVertex (A.second.endpointEquiv (e, 0))
      refine ⟨q, Or.inr ⟨e, ?_⟩⟩
      exact if_pos rfl ▸ he

/-- The lifted ambient circle carrier is exactly the union of both path colors. -/
theorem ambientCycleCarrierOfAmbient_eq_iUnion_ranges
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi) :
    H.ambientCycleCarrierOfAmbient hfirst hsecond =
      (⋃ e : A.first.edge, Set.range (firstPaths.path e)) ∪
        ⋃ e : A.second.edge, Set.range (secondPaths.path e) := by
  unfold ambientCycleCarrierOfAmbient
  change (⋃ q : A.CycleIndex,
      Set.range ((orientedFamily firstPaths secondPaths).circleMap q)) = _
  simp_rw [H.range_circleMap_eq_cycleEdgeCarrier]
  exact H.iUnion_cycleEdgeCarrier_eq

/-- Ambient alternating paths contained in the torus give an exact finite torus section. -/
noncomputable def finiteEmbeddedTorusCircleSectionOfAmbient
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (hfirst : ∀ e, Set.range (firstPaths.path e) ⊆ transportedTorus Phi)
    (hsecond : ∀ e, Set.range (secondPaths.path e) ⊆ transportedTorus Phi) :
    FiniteEmbeddedTorusCircleSection Phi
      (H.ambientCycleCarrierOfAmbient hfirst hsecond) A.CycleIndex where
  circle := H.embeddedTorusCircleOfAmbient hfirst hsecond
  circle_mem_section := by
    intro q x hx
    exact Set.mem_iUnion.mpr ⟨q, hx⟩
  pairwise_disjoint := by
    intro q r hqr
    rw [Set.disjoint_left]
    rintro x ⟨z, hz⟩ ⟨w, hw⟩
    have hambient :
        (orientedFamily firstPaths secondPaths).circleMap q z =
          (orientedFamily firstPaths secondPaths).circleMap r w := by
      exact hz.trans hw.symm
    exact Set.disjoint_left.mp (H.circleMap_ranges_disjoint hqr)
      ⟨z, rfl⟩ ⟨w, hambient.symm⟩
  section_exact := rfl

end FiniteAlternatingEndpointSystem.ClosedArcIncidenceData
end Submission.Topology
