import Submission.Topology.SphereCircleProper
import Submission.Topology.SuperellipsoidBarrierGraph

/-!
# Finite sphere systems from exact circle sections

For a finite disjoint embedded-sphere family, an exact finite torus-circle section already
determines the sphere component containing each circle.  Connectedness selects that component;
properness and planar Schoenflies then construct every sphere-side disk.  Thus the only geometric
inputs left are the sphere boundary, its parity side, the exact torus intersection, and an event
container.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {ambientSection : Set R3}
  {ι : Type*} [Fintype ι]

namespace FiniteSphereSurgeryIntersectionSystem

variable {κ : Type*} [Fintype κ]

/-- Reindex a finite sphere-surgery system along an equivalence of circle labels. -/
def reindex (S : FiniteSphereSurgeryIntersectionSystem Phi ι) (e : κ ≃ ι) :
    FiniteSphereSurgeryIntersectionSystem Phi κ where
  sphereFamily := S.sphereFamily
  insideCell := S.insideCell
  sphereFamily_is_boundary := S.sphereFamily_is_boundary
  circle k := S.circle (e k)
  pairwise_disjoint := by
    intro i j hij
    exact S.pairwise_disjoint (fun heq ↦ hij (e.injective heq))
  intersection_exact := by
    rw [S.intersection_exact]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa⟩
    · rintro ⟨k, hk⟩
      exact ⟨e k, hk⟩
  sphereDisk k := S.sphereDisk (e k)
  sphereDisk_mem k := S.sphereDisk_mem (e k)
  sphereDisk_boundary k := S.sphereDisk_boundary (e k)
  eventRegion := S.eventRegion
  circle_mem_event k := S.circle_mem_event (e k)

end FiniteSphereSurgeryIntersectionSystem

/-- Minimal geometric data turning an exact finite circle section into a regular sphere stage. -/
structure FiniteCircleSectionBasicStageGeometry
    (circleSection : FiniteEmbeddedTorusCircleSection Phi ambientSection ι) where
  sphereFamily : FiniteEmbeddedTopologicalSphereFamilyInR3
  insideCell : Set R3
  sphereFamily_is_boundary : sphereFamily.carrier = frontier insideCell
  intersection_eq : sphereFamily.carrier ∩ transportedTorus Phi = ambientSection
  eventRegion : Set R3
  circle_mem_event : ∀ i t,
    ((circleSection.circle i).windingLoop.curve t : R3) ∈ eventRegion

namespace FiniteCircleSectionBasicStageGeometry

variable {circleSection : FiniteEmbeddedTorusCircleSection Phi ambientSection ι}

/-- Each connected section circle lies on one component of the exact sphere family. -/
theorem exists_component
    (D : FiniteCircleSectionBasicStageGeometry circleSection) (i : ι) :
    ∃ j : Fin D.sphereFamily.count,
      Set.range (circleSection.circle i).circle ⊆ (D.sphereFamily.sphere j).carrier := by
  classical
  apply D.sphereFamily.exists_component_of_isConnected
    (isConnected_range (circleSection.circle i).isEmbedding.continuous)
  intro x hx
  have hxSection : x ∈ ambientSection := circleSection.circle_mem_section i hx
  have hxIntersection : x ∈ D.sphereFamily.carrier ∩ transportedTorus Phi := by
    rw [D.intersection_eq]
    exact hxSection
  exact hxIntersection.1

/-- Canonical component assignment obtained from exact intersection. -/
def componentData (D : FiniteCircleSectionBasicStageGeometry circleSection) :
    FiniteEmbeddedSphereCircleComponentData D.sphereFamily circleSection.circle where
  component i := (D.exists_component i).choose
  circle_mem i := (D.exists_component i).choose_spec

/-- Exact finite section data construct the complete sphere-surgery system. -/
def toFiniteSphereSurgeryIntersectionSystem
    (D : FiniteCircleSectionBasicStageGeometry circleSection) :
    FiniteSphereSurgeryIntersectionSystem Phi ι where
  sphereFamily := D.sphereFamily
  insideCell := D.insideCell
  sphereFamily_is_boundary := D.sphereFamily_is_boundary
  circle := circleSection.circle
  pairwise_disjoint := circleSection.pairwise_disjoint
  intersection_exact := D.intersection_eq.trans circleSection.section_exact
  sphereDisk := D.componentData.toPoleData.embeddedDisk
  sphereDisk_mem := D.componentData.toPoleData.embeddedDisk_range_subset_family
  sphereDisk_boundary := D.componentData.toPoleData.embeddedDisk_boundary
  eventRegion := D.eventRegion
  circle_mem_event := D.circle_mem_event

end FiniteCircleSectionBasicStageGeometry
end Submission.Topology
