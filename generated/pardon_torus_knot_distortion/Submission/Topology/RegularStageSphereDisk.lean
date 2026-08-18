import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.SphereCircleProper

/-!
# Canonical sphere-side disks for regular moving-sphere stages

An honest moving-sphere stage already supplies its embedded sphere family and exact torus
intersection.  To obtain the sphere-side disks used by the surgery dichotomy, it is enough to
identify the sphere component containing each intersection circle.  Properness of a circle in a
two-sphere chooses a stereographic pole, and planar Schoenflies then constructs every disk.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}
  {choice : Fin P.bandCount → Bool}

/-- Minimal regular-stage data after exact moving-sphere intersection has been proved.  Sphere
components, stereographic poles, and sphere-side filling disks are all derived below. -/
structure RegularStageBasicDecoration
    (D : PairedBandMovingSphereCollarData C choice)
    (ι : Type*) [Fintype ι] where
  insideCell : Set R3
  family_is_boundary : D.family.patchedFamily.carrier = frontier insideCell
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  resolvedCarrier_eq_circleUnion : C.resolvedGraphCarrier choice =
    ⋃ i, Set.range (circle i).circle
  eventRegion : Set R3
  circle_mem_event : ∀ i t, ((circle i).windingLoop.curve t : R3) ∈ eventRegion

namespace RegularStageBasicDecoration

variable {ι : Type*} [Fintype ι]
  {D : PairedBandMovingSphereCollarData C choice}

/-- Every connected stage circle lies on one sphere component. -/
theorem exists_component (E : RegularStageBasicDecoration D ι) (i : ι) :
    ∃ j : Fin D.family.patchedFamily.count,
      Set.range (E.circle i).circle ⊆ (D.family.patchedFamily.sphere j).carrier := by
  classical
  apply D.family.patchedFamily.exists_component_of_isConnected
    (isConnected_range (E.circle i).isEmbedding.continuous)
  intro x hx
  have hxUnion : x ∈ ⋃ j, Set.range (E.circle j).circle :=
    Set.mem_iUnion.mpr ⟨i, hx⟩
  have hxResolved : x ∈ C.resolvedGraphCarrier choice :=
    E.resolvedCarrier_eq_circleUnion.symm ▸ hxUnion
  have hxIntersection : x ∈ D.family.patchedFamily.carrier ∩ transportedTorus Phi := by
    rw [D.patchedFamily_inter_torus_eq_resolvedGraphCarrier]
    exact hxResolved
  exact hxIntersection.1

/-- The sphere component selected for a stage circle. -/
def component (E : RegularStageBasicDecoration D ι) (i : ι) :
    Fin D.family.patchedFamily.count :=
  (E.exists_component i).choose

theorem circle_mem_component (E : RegularStageBasicDecoration D ι) (i : ι) :
    Set.range (E.circle i).circle ⊆
      (D.family.patchedFamily.sphere (E.component i)).carrier :=
  (E.exists_component i).choose_spec

end RegularStageBasicDecoration

/-- A regular moving-sphere stage whose only sphere-side input is the component containing each
intersection circle.  All filling disks are derived canonically. -/
structure RegularStageComponentDecoration
    (D : PairedBandMovingSphereCollarData C choice)
    (ι : Type*) [Fintype ι] where
  insideCell : Set R3
  family_is_boundary : D.family.patchedFamily.carrier = frontier insideCell
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  resolvedCarrier_eq_circleUnion : C.resolvedGraphCarrier choice =
    ⋃ i, Set.range (circle i).circle
  components : FiniteEmbeddedSphereCircleComponentData
    D.family.patchedFamily circle
  eventRegion : Set R3
  circle_mem_event : ∀ i t, ((circle i).windingLoop.curve t : R3) ∈ eventRegion

namespace RegularStageComponentDecoration

variable {ι : Type*} [Fintype ι]
  {D : PairedBandMovingSphereCollarData C choice}

/-- Component assignments construct the full regular-stage decoration consumed by surgery. -/
def toRegularStageDecoration
    (E : RegularStageComponentDecoration D ι) :
    RegularStageDecoration D ι where
  insideCell := E.insideCell
  family_is_boundary := E.family_is_boundary
  circle := E.circle
  pairwise_disjoint := E.pairwise_disjoint
  resolvedCarrier_eq_circleUnion := E.resolvedCarrier_eq_circleUnion
  sphereDisk := E.components.toPoleData.embeddedDisk
  sphereDisk_mem := E.components.toPoleData.embeddedDisk_range_subset_family
  sphereDisk_boundary := E.components.toPoleData.embeddedDisk_boundary
  eventRegion := E.eventRegion
  circle_mem_event := E.circle_mem_event

/-- A component-decorated moving-sphere stage is an honest sphere-surgery system. -/
def toFiniteSphereSurgeryIntersectionSystem
    (E : RegularStageComponentDecoration D ι) :
    FiniteSphereSurgeryIntersectionSystem Phi ι :=
  E.toRegularStageDecoration.toFiniteSphereSurgeryIntersectionSystem

end RegularStageComponentDecoration

namespace RegularStageBasicDecoration

variable {ι : Type*} [Fintype ι]
  {D : PairedBandMovingSphereCollarData C choice}

/-- Exact intersection and connectedness construct all sphere-component assignments. -/
def toRegularStageComponentDecoration
    (E : RegularStageBasicDecoration D ι) :
    RegularStageComponentDecoration D ι where
  insideCell := E.insideCell
  family_is_boundary := E.family_is_boundary
  circle := E.circle
  pairwise_disjoint := E.pairwise_disjoint
  resolvedCarrier_eq_circleUnion := E.resolvedCarrier_eq_circleUnion
  components := {
    component := E.component
    circle_mem := E.circle_mem_component
  }
  eventRegion := E.eventRegion
  circle_mem_event := E.circle_mem_event

/-- Minimal regular-stage data construct the complete sphere-surgery system. -/
def toFiniteSphereSurgeryIntersectionSystem
    (E : RegularStageBasicDecoration D ι) :
    FiniteSphereSurgeryIntersectionSystem Phi ι :=
  E.toRegularStageComponentDecoration.toFiniteSphereSurgeryIntersectionSystem

end RegularStageBasicDecoration

end PairedBandMovingSphereCollarData
end Submission.Topology
