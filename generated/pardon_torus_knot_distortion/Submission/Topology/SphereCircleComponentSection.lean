import Submission.Topology.SphereCirclePlanarAxisFillingPasting

/-!
# Circle sections on one component of a finite sphere family

Every connected intersection circle of a finite disjoint sphere family lies on one unique
sphere component.  Restricting the global exact torus section to the fiber of this assignment
gives an exact circle section of that individual sphere.  This is the honest component-local
input for the planar innermost-circle filling argument; it does not invent a separate ambient
inside region for one component.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]

namespace FiniteSphereSurgeryIntersectionSystem

variable (F : FiniteSphereSurgeryIntersectionSystem Phi ι)

/-- Each connected stage circle lies on one component of the finite sphere family. -/
theorem exists_sphereComponent (i : ι) :
    ∃ j : Fin F.sphereFamily.count,
      Set.range (F.circle i).circle ⊆ (F.sphereFamily.sphere j).carrier := by
  classical
  apply F.sphereFamily.exists_component_of_isConnected
    (isConnected_range (F.circle i).isEmbedding.continuous)
  intro x hx
  have hxIntersection : x ∈ F.sphereFamily.carrier ∩ transportedTorus Phi := by
    rw [F.intersection_exact]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  exact hxIntersection.1

/-- The canonical sphere component containing a stage circle. -/
def sphereComponent (i : ι) : Fin F.sphereFamily.count :=
  (F.exists_sphereComponent i).choose

theorem circle_range_subset_sphereComponent (i : ι) :
    Set.range (F.circle i).circle ⊆
      (F.sphereFamily.sphere (F.sphereComponent i)).carrier :=
  (F.exists_sphereComponent i).choose_spec

/-- Circle labels assigned to one selected sphere component. -/
def sphereComponentFiber (j : Fin F.sphereFamily.count) :=
  {i : ι // F.sphereComponent i = j}

noncomputable instance (j : Fin F.sphereFamily.count) :
    Fintype (F.sphereComponentFiber j) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The circle family restricted to one sphere component. -/
def sphereComponentCircle (j : Fin F.sphereFamily.count)
    (i : F.sphereComponentFiber j) : EmbeddedTorusIntersectionCircle Phi :=
  F.circle i.1

theorem sphereComponentCircle_pairwise_disjoint (j : Fin F.sphereFamily.count) :
    Pairwise fun i k : F.sphereComponentFiber j ↦
      Disjoint (Set.range (F.sphereComponentCircle j i).circle)
        (Set.range (F.sphereComponentCircle j k).circle) := by
  intro i k hik
  apply F.pairwise_disjoint
  intro hval
  exact hik (Subtype.ext hval)

/-- The global exact section restricts exactly to the circles assigned to one sphere. -/
theorem sphereComponent_intersection_exact (j : Fin F.sphereFamily.count) :
    (F.sphereFamily.sphere j).carrier ∩ transportedTorus Phi =
      ⋃ i : F.sphereComponentFiber j,
        Set.range (F.sphereComponentCircle j i).circle := by
  classical
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hxGlobal : x ∈ F.sphereFamily.carrier ∩ transportedTorus Phi := by
      refine ⟨?_, hx.2⟩
      exact Set.mem_iUnion.mpr ⟨j, hx.1⟩
    rw [F.intersection_exact] at hxGlobal
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxGlobal
    have hiComponent : F.sphereComponent i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (F.sphereFamily.pairwise_disjoint hij)
        (F.circle_range_subset_sphereComponent i hi) hx.1
    exact Set.mem_iUnion.mpr ⟨⟨i, hiComponent⟩, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine ⟨?_, (F.sphereComponentCircle j i).range_subset_transportedTorus hi⟩
    have hiSphere := F.circle_range_subset_sphereComponent i.1 hi
    rw [i.2] at hiSphere
    exact hiSphere

/-- The circles assigned to one sphere form an exact finite torus-circle section of that
sphere component. -/
def sphereComponentSection (j : Fin F.sphereFamily.count) :
    FiniteEmbeddedTorusCircleSection Phi
      ((F.sphereFamily.sphere j).carrier ∩ transportedTorus Phi)
      (F.sphereComponentFiber j) where
  circle := F.sphereComponentCircle j
  circle_mem_section i x hx := by
    refine ⟨?_, (F.sphereComponentCircle j i).range_subset_transportedTorus hx⟩
    have hxSphere := F.circle_range_subset_sphereComponent i.1 hx
    rw [i.2] at hxSphere
    exact hxSphere
  pairwise_disjoint := F.sphereComponentCircle_pairwise_disjoint j
  section_exact := F.sphereComponent_intersection_exact j

/-- Every component fiber has one stereographic pole avoiding all its circles. -/
theorem nonempty_sphereComponentCommonPoleData (j : Fin F.sphereFamily.count) :
    Nonempty (FiniteEmbeddedSphereCircleCommonPoleData
      (F.sphereFamily.sphere j) (F.sphereComponentCircle j)) :=
  nonempty_finiteEmbeddedSphereCircleCommonPoleData
    (F.sphereFamily.sphere j) (F.sphereComponentCircle j) fun i ↦ by
      have hi := F.circle_range_subset_sphereComponent i.1
      rw [i.2] at hi
      exact hi

end FiniteSphereSurgeryIntersectionSystem

end Submission.Topology
