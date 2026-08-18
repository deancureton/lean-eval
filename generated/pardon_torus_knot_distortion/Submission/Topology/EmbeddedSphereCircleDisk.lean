import Submission.Topology.InessentialTorusCircleDisk
import Submission.Topology.HalfSphereSurgeryDichotomy
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Filling a circle on an embedded sphere

An embedded circle on an embedded two-sphere bounds a disk.  This module proves the constructive
part needed by the sphere-surgery interface from the minimal chart datum: a point of the standard
sphere whose ambient image is not on the circle.  Stereographic projection turns the pulled-back
circle into a planar Jordan circle, and the regional Schoenflies theorem supplies its filling.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

/-- A circle lies on one embedded sphere, together with a stereographic pole off that circle. -/
structure EmbeddedSphereCirclePoleData
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi) where
  circle_mem : Set.range C.circle ⊆ S.carrier
  pole : Metric.sphere (0 : R3) 1
  pole_not_mem : S.parametrization pole ∉ Set.range C.circle

namespace EmbeddedSphereCirclePoleData

variable {S : EmbeddedTopologicalSphereInR3} {C : EmbeddedTorusIntersectionCircle Phi}

/-- Pull the ambient circle back through the sphere parametrization. -/
def sphereCircle (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    Metric.sphere (0 : R3) 1 :=
  S.isEmbedding.toHomeomorph.symm ⟨C.circle z, D.circle_mem ⟨z, rfl⟩⟩

theorem continuous_sphereCircle (D : EmbeddedSphereCirclePoleData S C) :
    Continuous D.sphereCircle :=
  S.isEmbedding.toHomeomorph.symm.continuous.comp <|
    Continuous.subtype_mk C.isEmbedding.continuous fun z ↦ D.circle_mem ⟨z, rfl⟩

theorem sphere_parametrization_sphereCircle
    (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    S.parametrization (D.sphereCircle z) = C.circle z := by
  exact congrArg Subtype.val <|
    S.isEmbedding.toHomeomorph.apply_symm_apply
      ⟨C.circle z, D.circle_mem ⟨z, rfl⟩⟩

theorem injective_sphereCircle (D : EmbeddedSphereCirclePoleData S C) :
    Function.Injective D.sphereCircle := by
  intro z w hzw
  apply C.isEmbedding.injective
  rw [← D.sphere_parametrization_sphereCircle z,
    ← D.sphere_parametrization_sphereCircle w, hzw]

theorem sphereCircle_ne_pole (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    D.sphereCircle z ≠ D.pole := by
  intro hz
  apply D.pole_not_mem
  refine ⟨z, ?_⟩
  rw [← D.sphere_parametrization_sphereCircle z, hz]

private instance : Fact (Module.finrank ℝ R3 = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

/-- Stereographic image of the pulled-back circle in the standard plane. -/
def planeCircle (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    JordanCurve.Arcs.Plane :=
  stereographic' 2 D.pole (D.sphereCircle z)

theorem sphereCircle_mem_stereographicSource
    (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    D.sphereCircle z ∈ (stereographic' 2 D.pole).source := by
  rw [stereographic'_source]
  exact D.sphereCircle_ne_pole z

theorem continuous_planeCircle (D : EmbeddedSphereCirclePoleData S C) :
    Continuous D.planeCircle := by
  change Continuous ((stereographic' 2 D.pole) ∘ D.sphereCircle)
  rw [← continuousOn_univ]
  exact (stereographic' 2 D.pole).continuousOn.comp
    D.continuous_sphereCircle.continuousOn fun z _ ↦
      D.sphereCircle_mem_stereographicSource z

theorem injective_planeCircle (D : EmbeddedSphereCirclePoleData S C) :
    Function.Injective D.planeCircle := by
  intro z w hzw
  apply D.injective_sphereCircle
  exact (stereographic' 2 D.pole).injOn
    (D.sphereCircle_mem_stereographicSource z)
    (D.sphereCircle_mem_stereographicSource w) hzw

/-- The planar Jordan circle obtained by stereographic projection. -/
def planeJordanCircle (D : EmbeddedSphereCirclePoleData S C) : Schoenflies.JordanCircle where
  parametrization := D.planeCircle ∘ JordanCurve.Arcs.spherePlaneHomeoCircle
  continuous := D.continuous_planeCircle.comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  injective := D.injective_planeCircle.comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

/-- Regional Schoenflies extension for the stereographic circle. -/
def regionalExtension (D : EmbeddedSphereCirclePoleData S C) :
    Schoenflies.RegionalExtensionData D.planeJordanCircle :=
  (Schoenflies.MoiseChapter9.hasMoiseDiskExtensions D.planeJordanCircle).some

/-- The planar Schoenflies filling of the stereographic circle. -/
def planeDisk (D : EmbeddedSphereCirclePoleData S C) (z : ClosedUnitDisk) :
    JordanCurve.Arcs.Plane :=
  D.regionalExtension.insideHomeomorph.symm
    (EmbeddedTorusIntersectionCircle.complexDiskPlaneBall z)

theorem isEmbedding_planeDisk (D : EmbeddedSphereCirclePoleData S C) :
    IsEmbedding D.planeDisk :=
  IsEmbedding.subtypeVal.comp <|
    D.regionalExtension.insideHomeomorph.symm.isEmbedding.comp
      EmbeddedTorusIntersectionCircle.complexDiskPlaneBall.isEmbedding

/-- The planar filling has exactly the closed bounded Jordan region as its range. -/
theorem range_planeDisk (D : EmbeddedSphereCirclePoleData S C) :
    Set.range D.planeDisk = closure D.planeJordanCircle.inside := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact (D.regionalExtension.insideHomeomorph.symm
      (EmbeddedTorusIntersectionCircle.complexDiskPlaneBall z)).property
  · intro x hx
    let xb : closure D.planeJordanCircle.inside := ⟨x, hx⟩
    let y : closedBall (0 : JordanCurve.Arcs.Plane) 1 :=
      D.regionalExtension.insideHomeomorph xb
    let z : ClosedUnitDisk :=
      EmbeddedTorusIntersectionCircle.complexDiskPlaneBall.symm y
    refine ⟨z, ?_⟩
    change (D.regionalExtension.insideHomeomorph.symm
      (EmbeddedTorusIntersectionCircle.complexDiskPlaneBall z) :
        JordanCurve.Arcs.Plane) = x
    rw [show EmbeddedTorusIntersectionCircle.complexDiskPlaneBall z = y by
      exact EmbeddedTorusIntersectionCircle.complexDiskPlaneBall.apply_symm_apply y]
    exact congrArg Subtype.val <|
      D.regionalExtension.insideHomeomorph.symm_apply_apply xb

theorem planeDisk_boundary (D : EmbeddedSphereCirclePoleData S C) (t : ℝ) :
    D.planeDisk (unitDiskBoundary t) = D.planeCircle (Circle.exp t) := by
  let E := D.regionalExtension
  have hball : EmbeddedTorusIntersectionCircle.complexDiskPlaneBall
      (unitDiskBoundary t) =
      ⟨JordanCurve.Arcs.param t,
        Metric.sphere_subset_closedBall (JordanCurve.Arcs.param t).property⟩ := by
    apply Subtype.ext
    exact EmbeddedTorusIntersectionCircle.complexDiskPlaneBall_unitDiskBoundary t
  change (E.insideHomeomorph.symm
    (EmbeddedTorusIntersectionCircle.complexDiskPlaneBall
      (unitDiskBoundary t)) : JordanCurve.Arcs.Plane) = _
  rw [hball, E.inside_inverse_boundary]
  change D.planeCircle
      (JordanCurve.Arcs.spherePlaneHomeoCircle (JordanCurve.Arcs.param t)) = _
  rw [show JordanCurve.Arcs.spherePlaneHomeoCircle (JordanCurve.Arcs.param t) =
      Circle.exp t by
    exact JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply (Circle.exp t)]

/-- Lift the planar filling back to the standard sphere through the stereographic chart. -/
def sphereDisk (D : EmbeddedSphereCirclePoleData S C) (z : ClosedUnitDisk) :
    Metric.sphere (0 : R3) 1 :=
  (stereographic' 2 D.pole).symm (D.planeDisk z)

theorem continuous_sphereDisk (D : EmbeddedSphereCirclePoleData S C) :
    Continuous D.sphereDisk := by
  change Continuous ((stereographic' 2 D.pole).symm ∘ D.planeDisk)
  rw [← continuousOn_univ]
  exact (stereographic' 2 D.pole).symm.continuousOn.comp
    D.isEmbedding_planeDisk.continuous.continuousOn fun _ _ ↦ by
      rw [OpenPartialHomeomorph.symm_source, stereographic'_target]
      trivial

theorem injective_sphereDisk (D : EmbeddedSphereCirclePoleData S C) :
    Function.Injective D.sphereDisk := by
  intro z w hzw
  apply D.isEmbedding_planeDisk.injective
  exact (stereographic' 2 D.pole).symm.injOn
    (by rw [OpenPartialHomeomorph.symm_source, stereographic'_target]; trivial)
    (by rw [OpenPartialHomeomorph.symm_source, stereographic'_target]; trivial) hzw

theorem sphereDisk_boundary (D : EmbeddedSphereCirclePoleData S C) (t : ℝ) :
    D.sphereDisk (unitDiskBoundary t) = D.sphereCircle (Circle.exp t) := by
  change (stereographic' 2 D.pole).symm
    (D.planeDisk (unitDiskBoundary t)) = _
  rw [D.planeDisk_boundary]
  exact (stereographic' 2 D.pole).left_inv <|
    D.sphereCircle_mem_stereographicSource (Circle.exp t)

/-- The sphere-side filling, with the exact boundary parametrization expected by surgery. -/
def embeddedDisk (D : EmbeddedSphereCirclePoleData S C) :
    BoundaryParametrizedEmbeddedDiskInR3 where
  disk z := S.parametrization (D.sphereDisk z)
  isEmbedding := S.isEmbedding.comp <|
    (D.continuous_sphereDisk.isClosedEmbedding D.injective_sphereDisk).isEmbedding
  boundaryCurve t := C.windingLoop.curve t
  continuous_boundaryCurve :=
    continuous_subtype_val.comp C.windingLoop.continuous_curve
  periodic_boundaryCurve t := congrArg Subtype.val (C.windingLoop.periodic_curve t)
  boundary t := by
    rw [D.sphereDisk_boundary, D.sphere_parametrization_sphereCircle,
      C.parametrization]

theorem embeddedDisk_range_subset_carrier (D : EmbeddedSphereCirclePoleData S C) :
    Set.range D.embeddedDisk.disk ⊆ S.carrier := by
  rintro _ ⟨z, rfl⟩
  exact ⟨D.sphereDisk z, rfl⟩

end EmbeddedSphereCirclePoleData

universe u

/-- Component choices and off-circle poles for a finite circle family on a finite sphere family. -/
structure FiniteEmbeddedSphereCirclePoleData
    {ι : Type u}
    (F : FiniteEmbeddedTopologicalSphereFamilyInR3)
    (circle : ι → EmbeddedTorusIntersectionCircle Phi) where
  component : ι → Fin F.count
  circle_mem : ∀ i, Set.range (circle i).circle ⊆ (F.sphere (component i)).carrier
  pole : ι → Metric.sphere (0 : R3) 1
  pole_not_mem : ∀ i,
    (F.sphere (component i)).parametrization (pole i) ∉ Set.range (circle i).circle

namespace FiniteEmbeddedSphereCirclePoleData

variable {ι : Type*} {F : FiniteEmbeddedTopologicalSphereFamilyInR3}
  {circle : ι → EmbeddedTorusIntersectionCircle Phi}

/-- The single-circle pole package selected by the finite family. -/
def circleData (D : FiniteEmbeddedSphereCirclePoleData F circle) (i : ι) :
    EmbeddedSphereCirclePoleData (F.sphere (D.component i)) (circle i) where
  circle_mem := D.circle_mem i
  pole := D.pole i
  pole_not_mem := D.pole_not_mem i

/-- Canonical sphere-side Schoenflies disk for each circle. -/
def embeddedDisk (D : FiniteEmbeddedSphereCirclePoleData F circle) (i : ι) :
    BoundaryParametrizedEmbeddedDiskInR3 :=
  (D.circleData i).embeddedDisk

theorem embeddedDisk_range_subset_family
    (D : FiniteEmbeddedSphereCirclePoleData F circle) (i : ι) :
    Set.range (D.embeddedDisk i).disk ⊆ F.carrier := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨D.component i,
    (D.circleData i).embeddedDisk_range_subset_carrier hx⟩

theorem embeddedDisk_boundary
    (D : FiniteEmbeddedSphereCirclePoleData F circle) (i : ι) (t : ℝ) :
    (D.embeddedDisk i).disk (unitDiskBoundary t) = (circle i).windingLoop.curve t :=
  (D.embeddedDisk i).boundary t

end FiniteEmbeddedSphereCirclePoleData
end Submission.Topology
