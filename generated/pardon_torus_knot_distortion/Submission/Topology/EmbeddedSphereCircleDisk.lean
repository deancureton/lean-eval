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

/-- The Schoenflies disk parametrization as a homeomorphism onto the exact closed planar
Jordan disk. -/
def planeDiskHomeomorph (D : EmbeddedSphereCirclePoleData S C) :
    ClosedUnitDisk ≃ₜ closure D.planeJordanCircle.inside :=
  D.isEmbedding_planeDisk.toHomeomorph.trans (Homeomorph.setCongr D.range_planeDisk)

@[simp]
theorem coe_planeDiskHomeomorph
    (D : EmbeddedSphereCirclePoleData S C) (z : ClosedUnitDisk) :
    (D.planeDiskHomeomorph z : JordanCurve.Arcs.Plane) = D.planeDisk z :=
  rfl

/-- Reparameterize a map on the standard closed disk onto the corresponding closed planar
Jordan disk. -/
def planarizedDiskMap
    (D : EmbeddedSphereCirclePoleData S C) {Y : Type*}
    (f : ClosedUnitDisk → Y) : closure D.planeJordanCircle.inside → Y :=
  f ∘ D.planeDiskHomeomorph.symm

theorem continuous_planarizedDiskMap
    (D : EmbeddedSphereCirclePoleData S C) {Y : Type*} [TopologicalSpace Y]
    {f : ClosedUnitDisk → Y} (hf : Continuous f) :
    Continuous (D.planarizedDiskMap f) :=
  hf.comp D.planeDiskHomeomorph.symm.continuous

@[simp]
theorem planarizedDiskMap_planeDisk
    (D : EmbeddedSphereCirclePoleData S C) {Y : Type*}
    (f : ClosedUnitDisk → Y) (z : ClosedUnitDisk) :
    D.planarizedDiskMap f
      ⟨D.planeDisk z, D.range_planeDisk ▸ Set.mem_range_self z⟩ = f z := by
  change f (D.planeDiskHomeomorph.symm
    (D.planeDiskHomeomorph z)) = f z
  rw [D.planeDiskHomeomorph.symm_apply_apply]

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

/-- Every point of the planar Jordan carrier is reached by the standard boundary
parametrization of the Schoenflies disk. -/
theorem exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier
    (D : EmbeddedSphereCirclePoleData S C) {x : JordanCurve.Arcs.Plane}
    (hx : x ∈ D.planeJordanCircle.carrier) :
    ∃ t : ℝ, D.planeDisk (unitDiskBoundary t) = x := by
  obtain ⟨q, hq⟩ := hx
  obtain ⟨t, ht⟩ := Circle.exp_surjective
    (JordanCurve.Arcs.spherePlaneHomeoCircle q)
  refine ⟨t, ?_⟩
  rw [D.planeDisk_boundary, ht]
  exact hq

/-- On the Jordan carrier, a reparameterized planar disk map is one of the original
standard-boundary values. -/
theorem exists_planarizedDiskMap_eq_unitDiskBoundary_of_mem_carrier
    (D : EmbeddedSphereCirclePoleData S C) {Y : Type*}
    (f : ClosedUnitDisk → Y) (x : closure D.planeJordanCircle.inside)
    (hx : (x : JordanCurve.Arcs.Plane) ∈ D.planeJordanCircle.carrier) :
    ∃ t : ℝ, D.planarizedDiskMap f x = f (unitDiskBoundary t) := by
  obtain ⟨t, ht⟩ := D.exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier hx
  refine ⟨t, ?_⟩
  have hxEq : x =
      ⟨D.planeDisk (unitDiskBoundary t),
        D.range_planeDisk ▸ Set.mem_range_self (unitDiskBoundary t)⟩ := by
    apply Subtype.ext
    exact ht.symm
  rw [hxEq, D.planarizedDiskMap_planeDisk]

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

/-- The exact closed planar Jordan disk mapped back into the ambient sphere. -/
def planarDiskAmbientMap (D : EmbeddedSphereCirclePoleData S C) :
    closure D.planeJordanCircle.inside → R3 :=
  fun x ↦ S.parametrization ((stereographic' 2 D.pole).symm x)

theorem continuous_planarDiskAmbientMap (D : EmbeddedSphereCirclePoleData S C) :
    Continuous D.planarDiskAmbientMap := by
  have hstereographic : Continuous fun x : closure D.planeJordanCircle.inside ↦
      (stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane) := by
    rw [← continuousOn_univ]
    exact (stereographic' 2 D.pole).symm.continuousOn.comp
      continuous_subtype_val.continuousOn fun _ _ ↦ by
        rw [OpenPartialHomeomorph.symm_source, stereographic'_target]
        trivial
  exact S.isEmbedding.continuous.comp hstereographic

@[simp]
theorem planarDiskAmbientMap_planeDisk
    (D : EmbeddedSphereCirclePoleData S C) (z : ClosedUnitDisk) :
    D.planarDiskAmbientMap (D.planeDiskHomeomorph z) = D.embeddedDisk.disk z :=
  rfl

/-- A point of the planar Jordan circle, packaged as a point of its closed bounded disk. -/
def planeCirclePoint
    (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    closure D.planeJordanCircle.inside :=
  ⟨D.planeCircle z, by
    rw [D.planeJordanCircle.closure_inside]
    right
    refine ⟨JordanCurve.Arcs.spherePlaneHomeoCircle.symm z, ?_⟩
    exact congrArg D.planeCircle
      (JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply z)⟩

@[simp]
theorem coe_planeCirclePoint
    (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    (D.planeCirclePoint z : JordanCurve.Arcs.Plane) = D.planeCircle z :=
  rfl

/-- The canonical planar boundary point agrees with the Schoenflies disk boundary. -/
theorem planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary
    (D : EmbeddedSphereCirclePoleData S C) (t : ℝ) :
    D.planeCirclePoint (Circle.exp t) =
      D.planeDiskHomeomorph (unitDiskBoundary t) := by
  apply Subtype.ext
  exact (D.planeDisk_boundary t).symm

/-- Reparameterizing a standard disk map onto the planar Jordan disk preserves its boundary
values at the canonical circle points. -/
@[simp]
theorem planarizedDiskMap_planeCirclePoint_exp
    (D : EmbeddedSphereCirclePoleData S C) {Y : Type*}
    (f : ClosedUnitDisk → Y) (t : ℝ) :
    D.planarizedDiskMap f (D.planeCirclePoint (Circle.exp t)) =
      f (unitDiskBoundary t) := by
  rw [D.planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary]
  exact D.planarizedDiskMap_planeDisk f (unitDiskBoundary t)

/-- Mapping a canonical planar boundary point back to the ambient sphere recovers the original
embedded torus circle point. -/
@[simp]
theorem planarDiskAmbientMap_planeCirclePoint
    (D : EmbeddedSphereCirclePoleData S C) (z : Circle) :
    D.planarDiskAmbientMap (D.planeCirclePoint z) = C.circle z := by
  change S.parametrization
    ((stereographic' 2 D.pole).symm (D.planeCircle z)) = C.circle z
  rw [show (stereographic' 2 D.pole).symm (D.planeCircle z) =
      D.sphereCircle z by
    exact (stereographic' 2 D.pole).left_inv
      (D.sphereCircle_mem_stereographicSource z)]
  exact D.sphere_parametrization_sphereCircle z

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
