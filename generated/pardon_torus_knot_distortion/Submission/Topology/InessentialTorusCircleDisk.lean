import Submission.Topology.InessentialSliceCircle
import Submission.Topology.JordanTranslate

/-!
# Torus-side disks for zero-winding intersection circles

The two real covering coordinates of a zero-winding embedded circle are periodic.  They descend
to an embedded Jordan circle in the universal covering plane.  Schoenflies fills that Jordan
circle, and disjointness of all nontrivial lattice translates makes the covering projection
injective on the filled disk.  The resulting disk lies in the transported torus and has exactly
the original real-periodic boundary parametrization.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- The Euclidean plane used as the universal cover of the product torus. -/
abbrev TorusCoveringPlane := Schoenflies.Plane

namespace EmbeddedTorusIntersectionCircle

variable {Phi : AmbientIsotopy}

/-- The two chosen real covering coordinates, regarded as a curve in the Euclidean plane. -/
def zeroWindingPlaneLift (C : EmbeddedTorusIntersectionCircle Phi)
    (t : ℝ) : TorusCoveringPlane :=
  WithLp.toLp 2 ![C.windingLoop.lift.first.angle t,
    C.windingLoop.lift.second.angle t]

theorem continuous_zeroWindingPlaneLift (C : EmbeddedTorusIntersectionCircle Phi) :
    Continuous C.zeroWindingPlaneLift := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · simpa [zeroWindingPlaneLift] using C.windingLoop.lift.first.continuous_angle
  · simpa [zeroWindingPlaneLift] using C.windingLoop.lift.second.continuous_angle

private theorem first_winding_eq_zero (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.windingLoop.lift.first.winding = 0 := by
  simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair] using
    congrArg Prod.fst hzero

private theorem second_winding_eq_zero (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.windingLoop.lift.second.winding = 0 := by
  simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair] using
    congrArg Prod.snd hzero

theorem periodic_zeroWindingPlaneLift (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Function.Periodic C.zeroWindingPlaneLift (2 * Real.pi) := by
  intro t
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · simpa [zeroWindingPlaneLift, C.first_winding_eq_zero hzero] using
      C.windingLoop.lift.first.angle_add_period t
  · simpa [zeroWindingPlaneLift, C.second_winding_eq_zero hzero] using
      C.windingLoop.lift.second.angle_add_period t

/-- The periodic covering lift descended to the additive circle. -/
def zeroWindingPlaneAddCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    AddCircle (2 * Real.pi) → TorusCoveringPlane :=
  (C.periodic_zeroWindingPlaneLift hzero).lift

theorem continuous_zeroWindingPlaneAddCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.zeroWindingPlaneAddCircle hzero) := by
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  convert C.continuous_zeroWindingPlaneLift using 1
  funext t
  exact (C.periodic_zeroWindingPlaneLift hzero).lift_coe t

/-- The lifted embedded circle in the covering plane. -/
def zeroWindingPlaneCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Circle → TorusCoveringPlane := fun z ↦
  C.zeroWindingPlaneAddCircle hzero (AddCircle.homeomorphCircle'.symm z)

theorem continuous_zeroWindingPlaneCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.zeroWindingPlaneCircle hzero) :=
  (C.continuous_zeroWindingPlaneAddCircle hzero).comp
    AddCircle.homeomorphCircle'.symm.continuous

@[simp]
theorem zeroWindingPlaneCircle_exp (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.zeroWindingPlaneCircle hzero (Circle.exp t) = C.zeroWindingPlaneLift t := by
  have hquotient : AddCircle.homeomorphCircle'.symm (Circle.exp t) =
      (t : AddCircle (2 * Real.pi)) := by
    apply AddCircle.homeomorphCircle'.injective
    rw [AddCircle.homeomorphCircle'.apply_symm_apply,
      AddCircle.homeomorphCircle'_apply_mk]
  rw [zeroWindingPlaneCircle, hquotient]
  exact (C.periodic_zeroWindingPlaneLift hzero).lift_coe t

/-- The covering projection to the transported torus. -/
def torusCoveringProjection (Phi : AmbientIsotopy)
    (x : TorusCoveringPlane) : R3 :=
  transportedTorusMap Phi (Circle.exp (x 0), Circle.exp (x 1))

theorem continuous_torusCoveringProjection (Phi : AmbientIsotopy) :
    Continuous (torusCoveringProjection Phi) := by
  apply (transportedTorusMap_continuous Phi).comp
  exact
    (Circle.exp.continuous.comp
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 0)).prodMk
    (Circle.exp.continuous.comp
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 1))

theorem torusCoveringProjection_zeroWindingPlaneCircle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (z : Circle) :
    torusCoveringProjection Phi (C.zeroWindingPlaneCircle hzero z) = C.circle z := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [C.zeroWindingPlaneCircle_exp hzero, C.parametrization]
  change transportedTorusMap Phi
      (Circle.exp (C.windingLoop.lift.first.angle t),
        Circle.exp (C.windingLoop.lift.second.angle t)) =
    (C.windingLoop.curve t : R3)
  rw [C.windingLoop.lift.first.exp_angle,
    C.windingLoop.lift.second.exp_angle]
  change ((transportedTorusHomeomorph Phi)
    (transportedLoopCoordinates Phi C.windingLoop.curve t) : R3) = _
  exact congrArg Subtype.val <|
    (transportedTorusHomeomorph Phi).apply_symm_apply (C.windingLoop.curve t)

theorem injective_zeroWindingPlaneCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Function.Injective (C.zeroWindingPlaneCircle hzero) := by
  intro z w hzw
  apply C.isEmbedding.injective
  rw [← C.torusCoveringProjection_zeroWindingPlaneCircle hzero z,
    ← C.torusCoveringProjection_zeroWindingPlaneCircle hzero w, hzw]

theorem isEmbedding_zeroWindingPlaneCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    IsEmbedding (C.zeroWindingPlaneCircle hzero) :=
  ((C.continuous_zeroWindingPlaneCircle hzero).isClosedEmbedding
    (C.injective_zeroWindingPlaneCircle hzero)).isEmbedding

/-- The covering lift bundled as a Schoenflies Jordan circle. -/
def zeroWindingJordanCircle (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Schoenflies.JordanCircle where
  parametrization := fun q ↦
    C.zeroWindingPlaneCircle hzero (JordanCurve.Arcs.spherePlaneHomeoCircle q)
  continuous := (C.continuous_zeroWindingPlaneCircle hzero).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  injective := (C.injective_zeroWindingPlaneCircle hzero).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

/-- The period lattice in the real covering plane. -/
def torusLatticeVector (k : Fin 2 → ℤ) : TorusCoveringPlane :=
  WithLp.toLp 2 ![(k 0 : ℝ) * (2 * Real.pi), (k 1 : ℝ) * (2 * Real.pi)]

@[simp]
theorem torusLatticeVector_apply_zero (k : Fin 2 → ℤ) :
    torusLatticeVector k 0 = (k 0 : ℝ) * (2 * Real.pi) := by
  simp [torusLatticeVector]

@[simp]
theorem torusLatticeVector_apply_one (k : Fin 2 → ℤ) :
    torusLatticeVector k 1 = (k 1 : ℝ) * (2 * Real.pi) := by
  simp [torusLatticeVector]

theorem torusLatticeVector_ne_zero {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    torusLatticeVector k ≠ 0 := by
  intro hvector
  apply hk
  funext i
  fin_cases i
  · have hcoord := congrArg (fun x : TorusCoveringPlane ↦ x 0) hvector
    change (k 0 : ℝ) * (2 * Real.pi) = 0 at hcoord
    have hcast : (k 0 : ℝ) = 0 := by
      exact (mul_eq_zero.mp hcoord).resolve_right (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    exact_mod_cast hcast
  · have hcoord := congrArg (fun x : TorusCoveringPlane ↦ x 1) hvector
    change (k 1 : ℝ) * (2 * Real.pi) = 0 at hcoord
    have hcast : (k 1 : ℝ) = 0 := by
      exact (mul_eq_zero.mp hcoord).resolve_right (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    exact_mod_cast hcast

@[simp]
theorem torusLatticeVector_zero : torusLatticeVector (0 : Fin 2 → ℤ) = 0 := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp

theorem torusCoveringProjection_add_lattice (Phi : AmbientIsotopy)
    (x : TorusCoveringPlane) (k : Fin 2 → ℤ) :
    torusCoveringProjection Phi (x + torusLatticeVector k) =
      torusCoveringProjection Phi x := by
  unfold torusCoveringProjection
  congr 1
  apply Prod.ext
  · apply Circle.exp_eq_exp.mpr
    exact ⟨k 0, by simp [torusLatticeVector]⟩
  · apply Circle.exp_eq_exp.mpr
    exact ⟨k 1, by simp [torusLatticeVector]⟩

theorem disjoint_zeroWindingJordanCircle_carrier_lattice
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    Disjoint (C.zeroWindingJordanCircle hzero).carrier
      ((fun x ↦ x + torusLatticeVector k) ''
        (C.zeroWindingJordanCircle hzero).carrier) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨_, ⟨r, rfl⟩, hrq⟩
  have hprojection :
      torusCoveringProjection Phi
          (C.zeroWindingPlaneCircle hzero
            (JordanCurve.Arcs.spherePlaneHomeoCircle q)) =
        torusCoveringProjection Phi
          (C.zeroWindingPlaneCircle hzero
            (JordanCurve.Arcs.spherePlaneHomeoCircle r)) := by
    calc
      _ = torusCoveringProjection Phi
          (C.zeroWindingPlaneCircle hzero
              (JordanCurve.Arcs.spherePlaneHomeoCircle r) +
            torusLatticeVector k) := congrArg _ hrq.symm
      _ = _ := torusCoveringProjection_add_lattice Phi _ k
  have hparameters : JordanCurve.Arcs.spherePlaneHomeoCircle q =
      JordanCurve.Arcs.spherePlaneHomeoCircle r := by
    apply C.isEmbedding.injective
    simpa only [C.torusCoveringProjection_zeroWindingPlaneCircle hzero] using hprojection
  have hqr : q = r := JordanCurve.Arcs.spherePlaneHomeoCircle.injective hparameters
  subst r
  change C.zeroWindingPlaneCircle hzero
      (JordanCurve.Arcs.spherePlaneHomeoCircle q) + torusLatticeVector k =
    C.zeroWindingPlaneCircle hzero
      (JordanCurve.Arcs.spherePlaneHomeoCircle q) at hrq
  apply torusLatticeVector_ne_zero hk
  apply add_left_cancel (a :=
    C.zeroWindingPlaneCircle hzero (JordanCurve.Arcs.spherePlaneHomeoCircle q))
  simpa only [add_zero] using hrq

theorem disjoint_zeroWindingJordanCircle_closure_inside_lattice
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    Disjoint (closure (C.zeroWindingJordanCircle hzero).inside)
      ((fun x ↦ x + torusLatticeVector k) ''
        closure (C.zeroWindingJordanCircle hzero).inside) :=
  (C.zeroWindingJordanCircle hzero).disjoint_closure_inside_translate
    (torusLatticeVector k) (torusLatticeVector_ne_zero hk)
    (C.disjoint_zeroWindingJordanCircle_carrier_lattice hzero k hk)

theorem torusCoveringProjection_injOn_zeroWindingJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Set.InjOn (torusCoveringProjection Phi)
      (closure (C.zeroWindingJordanCircle hzero).inside) := by
  intro x hx y hy hxy
  have hpair : (Circle.exp (x 0), Circle.exp (x 1)) =
      (Circle.exp (y 0), Circle.exp (y 1)) := by
    apply transportedTorusMap_injective Phi
    exact hxy
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hpair)
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hpair)
  let k : Fin 2 → ℤ := ![m, n]
  have htranslate : x = y + torusLatticeVector k := by
    rw [WithLp.ext_iff]
    funext i
    fin_cases i
    · simpa [k, torusLatticeVector] using hm
    · simpa [k, torusLatticeVector] using hn
  by_cases hk : k = 0
  · rw [hk, torusLatticeVector_zero, add_zero] at htranslate
    exact htranslate
  · exfalso
    exact Set.disjoint_left.mp
      (C.disjoint_zeroWindingJordanCircle_closure_inside_lattice hzero k hk)
      hx ⟨y, hy, htranslate.symm⟩

private theorem complexLIE_mem_planeBall (z : ClosedUnitDisk) :
    JordanCurve.Arcs.complexLIE (z : ℂ) ∈
      Metric.closedBall (0 : TorusCoveringPlane) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right,
    JordanCurve.Arcs.complexLIE.norm_map]
  simpa only [Metric.mem_closedBall, dist_zero_right] using z.property

private theorem complexLIESymm_mem_complexDisk
    (x : Metric.closedBall (0 : TorusCoveringPlane) 1) :
    JordanCurve.Arcs.complexLIE.symm (x : TorusCoveringPlane) ∈ ClosedUnitDisk := by
  rw [Metric.mem_closedBall, dist_zero_right,
    JordanCurve.Arcs.complexLIE.symm.norm_map]
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.property

/-- The complex unit disk identified with the Euclidean closed unit ball used by Schoenflies. -/
def complexDiskPlaneBall : ClosedUnitDisk ≃ₜ
    Metric.closedBall (0 : TorusCoveringPlane) 1 where
  toFun z := ⟨JordanCurve.Arcs.complexLIE (z : ℂ), complexLIE_mem_planeBall z⟩
  invFun x := ⟨JordanCurve.Arcs.complexLIE.symm (x : TorusCoveringPlane),
    complexLIESymm_mem_complexDisk x⟩
  left_inv z := by
    apply Subtype.ext
    exact JordanCurve.Arcs.complexLIE.symm_apply_apply z
  right_inv x := by
    apply Subtype.ext
    exact JordanCurve.Arcs.complexLIE.apply_symm_apply x
  continuous_toFun := Continuous.subtype_mk
    (JordanCurve.Arcs.complexLIE.continuous.comp continuous_subtype_val)
    complexLIE_mem_planeBall
  continuous_invFun := Continuous.subtype_mk
    (JordanCurve.Arcs.complexLIE.symm.continuous.comp continuous_subtype_val)
    complexLIESymm_mem_complexDisk

@[simp]
theorem complexDiskPlaneBall_apply (z : ClosedUnitDisk) :
    (complexDiskPlaneBall z : TorusCoveringPlane) = JordanCurve.Arcs.complexLIE (z : ℂ) :=
  rfl

theorem complexDiskPlaneBall_unitDiskBoundary (t : ℝ) :
    (complexDiskPlaneBall (unitDiskBoundary t) : TorusCoveringPlane) =
      JordanCurve.Arcs.param t := by
  simp only [complexDiskPlaneBall_apply, unitDiskBoundary, JordanCurve.Arcs.param,
    JordanCurve.Arcs.circleHomeoSphere_coe]
  rw [circle_exp_coe_eq_unitCircleParam]

/-- The regional Schoenflies extension chosen for the lifted Jordan circle. -/
def zeroWindingRegionalExtension (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Schoenflies.RegionalExtensionData (C.zeroWindingJordanCircle hzero) :=
  (Schoenflies.MoiseChapter9.hasMoiseDiskExtensions
    (C.zeroWindingJordanCircle hzero)).some

/-- The Schoenflies filling before projection through the torus covering map. -/
def zeroWindingPlaneDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (z : ClosedUnitDisk) : TorusCoveringPlane :=
  C.zeroWindingRegionalExtension hzero |>.insideHomeomorph.symm
    (complexDiskPlaneBall z)

theorem isEmbedding_zeroWindingPlaneDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    IsEmbedding (C.zeroWindingPlaneDisk hzero) := by
  exact (IsEmbedding.subtypeVal.comp
    ((C.zeroWindingRegionalExtension hzero).insideHomeomorph.symm.isEmbedding.comp
      complexDiskPlaneBall.isEmbedding))

theorem zeroWindingPlaneDisk_mem_closure_inside
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (z : ClosedUnitDisk) :
    C.zeroWindingPlaneDisk hzero z ∈
      closure (C.zeroWindingJordanCircle hzero).inside :=
  ((C.zeroWindingRegionalExtension hzero).insideHomeomorph.symm
    (complexDiskPlaneBall z)).property

theorem zeroWindingPlaneDisk_boundary
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.zeroWindingPlaneDisk hzero (unitDiskBoundary t) =
      C.zeroWindingPlaneLift t := by
  let E := C.zeroWindingRegionalExtension hzero
  have hball : complexDiskPlaneBall (unitDiskBoundary t) =
      ⟨JordanCurve.Arcs.param t,
        Metric.sphere_subset_closedBall (JordanCurve.Arcs.param t).property⟩ := by
    apply Subtype.ext
    exact complexDiskPlaneBall_unitDiskBoundary t
  change (E.insideHomeomorph.symm
    (complexDiskPlaneBall (unitDiskBoundary t)) : TorusCoveringPlane) = _
  rw [hball, E.inside_inverse_boundary]
  change C.zeroWindingPlaneCircle hzero
      (JordanCurve.Arcs.spherePlaneHomeoCircle (JordanCurve.Arcs.param t)) = _
  rw [show JordanCurve.Arcs.spherePlaneHomeoCircle (JordanCurve.Arcs.param t) =
      Circle.exp t by
    exact JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply (Circle.exp t)]
  exact C.zeroWindingPlaneCircle_exp hzero t

/-- A torus-side embedded disk bounded by a specified intersection circle. -/
structure InessentialTorusCircleDisk (Phi : AmbientIsotopy)
    (C : EmbeddedTorusIntersectionCircle Phi) where
  disk : ClosedUnitDisk → R3
  isEmbedding : IsEmbedding disk
  range_subset : Set.range disk ⊆ transportedTorus Phi
  boundary : ∀ t, disk (unitDiskBoundary t) = C.windingLoop.curve t

/-- Projecting the lifted Schoenflies disk gives an embedded disk in the transported torus. -/
def inessentialTorusCircleDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    InessentialTorusCircleDisk Phi C where
  disk := fun z ↦ torusCoveringProjection Phi (C.zeroWindingPlaneDisk hzero z)
  isEmbedding := by
    have hcontinuous : Continuous
        (fun z ↦ torusCoveringProjection Phi (C.zeroWindingPlaneDisk hzero z)) :=
      (continuous_torusCoveringProjection Phi).comp
        (C.isEmbedding_zeroWindingPlaneDisk hzero).continuous
    have hinjective : Function.Injective
        (fun z ↦ torusCoveringProjection Phi (C.zeroWindingPlaneDisk hzero z)) := by
      intro z w hzw
      apply (C.isEmbedding_zeroWindingPlaneDisk hzero).injective
      exact C.torusCoveringProjection_injOn_zeroWindingJordanDisk hzero
        (C.zeroWindingPlaneDisk_mem_closure_inside hzero z)
        (C.zeroWindingPlaneDisk_mem_closure_inside hzero w) hzw
    exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding
  range_subset := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(Circle.exp ((C.zeroWindingPlaneDisk hzero z) 0),
      Circle.exp ((C.zeroWindingPlaneDisk hzero z) 1)), rfl⟩
  boundary := by
    intro t
    rw [C.zeroWindingPlaneDisk_boundary hzero]
    change transportedTorusMap Phi
        (Circle.exp (C.windingLoop.lift.first.angle t),
          Circle.exp (C.windingLoop.lift.second.angle t)) =
      (C.windingLoop.curve t : R3)
    rw [C.windingLoop.lift.first.exp_angle,
      C.windingLoop.lift.second.exp_angle]
    change ((transportedTorusHomeomorph Phi)
      (transportedLoopCoordinates Phi C.windingLoop.curve t) : R3) = _
    exact congrArg Subtype.val <|
      (transportedTorusHomeomorph Phi).apply_symm_apply (C.windingLoop.curve t)

end EmbeddedTorusIntersectionCircle
end Submission.Topology
