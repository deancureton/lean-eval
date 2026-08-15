import Submission.Topology.CoordinatePlane
import Submission.Topology.InnermostCircleSurgery

/-!
# Explicit closed disks in coordinate cutting planes

This file transports the complex closed unit disk through an affine chart of a coordinate
cutting plane.  The result is an actual embedded ambient disk with the boundary parametrization
expected by the innermost-circle surgery interface.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- The standard real-linear isometry from the complex plane to `CoordinatePlaneDomain`. -/
def complexCoordinatePlaneEquiv : ℂ ≃ₗᵢ[ℝ] CoordinatePlaneDomain :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Translation by `center` after multiplication by a nonzero real scalar. -/
def coordinatePlaneAffineHomeomorph (center : CoordinatePlaneDomain)
    (scale : ℝ) (hscale : scale ≠ 0) :
    CoordinatePlaneDomain ≃ₜ CoordinatePlaneDomain where
  toFun u := center + scale • u
  invFun u := scale⁻¹ • (u - center)
  left_inv u := by
    simp [smul_smul, hscale]
  right_inv u := by
    simp [smul_smul, hscale]
  continuous_toFun := continuous_const.add (continuous_id.const_smul scale)
  continuous_invFun := (continuous_id.sub continuous_const).const_smul scale⁻¹

/-- A closed round disk of radius `scale`, centered at `center`, inside a framed coordinate
plane. -/
def coordinatePlaneDiskPoint (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ)
    (z : ClosedUnitDisk) : R3 :=
  coordinatePlanePoint frame d
    (center + scale • complexCoordinatePlaneEquiv (z : ℂ))

theorem coordinatePlaneDiskPoint_mem (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) (z : ClosedUnitDisk) :
    coordinatePlaneDiskPoint frame d center scale z ∈ coordinateCuttingPlane frame d :=
  coordinatePlanePoint_mem frame d _

theorem continuous_coordinatePlaneDiskPoint (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) :
    Continuous (coordinatePlaneDiskPoint frame d center scale) := by
  exact (continuous_coordinatePlanePoint frame d).comp
    (continuous_const.add
      ((complexCoordinatePlaneEquiv.continuous.comp continuous_subtype_val).const_smul scale))

theorem isEmbedding_coordinatePlaneDiskPoint (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) {scale : ℝ} (hscale : scale ≠ 0) :
    IsEmbedding (coordinatePlaneDiskPoint frame d center scale) := by
  have h := (isEmbedding_coordinatePlanePoint frame d).comp
    ((coordinatePlaneAffineHomeomorph center scale hscale).isEmbedding.comp
      (complexCoordinatePlaneEquiv.toLinearIsometry.isEmbedding.comp
        (IsEmbedding.subtypeVal : IsEmbedding ((↑) : ClosedUnitDisk → ℂ))))
  convert h using 1
  rfl

/-- The explicit angular boundary curve of `coordinatePlaneDiskPoint`. -/
def coordinatePlaneDiskBoundary (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) (t : ℝ) : R3 :=
  coordinatePlanePoint frame d
    (center + scale • complexCoordinatePlaneEquiv (unitCircleParam t))

theorem continuous_coordinatePlaneDiskBoundary (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) :
    Continuous (coordinatePlaneDiskBoundary frame d center scale) := by
  exact (continuous_coordinatePlanePoint frame d).comp
    (continuous_const.add
      ((complexCoordinatePlaneEquiv.continuous.comp continuous_unitCircleParam).const_smul scale))

theorem periodic_coordinatePlaneDiskBoundary (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) :
    Function.Periodic (coordinatePlaneDiskBoundary frame d center scale) (2 * Real.pi) := by
  intro t
  simp only [coordinatePlaneDiskBoundary]
  rw [unitCircleParam_add_two_pi]

theorem coordinatePlaneDisk_boundary (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) (t : ℝ) :
    coordinatePlaneDiskPoint frame d center scale (unitDiskBoundary t) =
      coordinatePlaneDiskBoundary frame d center scale t :=
  rfl

/-- The round coordinate-plane disk as the bundled disk required by the surgery interface. -/
def coordinatePlaneEmbeddedDisk (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) (hscale : scale ≠ 0) :
    BoundaryParametrizedEmbeddedDiskInR3 where
  disk := coordinatePlaneDiskPoint frame d center scale
  isEmbedding := isEmbedding_coordinatePlaneDiskPoint frame d center hscale
  boundaryCurve := coordinatePlaneDiskBoundary frame d center scale
  continuous_boundaryCurve := continuous_coordinatePlaneDiskBoundary frame d center scale
  periodic_boundaryCurve := periodic_coordinatePlaneDiskBoundary frame d center scale
  boundary := coordinatePlaneDisk_boundary frame d center scale

theorem coordinatePlaneEmbeddedDisk_range_subset_plane
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) (scale : ℝ) (hscale : scale ≠ 0) :
    Set.range (coordinatePlaneEmbeddedDisk frame d center scale hscale).disk ⊆
      coordinateCuttingPlane frame d := by
  rintro _ ⟨z, rfl⟩
  exact coordinatePlaneDiskPoint_mem frame d center scale z

/-- Exact metric description of the range of a positive-radius coordinate-plane disk. -/
theorem mem_range_coordinatePlaneDiskPoint_iff
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (center : CoordinatePlaneDomain) {scale : ℝ} (hscale : 0 < scale)
    (x : coordinateCuttingPlane frame d) :
    x.1 ∈ Set.range (coordinatePlaneDiskPoint frame d center scale) ↔
      ‖coordinatePlaneCoordinates frame x - center‖ ≤ scale := by
  constructor
  · rintro ⟨z, hz⟩
    have hcoordinates := congrArg (coordinatePlaneCoordinates frame) hz
    change coordinatePlaneCoordinates frame
      (coordinatePlanePoint frame d
        (center + scale • complexCoordinatePlaneEquiv (z : ℂ))) =
      coordinatePlaneCoordinates frame x at hcoordinates
    rw [coordinatePlaneCoordinates_point] at hcoordinates
    rw [← hcoordinates]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hscale, complexCoordinatePlaneEquiv.norm_map]
    have hzmem := z.property
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (mul_le_mul_of_nonneg_left hzmem hscale.le)
  · intro hx
    let w : ℂ := complexCoordinatePlaneEquiv.symm
      (scale⁻¹ • (coordinatePlaneCoordinates frame x - center))
    have hw : ‖w‖ ≤ 1 := by
      rw [show ‖w‖ = ‖scale⁻¹ • (coordinatePlaneCoordinates frame x - center)‖ by
        exact complexCoordinatePlaneEquiv.symm.norm_map _]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscale]
      exact (inv_mul_le_one₀ hscale).2 hx
    let z : ClosedUnitDisk := ⟨w, by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw⟩
    refine ⟨z, ?_⟩
    rw [← coordinatePlanePoint_coordinates_of_mem frame d x]
    change coordinatePlanePoint frame d
      (center + scale • complexCoordinatePlaneEquiv (z : ℂ)) = _
    congr 1
    change center + scale • complexCoordinatePlaneEquiv w =
      coordinatePlaneCoordinates frame x
    rw [show complexCoordinatePlaneEquiv w =
        scale⁻¹ • (coordinatePlaneCoordinates frame x - center) by
      exact complexCoordinatePlaneEquiv.apply_symm_apply _]
    rw [smul_smul, mul_inv_cancel₀ hscale.ne']
    simp

/-- A sufficiently large round disk in a coordinate plane contains the entire intersection of
that plane with the compact transported torus. -/
theorem exists_coordinatePlaneDisk_containing_transportedTorus_section
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    ∃ scale > 0,
      transportedTorus Phi ∩ coordinateCuttingPlane frame d ⊆
        Set.range (coordinatePlaneDiskPoint frame d 0 scale) := by
  have htorus : IsCompact (transportedTorus Phi) := by
    exact isCompact_range (Submission.Torus.transportedTorusMap_isEmbedding Phi).continuous
  have hsection : IsCompact
      (transportedTorus Phi ∩ coordinateCuttingPlane frame d) :=
    htorus.inter_right (isClosed_coordinateCuttingPlane frame d)
  have himage : IsCompact
      (coordinatePlaneCoordinates frame ''
        (transportedTorus Phi ∩ coordinateCuttingPlane frame d)) :=
    hsection.image (continuous_coordinatePlaneCoordinates frame)
  obtain ⟨r, hr⟩ := himage.isBounded.subset_ball (0 : CoordinatePlaneDomain)
  refine ⟨max 1 r, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  let xp : coordinateCuttingPlane frame d := ⟨x, hx.2⟩
  rw [mem_range_coordinatePlaneDiskPoint_iff frame d 0
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) xp]
  have hmem : coordinatePlaneCoordinates frame xp ∈
      Metric.ball (0 : CoordinatePlaneDomain) r := by
    apply hr
    exact ⟨x, hx, rfl⟩
  have hnorm : ‖coordinatePlaneCoordinates frame xp‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hmem
  simpa using hnorm.le.trans (le_max_right 1 r)

end Submission.Topology
