import Mathlib.Topology.Homeomorph.Lemmas
import Submission.Topology.SuperellipsoidConvexSpheres

/-!
# The convex superellipsoid sphere has the analytic gauge boundary

Weighted, permuted coordinates give an affine homeomorphism from ambient
three-space to the finite `L^256` coordinate space.  The closed
superellipsoid is the inverse image of a norm closed ball, so its frontier is
exactly the inverse image of the corresponding sphere, namely the analytic
gauge level used by the regular-level construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped ENNReal

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion

instance instFactSuperellipsoidExponentAtLeastOne :
    Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Permute ambient coordinates into the chosen frame. -/
def orientedCoordinatePermutationHomeomorph
    (frame : Equiv.Perm (Fin 3)) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) :=
  Homeomorph.piCongrLeft (Y := fun _ : Fin 3 ↦ ℝ) frame.symm

@[simp]
theorem orientedCoordinatePermutationHomeomorph_apply
    (frame : Equiv.Perm (Fin 3)) (x : Fin 3 → ℝ) (i : Fin 3) :
    orientedCoordinatePermutationHomeomorph frame x i = x (frame i) := by
  change Homeomorph.piCongrLeft (Y := fun _ : Fin 3 ↦ ℝ) frame.symm x i =
    x (frame i)
  simpa using Homeomorph.piCongrLeft_apply_apply
    (Y := fun _ : Fin 3 ↦ ℝ) frame.symm x (frame i)

/-- Divide every oriented coordinate by its positive axis weight. -/
def axisWeightHomeomorph : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) :=
  Homeomorph.piCongrRight fun i ↦
    Homeomorph.smulOfNeZero ((axisWeight i)⁻¹)
      (inv_ne_zero (ne_of_gt (axisWeight_pos i)))

@[simp]
theorem axisWeightHomeomorph_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    axisWeightHomeomorph x i = x i / axisWeight i := by
  change (axisWeight i)⁻¹ • x i = x i / axisWeight i
  simp [div_eq_inv_mul]

/-- The affine weighted-coordinate homeomorphism whose norm is the superellipsoid gauge. -/
def superellipsoidCoordinateHomeomorph
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    R3 ≃ₜ PiLp 256 (fun _ : Fin 3 ↦ ℝ) :=
  (Homeomorph.subRight c).trans <|
    (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).trans <|
      (orientedCoordinatePermutationHomeomorph frame).trans <|
        axisWeightHomeomorph.trans
          (PiLp.homeomorph 256 (fun _ : Fin 3 ↦ ℝ)).symm

@[simp]
theorem superellipsoidCoordinateHomeomorph_apply
    (frame : Equiv.Perm (Fin 3)) (c x : R3) :
    superellipsoidCoordinateHomeomorph frame c x =
      superellipsoidCoordinates frame c x := by
  apply PiLp.ext
  intro i
  change axisWeightHomeomorph
      (orientedCoordinatePermutationHomeomorph frame (x - c).ofLp) i =
    normalizedOrientedBoxCoordinates frame c x i
  rw [axisWeightHomeomorph_apply,
    orientedCoordinatePermutationHomeomorph_apply]
  rfl

/-- The closed body is the inverse image of the coordinate norm ball. -/
theorem closedSuperellipsoidBody_eq_preimage_closedBall
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    closedSuperellipsoidBody frame c R =
      superellipsoidCoordinateHomeomorph frame c ⁻¹'
        Metric.closedBall 0 R := by
  ext x
  simp only [closedSuperellipsoidBody, mem_ofPred_eq, mem_preimage,
    Metric.mem_closedBall, dist_zero_right,
    superellipsoidCoordinateHomeomorph_apply, superellipsoidGauge]

/-- The analytic gauge boundary is the inverse image of the coordinate norm sphere. -/
theorem superellipsoidBoundary_eq_preimage_sphere
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    superellipsoidBoundary frame c R =
      superellipsoidCoordinateHomeomorph frame c ⁻¹' Metric.sphere 0 R := by
  ext x
  simp only [superellipsoidBoundary, mem_ofPred_eq, mem_preimage,
    Metric.mem_sphere, dist_zero_right,
    superellipsoidCoordinateHomeomorph_apply, superellipsoidGauge]

/-- At positive scale, the topological frontier and analytic gauge boundary coincide. -/
theorem frontier_closedSuperellipsoidBody_eq_boundary
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    frontier (closedSuperellipsoidBody frame c R) =
      superellipsoidBoundary frame c R := by
  rw [closedSuperellipsoidBody_eq_preimage_closedBall,
    ← (superellipsoidCoordinateHomeomorph frame c).preimage_frontier,
    frontier_closedBall (0 : PiLp 256 (fun _ : Fin 3 ↦ ℝ)) hR.ne',
    ← superellipsoidBoundary_eq_preimage_sphere]

/-- The convex-body outer sphere therefore has exactly the selected analytic carrier. -/
theorem outerSuperellipsoidSphereData_carrier_eq_boundary
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    (outerSuperellipsoidSphereData frame c hR).sphere.carrier =
      superellipsoidBoundary frame c R := by
  rw [ConvexBodySphereData.sphere_carrier_eq_frontier,
    frontier_closedSuperellipsoidBody_eq_boundary frame c hR]

end Submission.Topology
