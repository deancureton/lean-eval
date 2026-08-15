import Submission.Topology.HalfspaceCut

/-!
# Coordinate cutting planes as copies of the Euclidean plane

The cutting plane used in Pardon's box argument is an affine coordinate plane in `R3`.
This file gives an explicit homeomorphism with two-dimensional Euclidean space.  The
construction is useful when a planar Jordan curve theorem produces a disk that must be
transported back to the ambient three-space.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

/-- The standard two-dimensional model for a coordinate cutting plane. -/
abbrev CoordinatePlaneDomain := EuclideanSpace ℝ (Fin 2)

/-- Insert two planar coordinates in the first two axes of `frame`, and put `d` in its
third axis. -/
def coordinatePlanePoint (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (u : CoordinatePlaneDomain) : R3 :=
  WithLp.toLp 2 fun j => ![u.ofLp 0, u.ofLp 1, d] (frame.symm j)

/-- Read the first two framed coordinates of an ambient point. -/
def coordinatePlaneCoordinates (frame : Equiv.Perm (Fin 3))
    (x : R3) : CoordinatePlaneDomain :=
  WithLp.toLp 2 fun i => x.ofLp (frame i.castSucc)

@[simp] theorem coordinatePlanePoint_coordinate (frame : Equiv.Perm (Fin 3))
    (d : ℝ) (u : CoordinatePlaneDomain) (i : Fin 2) :
    (coordinatePlanePoint frame d u).ofLp (frame i.castSucc) = u.ofLp i := by
  fin_cases i <;> simp [coordinatePlanePoint]

@[simp] theorem coordinatePlanePoint_longCoordinate (frame : Equiv.Perm (Fin 3))
    (d : ℝ) (u : CoordinatePlaneDomain) :
    (coordinatePlanePoint frame d u).ofLp (frame 2) = d := by
  simp [coordinatePlanePoint]

theorem coordinatePlanePoint_mem (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (u : CoordinatePlaneDomain) :
    coordinatePlanePoint frame d u ∈ coordinateCuttingPlane frame d := by
  exact coordinatePlanePoint_longCoordinate frame d u

@[simp] theorem coordinatePlaneCoordinates_point (frame : Equiv.Perm (Fin 3))
    (d : ℝ) (u : CoordinatePlaneDomain) :
    coordinatePlaneCoordinates frame (coordinatePlanePoint frame d u) = u := by
  rw [WithLp.ext_iff]
  funext i
  exact coordinatePlanePoint_coordinate frame d u i

@[simp] theorem coordinatePlanePoint_coordinates_of_mem
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (x : coordinateCuttingPlane frame d) :
    coordinatePlanePoint frame d (coordinatePlaneCoordinates frame x) = x := by
  rw [WithLp.ext_iff]
  funext j
  generalize h : frame.symm j = i
  fin_cases i
  · have hj : frame 0 = j := by
      simpa [h] using frame.apply_symm_apply j
    rw [← hj]
    simp [coordinatePlaneCoordinates, coordinatePlanePoint]
  · have hj : frame 1 = j := by
      simpa [h] using frame.apply_symm_apply j
    rw [← hj]
    simp [coordinatePlaneCoordinates, coordinatePlanePoint]
  · have hj : frame 2 = j := by
      simpa [h] using frame.apply_symm_apply j
    rw [← hj]
    simpa [coordinatePlanePoint] using x.2.symm

theorem continuous_coordinatePlanePoint (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    Continuous (coordinatePlanePoint frame d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  rw [continuous_pi_iff]
  intro j
  generalize h : frame.symm j = i
  fin_cases i
  · simpa [coordinatePlanePoint] using
      PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 0
  · simpa [coordinatePlanePoint] using
      PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 1
  · exact continuous_const

theorem continuous_coordinatePlaneCoordinates (frame : Equiv.Perm (Fin 3)) :
    Continuous (coordinatePlaneCoordinates frame) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  rw [continuous_pi_iff]
  intro i
  exact (Submission.PardonDistortion.coordinateCLM (frame i.castSucc)).continuous

/-- The explicit homeomorphism from the Euclidean plane to a coordinate cutting plane. -/
def coordinatePlaneHomeomorph (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    CoordinatePlaneDomain ≃ₜ coordinateCuttingPlane frame d where
  toFun u := ⟨coordinatePlanePoint frame d u, coordinatePlanePoint_mem frame d u⟩
  invFun x := coordinatePlaneCoordinates frame x
  left_inv := coordinatePlaneCoordinates_point frame d
  right_inv := fun x => Subtype.ext (coordinatePlanePoint_coordinates_of_mem frame d x)
  continuous_toFun := (continuous_coordinatePlanePoint frame d).subtype_mk _
  continuous_invFun := (continuous_coordinatePlaneCoordinates frame).comp continuous_subtype_val

theorem isEmbedding_coordinatePlanePoint (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsEmbedding (coordinatePlanePoint frame d) := by
  have h := IsEmbedding.subtypeVal.comp (coordinatePlaneHomeomorph frame d).isEmbedding
  convert h using 1
  rfl

end Submission.Topology
