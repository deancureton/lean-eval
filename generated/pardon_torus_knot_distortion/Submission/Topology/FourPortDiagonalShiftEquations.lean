import Submission.Topology.FourPortDiagonalSharedEdgeAlignment

/-!
# Vertex equations for the diagonal four-port deck shifts

The cyclic endpoint identities turn the six shared-edge deck translations into four equations.
Comparing the two routes from the rectangle's left shift to its right shift forces those two
shifts to agree.  This is the finite cancellation at the heart of the coherent lift.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy}

namespace FourPortDiagonalPathSystem.ZeroWindingData

variable {G : FourPortDiagonalPathSystem (transportedTorus Phi)}
variable (Z : G.ZeroWindingData)

private def shiftVector (k : Fin 2 → ℤ) : TorusCoveringPlane :=
  EmbeddedTorusIntersectionCircle.torusLatticeVector k

theorem leftVector_eq_bottomVector_add_upperVector :
    shiftVector Z.leftShift = shiftVector Z.bottomShift + shiftVector Z.upperShift := by
  apply add_left_cancel (a := Z.rectangleLeftPlanePath 0)
  calc
    Z.rectangleLeftPlanePath 0 + shiftVector Z.leftShift = Z.preLeftPlanePath 0 :=
      (Z.preLeft_eq_rectangleLeft_add_shift 0).symm
    _ = Z.preUpperPlanePath 1 := Z.preUpper_target_eq_preLeft_source.symm
    _ = Z.postUpperPlanePath 1 + shiftVector Z.upperShift :=
      Z.preUpper_eq_postUpper_add_shift 1
    _ = Z.postBottomPlanePath 0 + shiftVector Z.upperShift := by
      rw [Z.postUpper_target_eq_postBottom_source]
    _ = (Z.rectangleBottomPlanePath 0 + shiftVector Z.bottomShift) +
        shiftVector Z.upperShift := by
      simpa only [shiftVector] using congrArg
        (fun x ↦ x + shiftVector Z.upperShift)
        (Z.postBottom_eq_rectangleBottom_add_shift 0)
    _ = (Z.rectangleLeftPlanePath 0 + shiftVector Z.bottomShift) +
        shiftVector Z.upperShift := by
      rw [Z.rectangleBottom_source_eq_rectangleLeft_source]
    _ = Z.rectangleLeftPlanePath 0 +
        (shiftVector Z.bottomShift + shiftVector Z.upperShift) := by
      rw [add_assoc]

theorem leftVector_eq_topVector_add_lowerVector :
    shiftVector Z.leftShift = shiftVector Z.topShift + shiftVector Z.lowerShift := by
  apply add_left_cancel (a := Z.rectangleLeftPlanePath 1)
  calc
    Z.rectangleLeftPlanePath 1 + shiftVector Z.leftShift = Z.preLeftPlanePath 1 :=
      (Z.preLeft_eq_rectangleLeft_add_shift 1).symm
    _ = Z.preLowerPlanePath 0 := Z.preLeft_target_eq_preLower_source
    _ = Z.postLowerPlanePath 0 + shiftVector Z.lowerShift :=
      Z.preLower_eq_postLower_add_shift 0
    _ = Z.postTopPlanePath 0 + shiftVector Z.lowerShift := by
      rw [Z.postLower_source_eq_postTop_source]
    _ = (Z.rectangleTopPlanePath 0 + shiftVector Z.topShift) +
        shiftVector Z.lowerShift := by
      simpa only [shiftVector] using congrArg
        (fun x ↦ x + shiftVector Z.lowerShift)
        (Z.postTop_eq_rectangleTop_add_shift 0)
    _ = (Z.rectangleLeftPlanePath 1 + shiftVector Z.topShift) +
        shiftVector Z.lowerShift := by
      rw [Z.rectangleLeft_target_eq_rectangleTop_source]
    _ = Z.rectangleLeftPlanePath 1 +
        (shiftVector Z.topShift + shiftVector Z.lowerShift) := by
      rw [add_assoc]

theorem rightVector_eq_bottomVector_add_lowerVector :
    shiftVector Z.rightShift = shiftVector Z.bottomShift + shiftVector Z.lowerShift := by
  apply add_left_cancel (a := Z.rectangleRightPlanePath 0)
  calc
    Z.rectangleRightPlanePath 0 + shiftVector Z.rightShift = Z.preRightPlanePath 0 :=
      (Z.preRight_eq_rectangleRight_add_shift 0).symm
    _ = Z.preLowerPlanePath 1 := Z.preLower_target_eq_preRight_source.symm
    _ = Z.postLowerPlanePath 1 + shiftVector Z.lowerShift :=
      Z.preLower_eq_postLower_add_shift 1
    _ = Z.postBottomPlanePath 1 + shiftVector Z.lowerShift := by
      rw [Z.postBottom_target_eq_postLower_target]
    _ = (Z.rectangleBottomPlanePath 1 + shiftVector Z.bottomShift) +
        shiftVector Z.lowerShift := by
      simpa only [shiftVector] using congrArg
        (fun x ↦ x + shiftVector Z.lowerShift)
        (Z.postBottom_eq_rectangleBottom_add_shift 1)
    _ = (Z.rectangleRightPlanePath 0 + shiftVector Z.bottomShift) +
        shiftVector Z.lowerShift := by
      rw [Z.rectangleRight_source_eq_rectangleBottom_target]
    _ = Z.rectangleRightPlanePath 0 +
        (shiftVector Z.bottomShift + shiftVector Z.lowerShift) := by
      rw [add_assoc]

theorem rightVector_eq_topVector_add_upperVector :
    shiftVector Z.rightShift = shiftVector Z.topShift + shiftVector Z.upperShift := by
  apply add_left_cancel (a := Z.rectangleRightPlanePath 1)
  calc
    Z.rectangleRightPlanePath 1 + shiftVector Z.rightShift = Z.preRightPlanePath 1 :=
      (Z.preRight_eq_rectangleRight_add_shift 1).symm
    _ = Z.preUpperPlanePath 0 := Z.preRight_target_eq_preUpper_source
    _ = Z.postUpperPlanePath 0 + shiftVector Z.upperShift :=
      Z.preUpper_eq_postUpper_add_shift 0
    _ = Z.postTopPlanePath 1 + shiftVector Z.upperShift := by
      rw [Z.postTop_target_eq_postUpper_source]
    _ = (Z.rectangleTopPlanePath 1 + shiftVector Z.topShift) +
        shiftVector Z.upperShift := by
      simpa only [shiftVector] using congrArg
        (fun x ↦ x + shiftVector Z.upperShift)
        (Z.postTop_eq_rectangleTop_add_shift 1)
    _ = (Z.rectangleRightPlanePath 1 + shiftVector Z.topShift) +
        shiftVector Z.upperShift := by
      rw [Z.rectangleTop_target_eq_rectangleRight_target]
    _ = Z.rectangleRightPlanePath 1 +
        (shiftVector Z.topShift + shiftVector Z.upperShift) := by
      rw [add_assoc]

/-- The pre-cycle copies of the left and right rectangle edges have the same deck shift. -/
theorem leftVector_eq_rightVector :
    EmbeddedTorusIntersectionCircle.torusLatticeVector Z.leftShift =
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.rightShift := by
  rw [WithLp.ext_iff]
  funext i
  have h₁ := congrArg (fun x : TorusCoveringPlane ↦ x i)
    Z.leftVector_eq_bottomVector_add_upperVector
  have h₂ := congrArg (fun x : TorusCoveringPlane ↦ x i)
    Z.leftVector_eq_topVector_add_lowerVector
  have h₃ := congrArg (fun x : TorusCoveringPlane ↦ x i)
    Z.rightVector_eq_bottomVector_add_lowerVector
  have h₄ := congrArg (fun x : TorusCoveringPlane ↦ x i)
    Z.rightVector_eq_topVector_add_upperVector
  change shiftVector Z.leftShift i =
    shiftVector Z.bottomShift i + shiftVector Z.upperShift i at h₁
  change shiftVector Z.leftShift i =
    shiftVector Z.topShift i + shiftVector Z.lowerShift i at h₂
  change shiftVector Z.rightShift i =
    shiftVector Z.bottomShift i + shiftVector Z.lowerShift i at h₃
  change shiftVector Z.rightShift i =
    shiftVector Z.topShift i + shiftVector Z.upperShift i at h₄
  change shiftVector Z.leftShift i = shiftVector Z.rightShift i
  linarith

end FourPortDiagonalPathSystem.ZeroWindingData
end Submission.Topology
