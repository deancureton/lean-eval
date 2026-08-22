import Submission.Topology.FourPortDiagonalShiftEquations

/-!
# Coherent plane paths for the diagonal four-port graph

The rectangle lift fixes the four port vertices.  The equality of the left and right deck
shifts lets us translate the two diagonal paths from the vertical-resolution lift onto those
same vertices.  All six resulting plane paths project to their prescribed torus paths.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy}

namespace FourPortDiagonalPathSystem.ZeroWindingData

variable {G : FourPortDiagonalPathSystem (transportedTorus Phi)}
variable (Z : G.ZeroWindingData)

private def commonShiftVector : TorusCoveringPlane :=
  EmbeddedTorusIntersectionCircle.torusLatticeVector Z.leftShift

/-- Lower-left vertex of the coherent plane graph. -/
def leftBottomLift : TorusCoveringPlane := Z.rectangleLeftPlanePath 0

/-- Upper-left vertex of the coherent plane graph. -/
def leftTopLift : TorusCoveringPlane := Z.rectangleLeftPlanePath 1

/-- Lower-right vertex of the coherent plane graph. -/
def rightBottomLift : TorusCoveringPlane := Z.rectangleRightPlanePath 0

/-- Upper-right vertex of the coherent plane graph. -/
def rightTopLift : TorusCoveringPlane := Z.rectangleRightPlanePath 1

/-- Left side of the coherent plane rectangle. -/
def coherentLeftPlanePath : Path Z.leftBottomLift Z.leftTopLift :=
  Z.rectangleLeftPlanePath

/-- Top side of the coherent plane rectangle. -/
def coherentTopPlanePath : Path Z.leftTopLift Z.rightTopLift :=
  Z.rectangleTopPlanePath.cast Z.rectangleLeft_target_eq_rectangleTop_source
    Z.rectangleTop_target_eq_rectangleRight_target.symm

/-- Bottom side of the coherent plane rectangle. -/
def coherentBottomPlanePath : Path Z.leftBottomLift Z.rightBottomLift :=
  Z.rectangleBottomPlanePath.cast
    Z.rectangleBottom_source_eq_rectangleLeft_source.symm
    Z.rectangleRight_source_eq_rectangleBottom_target

/-- Right side of the coherent plane rectangle. -/
def coherentRightPlanePath : Path Z.rightBottomLift Z.rightTopLift :=
  Z.rectangleRightPlanePath

private theorem preLower_source_sub_commonShift :
    Z.preLowerPlanePath 0 - commonShiftVector Z = Z.leftTopLift := by
  calc
    Z.preLowerPlanePath 0 - commonShiftVector Z =
        Z.preLeftPlanePath 1 - commonShiftVector Z := by
      rw [Z.preLeft_target_eq_preLower_source]
    _ = (Z.rectangleLeftPlanePath 1 + commonShiftVector Z) -
        commonShiftVector Z := by
      rw [Z.preLeft_eq_rectangleLeft_add_shift, commonShiftVector]
    _ = Z.leftTopLift := by simp [leftTopLift]

private theorem preLower_target_sub_commonShift :
    Z.preLowerPlanePath 1 - commonShiftVector Z = Z.rightBottomLift := by
  calc
    Z.preLowerPlanePath 1 - commonShiftVector Z =
        Z.preRightPlanePath 0 - commonShiftVector Z := by
      rw [Z.preLower_target_eq_preRight_source]
    _ = (Z.rectangleRightPlanePath 0 +
          EmbeddedTorusIntersectionCircle.torusLatticeVector Z.rightShift) -
        commonShiftVector Z := by
      rw [Z.preRight_eq_rectangleRight_add_shift]
    _ = (Z.rectangleRightPlanePath 0 + commonShiftVector Z) -
        commonShiftVector Z := by
      rw [← Z.leftVector_eq_rightVector, commonShiftVector]
    _ = Z.rightBottomLift := by simp [rightBottomLift]

private theorem preUpper_source_sub_commonShift :
    Z.preUpperPlanePath 0 - commonShiftVector Z = Z.rightTopLift := by
  calc
    Z.preUpperPlanePath 0 - commonShiftVector Z =
        Z.preRightPlanePath 1 - commonShiftVector Z := by
      rw [Z.preRight_target_eq_preUpper_source]
    _ = (Z.rectangleRightPlanePath 1 +
          EmbeddedTorusIntersectionCircle.torusLatticeVector Z.rightShift) -
        commonShiftVector Z := by
      rw [Z.preRight_eq_rectangleRight_add_shift]
    _ = (Z.rectangleRightPlanePath 1 + commonShiftVector Z) -
        commonShiftVector Z := by
      rw [← Z.leftVector_eq_rightVector, commonShiftVector]
    _ = Z.rightTopLift := by simp [rightTopLift]

private theorem preUpper_target_sub_commonShift :
    Z.preUpperPlanePath 1 - commonShiftVector Z = Z.leftBottomLift := by
  calc
    Z.preUpperPlanePath 1 - commonShiftVector Z =
        Z.preLeftPlanePath 0 - commonShiftVector Z := by
      rw [Z.preUpper_target_eq_preLeft_source]
    _ = (Z.rectangleLeftPlanePath 0 + commonShiftVector Z) -
        commonShiftVector Z := by
      rw [Z.preLeft_eq_rectangleLeft_add_shift, commonShiftVector]
    _ = Z.leftBottomLift := by simp [leftBottomLift]

/-- Lower diagonal translated onto the rectangle lift. -/
def coherentLowerPlanePath : Path Z.leftTopLift Z.rightBottomLift where
  toFun := fun t ↦ Z.preLowerPlanePath t - commonShiftVector Z
  continuous_toFun := Z.preLowerPlanePath.continuous.sub continuous_const
  source' := Z.preLower_source_sub_commonShift
  target' := Z.preLower_target_sub_commonShift

/-- Upper diagonal translated onto the rectangle lift. -/
def coherentUpperPlanePath : Path Z.rightTopLift Z.leftBottomLift where
  toFun := fun t ↦ Z.preUpperPlanePath t - commonShiftVector Z
  continuous_toFun := Z.preUpperPlanePath.continuous.sub continuous_const
  source' := Z.preUpper_source_sub_commonShift
  target' := Z.preUpper_target_sub_commonShift

private theorem neg_torusLatticeVector (k : Fin 2 → ℤ) :
    -EmbeddedTorusIntersectionCircle.torusLatticeVector k =
      EmbeddedTorusIntersectionCircle.torusLatticeVector (fun i ↦ -k i) := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp

private theorem projection_sub_lattice
    (x : TorusCoveringPlane) (k : Fin 2 → ℤ) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (x - EmbeddedTorusIntersectionCircle.torusLatticeVector k) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x := by
  rw [sub_eq_add_neg, neg_torusLatticeVector,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice]

@[simp] theorem projection_coherentLeftPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentLeftPlanePath t) = G.left t :=
  Z.projection_rectangleLeftPlanePath t

@[simp] theorem projection_coherentTopPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentTopPlanePath t) = G.top t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectangleTopPlanePath t) = G.top t
  exact Z.projection_rectangleTopPlanePath t

@[simp] theorem projection_coherentBottomPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentBottomPlanePath t) = G.bottom t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectangleBottomPlanePath t) = G.bottom t
  exact Z.projection_rectangleBottomPlanePath t

@[simp] theorem projection_coherentRightPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentRightPlanePath t) = G.right t :=
  Z.projection_rectangleRightPlanePath t

@[simp] theorem projection_coherentLowerPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentLowerPlanePath t) = G.lower t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.preLowerPlanePath t - commonShiftVector Z) = G.lower t
  unfold commonShiftVector
  rw [projection_sub_lattice, Z.projection_preLowerPlanePath]

@[simp] theorem projection_coherentUpperPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.coherentUpperPlanePath t) = G.upper t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.preUpperPlanePath t - commonShiftVector Z) = G.upper t
  unfold commonShiftVector
  rw [projection_sub_lattice, Z.projection_preUpperPlanePath]

theorem coherentLeftPlanePath_injective : Function.Injective Z.coherentLeftPlanePath := by
  intro s t hst
  apply G.left_injective
  rw [← Z.projection_coherentLeftPlanePath s,
    ← Z.projection_coherentLeftPlanePath t, hst]

theorem coherentTopPlanePath_injective : Function.Injective Z.coherentTopPlanePath := by
  intro s t hst
  apply G.top_injective
  rw [← Z.projection_coherentTopPlanePath s,
    ← Z.projection_coherentTopPlanePath t, hst]

theorem coherentBottomPlanePath_injective : Function.Injective Z.coherentBottomPlanePath := by
  intro s t hst
  apply G.bottom_injective
  rw [← Z.projection_coherentBottomPlanePath s,
    ← Z.projection_coherentBottomPlanePath t, hst]

theorem coherentRightPlanePath_injective : Function.Injective Z.coherentRightPlanePath := by
  intro s t hst
  apply G.right_injective
  rw [← Z.projection_coherentRightPlanePath s,
    ← Z.projection_coherentRightPlanePath t, hst]

theorem coherentLowerPlanePath_injective : Function.Injective Z.coherentLowerPlanePath := by
  intro s t hst
  apply G.lower_injective
  rw [← Z.projection_coherentLowerPlanePath s,
    ← Z.projection_coherentLowerPlanePath t, hst]

theorem coherentUpperPlanePath_injective : Function.Injective Z.coherentUpperPlanePath := by
  intro s t hst
  apply G.upper_injective
  rw [← Z.projection_coherentUpperPlanePath s,
    ← Z.projection_coherentUpperPlanePath t, hst]

end FourPortDiagonalPathSystem.ZeroWindingData
end Submission.Topology
