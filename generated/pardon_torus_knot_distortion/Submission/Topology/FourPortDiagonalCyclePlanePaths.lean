import Submission.Topology.CoherentThetaCoveringNeighborhood
import Submission.Topology.FourPortDiagonalTorusCycles

/-!
# Plane paths from the three diagonal four-port cycles

The zero-winding vertical, horizontal, and rectangle cycles have canonical closed lifts to the
torus covering plane.  Restricting those lifts to the path coordinates of their constituent
edges gives the twelve raw plane paths used by the subsequent deck-alignment argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

namespace TwoPiecePath

/-- Parameter on `p.trans q` corresponding to `p`. -/
def firstCoordinate (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩

/-- Parameter on `p.trans q` corresponding to `q`. -/
def secondCoordinate (t : unitInterval) : unitInterval :=
  ⟨1 / 2 + (t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩

theorem continuous_firstCoordinate : Continuous firstCoordinate := by
  apply Continuous.subtype_mk
  fun_prop

theorem continuous_secondCoordinate : Continuous secondCoordinate := by
  apply Continuous.subtype_mk
  fun_prop

theorem trans_firstCoordinate {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (firstCoordinate t) = p t := by
  rw [Path.trans_apply, dif_pos (by
    change (t : ℝ) / 2 ≤ 1 / 2
    nlinarith [t.2.2])]
  congr 1
  apply Subtype.ext
  simp only [firstCoordinate]
  ring

theorem trans_secondCoordinate {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (secondCoordinate t) = q t := by
  by_cases ht : t = 0
  · subst t
    rw [Path.trans_apply, dif_pos (by norm_num [secondCoordinate])]
    calc
      p ⟨2 * (secondCoordinate 0 : ℝ), by norm_num [secondCoordinate]⟩ = p 1 := by
        congr 1
        apply Subtype.ext
        norm_num [secondCoordinate]
      _ = q 0 := p.target.trans q.source.symm
  · have htpos : 0 < (t : ℝ) :=
      lt_of_le_of_ne t.2.1 (fun h ↦ ht (Subtype.ext h.symm))
    rw [Path.trans_apply, dif_neg (by
      change ¬(1 / 2 + (t : ℝ) / 2 ≤ 1 / 2)
      nlinarith)]
    congr 1
    apply Subtype.ext
    simp only [secondCoordinate]
    ring

end TwoPiecePath

variable {Phi : AmbientIsotopy}

namespace FourPortDiagonalPathSystem.ZeroWindingData

variable {G : FourPortDiagonalPathSystem (transportedTorus Phi)}
variable (Z : G.ZeroWindingData)

/-- Closed plane lift of the vertical-resolution cycle. -/
def prePlaneCircle : Circle → TorusCoveringPlane :=
  G.preTorusCircle.zeroWindingPlaneCircle Z.pre

/-- Closed plane lift of the horizontal-resolution cycle. -/
def postPlaneCircle : Circle → TorusCoveringPlane :=
  G.postTorusCircle.zeroWindingPlaneCircle Z.post

/-- Closed plane lift of the local rectangle cycle. -/
def rectanglePlaneCircle : Circle → TorusCoveringPlane :=
  G.rectangleTorusCircle.zeroWindingPlaneCircle Z.rectangle

theorem continuous_prePlaneCircle : Continuous Z.prePlaneCircle :=
  G.preTorusCircle.continuous_zeroWindingPlaneCircle Z.pre

theorem continuous_postPlaneCircle : Continuous Z.postPlaneCircle :=
  G.postTorusCircle.continuous_zeroWindingPlaneCircle Z.post

theorem continuous_rectanglePlaneCircle : Continuous Z.rectanglePlaneCircle :=
  G.rectangleTorusCircle.continuous_zeroWindingPlaneCircle Z.rectangle

@[simp] theorem projection_prePlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.prePlaneCircle z) = G.preCircle z := by
  apply Subtype.ext
  exact G.preTorusCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.pre z

@[simp] theorem projection_postPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.postPlaneCircle z) = G.postCircle z := by
  apply Subtype.ext
  exact G.postTorusCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.post z

@[simp] theorem projection_rectanglePlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rectanglePlaneCircle z) = G.rectangleCircle z := by
  apply Subtype.ext
  exact G.rectangleTorusCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.rectangle z

private theorem continuous_threeFirst :
    Continuous Schoenflies.ThreePiecePath.firstCoordinate := by
  apply Continuous.subtype_mk
  fun_prop

private theorem continuous_threeMiddle :
    Continuous Schoenflies.ThreePiecePath.middleCoordinate := by
  apply Continuous.subtype_mk
  fun_prop

private theorem continuous_threeThird :
    Continuous Schoenflies.ThreePiecePath.thirdCoordinate := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] private theorem referenceParameter_eq_firstCircleCoordinate
    (t : unitInterval) :
    TorusThetaPathSystem.referenceParameter t = TwoArcCircle.firstCircleCoordinate t :=
  rfl

@[simp] private theorem otherParameter_eq_secondCircleCoordinate
    (t : unitInterval) :
    TorusThetaPathSystem.otherParameter t = TwoArcCircle.secondCircleCoordinate t :=
  rfl

private def preFirstParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.firstCoordinate t)

private def preMiddleParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.middleCoordinate t)

private def preThirdParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.thirdCoordinate t)

private theorem continuous_preFirstParameter : Continuous preFirstParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp continuous_threeFirst

private theorem continuous_preMiddleParameter : Continuous preMiddleParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp continuous_threeMiddle

private theorem continuous_preThirdParameter : Continuous preThirdParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp continuous_threeThird

/-- Lift of the left edge as it occurs in the vertical-resolution cycle. -/
def preLeftPlanePath : Path
    (Z.prePlaneCircle (preFirstParameter 0))
    (Z.prePlaneCircle (preFirstParameter 1)) where
  toFun := fun t ↦ Z.prePlaneCircle (preFirstParameter t)
  continuous_toFun := Z.continuous_prePlaneCircle.comp continuous_preFirstParameter
  source' := rfl
  target' := rfl

/-- Lift of the lower diagonal as it occurs in the vertical-resolution cycle. -/
def preLowerPlanePath : Path
    (Z.prePlaneCircle (preMiddleParameter 0))
    (Z.prePlaneCircle (preMiddleParameter 1)) where
  toFun := fun t ↦ Z.prePlaneCircle (preMiddleParameter t)
  continuous_toFun := Z.continuous_prePlaneCircle.comp continuous_preMiddleParameter
  source' := rfl
  target' := rfl

/-- Lift of the right edge as it occurs in the vertical-resolution cycle. -/
def preRightPlanePath : Path
    (Z.prePlaneCircle (preThirdParameter 0))
    (Z.prePlaneCircle (preThirdParameter 1)) where
  toFun := fun t ↦ Z.prePlaneCircle (preThirdParameter t)
  continuous_toFun := Z.continuous_prePlaneCircle.comp continuous_preThirdParameter
  source' := rfl
  target' := rfl

/-- Lift of the upper diagonal as it occurs in the vertical-resolution cycle. -/
def preUpperPlanePath : Path
    (Z.prePlaneCircle (TorusThetaPathSystem.otherParameter 0))
    (Z.prePlaneCircle (TorusThetaPathSystem.otherParameter 1)) where
  toFun := fun t ↦ Z.prePlaneCircle (TorusThetaPathSystem.otherParameter t)
  continuous_toFun := Z.continuous_prePlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  source' := rfl
  target' := rfl

@[simp] theorem projection_preLeftPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.preLeftPlanePath t) = G.left t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.prePlaneCircle (preFirstParameter t)) = G.left t
  rw [Z.projection_prePlaneCircle, FourPortDiagonalPathSystem.preCircle,
    preFirstParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.preFirst,
    Schoenflies.ThreePiecePath.trans_trans_firstCoordinate]

@[simp] theorem projection_preLowerPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.preLowerPlanePath t) = G.lower t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.prePlaneCircle (preMiddleParameter t)) = G.lower t
  rw [Z.projection_prePlaneCircle, FourPortDiagonalPathSystem.preCircle,
    preMiddleParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.preFirst,
    Schoenflies.ThreePiecePath.trans_trans_middleCoordinate]

@[simp] theorem projection_preRightPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.preRightPlanePath t) = G.right t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.prePlaneCircle (preThirdParameter t)) = G.right t
  rw [Z.projection_prePlaneCircle, FourPortDiagonalPathSystem.preCircle,
    preThirdParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.preFirst,
    Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]

@[simp] theorem projection_preUpperPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.preUpperPlanePath t) = G.upper t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.prePlaneCircle (TorusThetaPathSystem.otherParameter t)) = G.upper t
  rw [Z.projection_prePlaneCircle, FourPortDiagonalPathSystem.preCircle,
    otherParameter_eq_secondCircleCoordinate,
    TwoArcCircle.circleMap_secondCircleCoordinate]

private def postFirstParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.firstCoordinate t)

private def postMiddleReverseParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.middleCoordinate (unitInterval.symm t))

private def postThirdParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter
    (Schoenflies.ThreePiecePath.thirdCoordinate t)

private theorem continuous_postFirstParameter : Continuous postFirstParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp continuous_threeFirst

private theorem continuous_postMiddleReverseParameter :
    Continuous postMiddleReverseParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp <|
    continuous_threeMiddle.comp unitInterval.continuous_symm

private theorem continuous_postThirdParameter : Continuous postThirdParameter :=
  TorusThetaPathSystem.continuous_referenceParameter.comp continuous_threeThird

/-- Lift of the bottom edge as it occurs in the horizontal-resolution cycle. -/
def postBottomPlanePath : Path
    (Z.postPlaneCircle (postFirstParameter 0))
    (Z.postPlaneCircle (postFirstParameter 1)) where
  toFun := fun t ↦ Z.postPlaneCircle (postFirstParameter t)
  continuous_toFun := Z.continuous_postPlaneCircle.comp continuous_postFirstParameter
  source' := rfl
  target' := rfl

/-- The horizontal-cycle lift of the lower diagonal, reoriented from left-top to right-bottom. -/
def postLowerPlanePath : Path
    (Z.postPlaneCircle (postMiddleReverseParameter 0))
    (Z.postPlaneCircle (postMiddleReverseParameter 1)) where
  toFun := fun t ↦ Z.postPlaneCircle (postMiddleReverseParameter t)
  continuous_toFun := Z.continuous_postPlaneCircle.comp
    continuous_postMiddleReverseParameter
  source' := rfl
  target' := rfl

/-- Lift of the top edge as it occurs in the horizontal-resolution cycle. -/
def postTopPlanePath : Path
    (Z.postPlaneCircle (postThirdParameter 0))
    (Z.postPlaneCircle (postThirdParameter 1)) where
  toFun := fun t ↦ Z.postPlaneCircle (postThirdParameter t)
  continuous_toFun := Z.continuous_postPlaneCircle.comp continuous_postThirdParameter
  source' := rfl
  target' := rfl

/-- Lift of the upper diagonal as it occurs in the horizontal-resolution cycle. -/
def postUpperPlanePath : Path
    (Z.postPlaneCircle (TorusThetaPathSystem.otherParameter 0))
    (Z.postPlaneCircle (TorusThetaPathSystem.otherParameter 1)) where
  toFun := fun t ↦ Z.postPlaneCircle (TorusThetaPathSystem.otherParameter t)
  continuous_toFun := Z.continuous_postPlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  source' := rfl
  target' := rfl

@[simp] theorem projection_postBottomPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.postBottomPlanePath t) = G.bottom t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.postPlaneCircle (postFirstParameter t)) = G.bottom t
  rw [Z.projection_postPlaneCircle, FourPortDiagonalPathSystem.postCircle,
    postFirstParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.postFirst,
    Schoenflies.ThreePiecePath.trans_trans_firstCoordinate]

@[simp] theorem projection_postLowerPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.postLowerPlanePath t) = G.lower t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.postPlaneCircle (postMiddleReverseParameter t)) = G.lower t
  rw [Z.projection_postPlaneCircle, FourPortDiagonalPathSystem.postCircle,
    postMiddleReverseParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.postFirst,
    Schoenflies.ThreePiecePath.trans_trans_middleCoordinate]
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

@[simp] theorem projection_postTopPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.postTopPlanePath t) = G.top t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.postPlaneCircle (postThirdParameter t)) = G.top t
  rw [Z.projection_postPlaneCircle, FourPortDiagonalPathSystem.postCircle,
    postThirdParameter, referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate, FourPortDiagonalPathSystem.postFirst,
    Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]

@[simp] theorem projection_postUpperPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.postUpperPlanePath t) = G.upper t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.postPlaneCircle (TorusThetaPathSystem.otherParameter t)) = G.upper t
  rw [Z.projection_postPlaneCircle, FourPortDiagonalPathSystem.postCircle,
    otherParameter_eq_secondCircleCoordinate,
    TwoArcCircle.circleMap_secondCircleCoordinate]

private def rectangleLeftParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter (TwoPiecePath.firstCoordinate t)

private def rectangleTopParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.referenceParameter (TwoPiecePath.secondCoordinate t)

private def rectangleBottomParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.otherParameter
    (unitInterval.symm (TwoPiecePath.firstCoordinate t))

private def rectangleRightParameter (t : unitInterval) : Circle :=
  TorusThetaPathSystem.otherParameter
    (unitInterval.symm (TwoPiecePath.secondCoordinate t))

/-- Rectangle-cycle lift of the left edge. -/
def rectangleLeftPlanePath : Path
    (Z.rectanglePlaneCircle (rectangleLeftParameter 0))
    (Z.rectanglePlaneCircle (rectangleLeftParameter 1)) where
  toFun := fun t ↦ Z.rectanglePlaneCircle (rectangleLeftParameter t)
  continuous_toFun := Z.continuous_rectanglePlaneCircle.comp <|
    TorusThetaPathSystem.continuous_referenceParameter.comp
      TwoPiecePath.continuous_firstCoordinate
  source' := rfl
  target' := rfl

/-- Rectangle-cycle lift of the top edge. -/
def rectangleTopPlanePath : Path
    (Z.rectanglePlaneCircle (rectangleTopParameter 0))
    (Z.rectanglePlaneCircle (rectangleTopParameter 1)) where
  toFun := fun t ↦ Z.rectanglePlaneCircle (rectangleTopParameter t)
  continuous_toFun := Z.continuous_rectanglePlaneCircle.comp <|
    TorusThetaPathSystem.continuous_referenceParameter.comp
      TwoPiecePath.continuous_secondCoordinate
  source' := rfl
  target' := rfl

/-- Rectangle-cycle lift of the bottom edge in its left-to-right orientation. -/
def rectangleBottomPlanePath : Path
    (Z.rectanglePlaneCircle (rectangleBottomParameter 0))
    (Z.rectanglePlaneCircle (rectangleBottomParameter 1)) where
  toFun := fun t ↦ Z.rectanglePlaneCircle (rectangleBottomParameter t)
  continuous_toFun := Z.continuous_rectanglePlaneCircle.comp <|
    TorusThetaPathSystem.continuous_otherParameter.comp <|
      unitInterval.continuous_symm.comp TwoPiecePath.continuous_firstCoordinate
  source' := rfl
  target' := rfl

/-- Rectangle-cycle lift of the right edge in its bottom-to-top orientation. -/
def rectangleRightPlanePath : Path
    (Z.rectanglePlaneCircle (rectangleRightParameter 0))
    (Z.rectanglePlaneCircle (rectangleRightParameter 1)) where
  toFun := fun t ↦ Z.rectanglePlaneCircle (rectangleRightParameter t)
  continuous_toFun := Z.continuous_rectanglePlaneCircle.comp <|
    TorusThetaPathSystem.continuous_otherParameter.comp <|
      unitInterval.continuous_symm.comp TwoPiecePath.continuous_secondCoordinate
  source' := rfl
  target' := rfl

@[simp] theorem projection_rectangleLeftPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rectangleLeftPlanePath t) = G.left t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectanglePlaneCircle (rectangleLeftParameter t)) = G.left t
  rw [Z.projection_rectanglePlaneCircle,
    FourPortDiagonalPathSystem.rectangleCircle, rectangleLeftParameter,
    referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate,
    FourPortDiagonalPathSystem.rectangleFirst, TwoPiecePath.trans_firstCoordinate]

@[simp] theorem projection_rectangleTopPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rectangleTopPlanePath t) = G.top t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectanglePlaneCircle (rectangleTopParameter t)) = G.top t
  rw [Z.projection_rectanglePlaneCircle,
    FourPortDiagonalPathSystem.rectangleCircle, rectangleTopParameter,
    referenceParameter_eq_firstCircleCoordinate,
    TwoArcCircle.circleMap_firstCircleCoordinate,
    FourPortDiagonalPathSystem.rectangleFirst, TwoPiecePath.trans_secondCoordinate]

@[simp] theorem projection_rectangleBottomPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rectangleBottomPlanePath t) = G.bottom t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectanglePlaneCircle (rectangleBottomParameter t)) = G.bottom t
  rw [Z.projection_rectanglePlaneCircle,
    FourPortDiagonalPathSystem.rectangleCircle, rectangleBottomParameter,
    otherParameter_eq_secondCircleCoordinate,
    TwoArcCircle.circleMap_secondCircleCoordinate,
    FourPortDiagonalPathSystem.rectangleSecond]
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
  exact TwoPiecePath.trans_firstCoordinate G.bottom G.right t

@[simp] theorem projection_rectangleRightPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rectangleRightPlanePath t) = G.right t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.rectanglePlaneCircle (rectangleRightParameter t)) = G.right t
  rw [Z.projection_rectanglePlaneCircle,
    FourPortDiagonalPathSystem.rectangleCircle, rectangleRightParameter,
    otherParameter_eq_secondCircleCoordinate,
    TwoArcCircle.circleMap_secondCircleCoordinate,
    FourPortDiagonalPathSystem.rectangleSecond]
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
  exact TwoPiecePath.trans_secondCoordinate G.bottom G.right t

theorem preLeft_target_eq_preLower_source :
    Z.preLeftPlanePath 1 = Z.preLowerPlanePath 0 := by
  apply congrArg Z.prePlaneCircle
  apply congrArg TorusThetaPathSystem.referenceParameter
  apply Subtype.ext
  norm_num [Schoenflies.ThreePiecePath.firstCoordinate,
    Schoenflies.ThreePiecePath.middleCoordinate]

theorem preLower_target_eq_preRight_source :
    Z.preLowerPlanePath 1 = Z.preRightPlanePath 0 := by
  apply congrArg Z.prePlaneCircle
  apply congrArg TorusThetaPathSystem.referenceParameter
  apply Subtype.ext
  norm_num [Schoenflies.ThreePiecePath.middleCoordinate,
    Schoenflies.ThreePiecePath.thirdCoordinate]

theorem preRight_target_eq_preUpper_source :
    Z.preRightPlanePath 1 = Z.preUpperPlanePath 0 := by
  change Z.prePlaneCircle (preThirdParameter 1) =
    Z.prePlaneCircle (TorusThetaPathSystem.otherParameter 0)
  rw [preThirdParameter, referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  have hthird : Schoenflies.ThreePiecePath.thirdCoordinate 1 = 1 := by
    apply Subtype.ext
    norm_num [Schoenflies.ThreePiecePath.thirdCoordinate]
  rw [hthird]
  rw [TwoArcCircle.firstCircleCoordinate_one_eq_secondCircleCoordinate_zero]

theorem preUpper_target_eq_preLeft_source :
    Z.preUpperPlanePath 1 = Z.preLeftPlanePath 0 := by
  change Z.prePlaneCircle (TorusThetaPathSystem.otherParameter 1) =
    Z.prePlaneCircle (preFirstParameter 0)
  rw [preFirstParameter, referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  have hfirst : Schoenflies.ThreePiecePath.firstCoordinate 0 = 0 := by
    apply Subtype.ext
    norm_num [Schoenflies.ThreePiecePath.firstCoordinate]
  rw [hfirst]
  rw [TwoArcCircle.firstCircleCoordinate_zero_eq_secondCircleCoordinate_one]

theorem postBottom_target_eq_postLower_target :
    Z.postBottomPlanePath 1 = Z.postLowerPlanePath 1 := by
  apply congrArg Z.postPlaneCircle
  apply congrArg TorusThetaPathSystem.referenceParameter
  apply Subtype.ext
  norm_num [postFirstParameter, postMiddleReverseParameter,
    Schoenflies.ThreePiecePath.firstCoordinate,
    Schoenflies.ThreePiecePath.middleCoordinate, unitInterval.symm]

theorem postLower_source_eq_postTop_source :
    Z.postLowerPlanePath 0 = Z.postTopPlanePath 0 := by
  apply congrArg Z.postPlaneCircle
  apply congrArg TorusThetaPathSystem.referenceParameter
  apply Subtype.ext
  norm_num [postMiddleReverseParameter, postThirdParameter,
    Schoenflies.ThreePiecePath.middleCoordinate,
    Schoenflies.ThreePiecePath.thirdCoordinate, unitInterval.symm]

theorem postTop_target_eq_postUpper_source :
    Z.postTopPlanePath 1 = Z.postUpperPlanePath 0 := by
  change Z.postPlaneCircle (postThirdParameter 1) =
    Z.postPlaneCircle (TorusThetaPathSystem.otherParameter 0)
  rw [postThirdParameter, referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  have hthird : Schoenflies.ThreePiecePath.thirdCoordinate 1 = 1 := by
    apply Subtype.ext
    norm_num [Schoenflies.ThreePiecePath.thirdCoordinate]
  rw [hthird]
  rw [TwoArcCircle.firstCircleCoordinate_one_eq_secondCircleCoordinate_zero]

theorem postUpper_target_eq_postBottom_source :
    Z.postUpperPlanePath 1 = Z.postBottomPlanePath 0 := by
  change Z.postPlaneCircle (TorusThetaPathSystem.otherParameter 1) =
    Z.postPlaneCircle (postFirstParameter 0)
  rw [postFirstParameter, referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  have hfirst : Schoenflies.ThreePiecePath.firstCoordinate 0 = 0 := by
    apply Subtype.ext
    norm_num [Schoenflies.ThreePiecePath.firstCoordinate]
  rw [hfirst]
  rw [TwoArcCircle.firstCircleCoordinate_zero_eq_secondCircleCoordinate_one]

theorem rectangleLeft_target_eq_rectangleTop_source :
    Z.rectangleLeftPlanePath 1 = Z.rectangleTopPlanePath 0 := by
  apply congrArg Z.rectanglePlaneCircle
  apply congrArg TorusThetaPathSystem.referenceParameter
  apply Subtype.ext
  norm_num [TwoPiecePath.firstCoordinate, TwoPiecePath.secondCoordinate]

theorem rectangleTop_target_eq_rectangleRight_target :
    Z.rectangleTopPlanePath 1 = Z.rectangleRightPlanePath 1 := by
  change Z.rectanglePlaneCircle (rectangleTopParameter 1) =
    Z.rectanglePlaneCircle (rectangleRightParameter 1)
  rw [rectangleTopParameter, rectangleRightParameter,
    referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  congr 1
  apply Subtype.ext
  norm_num [TwoPiecePath.secondCoordinate, unitInterval.symm]

theorem rectangleRight_source_eq_rectangleBottom_target :
    Z.rectangleRightPlanePath 0 = Z.rectangleBottomPlanePath 1 := by
  apply congrArg Z.rectanglePlaneCircle
  apply congrArg TorusThetaPathSystem.otherParameter
  congr 1
  apply Subtype.ext
  norm_num [TwoPiecePath.firstCoordinate, TwoPiecePath.secondCoordinate,
    unitInterval.symm]

theorem rectangleBottom_source_eq_rectangleLeft_source :
    Z.rectangleBottomPlanePath 0 = Z.rectangleLeftPlanePath 0 := by
  change Z.rectanglePlaneCircle (rectangleBottomParameter 0) =
    Z.rectanglePlaneCircle (rectangleLeftParameter 0)
  rw [rectangleBottomParameter, rectangleLeftParameter,
    referenceParameter_eq_firstCircleCoordinate,
    otherParameter_eq_secondCircleCoordinate]
  congr 1
  apply Subtype.ext
  norm_num [TwoPiecePath.firstCoordinate, unitInterval.symm]

end FourPortDiagonalPathSystem.ZeroWindingData
end Submission.Topology
