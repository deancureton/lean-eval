import Submission.Topology.FourPortSixEdgePlaneCircles

/-!
# The six coherent lifted edge paths

The aligned plane circles canonically restrict to six paths with four common lifted port
vertices.  Every path projects pointwise to its named torus edge.  These definitions expose the
actual four-vertex graph needed by the remaining planar rotation/face argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {G : FourPortSixEdgePathSystem (transportedTorus Phi)}

namespace FourPortSixEdgeZeroWindingData

variable (Z : FourPortSixEdgeZeroWindingData G)

def leftBottomLift : TorusCoveringPlane :=
  Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 1)

def leftTopLift : TorusCoveringPlane :=
  Z.centralPlaneCircle (centralTopOutsideParameter 1)

def rightBottomLift : TorusCoveringPlane :=
  Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 0)

def rightTopLift : TorusCoveringPlane :=
  Z.centralPlaneCircle (centralTopOutsideParameter 0)

private def centralLeftParameter (t : unitInterval) : Circle :=
  TwoArcCircle.firstCircleCoordinate
    (Schoenflies.ThreePiecePath.firstCoordinate t)

private def centralRightParameter (t : unitInterval) : Circle :=
  TwoArcCircle.firstCircleCoordinate
    (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t))

private theorem continuous_centralLeftParameter :
    Continuous centralLeftParameter := by
  have hfirst : Continuous Schoenflies.ThreePiecePath.firstCoordinate := by
    apply Continuous.subtype_mk
    fun_prop
  exact TorusThetaPathSystem.continuous_referenceParameter.comp hfirst

private theorem continuous_centralRightParameter :
    Continuous centralRightParameter := by
  have hthird : Continuous Schoenflies.ThreePiecePath.thirdCoordinate := by
    apply Continuous.subtype_mk
    fun_prop
  exact TorusThetaPathSystem.continuous_referenceParameter.comp <|
    hthird.comp unitInterval.continuous_symm

private theorem centralLeftParameter_zero :
    centralLeftParameter 0 = TwoArcCircle.secondCircleCoordinate 1 := by
  rw [← TwoArcCircle.firstCircleCoordinate_zero_eq_secondCircleCoordinate_one]
  apply Subtype.ext
  norm_num [centralLeftParameter, Schoenflies.ThreePiecePath.firstCoordinate]

private theorem centralLeftParameter_one :
    centralLeftParameter 1 = centralTopOutsideParameter 1 := by
  unfold centralLeftParameter centralTopOutsideParameter
  congr 1
  apply Subtype.ext
  norm_num [Schoenflies.ThreePiecePath.firstCoordinate,
    Schoenflies.ThreePiecePath.middleCoordinate]

private theorem centralRightParameter_zero :
    centralRightParameter 0 = TwoArcCircle.secondCircleCoordinate 0 := by
  rw [← TwoArcCircle.firstCircleCoordinate_one_eq_secondCircleCoordinate_zero]
  apply Subtype.ext
  norm_num [centralRightParameter, Schoenflies.ThreePiecePath.thirdCoordinate]

private theorem centralRightParameter_one :
    centralRightParameter 1 = centralTopOutsideParameter 0 := by
  unfold centralRightParameter centralTopOutsideParameter
  congr 1
  apply Subtype.ext
  norm_num [Schoenflies.ThreePiecePath.thirdCoordinate,
    Schoenflies.ThreePiecePath.middleCoordinate]

/-- Lift of the left vertical local edge. -/
def leftPlanePath : Path Z.leftBottomLift Z.leftTopLift where
  toFun := fun t ↦ Z.centralPlaneCircle (centralLeftParameter t)
  continuous_toFun := Z.continuous_centralPlaneCircle.comp
    continuous_centralLeftParameter
  source' := by
    change Z.centralPlaneCircle (centralLeftParameter 0) =
      Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 1)
    exact congrArg Z.centralPlaneCircle centralLeftParameter_zero
  target' := by
    change Z.centralPlaneCircle (centralLeftParameter 1) =
      Z.centralPlaneCircle (centralTopOutsideParameter 1)
    exact congrArg Z.centralPlaneCircle centralLeftParameter_one

/-- Lift of the right vertical local edge. -/
def rightPlanePath : Path Z.rightBottomLift Z.rightTopLift where
  toFun := fun t ↦ Z.centralPlaneCircle (centralRightParameter t)
  continuous_toFun := Z.continuous_centralPlaneCircle.comp
    continuous_centralRightParameter
  source' := by
    change Z.centralPlaneCircle (centralRightParameter 0) =
      Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 0)
    exact congrArg Z.centralPlaneCircle centralRightParameter_zero
  target' := by
    change Z.centralPlaneCircle (centralRightParameter 1) =
      Z.centralPlaneCircle (centralTopOutsideParameter 0)
    exact congrArg Z.centralPlaneCircle centralRightParameter_one

/-- Lift of the lower horizontal local edge, aligned through the lower outside edge. -/
def bottomPlanePath : Path Z.leftBottomLift Z.rightBottomLift where
  toFun := fun t ↦
    Z.alignedBottomPlaneCircle (TwoArcCircle.firstCircleCoordinate t)
  continuous_toFun := Z.continuous_alignedBottomPlaneCircle.comp
    TorusThetaPathSystem.continuous_referenceParameter
  source' := by
    rw [TwoArcCircle.firstCircleCoordinate_zero_eq_secondCircleCoordinate_one]
    exact (Z.alignedBottomOutside_eq_central 1).trans rfl
  target' := by
    rw [TwoArcCircle.firstCircleCoordinate_one_eq_secondCircleCoordinate_zero]
    exact (Z.alignedBottomOutside_eq_central 0).trans rfl

/-- Lift of the upper horizontal local edge, aligned through the upper outside edge. -/
def topPlanePath : Path Z.leftTopLift Z.rightTopLift where
  toFun := fun t ↦
    Z.alignedTopPlaneCircle (TwoArcCircle.firstCircleCoordinate t)
  continuous_toFun := Z.continuous_alignedTopPlaneCircle.comp
    TorusThetaPathSystem.continuous_referenceParameter
  source' := by
    rw [TwoArcCircle.firstCircleCoordinate_zero_eq_secondCircleCoordinate_one]
    exact (Z.alignedTopOutside_eq_central 1).trans rfl
  target' := by
    rw [TwoArcCircle.firstCircleCoordinate_one_eq_secondCircleCoordinate_zero]
    exact (Z.alignedTopOutside_eq_central 0).trans rfl

/-- Coherent lift of the lower outside edge. -/
def bottomOutsidePlanePath : Path Z.rightBottomLift Z.leftBottomLift where
  toFun := Z.bottomOutsidePlaneArc
  continuous_toFun := Z.continuous_centralPlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  source' := rfl
  target' := rfl

/-- Coherent lift of the upper outside edge. -/
def topOutsidePlanePath : Path Z.rightTopLift Z.leftTopLift where
  toFun := Z.topOutsidePlaneArc
  continuous_toFun := Z.continuous_centralPlaneCircle.comp
    continuous_centralTopOutsideParameter
  source' := rfl
  target' := rfl

@[simp] theorem projection_leftPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.leftPlanePath t) = G.left t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.centralPlaneCircle (centralLeftParameter t)) = G.left t
  rw [Z.projection_centralPlaneCircle,
    FourPortSixEdgePathSystem.centralCircle,
    centralLeftParameter,
    TwoArcCircle.circleMap_firstCircleCoordinate,
    fourPortCentralUpperPath,
    Schoenflies.ThreePiecePath.trans_trans_firstCoordinate]

@[simp] theorem projection_rightPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.rightPlanePath t) = G.right t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.centralPlaneCircle (centralRightParameter t)) = G.right t
  rw [Z.projection_centralPlaneCircle,
    FourPortSixEdgePathSystem.centralCircle,
    centralRightParameter,
    TwoArcCircle.circleMap_firstCircleCoordinate,
    fourPortCentralUpperPath,
    Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

@[simp] theorem projection_bottomPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.bottomPlanePath t) = G.bottom t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.alignedBottomPlaneCircle (TwoArcCircle.firstCircleCoordinate t)) = G.bottom t
  rw [Z.projection_alignedBottomPlaneCircle,
    FourPortSixEdgePathSystem.bottomCircle,
    TwoArcCircle.circleMap_firstCircleCoordinate]

@[simp] theorem projection_topPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.topPlanePath t) = G.top t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.alignedTopPlaneCircle (TwoArcCircle.firstCircleCoordinate t)) = G.top t
  rw [Z.projection_alignedTopPlaneCircle,
    FourPortSixEdgePathSystem.topCircle,
    TwoArcCircle.circleMap_firstCircleCoordinate]

@[simp] theorem projection_bottomOutsidePlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.bottomOutsidePlanePath t) = G.bottomOutside t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.bottomOutsidePlaneArc t) = G.bottomOutside t
  rw [bottomOutsidePlaneArc,
    Z.projection_centralPlaneCircle,
    FourPortSixEdgePathSystem.centralCircle,
    TwoArcCircle.circleMap_secondCircleCoordinate]

@[simp] theorem projection_topOutsidePlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.topOutsidePlanePath t) = G.topOutside t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
    (Z.topOutsidePlaneArc t) = G.topOutside t
  rw [topOutsidePlaneArc,
    Z.projection_centralPlaneCircle,
    centralCircle_centralTopOutsideParameter]

@[simp] theorem projection_centralUpperPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
          Z.rightPlanePath t) =
      fourPortCentralUpperPath G.left G.topOutside G.right t := by
  simp only [fourPortCentralUpperPath, Path.trans_apply]
  split_ifs <;>
    simp only [Path.symm_apply, Function.comp_apply,
      Z.projection_leftPlanePath, Z.projection_rightPlanePath,
      Z.projection_topOutsidePlanePath]

theorem leftPlanePath_injective : Function.Injective Z.leftPlanePath := by
  intro s t hst
  apply G.left_injective
  rw [← Z.projection_leftPlanePath s, ← Z.projection_leftPlanePath t, hst]

theorem rightPlanePath_injective : Function.Injective Z.rightPlanePath := by
  intro s t hst
  apply G.right_injective
  rw [← Z.projection_rightPlanePath s, ← Z.projection_rightPlanePath t, hst]

theorem bottomPlanePath_injective : Function.Injective Z.bottomPlanePath := by
  intro s t hst
  apply G.bottom_injective
  rw [← Z.projection_bottomPlanePath s, ← Z.projection_bottomPlanePath t, hst]

theorem topPlanePath_injective : Function.Injective Z.topPlanePath := by
  intro s t hst
  apply G.top_injective
  rw [← Z.projection_topPlanePath s, ← Z.projection_topPlanePath t, hst]

theorem bottomOutsidePlanePath_injective :
    Function.Injective Z.bottomOutsidePlanePath := by
  intro s t hst
  apply G.bottomOutside_injective
  rw [← Z.projection_bottomOutsidePlanePath s,
    ← Z.projection_bottomOutsidePlanePath t, hst]

theorem topOutsidePlanePath_injective :
    Function.Injective Z.topOutsidePlanePath := by
  intro s t hst
  apply G.topOutside_injective
  rw [← Z.projection_topOutsidePlanePath s,
    ← Z.projection_topOutsidePlanePath t, hst]

theorem centralUpperPlanePath_injective : Function.Injective
    (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
      Z.rightPlanePath) := by
  intro s t hst
  apply G.centralData.first_injective
  rw [← Z.projection_centralUpperPlanePath s,
    ← Z.projection_centralUpperPlanePath t, hst]

private theorem range_inter_of_projection
    {a b : TorusCoveringPlane} {a' b' : transportedTorus Phi}
    (p' : Path a b) (q' : Path b a) (p : Path a' b') (q : Path b' a')
    (D : TwoArcCircle.Data p q)
    (hp : ∀ t, EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (p' t) = p t)
    (hq : ∀ t, EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (q' t) = q t) :
    Set.range p' ∩ Set.range q' = {a, b} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hpq : p u = q v := by
      rw [← hp u, ← hq v, hu, hv]
    have hmem : p u ∈ Set.range p ∩ Set.range q :=
      ⟨⟨u, rfl⟩, ⟨v, hpq.symm⟩⟩
    rw [D.range_inter] at hmem
    rcases hmem with hfirst | hsecond
    · have hu0 : u = 0 := D.first_injective (hfirst.trans p.source.symm)
      left
      exact hu.symm.trans ((congrArg p' hu0).trans p'.source)
    · have hu1 : u = 1 := D.first_injective (hsecond.trans p.target.symm)
      right
      exact hu.symm.trans ((congrArg p' hu1).trans p'.target)
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨⟨0, p'.source⟩, ⟨1, q'.target⟩⟩
    · exact ⟨⟨1, p'.target⟩, ⟨0, q'.source⟩⟩

/-- The coherent lower pair retains the exact two-arc incidence. -/
theorem bottomPlaneData :
    TwoArcCircle.Data Z.bottomPlanePath Z.bottomOutsidePlanePath where
  first_injective := Z.bottomPlanePath_injective
  second_injective := Z.bottomOutsidePlanePath_injective
  range_inter := range_inter_of_projection _ _ G.bottom G.bottomOutside
    G.bottomData Z.projection_bottomPlanePath Z.projection_bottomOutsidePlanePath

/-- The coherent upper pair retains the exact two-arc incidence. -/
theorem topPlaneData : TwoArcCircle.Data Z.topPlanePath Z.topOutsidePlanePath where
  first_injective := Z.topPlanePath_injective
  second_injective := Z.topOutsidePlanePath_injective
  range_inter := range_inter_of_projection _ _ G.top G.topOutside
    G.topData Z.projection_topPlanePath Z.projection_topOutsidePlanePath

/-- The coherent central pair retains the exact two-arc incidence. -/
theorem centralPlaneData : TwoArcCircle.Data
    (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
      Z.rightPlanePath) Z.bottomOutsidePlanePath where
  first_injective := Z.centralUpperPlanePath_injective
  second_injective := Z.bottomOutsidePlanePath_injective
  range_inter := range_inter_of_projection _ _
    (fourPortCentralUpperPath G.left G.topOutside G.right) G.bottomOutside
    G.centralData Z.projection_centralUpperPlanePath
      Z.projection_bottomOutsidePlanePath

private theorem range_leftPlanePath_subset_centralPlaneCircle :
    Set.range Z.leftPlanePath ⊆ Set.range Z.centralPlaneCircle := by
  rintro _ ⟨t, rfl⟩
  exact ⟨centralLeftParameter t, rfl⟩

private theorem range_rightPlanePath_subset_centralPlaneCircle :
    Set.range Z.rightPlanePath ⊆ Set.range Z.centralPlaneCircle := by
  rintro _ ⟨t, rfl⟩
  exact ⟨centralRightParameter t, rfl⟩

private theorem range_bottomOutsidePlanePath_subset_centralPlaneCircle :
    Set.range Z.bottomOutsidePlanePath ⊆ Set.range Z.centralPlaneCircle := by
  rintro _ ⟨t, rfl⟩
  exact ⟨TwoArcCircle.secondCircleCoordinate t, rfl⟩

private theorem range_topOutsidePlanePath_subset_centralPlaneCircle :
    Set.range Z.topOutsidePlanePath ⊆ Set.range Z.centralPlaneCircle := by
  rintro _ ⟨t, rfl⟩
  exact ⟨centralTopOutsideParameter t, rfl⟩

private theorem centralPlaneCarrier_subset_centralPlaneCircle :
    Set.range (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
        Z.rightPlanePath) ∪ Set.range Z.bottomOutsidePlanePath ⊆
      Set.range Z.centralPlaneCircle := by
  simp only [fourPortCentralUpperPath, Path.trans_range, Path.symm_range]
  rintro x (((hx | hx) | hx) | hx)
  · exact Z.range_leftPlanePath_subset_centralPlaneCircle hx
  · exact Z.range_topOutsidePlanePath_subset_centralPlaneCircle hx
  · exact Z.range_rightPlanePath_subset_centralPlaneCircle hx
  · exact Z.range_bottomOutsidePlanePath_subset_centralPlaneCircle hx

private theorem bottomPlaneCarrier_subset_alignedBottomPlaneCircle :
    Set.range Z.bottomPlanePath ∪ Set.range Z.bottomOutsidePlanePath ⊆
      Set.range Z.alignedBottomPlaneCircle := by
  rintro x (hx | hx)
  · obtain ⟨t, rfl⟩ := hx
    exact ⟨TwoArcCircle.firstCircleCoordinate t, rfl⟩
  · obtain ⟨t, rfl⟩ := hx
    refine ⟨TwoArcCircle.secondCircleCoordinate t, ?_⟩
    exact Z.alignedBottomOutside_eq_central t

private theorem topPlaneCarrier_subset_alignedTopPlaneCircle :
    Set.range Z.topPlanePath ∪ Set.range Z.topOutsidePlanePath ⊆
      Set.range Z.alignedTopPlaneCircle := by
  rintro x (hx | hx)
  · obtain ⟨t, rfl⟩ := hx
    exact ⟨TwoArcCircle.firstCircleCoordinate t, rfl⟩
  · obtain ⟨t, rfl⟩ := hx
    refine ⟨TwoArcCircle.secondCircleCoordinate t, ?_⟩
    exact Z.alignedTopOutside_eq_central t

private theorem centralPlaneCarrier_inter_bottomPlaneCarrier :
    (Set.range (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
          Z.rightPlanePath) ∪ Set.range Z.bottomOutsidePlanePath) ∩
        (Set.range Z.bottomPlanePath ∪ Set.range Z.bottomOutsidePlanePath) =
      Set.range Z.bottomOutsidePlanePath := by
  apply Set.Subset.antisymm
  · intro x hx
    have hcircle : x ∈ Set.range Z.centralPlaneCircle ∩
        Set.range Z.alignedBottomPlaneCircle :=
      ⟨Z.centralPlaneCarrier_subset_centralPlaneCircle hx.1,
        Z.bottomPlaneCarrier_subset_alignedBottomPlaneCircle hx.2⟩
    rwa [Z.centralPlaneCircle_inter_alignedBottomPlaneCircle] at hcircle
  · intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩

private theorem centralPlaneCarrier_inter_topPlaneCarrier :
    (Set.range (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
          Z.rightPlanePath) ∪ Set.range Z.bottomOutsidePlanePath) ∩
        (Set.range Z.topPlanePath ∪ Set.range Z.topOutsidePlanePath) =
      Set.range Z.topOutsidePlanePath := by
  apply Set.Subset.antisymm
  · intro x hx
    have hcircle : x ∈ Set.range Z.centralPlaneCircle ∩
        Set.range Z.alignedTopPlaneCircle :=
      ⟨Z.centralPlaneCarrier_subset_centralPlaneCircle hx.1,
        Z.topPlaneCarrier_subset_alignedTopPlaneCircle hx.2⟩
    rwa [Z.centralPlaneCircle_inter_alignedTopPlaneCircle] at hcircle
  · intro x hx
    refine ⟨?_, Or.inr hx⟩
    rw [fourPortCentralUpperPath, Path.trans_range, Path.symm_range]
    have htop : x ∈ Set.range (Z.leftPlanePath.trans
        Z.topOutsidePlanePath.symm) := by
      rw [Path.trans_range, Path.symm_range]
      exact Or.inr hx
    exact Or.inl (Or.inl htop)

private theorem disjoint_bottomPlaneCarrier_topPlaneCarrier :
    Disjoint (Set.range Z.bottomPlanePath ∪ Set.range Z.bottomOutsidePlanePath)
      (Set.range Z.topPlanePath ∪ Set.range Z.topOutsidePlanePath) :=
  Z.disjoint_alignedBottomPlaneCircle_alignedTopPlaneCircle.mono
    Z.bottomPlaneCarrier_subset_alignedBottomPlaneCircle
    Z.topPlaneCarrier_subset_alignedTopPlaneCircle

/-- The six coherent lifts form the honest planar four-port graph. -/
def planePathSystem : FourPortSixEdgePathSystem TorusCoveringPlane where
  leftBottom := Z.leftBottomLift
  leftTop := Z.leftTopLift
  rightBottom := Z.rightBottomLift
  rightTop := Z.rightTopLift
  left := Z.leftPlanePath
  right := Z.rightPlanePath
  bottom := Z.bottomPlanePath
  top := Z.topPlanePath
  bottomOutside := Z.bottomOutsidePlanePath
  topOutside := Z.topOutsidePlanePath
  bottomData := Z.bottomPlaneData
  topData := Z.topPlaneData
  centralData := Z.centralPlaneData
  central_inter_bottom := Z.centralPlaneCarrier_inter_bottomPlaneCarrier
  central_inter_top := Z.centralPlaneCarrier_inter_topPlaneCarrier
  bottom_disjoint_top := Z.disjoint_bottomPlaneCarrier_topPlaneCarrier

end FourPortSixEdgeZeroWindingData
end Submission.Topology
