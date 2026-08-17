import Submission.Topology.CoherentThetaCanonicalCircles
import Submission.Topology.CoordinatePlaneIntersectionCircles

/-!
# The honest six-edge graph of a four-port move

The union of one central endpoint circle and its two split children is not a theta graph.  It has
four port vertices and six edges: four local rectangle sides and two outside arcs.  The central
cycle shares one outside arc with each child, while the two child cycles are disjoint.

This file packages exactly that path-level object.  It makes no outer-face or disk-side claim.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X]

/-- The upper route of the central circle, from the lower-left to the lower-right port. -/
def fourPortCentralUpperPath
    {leftBottom leftTop rightBottom rightTop : X}
    (left : Path leftBottom leftTop)
    (topOutside : Path rightTop leftTop)
    (right : Path rightBottom rightTop) : Path leftBottom rightBottom :=
  (left.trans topOutside.symm).trans right.symm

/-- Six paths forming the exact raw graph of one four-port split or merge.

The `TwoArcCircle.Data` fields are the local embedding facts for the three raw cycles.  The last
three fields retain their exact global incidence: the central cycle shares precisely one outside
arc with each child, and the two children are disjoint. -/
structure FourPortSixEdgePathSystem (X : Type*) [TopologicalSpace X] where
  leftBottom : X
  leftTop : X
  rightBottom : X
  rightTop : X
  left : Path leftBottom leftTop
  right : Path rightBottom rightTop
  bottom : Path leftBottom rightBottom
  top : Path leftTop rightTop
  bottomOutside : Path rightBottom leftBottom
  topOutside : Path rightTop leftTop
  bottomData : TwoArcCircle.Data bottom bottomOutside
  topData : TwoArcCircle.Data top topOutside
  centralData : TwoArcCircle.Data
    (fourPortCentralUpperPath left topOutside right) bottomOutside
  central_inter_bottom :
    (Set.range (fourPortCentralUpperPath left topOutside right) ∪
        Set.range bottomOutside) ∩
      (Set.range bottom ∪ Set.range bottomOutside) = Set.range bottomOutside
  central_inter_top :
    (Set.range (fourPortCentralUpperPath left topOutside right) ∪
        Set.range bottomOutside) ∩
      (Set.range top ∪ Set.range topOutside) = Set.range topOutside
  bottom_disjoint_top :
    Disjoint (Set.range bottom ∪ Set.range bottomOutside)
      (Set.range top ∪ Set.range topOutside)

namespace FourPortSixEdgePathSystem

variable (G : FourPortSixEdgePathSystem X)

/-- The raw central circle. -/
def centralCircle : Circle → X :=
  TwoArcCircle.circleMap
    (fourPortCentralUpperPath G.left G.topOutside G.right) G.bottomOutside

/-- The raw lower child circle. -/
def bottomCircle : Circle → X :=
  TwoArcCircle.circleMap G.bottom G.bottomOutside

/-- The raw upper child circle. -/
def topCircle : Circle → X :=
  TwoArcCircle.circleMap G.top G.topOutside

theorem continuous_centralCircle : Continuous G.centralCircle :=
  TwoArcCircle.continuous_circleMap _ _

theorem continuous_bottomCircle : Continuous G.bottomCircle :=
  TwoArcCircle.continuous_circleMap _ _

theorem continuous_topCircle : Continuous G.topCircle :=
  TwoArcCircle.continuous_circleMap _ _

theorem centralCircle_injective : Function.Injective G.centralCircle :=
  G.centralData.injective

theorem bottomCircle_injective : Function.Injective G.bottomCircle :=
  G.bottomData.injective

theorem topCircle_injective : Function.Injective G.topCircle :=
  G.topData.injective

theorem left_injective : Function.Injective G.left := by
  intro s t hst
  have hroute :
      fourPortCentralUpperPath G.left G.topOutside G.right
          (Schoenflies.ThreePiecePath.firstCoordinate s) =
        fourPortCentralUpperPath G.left G.topOutside G.right
          (Schoenflies.ThreePiecePath.firstCoordinate t) := by
    simpa only [fourPortCentralUpperPath,
      Schoenflies.ThreePiecePath.trans_trans_firstCoordinate] using hst
  have hcoordinate := G.centralData.first_injective hroute
  apply Subtype.ext
  have hvalue := congrArg Subtype.val hcoordinate
  simpa only [Schoenflies.ThreePiecePath.firstCoordinate,
    Subtype.coe_mk, div_left_inj' (by norm_num : (4 : ℝ) ≠ 0)] using hvalue

theorem right_injective : Function.Injective G.right := by
  intro s t hst
  have hroute :
      fourPortCentralUpperPath G.left G.topOutside G.right
          (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm s)) =
        fourPortCentralUpperPath G.left G.topOutside G.right
          (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t)) := by
    calc
      _ = G.right s := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
        simp only [Path.symm_apply, Function.comp_apply,
          unitInterval.symm_symm]
      _ = G.right t := hst
      _ = _ := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
        simp only [Path.symm_apply, Function.comp_apply,
          unitInterval.symm_symm]
  have hcoordinate := G.centralData.first_injective hroute
  apply Subtype.ext
  have hvalue := congrArg Subtype.val hcoordinate
  dsimp only [Schoenflies.ThreePiecePath.thirdCoordinate,
    unitInterval.symm] at hvalue
  linarith

theorem bottom_injective : Function.Injective G.bottom :=
  G.bottomData.first_injective

theorem top_injective : Function.Injective G.top :=
  G.topData.first_injective

theorem bottomOutside_injective : Function.Injective G.bottomOutside :=
  G.bottomData.second_injective

theorem topOutside_injective : Function.Injective G.topOutside :=
  G.topData.second_injective

@[simp] theorem range_centralCircle : Set.range G.centralCircle =
    Set.range (fourPortCentralUpperPath G.left G.topOutside G.right) ∪
      Set.range G.bottomOutside :=
  TwoArcCircle.range_circleMap _ _

@[simp] theorem range_bottomCircle : Set.range G.bottomCircle =
    Set.range G.bottom ∪ Set.range G.bottomOutside :=
  TwoArcCircle.range_circleMap _ _

@[simp] theorem range_topCircle : Set.range G.topCircle =
    Set.range G.top ∪ Set.range G.topOutside :=
  TwoArcCircle.range_circleMap _ _

/-- The central and lower child carriers share exactly the lower outside arc. -/
theorem centralCircle_inter_bottomCircle :
    Set.range G.centralCircle ∩ Set.range G.bottomCircle =
      Set.range G.bottomOutside := by
  rw [G.range_centralCircle, G.range_bottomCircle]
  exact G.central_inter_bottom

/-- The central and upper child carriers share exactly the upper outside arc. -/
theorem centralCircle_inter_topCircle :
    Set.range G.centralCircle ∩ Set.range G.topCircle =
      Set.range G.topOutside := by
  rw [G.range_centralCircle, G.range_topCircle]
  exact G.central_inter_top

/-- Unlike theta cycles, the two child carriers are disjoint. -/
theorem bottomCircle_disjoint_topCircle :
    Disjoint (Set.range G.bottomCircle) (Set.range G.topCircle) := by
  rw [G.range_bottomCircle, G.range_topCircle]
  exact G.bottom_disjoint_top

variable [T2Space X]

theorem centralCircle_isEmbedding : IsEmbedding G.centralCircle :=
  G.centralData.isEmbedding

theorem bottomCircle_isEmbedding : IsEmbedding G.bottomCircle :=
  G.bottomData.isEmbedding

theorem topCircle_isEmbedding : IsEmbedding G.topCircle :=
  G.topData.isEmbedding

end FourPortSixEdgePathSystem

/-! ## Transported-torus endpoint circles -/

namespace FourPortSixEdgePathSystem

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  (G : FourPortSixEdgePathSystem (transportedTorus Phi))

private noncomputable def transportedCircle
    (beta : Circle → transportedTorus Phi) (hbeta : IsEmbedding beta) :
    EmbeddedTorusIntersectionCircle Phi := by
  let coordinates : Circle → Circle × Circle :=
    fun z ↦ (transportedTorusHomeomorph Phi).symm (beta z)
  have hcoordinates : Continuous coordinates :=
    (transportedTorusHomeomorph Phi).symm.continuous.comp hbeta.continuous
  let loop := FiniteCoordinatePlaneTorusCircleFamily.windingLoopOfCircle
    (Phi := Phi) coordinates hcoordinates
  exact {
    circle := fun z ↦ beta z
    isEmbedding := IsEmbedding.subtypeVal.comp hbeta
    windingLoop := loop
    parametrization := fun t ↦ by
      change (beta (Circle.exp t) : R3) =
        transportedTorusHomeomorph Phi (coordinates (Circle.exp t))
      exact congrArg Subtype.val <|
        ((transportedTorusHomeomorph Phi).apply_symm_apply
          (beta (Circle.exp t))).symm }

/-- The raw central cycle with its canonical transported winding loop. -/
noncomputable def centralEmbeddedCircle : EmbeddedTorusIntersectionCircle Phi :=
  transportedCircle G.centralCircle G.centralCircle_isEmbedding

/-- The raw lower child with its canonical transported winding loop. -/
noncomputable def bottomEmbeddedCircle : EmbeddedTorusIntersectionCircle Phi :=
  transportedCircle G.bottomCircle G.bottomCircle_isEmbedding

/-- The raw upper child with its canonical transported winding loop. -/
noncomputable def topEmbeddedCircle : EmbeddedTorusIntersectionCircle Phi :=
  transportedCircle G.topCircle G.topCircle_isEmbedding

@[simp] theorem centralEmbeddedCircle_apply (z : Circle) :
    G.centralEmbeddedCircle.circle z = G.centralCircle z :=
  rfl

@[simp] theorem bottomEmbeddedCircle_apply (z : Circle) :
    G.bottomEmbeddedCircle.circle z = G.bottomCircle z :=
  rfl

@[simp] theorem topEmbeddedCircle_apply (z : Circle) :
    G.topEmbeddedCircle.circle z = G.topCircle z :=
  rfl

@[simp] theorem range_centralEmbeddedCircle :
    Set.range G.centralEmbeddedCircle.circle =
      (Subtype.val '' Set.range G.centralCircle) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨G.centralCircle z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

@[simp] theorem range_bottomEmbeddedCircle :
    Set.range G.bottomEmbeddedCircle.circle =
      (Subtype.val '' Set.range G.bottomCircle) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨G.bottomCircle z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

@[simp] theorem range_topEmbeddedCircle :
    Set.range G.topEmbeddedCircle.circle =
      (Subtype.val '' Set.range G.topCircle) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨G.topCircle z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

end FourPortSixEdgePathSystem

namespace FourPortSixEdgePathSystem

variable (G : FourPortSixEdgePathSystem Schoenflies.Plane)

/-- The central cycle as a planar Jordan circle. -/
def centralJordanCircle : Schoenflies.JordanCircle :=
  twoArcJordanCircle
    (fourPortCentralUpperPath G.left G.topOutside G.right) G.bottomOutside
    G.centralData.first_injective G.centralData.second_injective G.centralData.range_inter

/-- The lower child as a planar Jordan circle. -/
def bottomJordanCircle : Schoenflies.JordanCircle :=
  twoArcJordanCircle G.bottom G.bottomOutside
    G.bottomData.first_injective G.bottomData.second_injective G.bottomData.range_inter

/-- The upper child as a planar Jordan circle. -/
def topJordanCircle : Schoenflies.JordanCircle :=
  twoArcJordanCircle G.top G.topOutside
    G.topData.first_injective G.topData.second_injective G.topData.range_inter

@[simp] theorem carrier_centralJordanCircle : G.centralJordanCircle.carrier =
    Set.range (fourPortCentralUpperPath G.left G.topOutside G.right) ∪
      Set.range G.bottomOutside :=
  carrier_twoArcJordanCircle _ _ _ _ _

@[simp] theorem carrier_bottomJordanCircle : G.bottomJordanCircle.carrier =
    Set.range G.bottom ∪ Set.range G.bottomOutside :=
  carrier_twoArcJordanCircle _ _ _ _ _

@[simp] theorem carrier_topJordanCircle : G.topJordanCircle.carrier =
    Set.range G.top ∪ Set.range G.topOutside :=
  carrier_twoArcJordanCircle _ _ _ _ _

end FourPortSixEdgePathSystem
end Submission.Topology
