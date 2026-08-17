import Submission.Topology.FourPortSixEdgeGraph
import Submission.Topology.MaximalInessentialDiskFamilyExistence
import Submission.PlaneSchoenflies.Schoenflies.MoiseCellBoundaryRoutes

/-!
# Coherent plane lifts of the three raw four-port circles

The central raw circle shares its lower outside arc with the lower child and its upper outside
arc with the upper child.  If all three circles have zero winding, their canonical plane-circle
lifts can be deck-translated so that both shared arcs agree pointwise.  This is the coherent-lift
input for the honest six-edge planar graph; no theta incidence is asserted.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {G : FourPortSixEdgePathSystem (transportedTorus Phi)}

/-- The three actual endpoint cycles of the six-edge graph are inessential. -/
structure FourPortSixEdgeZeroWindingData
    (G : FourPortSixEdgePathSystem (transportedTorus Phi)) : Prop where
  central : G.centralEmbeddedCircle.windingLoop.windingPair = (0, 0)
  bottom : G.bottomEmbeddedCircle.windingLoop.windingPair = (0, 0)
  top : G.topEmbeddedCircle.windingLoop.windingPair = (0, 0)

namespace FourPortSixEdgeZeroWindingData

variable (Z : FourPortSixEdgeZeroWindingData G)

/-- Canonical plane-circle lift of the central raw cycle. -/
def centralPlaneCircle : Circle → TorusCoveringPlane :=
  G.centralEmbeddedCircle.zeroWindingPlaneCircle Z.central

/-- Canonical plane-circle lift of the lower raw child. -/
def bottomPlaneCircle : Circle → TorusCoveringPlane :=
  G.bottomEmbeddedCircle.zeroWindingPlaneCircle Z.bottom

/-- Canonical plane-circle lift of the upper raw child. -/
def topPlaneCircle : Circle → TorusCoveringPlane :=
  G.topEmbeddedCircle.zeroWindingPlaneCircle Z.top

theorem continuous_centralPlaneCircle : Continuous Z.centralPlaneCircle :=
  G.centralEmbeddedCircle.continuous_zeroWindingPlaneCircle Z.central

theorem continuous_bottomPlaneCircle : Continuous Z.bottomPlaneCircle :=
  G.bottomEmbeddedCircle.continuous_zeroWindingPlaneCircle Z.bottom

theorem continuous_topPlaneCircle : Continuous Z.topPlaneCircle :=
  G.topEmbeddedCircle.continuous_zeroWindingPlaneCircle Z.top

@[simp] theorem projection_centralPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.centralPlaneCircle z) = G.centralCircle z := by
  apply Subtype.ext
  exact G.centralEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.central z

@[simp] theorem projection_bottomPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.bottomPlaneCircle z) = G.bottomCircle z := by
  apply Subtype.ext
  exact G.bottomEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.bottom z

@[simp] theorem projection_topPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.topPlaneCircle z) = G.topCircle z := by
  apply Subtype.ext
  exact G.topEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.top z

private theorem projection_sharedBottom_source :
    EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 0)) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (Z.bottomPlaneCircle (TwoArcCircle.secondCircleCoordinate 0)) := by
  rw [centralPlaneCircle, bottomPlaneCircle,
    G.centralEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.central,
    G.bottomEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.bottom]
  simp only [G.centralEmbeddedCircle_apply, G.bottomEmbeddedCircle_apply,
    FourPortSixEdgePathSystem.centralCircle,
    FourPortSixEdgePathSystem.bottomCircle,
    TwoArcCircle.circleMap_secondCircleCoordinate]

/-- Deck vector translating the lower child lift onto the central lift. -/
def bottomAlignmentIndex : Fin 2 → ℤ :=
  Classical.choose <|
    EmbeddedTorusIntersectionCircle.exists_latticeVector_of_torusCoveringProjection_eq
      Z.projection_sharedBottom_source

theorem bottomAlignment_source :
    Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate 0) =
      Z.bottomPlaneCircle (TwoArcCircle.secondCircleCoordinate 0) +
        EmbeddedTorusIntersectionCircle.torusLatticeVector Z.bottomAlignmentIndex :=
  Classical.choose_spec <|
    EmbeddedTorusIntersectionCircle.exists_latticeVector_of_torusCoveringProjection_eq
      Z.projection_sharedBottom_source

/-- The deck-translated lower child plane circle. -/
def alignedBottomPlaneCircle (z : Circle) : TorusCoveringPlane :=
  Z.bottomPlaneCircle z +
    EmbeddedTorusIntersectionCircle.torusLatticeVector Z.bottomAlignmentIndex

theorem continuous_alignedBottomPlaneCircle : Continuous Z.alignedBottomPlaneCircle :=
  Z.continuous_bottomPlaneCircle.add continuous_const

@[simp] theorem projection_alignedBottomPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.alignedBottomPlaneCircle z) = G.bottomCircle z := by
  rw [alignedBottomPlaneCircle,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice,
    Z.projection_bottomPlaneCircle]

/-- After one deck translation, the lower outside arc agrees pointwise in the plane. -/
theorem alignedBottomOutside_eq_central (t : unitInterval) :
    Z.alignedBottomPlaneCircle (TwoArcCircle.secondCircleCoordinate t) =
      Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate t) := by
  let p : unitInterval → TorusCoveringPlane := fun u ↦
    Z.alignedBottomPlaneCircle (TwoArcCircle.secondCircleCoordinate u)
  let q : unitInterval → TorusCoveringPlane := fun u ↦
    Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate u)
  have hp : Continuous p := Z.continuous_alignedBottomPlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  have hq : Continuous q := Z.continuous_centralPlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  have hprojection : ∀ u,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p u) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q u) := by
    intro u
    dsimp [p, q]
    rw [Z.projection_alignedBottomPlaneCircle,
      Z.projection_centralPlaneCircle]
    simp only [FourPortSixEdgePathSystem.centralCircle,
      FourPortSixEdgePathSystem.bottomCircle,
      TwoArcCircle.circleMap_secondCircleCoordinate]
  have hsource : p 0 = q 0 := by
    dsimp [p, q]
    exact Z.bottomAlignment_source.symm
  exact congrFun
    (TorusThetaPathSystem.ZeroWindingThetaData.planePathLift_eq_of_projection_eq
      p q hp hq hprojection hsource) t

/-- Central-circle parameter traversing the upper outside edge in its given orientation. -/
def centralTopOutsideParameter (t : unitInterval) : Circle :=
  TwoArcCircle.firstCircleCoordinate
    (Schoenflies.ThreePiecePath.middleCoordinate (unitInterval.symm t))

theorem continuous_centralTopOutsideParameter :
    Continuous centralTopOutsideParameter := by
  have hmiddle : Continuous Schoenflies.ThreePiecePath.middleCoordinate := by
    apply Continuous.subtype_mk
    fun_prop
  exact TorusThetaPathSystem.continuous_referenceParameter.comp <|
    hmiddle.comp unitInterval.continuous_symm

@[simp] theorem centralCircle_centralTopOutsideParameter (t : unitInterval) :
    G.centralCircle (centralTopOutsideParameter t) = G.topOutside t := by
  rw [centralTopOutsideParameter,
    FourPortSixEdgePathSystem.centralCircle,
    TwoArcCircle.circleMap_firstCircleCoordinate]
  rw [fourPortCentralUpperPath,
    Schoenflies.ThreePiecePath.trans_trans_middleCoordinate]
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

private theorem projection_sharedTop_source :
    EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (Z.centralPlaneCircle (centralTopOutsideParameter 0)) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (Z.topPlaneCircle (TwoArcCircle.secondCircleCoordinate 0)) := by
  rw [centralPlaneCircle, topPlaneCircle,
    G.centralEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.central,
    G.topEmbeddedCircle.torusCoveringProjection_zeroWindingPlaneCircle Z.top]
  simp only [G.centralEmbeddedCircle_apply, G.topEmbeddedCircle_apply]
  rw [centralCircle_centralTopOutsideParameter]
  simp only [FourPortSixEdgePathSystem.topCircle,
    TwoArcCircle.circleMap_secondCircleCoordinate]

/-- Deck vector translating the upper child lift onto the central lift. -/
def topAlignmentIndex : Fin 2 → ℤ :=
  Classical.choose <|
    EmbeddedTorusIntersectionCircle.exists_latticeVector_of_torusCoveringProjection_eq
      Z.projection_sharedTop_source

theorem topAlignment_source :
    Z.centralPlaneCircle (centralTopOutsideParameter 0) =
      Z.topPlaneCircle (TwoArcCircle.secondCircleCoordinate 0) +
        EmbeddedTorusIntersectionCircle.torusLatticeVector Z.topAlignmentIndex :=
  Classical.choose_spec <|
    EmbeddedTorusIntersectionCircle.exists_latticeVector_of_torusCoveringProjection_eq
      Z.projection_sharedTop_source

/-- The deck-translated upper child plane circle. -/
def alignedTopPlaneCircle (z : Circle) : TorusCoveringPlane :=
  Z.topPlaneCircle z +
    EmbeddedTorusIntersectionCircle.torusLatticeVector Z.topAlignmentIndex

theorem continuous_alignedTopPlaneCircle : Continuous Z.alignedTopPlaneCircle :=
  Z.continuous_topPlaneCircle.add continuous_const

@[simp] theorem projection_alignedTopPlaneCircle (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.alignedTopPlaneCircle z) = G.topCircle z := by
  rw [alignedTopPlaneCircle,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice,
    Z.projection_topPlaneCircle]

/-- After one deck translation, the upper outside arc also agrees pointwise in the plane. -/
theorem alignedTopOutside_eq_central (t : unitInterval) :
    Z.alignedTopPlaneCircle (TwoArcCircle.secondCircleCoordinate t) =
      Z.centralPlaneCircle (centralTopOutsideParameter t) := by
  let p : unitInterval → TorusCoveringPlane := fun u ↦
    Z.alignedTopPlaneCircle (TwoArcCircle.secondCircleCoordinate u)
  let q : unitInterval → TorusCoveringPlane := fun u ↦
    Z.centralPlaneCircle (centralTopOutsideParameter u)
  have hp : Continuous p := Z.continuous_alignedTopPlaneCircle.comp
    TorusThetaPathSystem.continuous_otherParameter
  have hq : Continuous q := Z.continuous_centralPlaneCircle.comp
    continuous_centralTopOutsideParameter
  have hprojection : ∀ u,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p u) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q u) := by
    intro u
    dsimp [p, q]
    rw [Z.projection_alignedTopPlaneCircle,
      Z.projection_centralPlaneCircle,
      centralCircle_centralTopOutsideParameter]
    simp only [FourPortSixEdgePathSystem.topCircle,
      TwoArcCircle.circleMap_secondCircleCoordinate]
  have hsource : p 0 = q 0 := by
    dsimp [p, q]
    exact Z.topAlignment_source.symm
  exact congrFun
    (TorusThetaPathSystem.ZeroWindingThetaData.planePathLift_eq_of_projection_eq
      p q hp hq hprojection hsource) t

end FourPortSixEdgeZeroWindingData
end Submission.Topology
