import Submission.Topology.FourPortSixEdgeCircleLiftAlignment

/-!
# The three coherent planar circles of a four-port move

After deck-aligning the two child lifts, the central plane circle meets each child exactly along
the corresponding outside arc, while the two children remain disjoint.  This file packages the
three maps as planar Jordan circles and proves those exact carrier incidences.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {G : FourPortSixEdgePathSystem (transportedTorus Phi)}

private def jordanCircleOfPlaneCircle
    (beta : Circle → TorusCoveringPlane)
    (hcontinuous : Continuous beta) (hinjective : Function.Injective beta) :
    Schoenflies.JordanCircle where
  parametrization := beta ∘ JordanCurve.Arcs.spherePlaneHomeoCircle
  continuous := hcontinuous.comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  injective := hinjective.comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

private theorem carrier_jordanCircleOfPlaneCircle
    (beta : Circle → TorusCoveringPlane)
    (hcontinuous : Continuous beta) (hinjective : Function.Injective beta) :
    (jordanCircleOfPlaneCircle beta hcontinuous hinjective).carrier =
      Set.range beta := by
  change Set.range (beta ∘ JordanCurve.Arcs.spherePlaneHomeoCircle) =
    Set.range beta
  rw [Set.range_comp]
  rw [JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq,
    Set.image_univ]

namespace FourPortSixEdgeZeroWindingData

variable (Z : FourPortSixEdgeZeroWindingData G)

theorem centralPlaneCircle_injective : Function.Injective Z.centralPlaneCircle :=
  G.centralEmbeddedCircle.injective_zeroWindingPlaneCircle Z.central

theorem alignedBottomPlaneCircle_injective :
    Function.Injective Z.alignedBottomPlaneCircle := by
  intro z w hzw
  apply G.bottomEmbeddedCircle.injective_zeroWindingPlaneCircle Z.bottom
  exact add_right_cancel hzw

theorem alignedTopPlaneCircle_injective :
    Function.Injective Z.alignedTopPlaneCircle := by
  intro z w hzw
  apply G.topEmbeddedCircle.injective_zeroWindingPlaneCircle Z.top
  exact add_right_cancel hzw

/-- Central lifted endpoint cycle as a planar Jordan circle. -/
def centralPlaneJordanCircle : Schoenflies.JordanCircle :=
  jordanCircleOfPlaneCircle Z.centralPlaneCircle
    Z.continuous_centralPlaneCircle Z.centralPlaneCircle_injective

/-- Deck-aligned lower child as a planar Jordan circle. -/
def bottomPlaneJordanCircle : Schoenflies.JordanCircle :=
  jordanCircleOfPlaneCircle Z.alignedBottomPlaneCircle
    Z.continuous_alignedBottomPlaneCircle Z.alignedBottomPlaneCircle_injective

/-- Deck-aligned upper child as a planar Jordan circle. -/
def topPlaneJordanCircle : Schoenflies.JordanCircle :=
  jordanCircleOfPlaneCircle Z.alignedTopPlaneCircle
    Z.continuous_alignedTopPlaneCircle Z.alignedTopPlaneCircle_injective

@[simp] theorem carrier_centralPlaneJordanCircle :
    Z.centralPlaneJordanCircle.carrier = Set.range Z.centralPlaneCircle :=
  carrier_jordanCircleOfPlaneCircle _ _ _

@[simp] theorem carrier_bottomPlaneJordanCircle :
    Z.bottomPlaneJordanCircle.carrier = Set.range Z.alignedBottomPlaneCircle :=
  carrier_jordanCircleOfPlaneCircle _ _ _

@[simp] theorem carrier_topPlaneJordanCircle :
    Z.topPlaneJordanCircle.carrier = Set.range Z.alignedTopPlaneCircle :=
  carrier_jordanCircleOfPlaneCircle _ _ _

/-- The coherent lifted lower outside arc. -/
def bottomOutsidePlaneArc (t : unitInterval) : TorusCoveringPlane :=
  Z.centralPlaneCircle (TwoArcCircle.secondCircleCoordinate t)

/-- The coherent lifted upper outside arc. -/
def topOutsidePlaneArc (t : unitInterval) : TorusCoveringPlane :=
  Z.centralPlaneCircle (centralTopOutsideParameter t)

theorem centralPlaneCircle_inter_alignedBottomPlaneCircle :
    Set.range Z.centralPlaneCircle ∩ Set.range Z.alignedBottomPlaneCircle =
      Set.range Z.bottomOutsidePlaneArc := by
  ext x
  constructor
  · rintro ⟨⟨z, rfl⟩, ⟨w, hw⟩⟩
    have hprojection : G.centralCircle z = G.bottomCircle w := by
      rw [← Z.projection_centralPlaneCircle,
        ← Z.projection_alignedBottomPlaneCircle, hw]
    have hmem : G.centralCircle z ∈
        Set.range G.centralCircle ∩ Set.range G.bottomCircle :=
      ⟨⟨z, rfl⟩, ⟨w, hprojection.symm⟩⟩
    rw [G.centralCircle_inter_bottomCircle] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hz : z = TwoArcCircle.secondCircleCoordinate t := by
      apply G.centralCircle_injective
      calc
        G.centralCircle z = G.bottomOutside t := ht.symm
        _ = G.centralCircle (TwoArcCircle.secondCircleCoordinate t) := by
          simp only [FourPortSixEdgePathSystem.centralCircle,
            TwoArcCircle.circleMap_secondCircleCoordinate]
    exact ⟨t, by rw [bottomOutsidePlaneArc, hz]⟩
  · rintro ⟨t, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨TwoArcCircle.secondCircleCoordinate t, ?_⟩⟩
    rw [bottomOutsidePlaneArc]
    exact Z.alignedBottomOutside_eq_central t

theorem centralPlaneCircle_inter_alignedTopPlaneCircle :
    Set.range Z.centralPlaneCircle ∩ Set.range Z.alignedTopPlaneCircle =
      Set.range Z.topOutsidePlaneArc := by
  ext x
  constructor
  · rintro ⟨⟨z, rfl⟩, ⟨w, hw⟩⟩
    have hprojection : G.centralCircle z = G.topCircle w := by
      rw [← Z.projection_centralPlaneCircle,
        ← Z.projection_alignedTopPlaneCircle, hw]
    have hmem : G.centralCircle z ∈
        Set.range G.centralCircle ∩ Set.range G.topCircle :=
      ⟨⟨z, rfl⟩, ⟨w, hprojection.symm⟩⟩
    rw [G.centralCircle_inter_topCircle] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hz : z = centralTopOutsideParameter t := by
      apply G.centralCircle_injective
      calc
        G.centralCircle z = G.topOutside t := ht.symm
        _ = G.centralCircle (centralTopOutsideParameter t) :=
          (centralCircle_centralTopOutsideParameter t).symm
    exact ⟨t, by rw [topOutsidePlaneArc, hz]⟩
  · rintro ⟨t, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨TwoArcCircle.secondCircleCoordinate t, ?_⟩⟩
    rw [topOutsidePlaneArc]
    exact Z.alignedTopOutside_eq_central t

/-- Deck translation does not create a child-child intersection. -/
theorem disjoint_alignedBottomPlaneCircle_alignedTopPlaneCircle :
    Disjoint (Set.range Z.alignedBottomPlaneCircle)
      (Set.range Z.alignedTopPlaneCircle) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, rfl⟩ ⟨w, hw⟩
  have hprojection : G.bottomCircle z = G.topCircle w := by
    rw [← Z.projection_alignedBottomPlaneCircle,
      ← Z.projection_alignedTopPlaneCircle, hw]
  exact Set.disjoint_left.mp G.bottomCircle_disjoint_topCircle
    ⟨z, rfl⟩ ⟨w, hprojection.symm⟩

theorem centralPlaneJordanCircle_inter_bottomPlaneJordanCircle :
    Z.centralPlaneJordanCircle.carrier ∩
        Z.bottomPlaneJordanCircle.carrier =
      Set.range Z.bottomOutsidePlaneArc := by
  rw [Z.carrier_centralPlaneJordanCircle,
    Z.carrier_bottomPlaneJordanCircle,
    Z.centralPlaneCircle_inter_alignedBottomPlaneCircle]

theorem centralPlaneJordanCircle_inter_topPlaneJordanCircle :
    Z.centralPlaneJordanCircle.carrier ∩ Z.topPlaneJordanCircle.carrier =
      Set.range Z.topOutsidePlaneArc := by
  rw [Z.carrier_centralPlaneJordanCircle,
    Z.carrier_topPlaneJordanCircle,
    Z.centralPlaneCircle_inter_alignedTopPlaneCircle]

theorem disjoint_bottomPlaneJordanCircle_topPlaneJordanCircle :
    Disjoint Z.bottomPlaneJordanCircle.carrier Z.topPlaneJordanCircle.carrier := by
  rw [Z.carrier_bottomPlaneJordanCircle, Z.carrier_topPlaneJordanCircle]
  exact Z.disjoint_alignedBottomPlaneCircle_alignedTopPlaneCircle

end FourPortSixEdgeZeroWindingData
end Submission.Topology
