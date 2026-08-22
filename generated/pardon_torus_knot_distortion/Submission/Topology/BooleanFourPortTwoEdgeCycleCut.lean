import Submission.Topology.BooleanFourPortCycleCut
import Submission.Topology.FiniteAlternatingTwoEdgeCycleCut
import Submission.Topology.TorusCircleDiskCarrierInvariance

/-!
# Two selected Boolean four-port edges in one component

When the two local edges at one band lie in the same resolved component, cutting the component at
the first edge places the second edge in its embedded complementary outside path.  This file
specializes the finite alternating-cycle result to the Boolean four-port system.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}

namespace BooleanFourPortOutsidePathData

open FiniteAlternatingEndpointSystem

variable (D : BooleanFourPortOutsidePathData Phi F)

private theorem range_localEdgeCircle_subset_transportedTorus
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) ⊆ transportedTorus Phi := by
  let q := (D.system choice).swapCycleEquiv <|
    (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)
  intro x hx
  have hxSection := D.range_localEdgeCircle_subset_circleSection choice e hx
  exact ((D.circleSection choice).circle q).range_subset_transportedTorus hxSection

/-- The specified-edge cut circle, bundled directly as an embedded transported-torus circle. -/
noncomputable def localEdgeTorusCircle
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    EmbeddedTorusIntersectionCircle Phi := by
  let beta : Circle → transportedTorus Phi := fun z ↦
    ⟨D.localEdgeCircle choice e z,
      D.range_localEdgeCircle_subset_transportedTorus choice e ⟨z, rfl⟩⟩
  have hbeta : IsEmbedding beta := by
    apply IsEmbedding.codRestrict
    exact (D.localEdgeTwoArcData choice e).isEmbedding
  exact EmbeddedTorusIntersectionCircle.ofTorusEmbedding beta hbeta

@[simp] theorem localEdgeTorusCircle_apply
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) (z : Circle) :
    (D.localEdgeTorusCircle choice e).circle z = D.localEdgeCircle choice e z :=
  rfl

/-- Inessentiality of the canonical quotient circle descends to its specified-edge cut circle. -/
theorem localEdgeTorusCircle_windingPair_eq_zero
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero :
      ((D.circleSection choice).circle
        ((D.system choice).swapCycleEquiv <|
          (D.localFirstSystem choice).cycleOfVertex
            (localEdgeStart choice e))).windingLoop.windingPair = (0, 0)) :
    (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0) := by
  apply EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
    (D.localEdgeTorusCircle choice e)
    ((D.circleSection choice).circle
      ((D.system choice).swapCycleEquiv <|
        (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)))
  · apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
    change Set.range (D.localEdgeCircle choice e) ⊆ _
    exact D.range_localEdgeCircle_subset_circleSection choice e
  · exact hzero

private theorem continuous_firstCircleCoordinate :
    Continuous TwoArcCircle.firstCircleCoordinate := by
  apply (Circle.exp.continuous.comp
    (continuous_const.mul continuous_subtype_val)).congr
  intro t
  exact (TwoArcCircle.firstCircleCoordinate_eq_exp t).symm

private theorem continuous_secondCircleCoordinate :
    Continuous TwoArcCircle.secondCircleCoordinate := by
  apply (Circle.exp.continuous.comp
    (continuous_const.mul (continuous_subtype_val.add continuous_const))).congr
  intro t
  exact (TwoArcCircle.secondCircleCoordinate_eq_exp t).symm

/-- The covering-plane lift of the selected local edge obtained from its zero-winding cut
circle. -/
def localEdgePlanePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0)) :
    Path
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.firstCircleCoordinate 0))
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.firstCircleCoordinate 1)) where
  toFun := fun t ↦
    (D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
      (TwoArcCircle.firstCircleCoordinate t)
  continuous_toFun :=
    ((D.localEdgeTorusCircle choice e).continuous_zeroWindingPlaneCircle hzero).comp
      continuous_firstCircleCoordinate
  source' := rfl
  target' := rfl

/-- The covering-plane lift of the outside route complementary to the selected local edge. -/
def localEdgeComplementPlanePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0)) :
    Path
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.secondCircleCoordinate 0))
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.secondCircleCoordinate 1)) where
  toFun := fun t ↦
    (D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
      (TwoArcCircle.secondCircleCoordinate t)
  continuous_toFun :=
    ((D.localEdgeTorusCircle choice e).continuous_zeroWindingPlaneCircle hzero).comp
      continuous_secondCircleCoordinate
  source' := rfl
  target' := rfl

@[simp] theorem projection_localEdgePlanePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0))
    (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (D.localEdgePlanePath choice e hzero t) =
      D.localEdgePath choice e t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.firstCircleCoordinate t)) = _
  rw [
    (D.localEdgeTorusCircle choice e).torusCoveringProjection_zeroWindingPlaneCircle,
    D.localEdgeTorusCircle_apply, localEdgeCircle,
    TwoArcCircle.circleMap_firstCircleCoordinate]

@[simp] theorem projection_localEdgeComplementPlanePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0))
    (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (D.localEdgeComplementPlanePath choice e hzero t) =
      D.localEdgeComplementPath choice e t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
      ((D.localEdgeTorusCircle choice e).zeroWindingPlaneCircle hzero
        (TwoArcCircle.secondCircleCoordinate t)) = _
  rw [
    (D.localEdgeTorusCircle choice e).torusCoveringProjection_zeroWindingPlaneCircle,
    D.localEdgeTorusCircle_apply, localEdgeCircle,
    TwoArcCircle.circleMap_secondCircleCoordinate]

theorem localEdgePlanePath_injective
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0)) :
    Function.Injective (D.localEdgePlanePath choice e hzero) := by
  intro s t hst
  apply (D.localEdgeTwoArcData choice e).first_injective
  rw [← D.projection_localEdgePlanePath choice e hzero s,
    ← D.projection_localEdgePlanePath choice e hzero t, hst]

theorem localEdgeComplementPlanePath_injective
    (choice : Fin n → Bool) (e : FourPortLocalEdge n)
    (hzero : (D.localEdgeTorusCircle choice e).windingLoop.windingPair = (0, 0)) :
    Function.Injective (D.localEdgeComplementPlanePath choice e hzero) := by
  intro s t hst
  apply (D.localEdgeTwoArcData choice e).second_injective
  rw [← D.projection_localEdgeComplementPlanePath choice e hzero s,
    ← D.projection_localEdgeComplementPlanePath choice e hzero t, hst]

/-- A distinct same-component local edge lies in the complementary path cut at the selected
local edge. -/
theorem range_localEdgePath_subset_complementPath_of_cycle_eq
    (choice : Fin n → Bool) {e f : FourPortLocalEdge n} (hef : e ≠ f)
    (hcycle :
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice f) =
        (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)) :
    Set.range (D.localEdgePath choice f) ⊆
      Set.range (D.localEdgeComplementPath choice e) := by
  rw [D.range_localEdgePath choice f]
  exact ClosedArcIncidenceData.range_firstPath_subset_complementPathAt_of_cycle_eq hef hcycle

/-- The second local edge at a band determines an ordered subpath of the first edge's
complement whenever the two edges belong to one component. -/
theorem exists_ordered_localEdge_complement_parameters_of_cycle_eq
    (choice : Fin n → Bool) (b : Fin n)
    (hcycle :
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 1)) =
        (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 0))) :
    ∃ s t : unitInterval, s < t ∧
      Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path (b, 1)) =
        Set.range ((D.localEdgeComplementPath choice (b, 0)).subpath s t) ∧
      ((fourPortChartPoint F.band
            ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 0)) =
          D.localEdgeComplementPath choice (b, 0) s ∧
        fourPortChartPoint F.band
            ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 1)) =
          D.localEdgeComplementPath choice (b, 0) t) ∨
       (fourPortChartPoint F.band
            ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 0)) =
          D.localEdgeComplementPath choice (b, 0) t ∧
        fourPortChartPoint F.band
            ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 1)) =
          D.localEdgeComplementPath choice (b, 0) s)) := by
  have hef : ((b, 0) : FourPortLocalEdge n) ≠ (b, 1) := by
    intro h
    have hsnd := congrArg Prod.snd h
    norm_num at hsnd
  obtain ⟨s, t, hst, hrange, hends⟩ :=
    (D.localFirstIncidence choice).exists_ordered_complement_parameters_of_cycle_eq
      hef hcycle
  refine ⟨s, t, hst, ?_, ?_⟩
  · convert hrange using 1 <;> rfl
  · convert hends using 1 <;> rfl

end BooleanFourPortOutsidePathData
end Submission.Topology
