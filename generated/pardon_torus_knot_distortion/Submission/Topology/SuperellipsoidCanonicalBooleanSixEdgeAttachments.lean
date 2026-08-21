import Submission.Topology.BooleanFourPortSixEdgeGraph
import Submission.Topology.SuperellipsoidCanonicalBooleanSplit
import Submission.Topology.SuperellipsoidCanonicalReducedStageSideCovers

/-!
# Canonical reduced endpoint attachments for Boolean six-edge flips

The conditional split and merge graphs are built from specified-edge cuts of the same finite
alternating systems used by the canonical reduced stages.  Their three raw circles therefore
lie in the corresponding canonical quotient circles.  Carrier inclusion is sufficient for the
canonical disk attachment, so no parametrization equality is required.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open FiniteAlternatingEndpointSystem

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  (D : CanonicalEndpointRegularityData S)

private abbrev AugmentedCycleIndex
    (choice : D.CanonicalReducedBandIndex → Bool) :=
  (D.canonicalBooleanOutsidePathData.system choice).CycleIndex ⊕
    D.centralOuterOrder.InactiveOuterCircle

/-- The reduced `Fin` index corresponding to one active alternating quotient cycle. -/
noncomputable def canonicalReducedCycleIndex
    (choice : D.CanonicalReducedBandIndex → Bool)
    (q : (D.canonicalBooleanOutsidePathData.system choice).CycleIndex) :
    Fin (D.canonicalBooleanReducedStageEntry choice).circleCount :=
  Fintype.equivFin (D.AugmentedCycleIndex choice) (Sum.inl q)

@[simp] theorem canonicalBooleanReducedCircleFamily_circle_cycle
    (choice : D.CanonicalReducedBandIndex → Bool)
    (q : (D.canonicalBooleanOutsidePathData.system choice).CycleIndex) :
    (D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedCycleIndex choice q) =
      (D.canonicalBooleanOutsidePathData.circleSection choice).circle q := by
  change (D.canonicalBooleanAugmentedCircleSection choice).circle
      ((Fintype.equivFin (D.AugmentedCycleIndex choice)).symm
        (Fintype.equivFin (D.AugmentedCycleIndex choice) (Sum.inl q))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Reduced-family index of the quotient cycle containing one selected local edge. -/
noncomputable def canonicalReducedLocalEdgeIndex
    (choice : D.CanonicalReducedBandIndex → Bool)
    (e : FourPortLocalEdge D.centralCutOrder.toPairedSeamEnumeration.bandCount) :=
  D.canonicalReducedCycleIndex choice <|
    (D.canonicalBooleanOutsidePathData.system choice).swapCycleEquiv <|
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
        (BooleanFourPortOutsidePathData.localEdgeStart choice e)

/-- The specified-edge circle is contained in its canonical reduced-family quotient circle. -/
theorem localEdgeCircle_range_subset_reducedCircle
    (choice : D.CanonicalReducedBandIndex → Bool)
    (e : FourPortLocalEdge D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.canonicalBooleanOutsidePathData.localEdgeCircle choice e) ⊆
      Set.range ((D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedLocalEdgeIndex choice e)).circle := by
  unfold canonicalReducedLocalEdgeIndex
  rw [D.canonicalBooleanReducedCircleFamily_circle_cycle]
  exact D.canonicalBooleanOutsidePathData.range_localEdgeCircle_subset_circleSection choice e

namespace CanonicalReducedFlipSixEdge

variable {D : CanonicalEndpointRegularityData S}
  {choice : D.CanonicalReducedBandIndex → Bool} {b : D.CanonicalReducedBandIndex}
  {hb : choice b = false}

private theorem splitParallelCarrier_eq
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    reducedFourPortParallelCarrier
        (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct) =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let H := paths.sixEdgeCarrierData choice next b hb hnext hdistinct
  change Set.range H.toSubtypeGraph.left ∪ Set.range H.toSubtypeGraph.right = _
  rw [H.range_toSubtypeGraph_left, H.range_toSubtypeGraph_right,
    ← Set.preimage_union]
  change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
  congr 1
  rw [paths.range_sixEdgePathSystem_left choice next b hb hnext hdistinct,
    paths.range_sixEdgePathSystem_right choice next b hb hnext hdistinct,
    ← paths.range_localEdgePath choice (b, 0),
    ← paths.range_localEdgePath choice (b, 1)]
  exact D.range_false_localEdgePaths_eq_parallelPatch choice b hb

private theorem splitSurgeryCarrier_eq
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    reducedFourPortSurgeryCarrier
        (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct) =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let H := paths.sixEdgeCarrierData choice next b hb hnext hdistinct
  change Set.range H.toSubtypeGraph.bottom ∪ Set.range H.toSubtypeGraph.top = _
  rw [H.range_toSubtypeGraph_bottom, H.range_toSubtypeGraph_top,
    ← Set.preimage_union]
  change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
  congr 1
  exact D.range_true_localEdgePaths_eq_surgeryPatch next b hnext

private theorem mergeParallelCarrier_eq_surgeryPatch
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    reducedFourPortParallelCarrier
        (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct) =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let H := paths.mergeSixEdgeCarrierData choice next b hb hnext hdistinct
  unfold reducedFourPortParallelCarrier
  unfold BooleanFourPortOutsidePathData.mergeSixEdgeTorusPathSystem
  change Set.range H.toSubtypeGraph.left ∪ Set.range H.toSubtypeGraph.right = _
  rw [H.range_toSubtypeGraph_left, H.range_toSubtypeGraph_right,
    ← Set.preimage_union]
  change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
  congr 1
  rw [paths.range_mergeSixEdgePathSystem_left choice next b hb hnext hdistinct,
    paths.range_mergeSixEdgePathSystem_right choice next b hb hnext hdistinct,
    ← paths.range_localEdgePath next (b, 0),
    ← paths.range_localEdgePath next (b, 1)]
  exact D.range_true_localEdgePaths_eq_surgeryPatch next b hnext

private theorem mergeSurgeryCarrier_eq_parallelPatch
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    reducedFourPortSurgeryCarrier
        (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct) =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let H := paths.mergeSixEdgeCarrierData choice next b hb hnext hdistinct
  unfold reducedFourPortSurgeryCarrier
  unfold BooleanFourPortOutsidePathData.mergeSixEdgeTorusPathSystem
  change Set.range H.toSubtypeGraph.bottom ∪ Set.range H.toSubtypeGraph.top = _
  rw [H.range_toSubtypeGraph_bottom, H.range_toSubtypeGraph_top,
    ← Set.preimage_union]
  change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
  congr 1
  exact D.range_false_localEdgePaths_eq_parallelPatch choice b hb

private theorem splitCentral_range_subset_ambientSection
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.sixEdgePathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.centralCircle) ⊆
      D.canonicalBooleanOutsidePathData.ambientSection choice := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let G := paths.sixEdgePathSystem choice next b hb hnext hdistinct
  rw [G.range_centralCircle, fourPortCentralUpperPath, Path.trans_range,
    Path.trans_range, Path.symm_range, Path.symm_range]
  rintro x (((hxLeft | hxTopOutside) | hxRight) | hxBottomOutside)
  · rw [paths.range_sixEdgePathSystem_left choice next b hb hnext hdistinct] at hxLeft
    exact paths.localPath_range_subset_ambientSection choice (b, 0) hxLeft
  · change x ∈ Set.range (paths.localEdgeComplementPath next (b, 1)) at hxTopOutside
    exact paths.range_update_localEdgeComplementPath_subset_ambientSection
      choice b hb hdistinct 1 hxTopOutside
  · rw [paths.range_sixEdgePathSystem_right choice next b hb hnext hdistinct] at hxRight
    exact paths.localPath_range_subset_ambientSection choice (b, 1) hxRight
  · change x ∈ Set.range (paths.localEdgeComplementPath next (b, 0)) at hxBottomOutside
    exact paths.range_update_localEdgeComplementPath_subset_ambientSection
      choice b hb hdistinct 0 hxBottomOutside

private theorem splitCentral_torusCircleCarrier_subset_familyCarrier
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    torusCircleCarrier
        (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct
          |>.centralEmbeddedCircle) ⊆
      (D.canonicalBooleanReducedCircleFamily choice).carrier := by
  rw [FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
    (D.canonicalBooleanReducedStageEntry choice).circleSection]
  rintro x ⟨z, rfl⟩
  change ((((D.canonicalBooleanOutsidePathData.sixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.centralCircle z : transportedTorus Phi) : R3)) ∈
        D.canonicalBooleanAugmentedAmbientSection choice
  apply Or.inl
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_centralCircle]
  exact splitCentral_range_subset_ambientSection (D := D) hdistinct ⟨z, rfl⟩

private theorem exists_splitCentral_reducedCircle
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    ∃ i, torusCircleCarrier
        (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct
          |>.centralEmbeddedCircle) ⊆
      torusCircleCarrier ((D.canonicalBooleanReducedCircleFamily choice).circle i) := by
  apply FiniteDisjointTorusCircleFamily.exists_circleCarrier_of_isConnected_subset_carrier
    (F := D.canonicalBooleanReducedCircleFamily choice)
  · exact isConnected_range
      (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.centralEmbeddedCircle.continuous_torusCircle)
  · exact splitCentral_torusCircleCarrier_subset_familyCarrier (D := D) hdistinct

private theorem splitBottom_range_subset
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.bottomEmbeddedCircle.circle) ⊆
      Set.range ((D.canonicalBooleanReducedCircleFamily
        (Function.update choice b true)).circle
          (D.canonicalReducedLocalEdgeIndex (Function.update choice b true) (b, 0))).circle := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  apply D.localEdgeCircle_range_subset_reducedCircle
    (Function.update choice b true) (b, 0)
  refine ⟨z, ?_⟩
  symm
  change ((((D.canonicalBooleanOutsidePathData.sixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.bottomCircle z : transportedTorus Phi) : R3)) = _
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_bottomCircle]
  rfl

private theorem splitTop_range_subset
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.topEmbeddedCircle.circle) ⊆
      Set.range ((D.canonicalBooleanReducedCircleFamily
        (Function.update choice b true)).circle
          (D.canonicalReducedLocalEdgeIndex (Function.update choice b true) (b, 1))).circle := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  apply D.localEdgeCircle_range_subset_reducedCircle
    (Function.update choice b true) (b, 1)
  refine ⟨z, ?_⟩
  symm
  change ((((D.canonicalBooleanOutsidePathData.sixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.topCircle z : transportedTorus Phi) : R3)) = _
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_topCircle]
  rfl

/-- All three raw split cycles inherit zero winding from the canonical endpoint families. -/
theorem splitZeroWindingData
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1))) :
    FourPortSixEdgeZeroWindingData
      (D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct) := by
  let G := D.canonicalBooleanOutsidePathData.sixEdgeTorusPathSystem
    choice (Function.update choice b true) b hb (by simp) hdistinct
  constructor
  · obtain ⟨i, hi⟩ := exists_splitCentral_reducedCircle (D := D) hdistinct
    exact EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.centralEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily choice).circle i) hi (preZero i)
  · apply EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.bottomEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily (Function.update choice b true)).circle
        (D.canonicalReducedLocalEdgeIndex (Function.update choice b true) (b, 0)))
    · apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
      exact splitBottom_range_subset (D := D) hdistinct
    · exact postZero _
  · apply EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.topEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily (Function.update choice b true)).circle
        (D.canonicalReducedLocalEdgeIndex (Function.update choice b true) (b, 1)))
    · apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
      exact splitTop_range_subset (D := D) hdistinct
    · exact postZero _

/-- The planar outer split cycle belongs to the appropriate canonical endpoint family. -/
noncomputable def splitEndpointAttachment
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1)))
    (rotation : (splitZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.RectangleRotationData)
    (outer : (splitZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.OuterRawFaceData rotation) :
    ReducedFourPortEndpointCircleSideAttachment
      (splitZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct) outer
      (D.canonicalBooleanReducedCircleFamily choice)
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)) := by
  let Z := splitZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct
  by_cases hzero : outer.outerIndex = 0
  · let hexists := exists_splitCentral_reducedCircle (D := D) (hb := hb) hdistinct
    let i := Classical.choose hexists
    have hi := Classical.choose_spec hexists
    apply Sum.inl
    exact {
      circleIndex := i
      outerCircleCarrier_subset := by
        simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_zero, hzero] using hi }
  · by_cases hone : outer.outerIndex = 1
    · apply Sum.inr
      exact {
        circleIndex := D.canonicalReducedLocalEdgeIndex
          (Function.update choice b true) (b, 0)
        outerCircleCarrier_subset := by
          apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
          simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_one, hone] using
            splitBottom_range_subset (D := D) hdistinct }
    · have htwo : outer.outerIndex = 2 := by omega
      apply Sum.inr
      exact {
        circleIndex := D.canonicalReducedLocalEdgeIndex
          (Function.update choice b true) (b, 1)
        outerCircleCarrier_subset := by
          apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
          simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_two, htwo] using
            splitTop_range_subset (D := D) hdistinct }

private theorem mergeCentral_range_subset_ambientSection
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.mergeSixEdgePathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.centralCircle) ⊆
      D.canonicalBooleanOutsidePathData.ambientSection
        (Function.update choice b true) := by
  let paths := D.canonicalBooleanOutsidePathData
  let next := Function.update choice b true
  have hnext : next b = true := by simp [next]
  let G := paths.mergeSixEdgePathSystem choice next b hb hnext hdistinct
  rw [G.range_centralCircle, fourPortCentralUpperPath, Path.trans_range,
    Path.trans_range, Path.symm_range, Path.symm_range]
  rintro x (((hxLeft | hxTopOutside) | hxRight) | hxBottomOutside)
  · rw [paths.range_mergeSixEdgePathSystem_left
      choice next b hb hnext hdistinct] at hxLeft
    exact paths.localPath_range_subset_ambientSection next (b, 0) hxLeft
  · change x ∈ Set.range (paths.localEdgeComplementPath choice (b, 1)) at hxTopOutside
    exact paths.range_localEdgeComplementPath_subset_update_ambientSection
      choice b hb hdistinct 1 hxTopOutside
  · rw [paths.range_mergeSixEdgePathSystem_right
      choice next b hb hnext hdistinct] at hxRight
    exact paths.localPath_range_subset_ambientSection next (b, 1) hxRight
  · change x ∈ Set.range (paths.localEdgeComplementPath choice (b, 0)) at hxBottomOutside
    exact paths.range_localEdgeComplementPath_subset_update_ambientSection
      choice b hb hdistinct 0 hxBottomOutside

private theorem mergeCentral_torusCircleCarrier_subset_familyCarrier
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    torusCircleCarrier
        (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct
          |>.centralEmbeddedCircle) ⊆
      (D.canonicalBooleanReducedCircleFamily
        (Function.update choice b true)).carrier := by
  rw [FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
    (D.canonicalBooleanReducedStageEntry
      (Function.update choice b true)).circleSection]
  rintro x ⟨z, rfl⟩
  change ((((D.canonicalBooleanOutsidePathData.mergeSixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.centralCircle z : transportedTorus Phi) : R3)) ∈
        D.canonicalBooleanAugmentedAmbientSection (Function.update choice b true)
  apply Or.inl
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_centralCircle]
  exact mergeCentral_range_subset_ambientSection (D := D) hdistinct ⟨z, rfl⟩

private theorem exists_mergeCentral_reducedCircle
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    ∃ i, torusCircleCarrier
        (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
          choice (Function.update choice b true) b hb (by simp) hdistinct
          |>.centralEmbeddedCircle) ⊆
      torusCircleCarrier ((D.canonicalBooleanReducedCircleFamily
        (Function.update choice b true)).circle i) := by
  apply FiniteDisjointTorusCircleFamily.exists_circleCarrier_of_isConnected_subset_carrier
    (F := D.canonicalBooleanReducedCircleFamily (Function.update choice b true))
  · exact isConnected_range
      (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.centralEmbeddedCircle.continuous_torusCircle)
  · exact mergeCentral_torusCircleCarrier_subset_familyCarrier (D := D) hdistinct

private theorem mergeBottom_range_subset
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.bottomEmbeddedCircle.circle) ⊆
      Set.range ((D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedLocalEdgeIndex choice (b, 0))).circle := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  apply D.localEdgeCircle_range_subset_reducedCircle choice (b, 0)
  refine ⟨z, ?_⟩
  symm
  change ((((D.canonicalBooleanOutsidePathData.mergeSixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.bottomCircle z : transportedTorus Phi) : R3)) = _
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_bottomCircle]
  rfl

private theorem mergeTop_range_subset
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    Set.range (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct
        |>.topEmbeddedCircle.circle) ⊆
      Set.range ((D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedLocalEdgeIndex choice (b, 1))).circle := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  apply D.localEdgeCircle_range_subset_reducedCircle choice (b, 1)
  refine ⟨z, ?_⟩
  symm
  change ((((D.canonicalBooleanOutsidePathData.mergeSixEdgeCarrierData
    choice (Function.update choice b true) b hb (by simp) hdistinct).toSubtypeGraph
      |>.topCircle z : transportedTorus Phi) : R3)) = _
  rw [FourPortSixEdgeCarrierData.coe_toSubtypeGraph_topCircle]
  rfl

/-- All three raw merge cycles inherit zero winding from the canonical endpoint families. -/
theorem mergeZeroWindingData
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))) :
    FourPortSixEdgeZeroWindingData
      (D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
        choice (Function.update choice b true) b hb (by simp) hdistinct) := by
  let G := D.canonicalBooleanOutsidePathData.mergeSixEdgeTorusPathSystem
    choice (Function.update choice b true) b hb (by simp) hdistinct
  constructor
  · obtain ⟨i, hi⟩ := exists_mergeCentral_reducedCircle (D := D) hdistinct
    exact EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.centralEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily
        (Function.update choice b true)).circle i) hi (postZero i)
  · apply EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.bottomEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedLocalEdgeIndex choice (b, 0)))
    · apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
      exact mergeBottom_range_subset (D := D) hdistinct
    · exact preZero _
  · apply EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_subset
      G.topEmbeddedCircle
      ((D.canonicalBooleanReducedCircleFamily choice).circle
        (D.canonicalReducedLocalEdgeIndex choice (b, 1)))
    · apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
      exact mergeTop_range_subset (D := D) hdistinct
    · exact preZero _

/-- The planar outer merge cycle belongs to the appropriate canonical endpoint family. -/
noncomputable def mergeEndpointAttachment
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1)))
    (rotation : (mergeZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.RectangleRotationData)
    (outer : (mergeZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.OuterRawFaceData rotation) :
    ReducedFourPortEndpointCircleSideAttachment
      (mergeZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct) outer
      (D.canonicalBooleanReducedCircleFamily choice)
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)) := by
  by_cases hzero : outer.outerIndex = 0
  · let hexists := exists_mergeCentral_reducedCircle (D := D) (hb := hb) hdistinct
    let i := Classical.choose hexists
    have hi := Classical.choose_spec hexists
    apply Sum.inr
    exact {
      circleIndex := i
      outerCircleCarrier_subset := by
        simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_zero, hzero] using hi }
  · by_cases hone : outer.outerIndex = 1
    · apply Sum.inl
      exact {
        circleIndex := D.canonicalReducedLocalEdgeIndex choice (b, 0)
        outerCircleCarrier_subset := by
          apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
          simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_one, hone] using
            mergeBottom_range_subset (D := D) hdistinct }
    · have htwo : outer.outerIndex = 2 := by omega
      apply Sum.inl
      exact {
        circleIndex := D.canonicalReducedLocalEdgeIndex choice (b, 1)
        outerCircleCarrier_subset := by
          apply EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_of_range_subset
          simpa only [FourPortSixEdgeZeroWindingData.rawEmbeddedCircle_two, htwo] using
            mergeTop_range_subset (D := D) hdistinct }

/-- A conditional split, together with its explicit lifted lens, gives the full reduced cover. -/
noncomputable def splitReducedCircleStageSideCover
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem
          (Function.update choice b true)).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart
            (Function.update choice b true) (b, 1)))
    (rotation : (splitZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.RectangleRotationData)
    (outer : (splitZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.OuterRawFaceData rotation)
    (lensLift : ReducedFourPortFaceLensLiftData
      (splitZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct) outer
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage) :
    ReducedCircleStageSideCover
      (D.canonicalBooleanReducedCircleFamily choice) preZero
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)) postZero
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage :=
  reducedCircleStageSideCover (D := D) (hb := hb)
    (splitParallelCarrier_eq (D := D) hdistinct)
    (splitSurgeryCarrier_eq (D := D) hdistinct)
    (splitEndpointAttachment (D := D) preZero postZero hdistinct rotation outer)
    lensLift

/-- A conditional merge is the reverse local graph, hence gives the same forward stage cover. -/
noncomputable def mergeReducedCircleStageSideCover
    (preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential)
    (postZero : (D.canonicalBooleanReducedCircleFamily
      (Function.update choice b true)).AllInessential)
    (hdistinct :
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
        (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
          (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1)))
    (rotation : (mergeZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.RectangleRotationData)
    (outer : (mergeZeroWindingData (D := D) (hb := hb)
      preZero postZero hdistinct).planePathSystem.OuterRawFaceData rotation)
    (lensLift : ReducedFourPortFaceLensLiftData
      (mergeZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct) outer
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage) :
    ReducedCircleStageSideCover
      (D.canonicalBooleanReducedCircleFamily choice) preZero
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)) postZero
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage := by
  let Z := mergeZeroWindingData (D := D) (hb := hb) preZero postZero hdistinct
  let I := mergeEndpointAttachment (D := D) (hb := hb)
    preZero postZero hdistinct rotation outer
  let reverseAttachment : ReducedFourPortEndpointCircleSideAttachment Z outer
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true))
      (D.canonicalBooleanReducedCircleFamily choice) :=
    match I with
    | .inl pre => Sum.inr pre
    | .inr post => Sum.inl post
  apply ReducedCircleStageSideCover.reverse
  apply reducedFourPortLocalPatchSideAlternative
    (preBoundary_eq := (FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).circleSection).symm)
    (postBoundary_eq := (FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
      (D.canonicalBooleanReducedStageEntry choice).circleSection).symm)
    (I := reverseAttachment) (L := lensLift.reverse)
  · intro x hx
    rcases D.canonicalBooleanReducedStageEntry_boundary_subset_update_true
        choice b hb hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      rwa [mergeSurgeryCarrier_eq_parallelPatch (D := D) hdistinct]
  · intro x hx
    rcases D.canonicalBooleanReducedStageEntry_update_true_boundary_subset
        choice b hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      rwa [mergeParallelCarrier_eq_surgeryPatch (D := D) hdistinct]

end CanonicalReducedFlipSixEdge
end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
