import Submission.Topology.SuperellipsoidCanonicalHeightFlowFilledSweep
import Submission.Topology.SuperellipsoidCanonicalOuterGapTrim
import Submission.Topology.SuperellipsoidReducedInitialRegion
import Submission.Topology.SuperellipsoidGlobalFourPortCarrier
import Submission.Topology.JordanTranslate
import Submission.Topology.OpenRegionLensAttachment
import Submission.Topology.ReducedTorusBooleanStages

/-!
# Canonical reduced four-port regions

The canonical filled height-flow square lies on or inside the selected outer superellipsoid.
Its open square lies strictly inside.  These are the local sign facts needed to toggle the
reduced torus region across one four-port rectangle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily
open FiniteSuperellipsoidBarrierGraph.OuterCircleTransverseHeightCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev ConnectorBand := D.openChartNarrowedData.heightData.band

private abbrev ConnectorBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private theorem centralConnectorLeftCrossingParameter_eq_greatest
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    D.centralConnectorLeftCrossingParameter b t =
      D.greatestCentralConnectorLeftCrossingParameter b t.1 (by
        exact ⟨D.centralConnectorLeftCrossingParameter b t,
          D.centralConnectorLeftCrossingParameter_spec b t⟩) := by
  apply (D.existsUnique_centralConnectorLeftCrossing b t.1 t.2).unique
  · exact D.centralConnectorLeftCrossingParameter_spec b t
  · exact (D.greatestCentralConnectorLeftCrossingParameter_spec b t.1 _).1

private theorem centralConnectorRightCrossingParameter_eq_least
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    D.centralConnectorRightCrossingParameter b t =
      D.leastCentralConnectorRightCrossingParameter b t.1 (by
        exact ⟨D.centralConnectorRightCrossingParameter b t,
          D.centralConnectorRightCrossingParameter_spec b t⟩) := by
  apply (D.existsUnique_centralConnectorRightCrossing b t.1 t.2).unique
  · exact D.centralConnectorRightCrossingParameter_spec b t
  · exact (D.leastCentralConnectorRightCrossingParameter_spec b t.1 _).1

theorem centralHeightFlowOuterDefect_sweepParameter_neg
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval)
    (hp0 : p.1 ≠ 0) (hp1 : p.1 ≠ 1) :
    D.centralHeightFlowOuterDefect b (D.centralConnectorSweepTime p.2).1
        (D.centralConnectorSweepParameter b p) < 0 := by
  let t := D.centralConnectorSweepTime p.2
  let left := D.centralConnectorLeftCrossingParameter b t
  let right := D.centralConnectorRightCrossingParameter b t
  have hleftRight : left < right := D.centralConnectorCrossingParameter_order b t
  have hpLower : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.2.1 (Ne.symm <| by
    exact fun h ↦ hp0 (Subtype.ext h))
  have hpUpper : (p.1 : ℝ) < 1 := lt_of_le_of_ne p.1.2.2 (by
    exact fun h ↦ hp1 (Subtype.ext h))
  have hsweep : D.centralConnectorSweepParameter b p ∈ Ioo left right := by
    change left < Icc.convexComb left right p.1 ∧
      Icc.convexComb left right p.1 < right
    have hvalue :
        ((Icc.convexComb left right p.1 : unitInterval) : ℝ) =
          (1 - (p.1 : ℝ)) * left + (p.1 : ℝ) * right :=
      Icc.coe_convexComb left right p.1
    change (left : ℝ) < (Icc.convexComb left right p.1 : unitInterval) ∧
      (Icc.convexComb left right p.1 : unitInterval) < (right : ℝ)
    rw [hvalue]
    have hgap : 0 < (right : ℝ) - left := sub_pos.mpr hleftRight
    constructor
    · rw [show (1 - (p.1 : ℝ)) * left + (p.1 : ℝ) * right =
          left + (p.1 : ℝ) * (right - left) by ring]
      exact lt_add_of_pos_right _ (mul_pos hpLower hgap)
    · rw [show (1 - (p.1 : ℝ)) * left + (p.1 : ℝ) * right =
          right - (1 - (p.1 : ℝ)) * (right - left) by ring]
      exact sub_lt_self _ (mul_pos (sub_pos.mpr hpUpper) hgap)
  have hleftNonempty : (D.centralConnectorLeftZeroSet b t.1).Nonempty :=
    ⟨left, D.centralConnectorLeftCrossingParameter_spec b t⟩
  have hrightNonempty : (D.centralConnectorRightZeroSet b t.1).Nonempty :=
    ⟨right, D.centralConnectorRightCrossingParameter_spec b t⟩
  apply D.centralConnector_betweenExtremalCrossings_neg b t.1
    hleftNonempty hrightNonempty
  · intro u hu
    exact D.centralConnectorFullNegativeTimeRadius_spec b t.1
      ((D.abs_lt_uniformCentralConnectorTimeRadius t.2).trans_le
        (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) u hu
  · rw [← D.centralConnectorLeftCrossingParameter_eq_greatest b t,
      ← D.centralConnectorRightCrossingParameter_eq_least b t]
    exact hsweep

theorem centralHeightFlowOuterDefect_sweepParameter_nonpos
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    D.centralHeightFlowOuterDefect b (D.centralConnectorSweepTime p.2).1
        (D.centralConnectorSweepParameter b p) ≤ 0 := by
  by_cases hp0 : p.1 = 0
  · have hp : p = (0, p.2) := Prod.ext hp0 rfl
    rw [hp]
    simpa only [centralConnectorSweepParameter_zero] using
      (D.centralConnectorLeftCrossingParameter_spec b
        (D.centralConnectorSweepTime p.2)).2.le
  · by_cases hp1 : p.1 = 1
    · have hp : p = (1, p.2) := Prod.ext hp1 rfl
      rw [hp]
      simpa only [centralConnectorSweepParameter_one] using
        (D.centralConnectorRightCrossingParameter_spec b
          (D.centralConnectorSweepTime p.2)).2.le
    · exact (D.centralHeightFlowOuterDefect_sweepParameter_neg b p hp0 hp1).le

private theorem centralHeightFlowOuterAmbient_image_closure_inside
    (b : D.ConnectorBandIndex) :
    (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
        standardPlaneFourPortThetaSystem
        (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
        standardPlaneFourPortTheta_outer_decomposition ''
      closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside =
        closure standardPlaneFourPortThetaSystem.circle12.inside :=
  (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph_image_closure_inside
    standardPlaneFourPortThetaSystem
    (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
    standardPlaneFourPortTheta_outer_decomposition

private theorem centralHeightFlowFourPortHomeomorph_apply_coordinates
    (b : D.ConnectorBandIndex) (z : Schoenflies.Plane) :
    D.centralHeightFlowFourPortHomeomorph b (coveringPlaneCoordinates z) =
      coveringPlaneCoordinates
        ((D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition z) := by
  unfold centralHeightFlowFourPortHomeomorph
  simp only [Homeomorph.trans_apply, coveringPlaneCoordinates.symm_apply_apply]

theorem image_fourPortClosedRectangle_centralHeightFlowFourPortHomeomorph_symm
    (b : D.ConnectorBandIndex) :
    (D.centralHeightFlowFourPortHomeomorph b).symm '' fourPortClosedRectangle =
      coveringPlaneCoordinates ''
        closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside := by
  let A := (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
    standardPlaneFourPortThetaSystem
    (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
    standardPlaneFourPortTheta_outer_decomposition
  have hA : A '' closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside =
      closure standardPlaneFourPortThetaSystem.circle12.inside :=
    D.centralHeightFlowOuterAmbient_image_closure_inside b
  have hstandard : coveringPlaneCoordinates.symm '' fourPortClosedRectangle =
      closure standardPlaneFourPortThetaSystem.circle12.inside :=
    standardOuterRectangle_eq_closure_inside
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxTarget : coveringPlaneCoordinates.symm x ∈
        closure standardPlaneFourPortThetaSystem.circle12.inside := by
      rw [← hstandard]
      exact ⟨x, hx, rfl⟩
    rw [← hA] at hxTarget
    obtain ⟨q, hq, hqImage⟩ := hxTarget
    refine ⟨q, hq, ?_⟩
    apply (D.centralHeightFlowFourPortHomeomorph b).injective
    rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply,
      D.centralHeightFlowFourPortHomeomorph_apply_coordinates]
    rw [hqImage, coveringPlaneCoordinates.apply_symm_apply]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨coveringPlaneCoordinates (A q), ?_, ?_⟩
    · have hAq : A q ∈ closure standardPlaneFourPortThetaSystem.circle12.inside := by
        rw [← hA]
        exact ⟨q, hq, rfl⟩
      rw [← hstandard] at hAq
      obtain ⟨x, hx, hxEq⟩ := hAq
      have hxEq' : x = coveringPlaneCoordinates (A q) := by
        rw [← hxEq, coveringPlaneCoordinates.apply_symm_apply]
      rwa [← hxEq']
    · apply (D.centralHeightFlowFourPortHomeomorph b).injective
      rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply,
        D.centralHeightFlowFourPortHomeomorph_apply_coordinates]

theorem image_fourPortClosedRectangle_eq_range_centralConnectorFilledSweepCoordinate
    (b : D.ConnectorBandIndex) :
    (D.centralHeightFlowFourPortHomeomorph b).symm '' fourPortClosedRectangle =
      Set.range (D.centralConnectorFilledSweepCoordinate b) := by
  rw [D.image_fourPortClosedRectangle_centralHeightFlowFourPortHomeomorph_symm b]
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [← D.image_centralConnectorUnitSquare_eq_closure_inside b] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    refine ⟨centralConnectorSquareParameter s, ?_⟩
    unfold centralConnectorFilledPlaneSweepExtension centralConnectorFilledPlaneSweep
    exact coveringPlaneCoordinates.apply_symm_apply _
  · rintro ⟨p, rfl⟩
    let s := coveringPlaneCoordinates.symm (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ)
    have hs : s ∈ centralConnectorUnitSquare := by
      refine ⟨((p.1 : ℝ), (p.2 : ℝ)), ⟨p.1.2, p.2.2⟩, rfl⟩
    refine ⟨D.centralConnectorFilledPlaneSweepExtension b s, ?_, ?_⟩
    · rw [← D.image_centralConnectorUnitSquare_eq_closure_inside b]
      exact ⟨s, hs, rfl⟩
    · rw [show s = coveringPlaneCoordinates.symm
          (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ) by rfl,
        D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((p.1 : ℝ), (p.2 : ℝ)) ⟨p.1.2, p.2.2⟩]
      simp only [coveringPlaneCoordinates.apply_symm_apply]

theorem canonicalBandMap_centralConnectorFilledSweepCoordinate
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    D.canonicalBandMap b (D.centralConnectorFilledSweepCoordinate b p) =
      transportedTorusPlaneMap Phi
        (D.centralHeightFlowSliceLift b (D.centralConnectorSweepTime p.2).1
          (D.centralConnectorSweepParameter b p)) := by
  unfold canonicalBandMap centralConnectorFilledSweepCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  rfl

theorem superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    superellipsoidPolynomial frame c
        (D.canonicalBandMap b (D.centralConnectorFilledSweepCoordinate b p)) -
      S.outer.scale ^ 256 =
        D.centralHeightFlowOuterDefect b (D.centralConnectorSweepTime p.2).1
          (D.centralConnectorSweepParameter b p) := by
  rw [D.canonicalBandMap_centralConnectorFilledSweepCoordinate]
  unfold centralHeightFlowOuterDefect globalBandFlowOuterDefect
  unfold superellipsoidPolynomialLift
  rfl

/-- The straightened four-port chart with its transported-torus codomain retained. -/
def centralHeightFlowStraightenedTorusChart
    (b : D.ConnectorBandIndex) (z : Plane) : transportedTorus Phi :=
  ((D.centralHeightFlowStraightenedBandData b).strip z :
    (D.centralHeightFlowStraightenedBandData b).surfacePatch)

theorem centralHeightFlowStraightenedTorusChart_coe
    (b : D.ConnectorBandIndex) (z : Plane) :
    ((D.centralHeightFlowStraightenedTorusChart b z : transportedTorus Phi) : R3) =
      (D.centralHeightFlowStraightenedChartFamily.chart b).chart z :=
  rfl

theorem centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap
    (b : D.ConnectorBandIndex) (z : Plane) :
    ((D.centralHeightFlowStraightenedTorusChart b z : transportedTorus Phi) : R3) =
      D.canonicalBandMap b ((D.centralHeightFlowFourPortHomeomorph b).symm z) :=
  rfl

theorem centralHeightFlowStraightenedTorusChart_isOpenEmbedding
    (b : D.ConnectorBandIndex) :
    IsOpenEmbedding (D.centralHeightFlowStraightenedTorusChart b) := by
  exact
    (D.centralCutOrder.globalBandOpenTubularChartFamily_surfacePatch_open b)
      |>.isOpenEmbedding_subtypeVal.comp
        (D.centralHeightFlowStraightenedBandData b).strip.isOpenEmbedding

/-- The closed four-port disk on the transported torus in one canonical band. -/
def canonicalFourPortClosedLens (b : D.ConnectorBandIndex) :
    Set (transportedTorus Phi) :=
  D.centralHeightFlowStraightenedTorusChart b '' fourPortClosedRectangle

/-- Its open interior, used to toggle the Boolean parity label. -/
def canonicalFourPortOpenLens (b : D.ConnectorBandIndex) :
    Set (transportedTorus Phi) :=
  D.centralHeightFlowStraightenedTorusChart b '' interior fourPortClosedRectangle

def canonicalFourPortVerticalFace (b : D.ConnectorBandIndex) :
    Set (transportedTorus Phi) :=
  D.centralHeightFlowStraightenedTorusChart b '' fourPortVerticalCarrier

def canonicalFourPortHorizontalFace (b : D.ConnectorBandIndex) :
    Set (transportedTorus Phi) :=
  D.centralHeightFlowStraightenedTorusChart b '' fourPortHorizontalCarrier

theorem isCompact_canonicalFourPortClosedLens (b : D.ConnectorBandIndex) :
    IsCompact (D.canonicalFourPortClosedLens b) :=
  isCompact_fourPortClosedRectangle.image
    (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).continuous

theorem isClosed_canonicalFourPortClosedLens (b : D.ConnectorBandIndex) :
    IsClosed (D.canonicalFourPortClosedLens b) :=
  (D.isCompact_canonicalFourPortClosedLens b).isClosed

theorem canonicalFourPortClosedLens_coe_subset_bandNeighborhood
    (b : D.ConnectorBandIndex) {x : transportedTorus Phi}
    (hx : x ∈ D.canonicalFourPortClosedLens b) :
    (x : R3) ∈ D.centralCutOrder.globalBandOpenNeighborhood b := by
  obtain ⟨z, _, rfl⟩ := hx
  exact (D.centralHeightFlowStraightenedBandData b).strip_mem_neighborhood ⟨z, rfl⟩

theorem canonicalFourPortClosedLens_pairwise_disjoint :
    Pairwise fun b e : D.ConnectorBandIndex ↦
      Disjoint (D.canonicalFourPortClosedLens b)
        (D.canonicalFourPortClosedLens e) := by
  intro b e hbe
  rw [Set.disjoint_left]
  intro x hxb hxe
  exact Set.disjoint_left.mp
    (D.centralCutOrder.globalBandOpenNeighborhood_spec.2 hbe)
    (D.canonicalFourPortClosedLens_coe_subset_bandNeighborhood b hxb)
    (D.canonicalFourPortClosedLens_coe_subset_bandNeighborhood e hxe)

theorem isOpen_canonicalFourPortOpenLens (b : D.ConnectorBandIndex) :
    IsOpen (D.canonicalFourPortOpenLens b) :=
  (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).isOpenMap _
    isOpen_interior

theorem interior_canonicalFourPortClosedLens (b : D.ConnectorBandIndex) :
    interior (D.canonicalFourPortClosedLens b) = D.canonicalFourPortOpenLens b := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxLens : x ∈ D.canonicalFourPortClosedLens b := interior_subset hx
    obtain ⟨z, hz, rfl⟩ := hxLens
    refine ⟨z, ?_, rfl⟩
    let U := D.centralHeightFlowStraightenedTorusChart b ⁻¹'
      interior (D.canonicalFourPortClosedLens b)
    have hUopen : IsOpen U := isOpen_interior.preimage
      (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).continuous
    have hUsubset : U ⊆ fourPortClosedRectangle := by
      intro w hw
      have hfw : D.centralHeightFlowStraightenedTorusChart b w ∈
          D.canonicalFourPortClosedLens b := interior_subset hw
      obtain ⟨v, hv, hvw⟩ := hfw
      exact (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).injective hvw ▸ hv
    apply interior_maximal hUsubset hUopen
    exact hx
  · exact interior_maximal (Set.image_mono interior_subset)
      (D.isOpen_canonicalFourPortOpenLens b)

theorem canonicalFourPortClosedLens_subset_closure_openLens
    (b : D.ConnectorBandIndex) :
    D.canonicalFourPortClosedLens b ⊆
      closure (D.canonicalFourPortOpenLens b) := by
  rintro _ ⟨z, hz, rfl⟩
  apply map_mem_closure
    (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).continuous
  · rw [closure_interior_fourPortClosedRectangle]
    exact hz
  · exact Set.mapsTo_image _ _

theorem frontier_canonicalFourPortClosedLens (b : D.ConnectorBandIndex) :
    frontier (D.canonicalFourPortClosedLens b) =
      D.centralHeightFlowStraightenedTorusChart b ''
        frontier fourPortClosedRectangle := by
  rw [frontier, (D.isClosed_canonicalFourPortClosedLens b).closure_eq,
    D.interior_canonicalFourPortClosedLens]
  rw [frontier, isClosed_fourPortClosedRectangle.closure_eq]
  exact (Set.image_sdiff
    (D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).injective _ _).symm

theorem frontier_canonicalFourPortClosedLens_eq_faces (b : D.ConnectorBandIndex) :
    frontier (D.canonicalFourPortClosedLens b) =
      D.canonicalFourPortVerticalFace b ∪ D.canonicalFourPortHorizontalFace b := by
  rw [D.frontier_canonicalFourPortClosedLens b, frontier_fourPortClosedRectangle,
    Set.image_union]
  rfl

theorem canonicalFourPortClosedLens_exists_filledSweepCoordinate
    (b : D.ConnectorBandIndex) {x : transportedTorus Phi}
    (hx : x ∈ D.canonicalFourPortClosedLens b) :
    ∃ p : unitInterval × unitInterval,
      (x : R3) = D.canonicalBandMap b (D.centralConnectorFilledSweepCoordinate b p) := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hzFilled : (D.centralHeightFlowFourPortHomeomorph b).symm z ∈
      Set.range (D.centralConnectorFilledSweepCoordinate b) := by
    rw [← D.image_fourPortClosedRectangle_eq_range_centralConnectorFilledSweepCoordinate b]
    exact ⟨z, hz, rfl⟩
  obtain ⟨p, hp⟩ := hzFilled
  refine ⟨p, ?_⟩
  rw [D.centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap, hp]

private theorem centralHeightFlowFourPortHomeomorph_filledSweep_endpoint_mem_frontier
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval)
    (hp : p.1 = 0 ∨ p.1 = 1) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralConnectorFilledSweepCoordinate b p) ∈
      frontier fourPortClosedRectangle := by
  let s := coveringPlaneCoordinates.symm (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ)
  let q := coveringPlaneCoordinates.symm (D.centralConnectorFilledSweepCoordinate b p)
  have hs : s ∈ frontier centralConnectorUnitSquare := by
    rw [frontier_centralConnectorUnitSquare]
    refine ⟨((p.1 : ℝ), (p.2 : ℝ)), Or.inl ⟨?_, p.2.2⟩, rfl⟩
    rcases hp with hp | hp
    · exact Or.inl (congrArg Subtype.val hp)
    · exact Or.inr (congrArg Subtype.val hp)
  have hqExtension : D.centralConnectorFilledPlaneSweepExtension b s = q := by
    rw [show s = coveringPlaneCoordinates.symm
        (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ) by rfl,
      D.centralConnectorFilledPlaneSweepExtension_apply_symm b
        ((p.1 : ℝ), (p.2 : ℝ)) ⟨p.1.2, p.2.2⟩]
  have hqCarrier : q ∈ (D.centralHeightFlowCompletedThetaSystem b).circle12.carrier := by
    rw [← D.image_frontier_centralConnectorFilledPlaneSweepExtension_eq_carrier b]
    exact ⟨s, hs, hqExtension⟩
  let A := (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
    standardPlaneFourPortThetaSystem
    (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
    standardPlaneFourPortTheta_outer_decomposition
  have hAqCarrier : A q ∈ standardPlaneFourPortThetaSystem.circle12.carrier := by
    rw [← (D.centralHeightFlowCompletedThetaSystem b)
      |>.outer12AmbientHomeomorph_image_circle12_carrier standardPlaneFourPortThetaSystem
        (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
        standardPlaneFourPortTheta_outer_decomposition]
    exact ⟨q, hqCarrier, rfl⟩
  rw [standardPlaneOuterThetaCarrier_eq_frontier,
    frontier_fourPortClosedRectangleInCoveringPlane] at hAqCarrier
  rw [← frontier_fourPortClosedRectangle] at hAqCarrier
  obtain ⟨z, hz, hzEq⟩ := hAqCarrier
  have hzValue : z = coveringPlaneCoordinates (A q) := by
    rw [← hzEq, coveringPlaneCoordinates.apply_symm_apply]
  rw [hzValue, ← D.centralHeightFlowFourPortHomeomorph_apply_coordinates] at hz
  simpa only [q, coveringPlaneCoordinates.apply_symm_apply] using hz

theorem centralHeightFlowFourPortHomeomorph_filledSweep_endpoint_mem_vertical
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval)
    (hp : p.1 = 0 ∨ p.1 = 1) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralConnectorFilledSweepCoordinate b p) ∈
      fourPortVerticalCarrier := by
  rw [fourPortVerticalCarrier_eq_pathRanges]
  rcases hp with hp | hp
  · have hpEq : p = (0, p.2) := Prod.ext hp rfl
    rw [hpEq, D.centralConnectorFilledSweepCoordinate_left]
    have hroute : D.centralLeftOuterArmCoordinate b
        (D.centralConnectorSweepTime p.2).1 ∈
        Set.range (D.centralLeftLowerHeightFlowBranchPath b) ∪
          Set.range (D.centralLeftUpperHeightFlowBranchPath b) := by
      rw [← D.range_centralConnectorFilledSweepCoordinate_left b]
      exact ⟨p.2, D.centralConnectorFilledSweepCoordinate_left b p.2⟩
    rcases hroute with ⟨u, hu⟩ | ⟨u, hu⟩
    · apply Or.inl
      rw [range_bandLeftPath_eq_standardHalves]
      exact Or.inl ⟨unitInterval.symm u, by
        rw [← D.centralHeightFlowFourPortHomeomorph_apply_leftLowerBranch b u, hu]⟩
    · apply Or.inl
      rw [range_bandLeftPath_eq_standardHalves]
      exact Or.inr ⟨u, by
        rw [← D.centralHeightFlowFourPortHomeomorph_apply_leftUpperBranch b u, hu]⟩
  · have hpEq : p = (1, p.2) := Prod.ext hp rfl
    rw [hpEq, D.centralConnectorFilledSweepCoordinate_right]
    have hroute : D.centralRightOuterArmCoordinate b
        (D.centralConnectorSweepTime p.2).1 ∈
        Set.range (D.centralRightLowerHeightFlowBranchPath b) ∪
          Set.range (D.centralRightUpperHeightFlowBranchPath b) := by
      rw [← D.range_centralConnectorFilledSweepCoordinate_right b]
      exact ⟨p.2, D.centralConnectorFilledSweepCoordinate_right b p.2⟩
    rcases hroute with ⟨u, hu⟩ | ⟨u, hu⟩
    · apply Or.inr
      rw [range_bandRightPath_eq_standardHalves]
      exact Or.inl ⟨u, by
        rw [← D.centralHeightFlowFourPortHomeomorph_apply_rightLowerBranch b u, hu]⟩
    · apply Or.inr
      rw [range_bandRightPath_eq_standardHalves]
      exact Or.inr ⟨unitInterval.symm u, by
        rw [← D.centralHeightFlowFourPortHomeomorph_apply_rightUpperBranch b u, hu]⟩

theorem canonicalFourPortVerticalFace_subset_initialFrontier
    (b : D.ConnectorBandIndex) :
    D.canonicalFourPortVerticalFace b ⊆
      frontier (superellipsoidReducedInside Phi frame c S.outer.scale) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [frontier_superellipsoidReducedInside Phi frame c D.scale_pos S.outer.surfaceRegular]
  change ((D.centralHeightFlowStraightenedTorusChart b z : transportedTorus Phi) : R3) ∈
    superellipsoidOuterTorusSection Phi frame c S.outer.scale
  rw [D.centralHeightFlowStraightenedTorusChart_coe,
    D.superellipsoidOuterTorusSection_eq_active_union_inactive]
  apply Or.inl
  rw [fourPortVerticalCarrier_eq_pathRanges] at hz
  rcases hz with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · have hx : (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (bandLeftPath u) ∈
        Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath :=
      ⟨u, rfl⟩
    rw [D.leftPath_range_eq_portBranches b] at hx
    rcases hx with hx | hx
    · exact D.lowerPortBranch_range_subset_activeCarrier b 0 hx
    · exact D.upperPortBranch_range_subset_activeCarrier b 0 hx
  · have hx : (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (bandRightPath u) ∈
        Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).rightPath :=
      ⟨u, rfl⟩
    rw [D.rightPath_range_eq_portBranches b] at hx
    rcases hx with hx | hx
    · exact D.lowerPortBranch_range_subset_activeCarrier b 1 hx
    · exact D.upperPortBranch_range_subset_activeCarrier b 1 hx

theorem canonicalFourPortClosedLens_inter_initialFrontier
    (b : D.ConnectorBandIndex) :
    D.canonicalFourPortClosedLens b ∩
        frontier (superellipsoidReducedInside Phi frame c S.outer.scale) =
      D.canonicalFourPortVerticalFace b := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxLens, hxFrontier⟩
    obtain ⟨p, hxValue⟩ :=
      D.canonicalFourPortClosedLens_exists_filledSweepCoordinate b hxLens
    have hpolynomial :
        superellipsoidPolynomial frame c (x : R3) = S.outer.scale ^ 256 := by
      rw [frontier_superellipsoidReducedInside Phi frame c D.scale_pos
        S.outer.surfaceRegular] at hxFrontier
      exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _
        D.scale_pos.le).mp hxFrontier.2
    have hdefect : D.centralHeightFlowOuterDefect b
        (D.centralConnectorSweepTime p.2).1
        (D.centralConnectorSweepParameter b p) = 0 := by
      have heq := D.superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate b p
      rw [← hxValue, hpolynomial] at heq
      simpa only [sub_self] using heq.symm
    have hp : p.1 = 0 ∨ p.1 = 1 := by
      by_contra hp
      push Not at hp
      have hneg := D.centralHeightFlowOuterDefect_sweepParameter_neg b p hp.1 hp.2
      linarith
    let z := D.centralHeightFlowFourPortHomeomorph b
      (D.centralConnectorFilledSweepCoordinate b p)
    refine ⟨z, D.centralHeightFlowFourPortHomeomorph_filledSweep_endpoint_mem_vertical
      b p hp, ?_⟩
    apply Subtype.ext
    rw [D.centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap]
    rw [show (D.centralHeightFlowFourPortHomeomorph b).symm z =
        D.centralConnectorFilledSweepCoordinate b p by
      exact (D.centralHeightFlowFourPortHomeomorph b).symm_apply_apply _]
    exact hxValue.symm
  · intro x hx
    exact ⟨Set.image_mono (by
      rintro ⟨u, v⟩ hu
      simp only [fourPortVerticalCarrier, Set.mem_ofPred_eq] at hu
      simp only [fourPortClosedRectangle, Set.mem_prod, mem_Icc]
      rcases hu with ⟨hu | hu, hv⟩
      · subst u
        exact ⟨⟨by norm_num, by norm_num⟩, hv⟩
      · subst u
        exact ⟨⟨by norm_num, by norm_num⟩, hv⟩) hx,
      D.canonicalFourPortVerticalFace_subset_initialFrontier b hx⟩

theorem fourPortCorner_mem_horizontalCarrier (side level : Fin 2) :
    fourPortCorner side level ∈ fourPortHorizontalCarrier := by
  fin_cases side <;> fin_cases level <;>
    simp [fourPortCorner, fourPortHorizontalCarrier, bandLeftBottom, bandLeftTop,
      bandRightBottom, bandRightTop]

theorem iUnion_range_canonicalBooleanLocalPaths_at_band
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex) :
    (⋃ e : Fin 2, Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart choice).path (b, e))) =
      if choice b then
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch
      else (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  by_cases hb : choice b = true
  · rw [if_pos hb]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨e, he⟩
      have heValue : e.1 = 0 ∨ e.1 = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp e.2)
      rcases heValue with heValue | heValue
      · have heEq : e = 0 := Fin.ext heValue
        subst e
        apply Or.inl
        simpa [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb] using he
      · have heEq : e = Fin.succ 0 := Fin.ext heValue
        subst e
        apply Or.inr
        change x ∈ Set.range (booleanFourPortLocalPath
          D.centralHeightFlowStraightenedChartFamily.chart choice
            (b, Fin.succ 0)) at he
        unfold booleanFourPortLocalPath at he
        simp only at he
        rw [dif_pos hb] at he
        simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using he
    · rintro (hx | hx)
      · exact ⟨0, by
          simpa [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb] using hx⟩
      · refine ⟨Fin.succ 0, ?_⟩
        change x ∈ Set.range (booleanFourPortLocalPath
          D.centralHeightFlowStraightenedChartFamily.chart choice
            (b, Fin.succ 0))
        unfold booleanFourPortLocalPath
        simp only
        rw [dif_pos hb]
        simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using hx
  · have hb' : choice b = false := by
      cases h : choice b <;> simp_all
    rw [if_neg hb]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨e, he⟩
      have heValue : e.1 = 0 ∨ e.1 = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp e.2)
      rcases heValue with heValue | heValue
      · have heEq : e = 0 := Fin.ext heValue
        subst e
        apply Or.inl
        simpa [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb'] using he
      · have heEq : e = Fin.succ 0 := Fin.ext heValue
        subst e
        apply Or.inr
        change x ∈ Set.range (booleanFourPortLocalPath
          D.centralHeightFlowStraightenedChartFamily.chart choice
            (b, Fin.succ 0)) at he
        unfold booleanFourPortLocalPath at he
        simp only at he
        rw [dif_neg hb] at he
        simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using he
    · rintro (hx | hx)
      · exact ⟨0, by
          simpa [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb'] using hx⟩
      · refine ⟨Fin.succ 0, ?_⟩
        change x ∈ Set.range (booleanFourPortLocalPath
          D.centralHeightFlowStraightenedChartFamily.chart choice
            (b, Fin.succ 0))
        unfold booleanFourPortLocalPath
        simp only
        rw [dif_neg hb]
        simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using hx

theorem iUnion_range_canonicalBooleanLocalPaths
    (choice : D.ConnectorBandIndex → Bool) :
    (⋃ e : FourPortLocalEdge
        D.centralCutOrder.toPairedSeamEnumeration.bandCount,
      Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart choice).path e)) =
      ⋃ b, if choice b then
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch
      else (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  calc
    (⋃ e : FourPortLocalEdge
        D.centralCutOrder.toPairedSeamEnumeration.bandCount,
      Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart choice).path e)) =
        ⋃ b, ⋃ e : Fin 2,
          Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart choice).path (b, e)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨⟨b, e⟩, he⟩
        exact ⟨b, e, he⟩
      · rintro ⟨b, e, he⟩
        exact ⟨⟨b, e⟩, he⟩
    _ = _ := by
      apply iUnion_congr
      intro b
      exact D.iUnion_range_canonicalBooleanLocalPaths_at_band choice b

theorem transportedTorusPart_parallelPatch
    (b : D.ConnectorBandIndex) :
    transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch =
      D.canonicalFourPortVerticalFace b := by
  change transportedTorusPart Phi
      (D.centralHeightFlowStraightenedBandData b).toPairedSeamBandChart.parallelPatch = _
  rw [← image_chart_fourPortVerticalCarrier
    (D.centralHeightFlowStraightenedBandData b)]
  ext x
  constructor
  · rintro ⟨z, hz, hzValue⟩
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    exact hzValue
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem transportedTorusPart_surgeryPatch
    (b : D.ConnectorBandIndex) :
    transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch =
      D.canonicalFourPortHorizontalFace b := by
  change transportedTorusPart Phi
      (D.centralHeightFlowStraightenedBandData b).toPairedSeamBandChart.surgeryPatch = _
  rw [← image_chart_fourPortHorizontalCarrier
    (D.centralHeightFlowStraightenedBandData b)]
  ext x
  constructor
  · rintro ⟨z, hz, hzValue⟩
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    exact hzValue
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem canonicalFourPortClosedLens_subset_closure_reducedInside
    (b : D.ConnectorBandIndex) :
    D.canonicalFourPortClosedLens b ⊆
      closure (superellipsoidReducedInside Phi frame c S.outer.scale) := by
  intro x hx
  obtain ⟨p, hxValue⟩ := D.canonicalFourPortClosedLens_exists_filledSweepCoordinate b hx
  have hnonpos := D.centralHeightFlowOuterDefect_sweepParameter_nonpos b p
  have hpolynomial :
      superellipsoidPolynomial frame c (x : R3) - S.outer.scale ^ 256 ≤ 0 := by
    rw [hxValue, D.superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate]
    exact hnonpos
  rcases lt_or_eq_of_le hpolynomial with hneg | hzero
  · apply subset_closure
    rw [superellipsoidReducedInside_eq_transportedTorusPart Phi frame c D.scale_pos]
    change (x : R3) ∈ superellipsoidBody frame c S.outer.scale
    rw [mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ D.scale_pos]
    linarith
  · apply frontier_subset_closure
    rw [frontier_superellipsoidReducedInside Phi frame c D.scale_pos
      S.outer.surfaceRegular]
    change (x : R3) ∈ superellipsoidOuterTorusSection Phi frame c S.outer.scale
    refine ⟨x.2, ?_⟩
    rw [mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ D.scale_pos.le]
    linarith

theorem canonicalFourPortOpenLens_subset_reducedInside
    (b : D.ConnectorBandIndex) :
    D.canonicalFourPortOpenLens b ⊆
      superellipsoidReducedInside Phi frame c S.outer.scale := by
  rintro _ ⟨z, hz, rfl⟩
  have hzFilled : (D.centralHeightFlowFourPortHomeomorph b).symm z ∈
      Set.range (D.centralConnectorFilledSweepCoordinate b) := by
    rw [← D.image_fourPortClosedRectangle_eq_range_centralConnectorFilledSweepCoordinate b]
    exact ⟨z, interior_subset hz, rfl⟩
  obtain ⟨p, hp⟩ := hzFilled
  have hp0 : p.1 ≠ 0 := by
    intro hp0
    have hfrontier :=
      D.centralHeightFlowFourPortHomeomorph_filledSweep_endpoint_mem_frontier b p
        (Or.inl hp0)
    have hzEq : z = D.centralHeightFlowFourPortHomeomorph b
        (D.centralConnectorFilledSweepCoordinate b p) := by
      calc
        z = D.centralHeightFlowFourPortHomeomorph b
            ((D.centralHeightFlowFourPortHomeomorph b).symm z) :=
          ((D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply z).symm
        _ = _ := congrArg (D.centralHeightFlowFourPortHomeomorph b) hp.symm
    exact Set.disjoint_left.mp disjoint_interior_frontier hz (hzEq ▸ hfrontier)
  have hp1 : p.1 ≠ 1 := by
    intro hp1
    have hfrontier :=
      D.centralHeightFlowFourPortHomeomorph_filledSweep_endpoint_mem_frontier b p
        (Or.inr hp1)
    have hzEq : z = D.centralHeightFlowFourPortHomeomorph b
        (D.centralConnectorFilledSweepCoordinate b p) := by
      calc
        z = D.centralHeightFlowFourPortHomeomorph b
            ((D.centralHeightFlowFourPortHomeomorph b).symm z) :=
          ((D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply z).symm
        _ = _ := congrArg (D.centralHeightFlowFourPortHomeomorph b) hp.symm
    exact Set.disjoint_left.mp disjoint_interior_frontier hz (hzEq ▸ hfrontier)
  rw [superellipsoidReducedInside_eq_transportedTorusPart Phi frame c D.scale_pos]
  change ((D.centralHeightFlowStraightenedTorusChart b z : transportedTorus Phi) : R3) ∈
    superellipsoidBody frame c S.outer.scale
  rw [mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ D.scale_pos]
  rw [D.centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap, ← hp]
  have heq := D.superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate b p
  have hneg := D.centralHeightFlowOuterDefect_sweepParameter_neg b p hp0 hp1
  linarith

theorem centralHeightFlowStraightened_bottom_mem_reducedInside
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    D.centralHeightFlowStraightenedTorusChart b (bandBottomPath u) ∈
      superellipsoidReducedInside Phi frame c S.outer.scale := by
  rw [superellipsoidReducedInside_eq_transportedTorusPart Phi frame c D.scale_pos]
  change ((D.centralHeightFlowStraightenedTorusChart b (bandBottomPath u) :
    transportedTorus Phi) : R3) ∈ superellipsoidBody frame c S.outer.scale
  rw [mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ D.scale_pos]
  rw [D.centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap,
    D.centralHeightFlowFourPortHomeomorph_symm_apply_lowerConnector,
    ← D.centralConnectorFilledSweepCoordinate_bottom]
  have heq := D.superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate b (u, 0)
  have hneg := D.centralHeightFlowOuterDefect_sweepParameter_neg b (u, 0) hu0 hu1
  linarith

theorem centralHeightFlowStraightened_top_mem_reducedInside
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    D.centralHeightFlowStraightenedTorusChart b (bandTopPath u) ∈
      superellipsoidReducedInside Phi frame c S.outer.scale := by
  rw [superellipsoidReducedInside_eq_transportedTorusPart Phi frame c D.scale_pos]
  change ((D.centralHeightFlowStraightenedTorusChart b (bandTopPath u) :
    transportedTorus Phi) : R3) ∈ superellipsoidBody frame c S.outer.scale
  rw [mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ D.scale_pos]
  rw [D.centralHeightFlowStraightenedTorusChart_eq_canonicalBandMap,
    D.centralHeightFlowFourPortHomeomorph_symm_apply_upperConnector,
    ← D.centralConnectorFilledSweepCoordinate_top]
  have heq := D.superellipsoidPolynomial_canonicalBandMap_filledSweepCoordinate b (u, 1)
  have hneg := D.centralHeightFlowOuterDefect_sweepParameter_neg b (u, 1) hu0 hu1
  linarith

/-- The finite closed union removed by one Boolean resolution choice. -/
def canonicalBooleanRemovedLenses
    (choice : D.ConnectorBandIndex → Bool) : Set (transportedTorus Phi) :=
  ⋃ b, if choice b then D.canonicalFourPortClosedLens b else ∅

theorem canonicalBooleanRemovedLenses_update_true
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    D.canonicalBooleanRemovedLenses (Function.update choice b true) =
      D.canonicalBooleanRemovedLenses choice ∪ D.canonicalFourPortClosedLens b := by
  ext x
  constructor
  · intro hx
    rw [canonicalBooleanRemovedLenses] at hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    by_cases heb : e = b
    · subst e
      exact Or.inr (by simpa using he)
    · apply Or.inl
      rw [canonicalBooleanRemovedLenses]
      exact Set.mem_iUnion.mpr ⟨e, by
        simpa [Function.update_of_ne heb] using he⟩
  · rintro (hx | hx)
    · rw [canonicalBooleanRemovedLenses] at hx ⊢
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨e, ?_⟩
      by_cases heb : e = b
      · subst e
        simp [hb] at he
      · simpa [Function.update_of_ne heb] using he
    · rw [canonicalBooleanRemovedLenses]
      exact Set.mem_iUnion.mpr ⟨b, by simpa using hx⟩

theorem isClosed_canonicalBooleanRemovedLenses
    (choice : D.ConnectorBandIndex → Bool) :
    IsClosed (D.canonicalBooleanRemovedLenses choice) := by
  apply isClosed_iUnion_of_finite
  intro b
  split
  · exact D.isClosed_canonicalFourPortClosedLens b
  · exact isClosed_empty

theorem canonicalBooleanSelectedLenses_pairwise_disjoint
    (choice : D.ConnectorBandIndex → Bool) :
    Pairwise fun b e : D.ConnectorBandIndex ↦
      Disjoint (if choice b then D.canonicalFourPortClosedLens b else ∅)
        (if choice e then D.canonicalFourPortClosedLens e else ∅) := by
  intro b e hbe
  split <;> split
  · exact D.canonicalFourPortClosedLens_pairwise_disjoint hbe
  · exact Set.disjoint_empty _
  · exact Set.empty_disjoint _
  · exact Set.empty_disjoint _

theorem interior_canonicalBooleanRemovedLenses
    (choice : D.ConnectorBandIndex → Bool) :
    interior (D.canonicalBooleanRemovedLenses choice) =
      ⋃ b, if choice b then D.canonicalFourPortOpenLens b else ∅ := by
  rw [canonicalBooleanRemovedLenses,
    interior_iUnion_eq_iUnion_interior_of_pairwise_disjoint]
  · apply iUnion_congr
    intro b
    split
    · exact D.interior_canonicalFourPortClosedLens b
    · exact interior_empty
  · intro b
    split
    · exact D.isClosed_canonicalFourPortClosedLens b
    · exact isClosed_empty
  · exact D.canonicalBooleanSelectedLenses_pairwise_disjoint choice

theorem interior_canonicalBooleanRemovedLenses_subset_reducedInside
    (choice : D.ConnectorBandIndex → Bool) :
    interior (D.canonicalBooleanRemovedLenses choice) ⊆
      superellipsoidReducedInside Phi frame c S.outer.scale := by
  rw [D.interior_canonicalBooleanRemovedLenses choice]
  apply iUnion_subset
  intro b
  split
  · exact D.canonicalFourPortOpenLens_subset_reducedInside b
  · exact Set.empty_subset _

theorem canonicalBooleanRemovedLenses_subset_closure_reducedInside
    (choice : D.ConnectorBandIndex → Bool) :
    D.canonicalBooleanRemovedLenses choice ⊆
      closure (superellipsoidReducedInside Phi frame c S.outer.scale) := by
  rw [canonicalBooleanRemovedLenses]
  apply iUnion_subset
  intro b
  split
  · exact D.canonicalFourPortClosedLens_subset_closure_reducedInside b
  · exact Set.empty_subset _

theorem canonicalBooleanRemovedLenses_subset_closure_interior
    (choice : D.ConnectorBandIndex → Bool) :
    D.canonicalBooleanRemovedLenses choice ⊆
      closure (interior (D.canonicalBooleanRemovedLenses choice)) := by
  intro x hx
  rw [canonicalBooleanRemovedLenses] at hx
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hx
  split at hxb
  · rw [D.interior_canonicalBooleanRemovedLenses choice]
    apply closure_mono ?_
      (D.canonicalFourPortClosedLens_subset_closure_openLens b hxb)
    intro y hy
    exact Set.mem_iUnion.mpr ⟨b, by simp_all⟩
  · exact hxb.elim

/-- The initial strict body with the selected disjoint four-port disks removed. -/
def canonicalBooleanReducedRegion
    (choice : D.ConnectorBandIndex → Bool) : Set (transportedTorus Phi) :=
  superellipsoidReducedInside Phi frame c S.outer.scale \
    D.canonicalBooleanRemovedLenses choice

@[simp] theorem canonicalBooleanRemovedLenses_false :
    D.canonicalBooleanRemovedLenses (fun _ ↦ false) = ∅ := by
  rw [canonicalBooleanRemovedLenses]
  simp

@[simp] theorem canonicalBooleanReducedRegion_false :
    D.canonicalBooleanReducedRegion (fun _ ↦ false) =
      superellipsoidReducedInside Phi frame c S.outer.scale := by
  rw [canonicalBooleanReducedRegion, D.canonicalBooleanRemovedLenses_false]
  exact Set.sdiff_empty

theorem canonicalBooleanReducedRegion_update_true
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    D.canonicalBooleanReducedRegion (Function.update choice b true) =
      D.canonicalBooleanReducedRegion choice \ D.canonicalFourPortClosedLens b := by
  rw [canonicalBooleanReducedRegion, D.canonicalBooleanRemovedLenses_update_true choice b hb,
    canonicalBooleanReducedRegion]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

theorem canonicalBooleanReducedRegion_labelChange_subset_lens
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    {x | (x ∈ D.canonicalBooleanReducedRegion choice) ≠
        (x ∈ D.canonicalBooleanReducedRegion (Function.update choice b true))} ⊆
      D.canonicalFourPortClosedLens b := by
  intro x hx
  by_contra hxLens
  apply hx
  rw [D.canonicalBooleanReducedRegion_update_true choice b hb]
  simp only [Set.mem_sdiff, hxLens, not_false_eq_true, and_true]

theorem isOpen_canonicalBooleanReducedRegion
    (choice : D.ConnectorBandIndex → Bool) :
    IsOpen (D.canonicalBooleanReducedRegion choice) :=
  (isOpen_superellipsoidReducedInside Phi frame c S.outer.scale).sdiff
    (D.isClosed_canonicalBooleanRemovedLenses choice)

theorem frontier_canonicalBooleanReducedRegion_eq_closure_active
    (choice : D.ConnectorBandIndex → Bool) :
    frontier (D.canonicalBooleanReducedRegion choice) =
      closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) := by
  rw [canonicalBooleanReducedRegion]
  apply frontier_sdiff_eq_closure_active_of_locallyPreconnected
    (isOpen_superellipsoidReducedInside Phi frame c S.outer.scale)
    (D.isClosed_canonicalBooleanRemovedLenses choice)
    (D.interior_canonicalBooleanRemovedLenses_subset_reducedInside choice)
    (D.canonicalBooleanRemovedLenses_subset_closure_interior choice)
  intro x hx
  exact isLocallyPreconnectedWithinAt_superellipsoidReducedInside
    Phi frame c D.scale_pos S.outer.surfaceRegular hx.1

/-- The moving active carrier together with the fixed seam-free outer circles. -/
def canonicalBooleanAugmentedAmbientSection
    (choice : D.ConnectorBandIndex → Bool) : Set R3 :=
  D.canonicalBooleanOutsidePathData.ambientSection choice ∪
    D.canonicalInactiveOuterCarrier

theorem canonicalBooleanAugmentedAmbientSection_eq_paths
    (choice : D.ConnectorBandIndex → Bool) :
    D.canonicalBooleanAugmentedAmbientSection choice =
      (⋃ e : BooleanOutsideEdge D.centralOuterOrder,
          Set.range (D.canonicalBooleanOutsidePath e)) ∪
        (⋃ b, if choice b then
          (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch
        else (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch) ∪
          D.canonicalInactiveOuterCarrier := by
  rw [canonicalBooleanAugmentedAmbientSection,
    D.canonicalBooleanOutsidePathData.ambientSection_eq_iUnion_ranges]
  change ((⋃ e : BooleanOutsideEdge D.centralOuterOrder,
      Set.range (D.canonicalBooleanOutsidePath e)) ∪
        (⋃ e : FourPortLocalEdge
          D.centralCutOrder.toPairedSeamEnumeration.bandCount,
          Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart choice).path e))) ∪
      D.canonicalInactiveOuterCarrier = _
  rw [D.iUnion_range_canonicalBooleanLocalPaths choice]

theorem canonicalBooleanAugmentedAmbientSection_update_true_subset
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex) :
    D.canonicalBooleanAugmentedAmbientSection (Function.update choice b true) ⊆
      D.canonicalBooleanAugmentedAmbientSection choice ∪
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
  intro x hx
  rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths] at hx ⊢
  rcases hx with (hxOutside | hxLocal) | hxInactive
  · exact Or.inl (Or.inl (Or.inl hxOutside))
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxLocal
    by_cases heb : e = b
    · subst e
      exact Or.inr (by simpa using he)
    · apply Or.inl
      apply Or.inl
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨e, by
        simpa [Function.update_of_ne heb] using he⟩
  · exact Or.inl (Or.inr hxInactive)

theorem canonicalBooleanAugmentedAmbientSection_subset_update_true_union
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    D.canonicalBooleanAugmentedAmbientSection choice ⊆
      D.canonicalBooleanAugmentedAmbientSection (Function.update choice b true) ∪
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  intro x hx
  rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths] at hx ⊢
  rcases hx with (hxOutside | hxLocal) | hxInactive
  · exact Or.inl (Or.inl (Or.inl hxOutside))
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxLocal
    by_cases heb : e = b
    · subst e
      exact Or.inr (by simpa [hb] using he)
    · apply Or.inl
      apply Or.inl
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨e, by
        simpa [Function.update_of_ne heb] using he⟩
  · exact Or.inl (Or.inr hxInactive)

/-- The exact finite circle section including the fixed seam-free outer circles. -/
noncomputable def canonicalBooleanAugmentedCircleSection
    (choice : D.ConnectorBandIndex → Bool) :
    FiniteEmbeddedTorusCircleSection Phi
      (D.canonicalBooleanAugmentedAmbientSection choice)
      ((D.canonicalBooleanOutsidePathData.system choice).CycleIndex ⊕
        D.centralOuterOrder.InactiveOuterCircle) where
  circle
    | Sum.inl q => D.canonicalBooleanOutsidePathData.circleSection choice |>.circle q
    | Sum.inr i => D.centralGraph.outer.circle i.1
  circle_mem_section := by
    intro i x hx
    rcases i with q | i
    · exact Or.inl
        (D.canonicalBooleanOutsidePathData.circleSection choice |>.circle_mem_section q hx)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)
  pairwise_disjoint := by
    intro i j hij
    rcases i with q | i <;> rcases j with r | j
    · exact D.canonicalBooleanOutsidePathData.circleSection choice |>.pairwise_disjoint
        (fun h ↦ hij (congrArg Sum.inl h))
    · exact
        (D.canonicalBooleanOutsidePathData_ambientSection_disjoint_inactiveOuterCircle
          choice j).mono
          (D.canonicalBooleanOutsidePathData.circleSection choice |>.circle_mem_section q)
          Set.Subset.rfl
    · exact ((D.canonicalBooleanOutsidePathData_ambientSection_disjoint_inactiveOuterCircle
          choice i).mono
          (D.canonicalBooleanOutsidePathData.circleSection choice |>.circle_mem_section r)
          Set.Subset.rfl).symm
    · exact D.centralGraph.outer.pairwise_disjoint
        (fun h ↦ hij (congrArg Sum.inr (Subtype.ext h)))
  section_exact := by
    ext x
    constructor
    · intro hx
      change x ∈ D.canonicalBooleanOutsidePathData.ambientSection choice ∪
        D.canonicalInactiveOuterCarrier at hx
      rcases hx with hx | hx
      · have hxCycles := Set.ext_iff.mp
          (D.canonicalBooleanOutsidePathData.circleSection choice).section_exact x |>.mp hx
        obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hxCycles
        exact Set.mem_iUnion.mpr ⟨Sum.inl q, hq⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      change x ∈ D.canonicalBooleanOutsidePathData.ambientSection choice ∪
        D.canonicalInactiveOuterCarrier
      rcases q with q | i
      · apply Or.inl
        apply Set.ext_iff.mp
          (D.canonicalBooleanOutsidePathData.circleSection choice).section_exact x |>.mpr
        exact Set.mem_iUnion.mpr ⟨q, hq⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hq⟩)

theorem isCompact_canonicalBooleanAugmentedAmbientSection
    (choice : D.ConnectorBandIndex → Bool) :
    IsCompact (D.canonicalBooleanAugmentedAmbientSection choice) := by
  rw [(D.canonicalBooleanAugmentedCircleSection choice).section_exact]
  exact isCompact_iUnion fun i ↦
    isCompact_range (D.canonicalBooleanAugmentedCircleSection choice |>.circle i
      |>.isEmbedding.continuous)

theorem isClosed_transportedTorusPart_canonicalBooleanAugmentedAmbientSection
    (choice : D.ConnectorBandIndex → Bool) :
    IsClosed (transportedTorusPart Phi
      (D.canonicalBooleanAugmentedAmbientSection choice)) :=
  (D.isCompact_canonicalBooleanAugmentedAmbientSection choice).isClosed.preimage
    continuous_subtype_val

theorem canonicalBooleanAugmentedAmbientSection_false :
    D.canonicalBooleanAugmentedAmbientSection (fun _ ↦ false) =
      superellipsoidOuterTorusSection Phi frame c S.outer.scale := by
  calc
    D.canonicalBooleanAugmentedAmbientSection (fun _ ↦ false) =
        (⋃ i : D.centralOuterOrder.ActiveOuterCircle,
          Set.range (D.centralGraph.outer.circle i.1).circle) ∪
            D.canonicalInactiveOuterCarrier := by
      rw [canonicalBooleanAugmentedAmbientSection,
        D.canonicalBooleanOutsidePathData_ambientSection_false_eq_activeOuterCarrier]
    _ = superellipsoidOuterTorusSection Phi frame c S.outer.scale :=
      D.superellipsoidOuterTorusSection_eq_active_union_inactive.symm

theorem frontier_canonicalBooleanReducedRegion_false :
    frontier (D.canonicalBooleanReducedRegion (fun _ ↦ false)) =
      transportedTorusPart Phi
        (D.canonicalBooleanAugmentedAmbientSection (fun _ ↦ false)) := by
  have hremoved : D.canonicalBooleanRemovedLenses (fun _ ↦ false) = ∅ := by
    ext x
    simp [canonicalBooleanRemovedLenses]
  rw [canonicalBooleanReducedRegion, hremoved, sdiff_empty,
    frontier_superellipsoidReducedInside Phi frame c D.scale_pos S.outer.surfaceRegular,
    D.canonicalBooleanAugmentedAmbientSection_false]

theorem initialFrontier_sdiff_removedLenses_subset_augmentedCarrier
    (choice : D.ConnectorBandIndex → Bool) :
    frontier (superellipsoidReducedInside Phi frame c S.outer.scale) \
        D.canonicalBooleanRemovedLenses choice ⊆
      transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) := by
  intro x hx
  have hxFalse : x ∈ transportedTorusPart Phi
      (D.canonicalBooleanAugmentedAmbientSection (fun _ ↦ false)) := by
    rw [← D.frontier_canonicalBooleanReducedRegion_false]
    simpa [canonicalBooleanReducedRegion, canonicalBooleanRemovedLenses] using hx.1
  change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection (fun _ ↦ false) at hxFalse
  rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths] at hxFalse
  change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection choice
  rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths]
  rcases hxFalse with (hxOutside | hxLocal) | hxInactive
  · exact Or.inl (Or.inl hxOutside)
  · obtain ⟨b, hxParallel⟩ := Set.mem_iUnion.mp hxLocal
    by_cases hb : choice b = true
    · exfalso
      apply hx.2
      rw [canonicalBooleanRemovedLenses]
      apply Set.mem_iUnion.mpr
      refine ⟨b, ?_⟩
      rw [if_pos hb]
      have hxVertical : x ∈ D.canonicalFourPortVerticalFace b := by
        rw [← D.transportedTorusPart_parallelPatch b]
        exact hxParallel
      rw [← D.canonicalFourPortClosedLens_inter_initialFrontier b] at hxVertical
      exact hxVertical.1
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨b, by simpa [hb] using hxParallel⟩))
  · exact Or.inr hxInactive

theorem removedLensesFrontier_inter_initial_subset_augmentedCarrier
    (choice : D.ConnectorBandIndex → Bool) :
    frontier (D.canonicalBooleanRemovedLenses choice) ∩
        superellipsoidReducedInside Phi frame c S.outer.scale ⊆
      transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) := by
  intro x hx
  have hxRemoved : x ∈ D.canonicalBooleanRemovedLenses choice := by
    rw [← (D.isClosed_canonicalBooleanRemovedLenses choice).closure_eq]
    exact frontier_subset_closure hx.1
  rw [canonicalBooleanRemovedLenses] at hxRemoved
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxRemoved
  split at hxb
  next hb =>
    have hxNotInterior : x ∉ interior (D.canonicalFourPortClosedLens b) := by
      intro hxInterior
      have hxInteriorUnion : x ∈ interior (D.canonicalBooleanRemovedLenses choice) := by
        rw [D.interior_canonicalBooleanRemovedLenses choice]
        apply Set.mem_iUnion.mpr
        refine ⟨b, ?_⟩
        rw [if_pos hb, ← D.interior_canonicalFourPortClosedLens b]
        exact hxInterior
      rw [(D.isClosed_canonicalBooleanRemovedLenses choice).frontier_eq] at hx
      exact hx.1.2 hxInteriorUnion
    have hxLensFrontier : x ∈ frontier (D.canonicalFourPortClosedLens b) := by
      rw [(D.isClosed_canonicalFourPortClosedLens b).frontier_eq]
      exact ⟨hxb, hxNotInterior⟩
    rw [D.frontier_canonicalFourPortClosedLens_eq_faces b] at hxLensFrontier
    rcases hxLensFrontier with hxVertical | hxHorizontal
    · exfalso
      have hxInitialFrontier := D.canonicalFourPortVerticalFace_subset_initialFrontier
        b hxVertical
      rw [(isOpen_superellipsoidReducedInside Phi frame c S.outer.scale).frontier_eq]
        at hxInitialFrontier
      exact hxInitialFrontier.2 hx.2
    · change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection choice
      rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths]
      apply Or.inl
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨b, ?_⟩
      rw [if_pos hb]
      have hxSurgery : x ∈ transportedTorusPart Phi
          (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
        rw [D.transportedTorusPart_surgeryPatch b]
        exact hxHorizontal
      exact hxSurgery
  next hb => exact hxb.elim

theorem selectedLens_frontier_subset_removedLenses_frontier
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = true) :
    frontier (D.canonicalFourPortClosedLens b) ⊆
      frontier (D.canonicalBooleanRemovedLenses choice) := by
  intro x hx
  rw [(D.isClosed_canonicalBooleanRemovedLenses choice).frontier_eq]
  constructor
  · rw [canonicalBooleanRemovedLenses]
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    rw [if_pos hb]
    rw [← (D.isClosed_canonicalFourPortClosedLens b).closure_eq]
    exact frontier_subset_closure hx
  · intro hxInterior
    rw [D.interior_canonicalBooleanRemovedLenses choice] at hxInterior
    obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxInterior
    split at hxe
    next he =>
      by_cases heb : e = b
      · subst e
        have hxeInterior : x ∈ interior (D.canonicalFourPortClosedLens b) := by
          rw [D.interior_canonicalFourPortClosedLens b]
          exact hxe
        exact Set.disjoint_left.mp disjoint_interior_frontier hxeInterior hx
      · have hxb : x ∈ D.canonicalFourPortClosedLens b := by
          rw [(D.isClosed_canonicalFourPortClosedLens b).frontier_eq] at hx
          exact hx.1
        have hxeClosed : x ∈ D.canonicalFourPortClosedLens e := by
          apply interior_subset
          rw [D.interior_canonicalFourPortClosedLens e]
          exact hxe
        exact Set.disjoint_left.mp (D.canonicalFourPortClosedLens_pairwise_disjoint heb)
          hxeClosed hxb
    next he => exact hxe.elim

theorem selectedHorizontalFace_subset_closure_active
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = true) :
    D.canonicalFourPortHorizontalFace b ⊆
      closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [fourPortHorizontalCarrier_eq_pathRanges] at hz
  rcases hz with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · apply map_mem_closure
      ((D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).continuous.comp
        bandBottomPath.continuous)
      (s := Ioo (0 : unitInterval) 1)
    · rw [closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1)]
      exact ⟨u.2.1, u.2.2⟩
    · intro v hv
      apply Or.inr
      constructor
      · apply D.selectedLens_frontier_subset_removedLenses_frontier choice b hb
        rw [D.frontier_canonicalFourPortClosedLens_eq_faces b]
        exact Or.inr ⟨bandBottomPath v, by
          rw [fourPortHorizontalCarrier_eq_pathRanges]
          exact Or.inl ⟨v, rfl⟩, rfl⟩
      · change D.centralHeightFlowStraightenedTorusChart b (bandBottomPath v) ∈ _
        exact D.centralHeightFlowStraightened_bottom_mem_reducedInside b v
          (ne_of_gt hv.1) (ne_of_lt hv.2)
  · apply map_mem_closure
      ((D.centralHeightFlowStraightenedTorusChart_isOpenEmbedding b).continuous.comp
        bandTopPath.continuous)
      (s := Ioo (0 : unitInterval) 1)
    · rw [closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1)]
      exact ⟨u.2.1, u.2.2⟩
    · intro v hv
      apply Or.inr
      constructor
      · apply D.selectedLens_frontier_subset_removedLenses_frontier choice b hb
        rw [D.frontier_canonicalFourPortClosedLens_eq_faces b]
        exact Or.inr ⟨bandTopPath v, by
          rw [fourPortHorizontalCarrier_eq_pathRanges]
          exact Or.inr ⟨v, rfl⟩, rfl⟩
      · change D.centralHeightFlowStraightenedTorusChart b (bandTopPath v) ∈ _
        exact D.centralHeightFlowStraightened_top_mem_reducedInside b v
          (ne_of_gt hv.1) (ne_of_lt hv.2)

theorem canonicalBooleanOutsidePath_subset_initialFrontier
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    transportedTorusPart Phi (Set.range (D.canonicalBooleanOutsidePath e)) ⊆
      frontier (superellipsoidReducedInside Phi frame c S.outer.scale) := by
  intro x hx
  rw [frontier_superellipsoidReducedInside Phi frame c D.scale_pos S.outer.surfaceRegular]
  change (x : R3) ∈ superellipsoidOuterTorusSection Phi frame c S.outer.scale
  rw [D.superellipsoidOuterTorusSection_eq_active_union_inactive]
  exact Or.inl (D.canonicalBooleanOutsidePath_range_subset_activeCarrier e hx)

theorem canonicalInactiveOuterCarrier_subset_initialFrontier :
    transportedTorusPart Phi D.canonicalInactiveOuterCarrier ⊆
      frontier (superellipsoidReducedInside Phi frame c S.outer.scale) := by
  intro x hx
  rw [frontier_superellipsoidReducedInside Phi frame c D.scale_pos S.outer.surfaceRegular]
  change (x : R3) ∈ superellipsoidOuterTorusSection Phi frame c S.outer.scale
  rw [D.superellipsoidOuterTorusSection_eq_active_union_inactive]
  exact Or.inr hx

theorem unselectedVerticalFace_subset_active
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    D.canonicalFourPortVerticalFace b ⊆
      sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice) := by
  intro x hx
  apply Or.inl
  refine ⟨D.canonicalFourPortVerticalFace_subset_initialFrontier b hx, ?_⟩
  intro hxRemoved
  rw [canonicalBooleanRemovedLenses] at hxRemoved
  obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxRemoved
  split at hxe
  next he =>
    have hxb : x ∈ D.canonicalFourPortClosedLens b := by
      have hxInter : x ∈ D.canonicalFourPortClosedLens b ∩
          frontier (superellipsoidReducedInside Phi frame c S.outer.scale) := by
        rw [D.canonicalFourPortClosedLens_inter_initialFrontier b]
        exact hx
      exact hxInter.1
    by_cases heb : e = b
    · subst e
      simp_all
    · exact Set.disjoint_left.mp (D.canonicalFourPortClosedLens_pairwise_disjoint heb)
        hxe hxb
  next he => exact hxe.elim

theorem canonicalBooleanOutsidePath_subset_closure_active
    (choice : D.ConnectorBandIndex → Bool)
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    transportedTorusPart Phi (Set.range (D.canonicalBooleanOutsidePath e)) ⊆
      closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) := by
  intro x hx
  have hxFrontier := D.canonicalBooleanOutsidePath_subset_initialFrontier e hx
  by_cases hxRemoved : x ∈ D.canonicalBooleanRemovedLenses choice
  · rw [canonicalBooleanRemovedLenses] at hxRemoved
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxRemoved
    split at hxb
    next hb =>
      have hxVertical : x ∈ D.canonicalFourPortVerticalFace b := by
        rw [← D.canonicalFourPortClosedLens_inter_initialFrontier b]
        exact ⟨hxb, hxFrontier⟩
      have hxParallel : x ∈ transportedTorusPart Phi
          (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
        rw [D.transportedTorusPart_parallelPatch b]
        exact hxVertical
      have hxSupport : (x : R3) ∈
          (D.centralHeightFlowStraightenedChartFamily.chart b).support :=
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch_subset_support
          hxParallel
      obtain ⟨j, hband, hxPoint⟩ :=
        D.canonicalBooleanOutsidePath_mem_support_exists_endpoint e b hx hxSupport
      let v := booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder (e, j)
      have hxHorizontal : x ∈ D.canonicalFourPortHorizontalFace b := by
        refine ⟨fourPortCorner v.2.1 v.2.2,
          fourPortCorner_mem_horizontalCarrier v.2.1 v.2.2, ?_⟩
        apply Subtype.ext
        rw [D.centralHeightFlowStraightenedTorusChart_coe]
        rw [← hband]
        simpa only [fourPortChartPoint, v] using hxPoint.symm
      exact D.selectedHorizontalFace_subset_closure_active choice b hb hxHorizontal
    next hb => exact hxb.elim
  · apply subset_closure
    exact Or.inl ⟨hxFrontier, hxRemoved⟩

theorem canonicalInactiveOuterCarrier_subset_closure_active
    (choice : D.ConnectorBandIndex → Bool) :
    transportedTorusPart Phi D.canonicalInactiveOuterCarrier ⊆
      closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) := by
  intro x hx
  have hxFrontier := D.canonicalInactiveOuterCarrier_subset_initialFrontier hx
  by_cases hxRemoved : x ∈ D.canonicalBooleanRemovedLenses choice
  · rw [canonicalBooleanRemovedLenses] at hxRemoved
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxRemoved
    split at hxb
    next hb =>
      have hxVertical : x ∈ D.canonicalFourPortVerticalFace b := by
        rw [← D.canonicalFourPortClosedLens_inter_initialFrontier b]
        exact ⟨hxb, hxFrontier⟩
      have hxParallel : x ∈ transportedTorusPart Phi
          (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
        rw [D.transportedTorusPart_parallelPatch b]
        exact hxVertical
      have hxSupport : (x : R3) ∈
          (D.centralHeightFlowStraightenedChartFamily.chart b).support :=
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch_subset_support
          hxParallel
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact False.elim <| Set.disjoint_left.mp
        (D.inactiveOuterCircle_range_disjoint_support i b) hi hxSupport
    next hb => exact hxb.elim
  · apply subset_closure
    exact Or.inl ⟨hxFrontier, hxRemoved⟩

theorem activeFrontier_subset_augmentedCarrier
    (choice : D.ConnectorBandIndex → Bool) :
    sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice) ⊆
      transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) := by
  intro x hx
  rcases hx with hx | hx
  · exact D.initialFrontier_sdiff_removedLenses_subset_augmentedCarrier choice hx
  · exact D.removedLensesFrontier_inter_initial_subset_augmentedCarrier choice hx

theorem augmentedCarrier_subset_closure_activeFrontier
    (choice : D.ConnectorBandIndex → Bool) :
    transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) ⊆
      closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) := by
  intro x hx
  change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection choice at hx
  rw [D.canonicalBooleanAugmentedAmbientSection_eq_paths] at hx
  rcases hx with (hxOutside | hxLocal) | hxInactive
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxOutside
    exact D.canonicalBooleanOutsidePath_subset_closure_active choice e he
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxLocal
    split at hb
    next hchoice =>
      apply D.selectedHorizontalFace_subset_closure_active choice b hchoice
      rw [← D.transportedTorusPart_surgeryPatch b]
      exact hb
    next hchoice =>
      apply subset_closure
      apply D.unselectedVerticalFace_subset_active choice b
        (by cases h : choice b <;> simp_all)
      rw [← D.transportedTorusPart_parallelPatch b]
      exact hb
  · exact D.canonicalInactiveOuterCarrier_subset_closure_active choice hxInactive

theorem closure_activeFrontier_eq_augmentedCarrier
    (choice : D.ConnectorBandIndex → Bool) :
    closure (sdiffActiveFrontier
        (superellipsoidReducedInside Phi frame c S.outer.scale)
        (D.canonicalBooleanRemovedLenses choice)) =
      transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (D.activeFrontier_subset_augmentedCarrier choice)
      (D.isClosed_transportedTorusPart_canonicalBooleanAugmentedAmbientSection choice)
  · exact D.augmentedCarrier_subset_closure_activeFrontier choice

theorem frontier_canonicalBooleanReducedRegion
    (choice : D.ConnectorBandIndex → Bool) :
    frontier (D.canonicalBooleanReducedRegion choice) =
      transportedTorusPart Phi (D.canonicalBooleanAugmentedAmbientSection choice) := by
  rw [D.frontier_canonicalBooleanReducedRegion_eq_closure_active,
    D.closure_activeFrontier_eq_augmentedCarrier]

noncomputable def canonicalBooleanReducedStageEntry
    (choice : D.ConnectorBandIndex → Bool) :
    ReducedTorusCircleStageEntry Phi where
  circleCount := Fintype.card
    ((D.canonicalBooleanOutsidePathData.system choice).CycleIndex ⊕
      D.centralOuterOrder.InactiveOuterCircle)
  ambientSection := D.canonicalBooleanAugmentedAmbientSection choice
  circleSection := (D.canonicalBooleanAugmentedCircleSection choice).reindex
    (Fintype.equivFin _).symm
  region := D.canonicalBooleanReducedRegion choice
  isOpen_region := D.isOpen_canonicalBooleanReducedRegion choice
  frontier_region := D.frontier_canonicalBooleanReducedRegion choice

theorem canonicalBooleanReducedStageEntry_update_true_boundary_subset
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex) :
    (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage.boundary ⊆
      (D.canonicalBooleanReducedStageEntry choice).parityStage.boundary ∪
        transportedTorusPart Phi
          (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
  intro x hx
  change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection
    (Function.update choice b true) at hx
  rcases D.canonicalBooleanAugmentedAmbientSection_update_true_subset choice b hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

theorem canonicalBooleanReducedStageEntry_boundary_subset_update_true
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    (D.canonicalBooleanReducedStageEntry choice).parityStage.boundary ⊆
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage.boundary ∪
          transportedTorusPart Phi
            (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  intro x hx
  change (x : R3) ∈ D.canonicalBooleanAugmentedAmbientSection choice at hx
  rcases D.canonicalBooleanAugmentedAmbientSection_subset_update_true_union
      choice b hb hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

theorem canonicalBooleanReducedStageEntry_update_true_labelChange_subset_lens
    (choice : D.ConnectorBandIndex → Bool) (b : D.ConnectorBandIndex)
    (hb : choice b = false) :
    {x | (x ∈ (D.canonicalBooleanReducedStageEntry choice).parityStage.inside) ≠
        (x ∈ (D.canonicalBooleanReducedStageEntry
          (Function.update choice b true)).parityStage.inside)} ⊆
      D.canonicalFourPortClosedLens b :=
  D.canonicalBooleanReducedRegion_labelChange_subset_lens choice b hb

noncomputable def canonicalBooleanReducedStageData :
    BooleanChoiceReducedTorusCircleStageData Phi
      D.centralCutOrder.toPairedSeamEnumeration.bandCount where
  stage := D.canonicalBooleanReducedStageEntry

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
