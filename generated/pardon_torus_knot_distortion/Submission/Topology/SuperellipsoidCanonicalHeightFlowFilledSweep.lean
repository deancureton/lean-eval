import Submission.PlaneSchoenflies.Schoenflies.TriangleDiskEmbeddingRecognition
import Submission.Topology.SuperellipsoidCanonicalHeightFlowCrossingGraphs

/-!
# The canonical filled height-flow sweep

The continuous left and right crossing graphs bound a rectangular sweep in the canonical strip.
Every horizontal slice is the portion of one height-flow arc between its two outer crossings.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev ConnectorBand := D.openChartNarrowedData.heightData.band

private abbrev ConnectorBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private abbrev ConnectorFlowTimes := globalBandFlowCollarTimes D.ConnectorBand

/-- Affine interpolation through the selected closed flow-time interval. -/
def centralConnectorSweepTime (v : unitInterval) : D.CentralConnectorSelectedTime := by
  let t : D.ConnectorFlowTimes :=
    Icc.convexComb D.centralLowerConnectorTime D.centralUpperConnectorTime v
  refine ⟨t, ?_⟩
  change t ∈ Icc D.centralLowerConnectorTime D.centralUpperConnectorTime
  have htValue : (t : ℝ) =
      (1 - (v : ℝ)) * D.centralLowerConnectorTime +
        (v : ℝ) * D.centralUpperConnectorTime := by
    exact Icc.coe_convexComb
      (show Icc (-D.ConnectorBand.ε) D.ConnectorBand.ε from
        D.centralLowerConnectorTime)
      (show Icc (-D.ConnectorBand.ε) D.ConnectorBand.ε from
        D.centralUpperConnectorTime) v
  constructor
  · change (D.centralLowerConnectorTime : ℝ) ≤ (t : ℝ)
    rw [htValue]
    nlinarith [v.2.1, v.2.2,
      D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos]
  · change (t : ℝ) ≤ D.centralUpperConnectorTime
    rw [htValue]
    nlinarith [v.2.1, v.2.2,
      D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos]

theorem continuous_centralConnectorSweepTime :
    Continuous D.centralConnectorSweepTime := by
  apply Continuous.subtype_mk
  exact Icc.continuous_convexComb
    D.centralLowerConnectorTime D.centralUpperConnectorTime

@[simp]
theorem centralConnectorSweepTime_zero :
    D.centralConnectorSweepTime 0 = D.centralLowerSelectedTime := by
  apply Subtype.ext
  exact Icc.convexComb_zero _ _

@[simp]
theorem centralConnectorSweepTime_one :
    D.centralConnectorSweepTime 1 = D.centralUpperSelectedTime := by
  apply Subtype.ext
  exact Icc.convexComb_one _ _

/-- The midpoint parameter corresponding to the original zero-height seam. -/
def centralConnectorSweepMidpoint : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

theorem centralConnectorSweepTime_midpoint :
    (D.centralConnectorSweepTime centralConnectorSweepMidpoint).1 =
      globalBandFlowCollarZeroTime D.ConnectorBand := by
  apply Subtype.ext
  change (1 - (centralConnectorSweepMidpoint : ℝ)) *
      (D.centralLowerConnectorTime : ℝ) +
    (centralConnectorSweepMidpoint : ℝ) * D.centralUpperConnectorTime = 0
  unfold centralConnectorSweepMidpoint centralLowerConnectorTime
    centralUpperConnectorTime
  norm_num
  ring

theorem centralConnectorCrossingParameter_order
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    D.centralConnectorLeftCrossingParameter b t <
      D.centralConnectorRightCrossingParameter b t :=
  (D.centralConnectorLeftCrossingParameter_spec b t).1.2.trans_lt <|
    (D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).trans_le
      (D.centralConnectorRightCrossingParameter_spec b t).1.1

private theorem range_comp_connectorConvexComb {X : Type*}
    (f : D.ConnectorFlowTimes → X) (a b : D.ConnectorFlowTimes) (hab : a ≤ b) :
    Set.range (fun u ↦ f (Icc.convexComb a b u)) = f '' Icc a b := by
  ext x
  have hvalue (u : unitInterval) :
      ((Icc.convexComb a b u : D.ConnectorFlowTimes) : ℝ) =
        (1 - (u : ℝ)) * a + (u : ℝ) * b := by
    exact Icc.coe_convexComb
      (show Icc (-D.ConnectorBand.ε) D.ConnectorBand.ε from a)
      (show Icc (-D.ConnectorBand.ε) D.ConnectorBand.ε from b) u
  have habReal : (a : ℝ) ≤ (b : ℝ) := hab
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Icc.convexComb a b u, ?_, rfl⟩
    constructor
    · change (a : ℝ) ≤ ((Icc.convexComb a b u : D.ConnectorFlowTimes) : ℝ)
      rw [hvalue]
      nlinarith [u.2.1, u.2.2, habReal]
    · change ((Icc.convexComb a b u : D.ConnectorFlowTimes) : ℝ) ≤ (b : ℝ)
      rw [hvalue]
      nlinarith [u.2.1, u.2.2, habReal]
  · rintro ⟨t, ht, rfl⟩
    by_cases habEq : a = b
    · subst b
      have htEq : t = a := le_antisymm ht.2 ht.1
      subst t
      refine ⟨0, congrArg f ?_⟩
      apply Subtype.ext
      rw [hvalue]
      norm_num
    · have habLt : a < b := lt_of_le_of_ne hab habEq
      have habPos : (0 : ℝ) < (b : ℝ) - (a : ℝ) := sub_pos.mpr habLt
      have htLower : (a : ℝ) ≤ (t : ℝ) := ht.1
      have htUpper : (t : ℝ) ≤ (b : ℝ) := ht.2
      let u : unitInterval :=
        ⟨((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)), by
          constructor
          · exact div_nonneg (sub_nonneg.mpr htLower) habPos.le
          · exact (div_le_one habPos).2 (sub_le_sub_right htUpper (a : ℝ))⟩
      refine ⟨u, ?_⟩
      apply congrArg f
      apply Subtype.ext
      rw [hvalue]
      dsimp [u]
      field_simp [ne_of_gt habPos]
      ring

theorem centralConnectorLeftCrossingParameter_midpoint
    (b : D.ConnectorBandIndex) :
    D.centralConnectorLeftCrossingParameter b
        (D.centralConnectorSweepTime centralConnectorSweepMidpoint) =
      D.centralCutOrder.globalBandCoreLeft b := by
  apply (D.existsUnique_centralConnectorLeftCrossing b
    (D.centralConnectorSweepTime centralConnectorSweepMidpoint).1
    (D.centralConnectorSweepTime centralConnectorSweepMidpoint).2).unique
  · exact D.centralConnectorLeftCrossingParameter_spec b _
  · constructor
    · exact ⟨(D.centralConnectorLeftProbe_lt_coreLeft b).le,
        (D.centralConnectorCoreLeft_lt_leftInnerProbe b).le⟩
    · rw [D.centralConnectorSweepTime_midpoint]
      exact D.centralHeightFlowOuterDefect_coreLeft_zero b

theorem centralConnectorRightCrossingParameter_midpoint
    (b : D.ConnectorBandIndex) :
    D.centralConnectorRightCrossingParameter b
        (D.centralConnectorSweepTime centralConnectorSweepMidpoint) =
      D.centralCutOrder.globalBandCoreRight b := by
  apply (D.existsUnique_centralConnectorRightCrossing b
    (D.centralConnectorSweepTime centralConnectorSweepMidpoint).1
    (D.centralConnectorSweepTime centralConnectorSweepMidpoint).2).unique
  · exact D.centralConnectorRightCrossingParameter_spec b _
  · constructor
    · exact ⟨(D.centralConnectorRightInnerProbe_lt_coreRight b).le,
        (D.centralConnectorCoreRight_lt_rightProbe b).le⟩
    · rw [D.centralConnectorSweepTime_midpoint]
      exact D.centralHeightFlowOuterDefect_coreRight_zero b

/-- Affine interpolation between the two moving outer crossings. -/
def centralConnectorSweepParameter
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) : unitInterval :=
  Icc.convexComb
    (D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime p.2))
    (D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime p.2)) p.1

theorem continuous_centralConnectorSweepParameter (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorSweepParameter b) := by
  apply Continuous.subtype_mk
  have hu : Continuous (fun p : unitInterval × unitInterval ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun p : unitInterval × unitInterval ↦
      D.centralConnectorSweepTime p.2) :=
    D.continuous_centralConnectorSweepTime.comp continuous_snd
  have hleft : Continuous (fun p : unitInterval × unitInterval ↦
      (D.centralConnectorLeftCrossingParameter b
        (D.centralConnectorSweepTime p.2) : ℝ)) :=
    continuous_subtype_val.comp <|
      (D.continuous_centralConnectorLeftCrossingParameter b).comp ht
  have hright : Continuous (fun p : unitInterval × unitInterval ↦
      (D.centralConnectorRightCrossingParameter b
        (D.centralConnectorSweepTime p.2) : ℝ)) :=
    continuous_subtype_val.comp <|
      (D.continuous_centralConnectorRightCrossingParameter b).comp ht
  change Continuous (fun p : unitInterval × unitInterval ↦
    (1 - (p.1 : ℝ)) *
        D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime p.2) +
      (p.1 : ℝ) *
        D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime p.2))
  exact ((continuous_const.sub hu).mul hleft).add (hu.mul hright)

@[simp]
theorem centralConnectorSweepParameter_zero
    (b : D.ConnectorBandIndex) (v : unitInterval) :
    D.centralConnectorSweepParameter b (0, v) =
      D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime v) :=
  Icc.convexComb_zero _ _

@[simp]
theorem centralConnectorSweepParameter_one
    (b : D.ConnectorBandIndex) (v : unitInterval) :
    D.centralConnectorSweepParameter b (1, v) =
      D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime v) :=
  Icc.convexComb_one _ _

theorem centralConnectorSweepParameter_midpoint
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralConnectorSweepParameter b (u, centralConnectorSweepMidpoint) =
      Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
        (D.centralCutOrder.globalBandCoreRight b) u := by
  unfold centralConnectorSweepParameter
  rw [D.centralConnectorLeftCrossingParameter_midpoint,
    D.centralConnectorRightCrossingParameter_midpoint]

private theorem centralConnectorSweepParameter_mem_crossingInterval
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    D.centralConnectorSweepParameter b p ∈
      Icc
        (D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime p.2))
        (D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime p.2)) := by
  rw [← uIcc_of_le (D.centralConnectorCrossingParameter_order b _).le,
    ← Path.range_subpathAux]
  exact Set.mem_range_self p.1

theorem centralConnectorSweepParameter_mem_probeInterval
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    D.centralConnectorSweepParameter b p ∈
      Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b) := by
  have hp := D.centralConnectorSweepParameter_mem_crossingInterval b p
  exact
    ⟨(D.centralConnectorLeftCrossingParameter_spec b _).1.1.trans hp.1,
      hp.2.trans (D.centralConnectorRightCrossingParameter_spec b _).1.2⟩

private theorem centralConnectorSweepSurfacePatch
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) :
    D.centralHeightFlowSlicePoint b
        (D.centralConnectorSweepParameter b p, (D.centralConnectorSweepTime p.2).1) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  apply D.centralConnectorSurfacePatchTimeRadius_spec b
  · exact (D.abs_lt_uniformCentralConnectorTimeRadius
      (D.centralConnectorSweepTime p.2).2).trans_le
      (D.uniformCentralConnectorTimeRadius_le_surfacePatch b)
  · exact D.centralConnectorSweepParameter_mem_probeInterval b p

/-- The filled sweep in the canonical strip coordinate plane. -/
def centralConnectorFilledSweepCoordinate
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) : Plane :=
  (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    ⟨D.centralHeightFlowSlicePoint b
      (D.centralConnectorSweepParameter b p, (D.centralConnectorSweepTime p.2).1),
        D.centralConnectorSweepSurfacePatch b p⟩

theorem continuous_centralConnectorFilledSweepCoordinate
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorFilledSweepCoordinate b) := by
  apply (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.continuous.comp
  apply Continuous.subtype_mk
  apply (D.continuous_centralHeightFlowSlicePoint b).comp
  exact (D.continuous_centralConnectorSweepParameter b).prodMk <|
    continuous_subtype_val.comp <|
      D.continuous_centralConnectorSweepTime.comp continuous_snd

theorem centralConnectorFilledSweepCoordinate_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralConnectorFilledSweepCoordinate b) := by
  intro p q hpq
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective hpq
  have hpoint := congrArg Subtype.val hsurface
  have hheight := congrArg (fun z : transportedTorus Phi ↦
      ambientCoordinate (frame 2) (z : R3)) hpoint
  change orientedCoordinateLift Phi frame 2
      (D.centralHeightFlowSliceLift b (D.centralConnectorSweepTime p.2).1
        (D.centralConnectorSweepParameter b p)) =
    orientedCoordinateLift Phi frame 2
      (D.centralHeightFlowSliceLift b (D.centralConnectorSweepTime q.2).1
        (D.centralConnectorSweepParameter b q)) at hheight
  rw [D.orientedCoordinateLift_centralHeightFlowSliceLift,
    D.orientedCoordinateLift_centralHeightFlowSliceLift] at hheight
  have htime : D.centralConnectorSweepTime p.2 = D.centralConnectorSweepTime q.2 := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_left_cancel hheight
  have hv : p.2 = q.2 := by
    have hvalue := congrArg (fun t : D.CentralConnectorSelectedTime ↦ (t.1 : ℝ)) htime
    apply Subtype.ext
    change (1 - (p.2 : ℝ)) * D.centralLowerConnectorTime +
        (p.2 : ℝ) * D.centralUpperConnectorTime =
      (1 - (q.2 : ℝ)) * D.centralLowerConnectorTime +
        (q.2 : ℝ) * D.centralUpperConnectorTime at hvalue
    have hgap : (D.centralUpperConnectorTime : ℝ) -
        D.centralLowerConnectorTime ≠ 0 := by
      exact ne_of_gt <| sub_pos.mpr <|
        D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos
    have hmul : ((p.2 : ℝ) - q.2) *
        ((D.centralUpperConnectorTime : ℝ) - D.centralLowerConnectorTime) = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hgap)
  have hparameter : D.centralConnectorSweepParameter b p =
      D.centralConnectorSweepParameter b q := by
    apply D.centralHeightFlowSlicePoint_fixedTime_injective b
      (D.centralConnectorSweepTime p.2).1
    simpa only [hv] using hpoint
  have hu : p.1 = q.1 := by
    have hvalue := congrArg Subtype.val hparameter
    apply Subtype.ext
    have hvalue' :
        (D.centralConnectorSweepParameter b p : ℝ) =
          D.centralConnectorSweepParameter b (q.1, p.2) := by
      simpa only [hv] using hvalue
    simp only [centralConnectorSweepParameter, Icc.coe_convexComb] at hvalue'
    have hgap : 0 <
        (D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime p.2) : ℝ) -
          D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime p.2) :=
      sub_pos.mpr (D.centralConnectorCrossingParameter_order b _)
    nlinarith
  exact Prod.ext hu hv

/-- The same filled sweep in the Euclidean Schoenflies plane. -/
def centralConnectorFilledPlaneSweep
    (b : D.ConnectorBandIndex) (p : unitInterval × unitInterval) : Schoenflies.Plane :=
  coveringPlaneCoordinates.symm (D.centralConnectorFilledSweepCoordinate b p)

theorem continuous_centralConnectorFilledPlaneSweep
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorFilledPlaneSweep b) :=
  coveringPlaneCoordinates.symm.continuous.comp
    (D.continuous_centralConnectorFilledSweepCoordinate b)

theorem centralConnectorFilledPlaneSweep_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralConnectorFilledPlaneSweep b) :=
  coveringPlaneCoordinates.symm.injective.comp
    (D.centralConnectorFilledSweepCoordinate_injective b)

theorem centralConnectorFilledSweepCoordinate_bottom
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralConnectorFilledSweepCoordinate b (u, 0) =
      D.centralHeightFlowLowerConnector b u := by
  have hparameter : D.centralConnectorSweepParameter b (u, 0) =
      D.centralLowerConnectorParameter b u := by
    unfold centralConnectorSweepParameter centralLowerConnectorParameter
    rw [D.centralConnectorSweepTime_zero,
      D.centralConnectorLeftCrossingParameter_lower,
      D.centralConnectorRightCrossingParameter_lower]
  unfold centralConnectorFilledSweepCoordinate centralHeightFlowLowerConnector
  apply congrArg
  apply Subtype.ext
  apply congrArg (D.centralHeightFlowSlicePoint b)
  exact Prod.ext hparameter (congrArg Subtype.val D.centralConnectorSweepTime_zero)

theorem centralConnectorFilledSweepCoordinate_top
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralConnectorFilledSweepCoordinate b (u, 1) =
      D.centralHeightFlowUpperConnector b u := by
  have hparameter : D.centralConnectorSweepParameter b (u, 1) =
      D.centralUpperConnectorParameter b u := by
    unfold centralConnectorSweepParameter centralUpperConnectorParameter
    rw [D.centralConnectorSweepTime_one,
      D.centralConnectorLeftCrossingParameter_upper,
      D.centralConnectorRightCrossingParameter_upper]
  unfold centralConnectorFilledSweepCoordinate centralHeightFlowUpperConnector
  apply congrArg
  apply Subtype.ext
  apply congrArg (D.centralHeightFlowSlicePoint b)
  exact Prod.ext hparameter (congrArg Subtype.val D.centralConnectorSweepTime_one)

theorem centralConnectorFilledSweepCoordinate_left
    (b : D.ConnectorBandIndex) (v : unitInterval) :
    D.centralConnectorFilledSweepCoordinate b (0, v) =
      D.centralLeftOuterArmCoordinate b (D.centralConnectorSweepTime v).1 := by
  unfold centralConnectorFilledSweepCoordinate centralLeftOuterArmCoordinate
  apply congrArg
  apply Subtype.ext
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (D.centralHeightFlowSliceLift b (D.centralConnectorSweepTime v).1
        (D.centralConnectorSweepParameter b (0, v))) =
    transportedTorusPlaneMap Phi
      (D.centralLeftOuterArmLift b
        (D.openChartNarrowedTime (D.centralConnectorSweepTime v).1))
  rw [D.centralConnectorSweepParameter_zero]
  apply congrArg
  exact D.centralConnectorLeftCrossing_eq_outerArm b
    (D.centralConnectorSweepTime v).1
    (D.abs_lt_uniformCentralConnectorTimeRadius (D.centralConnectorSweepTime v).2)
    (D.centralConnectorLeftCrossingParameter b (D.centralConnectorSweepTime v))
    (D.centralConnectorLeftCrossingParameter_spec b (D.centralConnectorSweepTime v)).1
    (D.centralConnectorLeftCrossingParameter_spec b (D.centralConnectorSweepTime v)).2

theorem centralConnectorFilledSweepCoordinate_right
    (b : D.ConnectorBandIndex) (v : unitInterval) :
    D.centralConnectorFilledSweepCoordinate b (1, v) =
      D.centralRightOuterArmCoordinate b (D.centralConnectorSweepTime v).1 := by
  unfold centralConnectorFilledSweepCoordinate centralRightOuterArmCoordinate
  apply congrArg
  apply Subtype.ext
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (D.centralHeightFlowSliceLift b (D.centralConnectorSweepTime v).1
        (D.centralConnectorSweepParameter b (1, v))) =
    transportedTorusPlaneMap Phi
      (D.centralRightOuterArmLift b
        (D.openChartNarrowedTime (D.centralConnectorSweepTime v).1))
  rw [D.centralConnectorSweepParameter_one]
  apply congrArg
  exact D.centralConnectorRightCrossing_eq_outerArm b
    (D.centralConnectorSweepTime v).1
    (D.abs_lt_uniformCentralConnectorTimeRadius (D.centralConnectorSweepTime v).2)
    (D.centralConnectorRightCrossingParameter b (D.centralConnectorSweepTime v))
    (D.centralConnectorRightCrossingParameter_spec b (D.centralConnectorSweepTime v)).1
    (D.centralConnectorRightCrossingParameter_spec b (D.centralConnectorSweepTime v)).2

theorem centralConnectorFilledSweepCoordinate_midpoint
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralConnectorFilledSweepCoordinate b (u, centralConnectorSweepMidpoint) =
      bandSeamPath u := by
  let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  unfold centralConnectorFilledSweepCoordinate
  rw [← T.strip.symm_apply_apply (bandSeamPath u)]
  apply congrArg T.strip.symm
  apply Subtype.ext
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (D.centralHeightFlowSliceLift b
        (D.centralConnectorSweepTime centralConnectorSweepMidpoint).1
        (D.centralConnectorSweepParameter b (u, centralConnectorSweepMidpoint))) =
    (((T.strip (bandSeamPath u) : T.surfacePatch) : transportedTorus Phi) : R3)
  rw [D.centralConnectorSweepTime_midpoint,
    D.centralConnectorSweepParameter_midpoint]
  calc
    transportedTorusPlaneMap Phi
        (D.centralHeightFlowSliceLift b
          (globalBandFlowCollarZeroTime D.ConnectorBand)
          (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
            (D.centralCutOrder.globalBandCoreRight b) u)) =
      ((D.centralCutOrder.globalBandPath b u : transportedTorus Phi) : R3) :=
        D.transportedTorusPlaneMap_centralHeightFlowCoreSliceLift_zero b u
    _ = (((T.strip (bandSeamPath u) : T.surfacePatch) : transportedTorus Phi) : R3) :=
      (T.core_alignment u).symm

theorem range_centralConnectorFilledSweepCoordinate_left
    (b : D.ConnectorBandIndex) :
    Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (0, v)) =
      Set.range (D.centralLeftLowerHeightFlowBranchPath b) ∪
        Set.range (D.centralLeftUpperHeightFlowBranchPath b) := by
  have hfull : Set.range (fun v ↦
      D.centralLeftOuterArmCoordinate b (D.centralConnectorSweepTime v).1) =
      D.centralLeftOuterArmCoordinate b ''
        Icc D.centralLowerConnectorTime D.centralUpperConnectorTime := by
    exact D.range_comp_connectorConvexComb _ _ _
      (D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos).le
  have hlower : Set.range (D.centralLeftLowerHeightFlowBranchPath b) =
      D.centralLeftOuterArmCoordinate b ''
        Icc D.centralLowerConnectorTime
          (globalBandFlowCollarZeroTime D.ConnectorBand) := by
    exact D.range_comp_connectorConvexComb (D.centralLeftOuterArmCoordinate b)
      D.centralLowerConnectorTime (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralLowerConnectorTime_neg.le
  have hupper : Set.range (D.centralLeftUpperHeightFlowBranchPath b) =
      D.centralLeftOuterArmCoordinate b ''
        Icc (globalBandFlowCollarZeroTime D.ConnectorBand)
          D.centralUpperConnectorTime := by
    exact D.range_comp_connectorConvexComb (D.centralLeftOuterArmCoordinate b)
      (globalBandFlowCollarZeroTime D.ConnectorBand) D.centralUpperConnectorTime
      D.centralUpperConnectorTime_pos.le
  have hlowerZero : D.centralLowerConnectorTime ≤
      globalBandFlowCollarZeroTime D.ConnectorBand := by
    change (D.centralLowerConnectorTime : ℝ) ≤ 0
    exact D.centralLowerConnectorTime_neg.le
  have hzeroUpper : globalBandFlowCollarZeroTime D.ConnectorBand ≤
      D.centralUpperConnectorTime := by
    change (0 : ℝ) ≤ D.centralUpperConnectorTime
    exact D.centralUpperConnectorTime_pos.le
  rw [funext (D.centralConnectorFilledSweepCoordinate_left b), hfull,
    hlower, hupper, ← Set.image_union, Set.Icc_union_Icc_eq_Icc
      hlowerZero hzeroUpper]

theorem range_centralConnectorFilledSweepCoordinate_right
    (b : D.ConnectorBandIndex) :
    Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (1, v)) =
      Set.range (D.centralRightLowerHeightFlowBranchPath b) ∪
        Set.range (D.centralRightUpperHeightFlowBranchPath b) := by
  have hfull : Set.range (fun v ↦
      D.centralRightOuterArmCoordinate b (D.centralConnectorSweepTime v).1) =
      D.centralRightOuterArmCoordinate b ''
        Icc D.centralLowerConnectorTime D.centralUpperConnectorTime := by
    exact D.range_comp_connectorConvexComb _ _ _
      (D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos).le
  have hlower : Set.range (D.centralRightLowerHeightFlowBranchPath b) =
      D.centralRightOuterArmCoordinate b ''
        Icc D.centralLowerConnectorTime
          (globalBandFlowCollarZeroTime D.ConnectorBand) := by
    exact D.range_comp_connectorConvexComb (D.centralRightOuterArmCoordinate b)
      D.centralLowerConnectorTime (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralLowerConnectorTime_neg.le
  have hupper : Set.range (D.centralRightUpperHeightFlowBranchPath b) =
      D.centralRightOuterArmCoordinate b ''
        Icc (globalBandFlowCollarZeroTime D.ConnectorBand)
          D.centralUpperConnectorTime := by
    exact D.range_comp_connectorConvexComb (D.centralRightOuterArmCoordinate b)
      (globalBandFlowCollarZeroTime D.ConnectorBand) D.centralUpperConnectorTime
      D.centralUpperConnectorTime_pos.le
  have hlowerZero : D.centralLowerConnectorTime ≤
      globalBandFlowCollarZeroTime D.ConnectorBand := by
    change (D.centralLowerConnectorTime : ℝ) ≤ 0
    exact D.centralLowerConnectorTime_neg.le
  have hzeroUpper : globalBandFlowCollarZeroTime D.ConnectorBand ≤
      D.centralUpperConnectorTime := by
    change (0 : ℝ) ≤ D.centralUpperConnectorTime
    exact D.centralUpperConnectorTime_pos.le
  rw [funext (D.centralConnectorFilledSweepCoordinate_right b), hfull,
    hlower, hupper, ← Set.image_union, Set.Icc_union_Icc_eq_Icc
      hlowerZero hzeroUpper]

theorem range_centralConnectorFilledSweepCoordinate_bottom
    (b : D.ConnectorBandIndex) :
    Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 0)) =
      Set.range (D.centralHeightFlowLowerConnector b) := by
  apply congrArg Set.range
  funext u
  exact D.centralConnectorFilledSweepCoordinate_bottom b u

theorem range_centralConnectorFilledSweepCoordinate_top
    (b : D.ConnectorBandIndex) :
    Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 1)) =
      Set.range (D.centralHeightFlowUpperConnector b) := by
  apply congrArg Set.range
  funext u
  exact D.centralConnectorFilledSweepCoordinate_top b u

theorem range_centralConnectorFilledSweepCoordinate_boundaryEdges
    (b : D.ConnectorBandIndex) :
    Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (0, v)) ∪
        Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (1, v)) ∪
        Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 0)) ∪
        Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 1)) =
      Set.range (D.centralHeightFlowLowerThetaRoute b) ∪
        Set.range (D.centralHeightFlowUpperThetaRoute b) := by
  rw [D.range_centralConnectorFilledSweepCoordinate_left,
    D.range_centralConnectorFilledSweepCoordinate_right,
    D.range_centralConnectorFilledSweepCoordinate_bottom,
    D.range_centralConnectorFilledSweepCoordinate_top,
    centralHeightFlowLowerThetaRoute, centralHeightFlowUpperThetaRoute,
    Path.trans_range, Path.trans_range, Path.trans_range, Path.trans_range,
    Path.symm_range, Path.symm_range]
  ac_rfl

/-- The closed unit square in the Euclidean Schoenflies plane. -/
def centralConnectorUnitSquare : Set Schoenflies.Plane :=
  coveringPlaneCoordinates.symm '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

private theorem frontier_unitCoordinateSquare :
    frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      ({0, 1} ×ˢ Icc (0 : ℝ) 1) ∪ (Icc (0 : ℝ) 1 ×ˢ {0, 1}) := by
  simp only [frontier_prod_eq, closure_Icc,
    frontier_Icc zero_le_one]
  ac_rfl

theorem frontier_centralConnectorUnitSquare :
    frontier centralConnectorUnitSquare =
      coveringPlaneCoordinates.symm ''
        (({0, 1} ×ˢ Icc (0 : ℝ) 1) ∪ (Icc (0 : ℝ) 1 ×ˢ {0, 1})) := by
  rw [centralConnectorUnitSquare, ← coveringPlaneCoordinates.symm.image_frontier,
    frontier_unitCoordinateSquare]

theorem isCompact_centralConnectorUnitSquare :
    IsCompact centralConnectorUnitSquare :=
  (isCompact_Icc.prod isCompact_Icc).image coveringPlaneCoordinates.symm.continuous

theorem interior_centralConnectorUnitSquare_nonempty :
    (interior centralConnectorUnitSquare).Nonempty := by
  rw [centralConnectorUnitSquare, ← coveringPlaneCoordinates.symm.image_interior]
  refine Set.Nonempty.image coveringPlaneCoordinates.symm ⟨((1 : ℝ) / 2, (1 : ℝ) / 2), ?_⟩
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem convex_centralConnectorUnitSquare :
    Convex ℝ centralConnectorUnitSquare := by
  rw [centralConnectorUnitSquare, coveringPlaneCoordinates.image_symm]
  intro x hx y hy a d ha hd had
  change coveringPlaneCoordinates (a • x + d • y) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  change (x 0, x 1) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 at hx
  change (y 0, y 1) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 at hy
  change (a * x 0 + d * y 0, a * x 1 + d * y 1) ∈
    Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  exact ⟨convex_Icc (0 : ℝ) 1 hx.1 hy.1 ha hd had,
    convex_Icc (0 : ℝ) 1 hx.2 hy.2 ha hd had⟩

/-- Clamp arbitrary Euclidean plane coordinates to the unit-square parameters. -/
def centralConnectorSquareParameter
    (z : Schoenflies.Plane) : unitInterval × unitInterval :=
  (Set.projIcc 0 1 zero_le_one (z 0), Set.projIcc 0 1 zero_le_one (z 1))

theorem continuous_centralConnectorSquareParameter :
    Continuous centralConnectorSquareParameter :=
  (continuous_projIcc.comp
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 0)).prodMk
      (continuous_projIcc.comp
        (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 1))

private theorem centralConnectorSquareParameter_eq_of_mem
    {z : Schoenflies.Plane} (hz : z ∈ centralConnectorUnitSquare) :
    (((centralConnectorSquareParameter z).1 : ℝ),
        ((centralConnectorSquareParameter z).2 : ℝ)) =
      coveringPlaneCoordinates z := by
  rw [centralConnectorUnitSquare] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  rw [coveringPlaneCoordinates.apply_symm_apply]
  apply Prod.ext
  · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hq.1)
  · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hq.2)

/-- A total planar extension of the filled sweep, obtained by clamping to the source square. -/
def centralConnectorFilledPlaneSweepExtension
    (b : D.ConnectorBandIndex) (z : Schoenflies.Plane) : Schoenflies.Plane :=
  D.centralConnectorFilledPlaneSweep b (centralConnectorSquareParameter z)

theorem centralConnectorFilledPlaneSweepExtension_apply_symm
    (b : D.ConnectorBandIndex) (q : ℝ × ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    D.centralConnectorFilledPlaneSweepExtension b (coveringPlaneCoordinates.symm q) =
      coveringPlaneCoordinates.symm
        (D.centralConnectorFilledSweepCoordinate b (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)) := by
  unfold centralConnectorFilledPlaneSweepExtension centralConnectorFilledPlaneSweep
  apply congrArg coveringPlaneCoordinates.symm
  apply congrArg (D.centralConnectorFilledSweepCoordinate b)
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hq.1)
  · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hq.2)

theorem continuous_centralConnectorFilledPlaneSweepExtension
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorFilledPlaneSweepExtension b) :=
  (D.continuous_centralConnectorFilledPlaneSweep b).comp
    continuous_centralConnectorSquareParameter

theorem centralConnectorFilledPlaneSweepExtension_injOn
    (b : D.ConnectorBandIndex) :
    Set.InjOn (D.centralConnectorFilledPlaneSweepExtension b)
      centralConnectorUnitSquare := by
  intro x hx y hy hxy
  have hparameter : centralConnectorSquareParameter x =
      centralConnectorSquareParameter y :=
    D.centralConnectorFilledPlaneSweep_injective b hxy
  apply coveringPlaneCoordinates.injective
  rw [← centralConnectorSquareParameter_eq_of_mem hx,
    ← centralConnectorSquareParameter_eq_of_mem hy]
  exact congrArg (fun p : unitInterval × unitInterval ↦
    (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ)) hparameter

theorem image_frontier_centralConnectorFilledPlaneSweepExtension
    (b : D.ConnectorBandIndex) :
    D.centralConnectorFilledPlaneSweepExtension b ''
        frontier centralConnectorUnitSquare =
      coveringPlaneCoordinates.symm ''
        (Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (0, v)) ∪
          Set.range (fun v ↦ D.centralConnectorFilledSweepCoordinate b (1, v)) ∪
          Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 0)) ∪
          Set.range (fun u ↦ D.centralConnectorFilledSweepCoordinate b (u, 1))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [frontier_centralConnectorUnitSquare] at hx
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := hx
    rcases hst with hs | ht
    · rcases hs.1 with hs0 | hs1
      · change s = 0 at hs0
        subst s
        let v : unitInterval := ⟨t, hs.2⟩
        refine ⟨D.centralConnectorFilledSweepCoordinate b (0, v),
          Or.inl (Or.inl (Or.inl ⟨v, rfl⟩)), ?_⟩
        rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((0 : ℝ), t) ⟨⟨by norm_num, by norm_num⟩, hs.2⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
      · change s = 1 at hs1
        subst s
        let v : unitInterval := ⟨t, hs.2⟩
        refine ⟨D.centralConnectorFilledSweepCoordinate b (1, v),
          Or.inl (Or.inl (Or.inr ⟨v, rfl⟩)), ?_⟩
        rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((1 : ℝ), t) ⟨⟨by norm_num, by norm_num⟩, hs.2⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
    · rcases ht.2 with ht0 | ht1
      · change t = 0 at ht0
        subst t
        let u : unitInterval := ⟨s, ht.1⟩
        refine ⟨D.centralConnectorFilledSweepCoordinate b (u, 0),
          Or.inl (Or.inr ⟨u, rfl⟩), ?_⟩
        rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          (s, (0 : ℝ)) ⟨ht.1, ⟨by norm_num, by norm_num⟩⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
      · change t = 1 at ht1
        subst t
        let u : unitInterval := ⟨s, ht.1⟩
        refine ⟨D.centralConnectorFilledSweepCoordinate b (u, 1),
          Or.inr ⟨u, rfl⟩, ?_⟩
        rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          (s, (1 : ℝ)) ⟨ht.1, ⟨by norm_num, by norm_num⟩⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ((hw | hw) | hw) | hw
    · obtain ⟨v, rfl⟩ := hw
      refine ⟨coveringPlaneCoordinates.symm ((0 : ℝ), (v : ℝ)), ?_, ?_⟩
      · rw [frontier_centralConnectorUnitSquare]
        exact ⟨((0 : ℝ), (v : ℝ)), Or.inl ⟨Or.inl rfl, v.2⟩, rfl⟩
      · rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((0 : ℝ), (v : ℝ)) ⟨⟨by norm_num, by norm_num⟩, v.2⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
    · obtain ⟨v, rfl⟩ := hw
      refine ⟨coveringPlaneCoordinates.symm ((1 : ℝ), (v : ℝ)), ?_, ?_⟩
      · rw [frontier_centralConnectorUnitSquare]
        exact ⟨((1 : ℝ), (v : ℝ)), Or.inl ⟨Or.inr rfl, v.2⟩, rfl⟩
      · rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((1 : ℝ), (v : ℝ)) ⟨⟨by norm_num, by norm_num⟩, v.2⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
    · obtain ⟨u, rfl⟩ := hw
      refine ⟨coveringPlaneCoordinates.symm ((u : ℝ), (0 : ℝ)), ?_, ?_⟩
      · rw [frontier_centralConnectorUnitSquare]
        exact ⟨((u : ℝ), (0 : ℝ)), Or.inr ⟨u.2, Or.inl rfl⟩, rfl⟩
      · rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((u : ℝ), (0 : ℝ)) ⟨u.2, ⟨by norm_num, by norm_num⟩⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl
    · obtain ⟨u, rfl⟩ := hw
      refine ⟨coveringPlaneCoordinates.symm ((u : ℝ), (1 : ℝ)), ?_, ?_⟩
      · rw [frontier_centralConnectorUnitSquare]
        exact ⟨((u : ℝ), (1 : ℝ)), Or.inr ⟨u.2, Or.inr rfl⟩, rfl⟩
      · rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b
          ((u : ℝ), (1 : ℝ)) ⟨u.2, ⟨by norm_num, by norm_num⟩⟩]
        apply congrArg coveringPlaneCoordinates.symm
        apply congrArg (D.centralConnectorFilledSweepCoordinate b)
        apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem image_frontier_centralConnectorFilledPlaneSweepExtension_eq_carrier
    (b : D.ConnectorBandIndex) :
    D.centralConnectorFilledPlaneSweepExtension b ''
        frontier centralConnectorUnitSquare =
      (D.centralHeightFlowCompletedThetaSystem b).circle12.carrier := by
  rw [D.image_frontier_centralConnectorFilledPlaneSweepExtension,
    D.range_centralConnectorFilledSweepCoordinate_boundaryEdges,
    ThreePathSystem.carrier_circle12]
  change coveringPlaneCoordinates.symm ''
      (Set.range (D.centralHeightFlowLowerThetaRoute b) ∪
        Set.range (D.centralHeightFlowUpperThetaRoute b)) =
    Set.range (coveringPlaneCoordinates.symm ∘ D.centralHeightFlowLowerThetaRoute b) ∪
      Set.range (coveringPlaneCoordinates.symm ∘ D.centralHeightFlowUpperThetaRoute b)
  rw [Set.image_union, Set.range_comp, Set.range_comp]

theorem image_centralConnectorUnitSquare_eq_closure_inside
    (b : D.ConnectorBandIndex) :
    D.centralConnectorFilledPlaneSweepExtension b '' centralConnectorUnitSquare =
      closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside := by
  apply Schoenflies.JordanCircle.image_compactConvex_eq_closure_inside
  · exact convex_centralConnectorUnitSquare
  · exact isCompact_centralConnectorUnitSquare
  · exact interior_centralConnectorUnitSquare_nonempty
  · exact (D.continuous_centralConnectorFilledPlaneSweepExtension b).continuousOn
  · exact D.centralConnectorFilledPlaneSweepExtension_injOn b
  · exact D.image_frontier_centralConnectorFilledPlaneSweepExtension_eq_carrier b

theorem image_interior_centralConnectorUnitSquare_eq_inside
    (b : D.ConnectorBandIndex) :
    D.centralConnectorFilledPlaneSweepExtension b '' interior centralConnectorUnitSquare =
      (D.centralHeightFlowCompletedThetaSystem b).circle12.inside := by
  let J := (D.centralHeightFlowCompletedThetaSystem b).circle12
  let F := D.centralConnectorFilledPlaneSweepExtension b
  have hFinj : Set.InjOn F centralConnectorUnitSquare :=
    D.centralConnectorFilledPlaneSweepExtension_injOn b
  have hboundary : F '' frontier centralConnectorUnitSquare = J.carrier :=
    D.image_frontier_centralConnectorFilledPlaneSweepExtension_eq_carrier b
  have hclosedImage : F '' centralConnectorUnitSquare = closure J.inside :=
    D.image_centralConnectorUnitSquare_eq_closure_inside b
  have hclosed : IsClosed centralConnectorUnitSquare :=
    isCompact_centralConnectorUnitSquare.isClosed
  have hsplit : centralConnectorUnitSquare =
      interior centralConnectorUnitSquare ∪ frontier centralConnectorUnitSquare := by
    calc
      centralConnectorUnitSquare = closure centralConnectorUnitSquare := hclosed.closure_eq.symm
      _ = _ := closure_eq_interior_union_frontier _
  have havoid : F '' interior centralConnectorUnitSquare ⊆ J.carrierᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxCarrier
    rw [← hboundary] at hxCarrier
    obtain ⟨y, hy, hxy⟩ := hxCarrier
    have hxy' : x = y :=
      hFinj (interior_subset hx) (hclosed.frontier_subset hy) hxy.symm
    exact Set.disjoint_left.mp disjoint_interior_frontier hx (hxy' ▸ hy)
  have hmeets :
      (F '' interior centralConnectorUnitSquare ∩ J.inside).Nonempty := by
    have hp := J.insidePoint_mem_inside
    have hpClosure : J.insidePoint ∈ closure J.inside := subset_closure hp
    rw [← hclosedImage] at hpClosure
    obtain ⟨x, hx, hxImage⟩ := hpClosure
    rw [hsplit] at hx
    rcases hx with hxInterior | hxFrontier
    · exact ⟨J.insidePoint, ⟨x, hxInterior, hxImage⟩, hp⟩
    · have hcarrier : F x ∈ J.carrier := by
        rw [← hboundary]
        exact ⟨x, hxFrontier, rfl⟩
      exact False.elim (J.inside_subset_compl hp (hxImage ▸ hcarrier))
  have hside : F '' interior centralConnectorUnitSquare ⊆ J.inside := by
    have hconnected : IsPreconnected (F '' interior centralConnectorUnitSquare) :=
      convex_centralConnectorUnitSquare.interior.isPreconnected.image F
        ((D.continuous_centralConnectorFilledPlaneSweepExtension b).continuousOn)
    have hcover : F '' interior centralConnectorUnitSquare ⊆ J.inside ∪ J.outside := by
      rw [J.inside_union_outside]
      exact havoid
    rcases hconnected.subset_or_subset J.inside_isOpen J.outside_isOpen
        J.inside_disjoint_outside hcover with hinside | houtside
    · exact hinside
    · obtain ⟨y, hyImage, hyInside⟩ := hmeets
      exact False.elim <|
        Set.disjoint_left.mp J.inside_disjoint_outside hyInside (houtside hyImage)
  apply Set.Subset.antisymm hside
  intro y hy
  have hyClosure : y ∈ closure J.inside := subset_closure hy
  rw [← hclosedImage] at hyClosure
  obtain ⟨x, hx, rfl⟩ := hyClosure
  rw [hsplit] at hx
  rcases hx with hxInterior | hxFrontier
  · exact ⟨x, hxInterior, rfl⟩
  · have hcarrier : F x ∈ J.carrier := by
      rw [← hboundary]
      exact ⟨x, hxFrontier, rfl⟩
    exact False.elim (J.inside_subset_compl hy hcarrier)

theorem range_centralHeightFlowCompletedPlaneThetaPath_zero_subset_sweep
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowCompletedPlaneThetaPath b 0) ⊆
      D.centralConnectorFilledPlaneSweepExtension b '' centralConnectorUnitSquare := by
  rintro z ⟨u, rfl⟩
  let q : ℝ × ℝ := ((u : ℝ), (centralConnectorSweepMidpoint : ℝ))
  have hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨u.2, centralConnectorSweepMidpoint.2⟩
  refine ⟨coveringPlaneCoordinates.symm q, ⟨q, hq, rfl⟩, ?_⟩
  rw [D.centralConnectorFilledPlaneSweepExtension_apply_symm b q hq,
    D.centralConnectorFilledSweepCoordinate_midpoint]
  rfl

/-- The canonical height-flow square fills the lower-upper cycle and contains the original seam. -/
noncomputable def centralHeightFlowFilledOuterRegionData
    (b : D.ConnectorBandIndex) :
    (D.centralHeightFlowCompletedThetaSystem b).FilledOuterRegionData where
  region := D.centralConnectorFilledPlaneSweepExtension b '' centralConnectorUnitSquare
  region_isCompact := isCompact_centralConnectorUnitSquare.image
    (D.continuous_centralConnectorFilledPlaneSweepExtension b)
  region_frontier_subset := by
    rw [D.image_centralConnectorUnitSquare_eq_closure_inside b]
    exact frontier_closure_subset.trans <| by
      rw [(D.centralHeightFlowCompletedThetaSystem b).circle12.frontier_inside]
  path0_subset_region :=
    D.range_centralHeightFlowCompletedPlaneThetaPath_zero_subset_sweep b

/-- The unconditional filled theta package for the canonical height-flow construction. -/
noncomputable def centralHeightFlowCanonicalFilledThetaSystemData
    (b : D.ConnectorBandIndex) :
    FilledThetaSystemData (D.centralHeightFlowCompletedPlaneThetaPath b) :=
  D.centralHeightFlowFilledThetaSystemData b
    (D.centralHeightFlowFilledOuterRegionData b)

private theorem centralHeightFlowLowerThetaRoute_firstCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowLowerThetaRoute b
        (Schoenflies.ThreePiecePath.firstCoordinate u) =
      (D.centralLeftLowerHeightFlowBranchPath b).symm u :=
  Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

private theorem centralHeightFlowLowerThetaRoute_middleCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowLowerThetaRoute b
        (Schoenflies.ThreePiecePath.middleCoordinate u) =
      D.centralHeightFlowLowerConnector b u :=
  Schoenflies.ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

private theorem centralHeightFlowLowerThetaRoute_thirdCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowLowerThetaRoute b
        (Schoenflies.ThreePiecePath.thirdCoordinate u) =
      D.centralRightLowerHeightFlowBranchPath b u :=
  Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

private theorem centralHeightFlowUpperThetaRoute_firstCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowUpperThetaRoute b
        (Schoenflies.ThreePiecePath.firstCoordinate u) =
      D.centralLeftUpperHeightFlowBranchPath b u :=
  Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

private theorem centralHeightFlowUpperThetaRoute_middleCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowUpperThetaRoute b
        (Schoenflies.ThreePiecePath.middleCoordinate u) =
      D.centralHeightFlowUpperConnector b u :=
  Schoenflies.ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

private theorem centralHeightFlowUpperThetaRoute_thirdCoordinate
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowUpperThetaRoute b
        (Schoenflies.ThreePiecePath.thirdCoordinate u) =
      (D.centralRightUpperHeightFlowBranchPath b).symm u :=
  Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

/-- The unconditional filled height-flow theta straightened to the standard four-port theta. -/
noncomputable def centralHeightFlowFourPortHomeomorph
    (b : D.ConnectorBandIndex) : Plane ≃ₜ Plane :=
  coveringPlaneCoordinates.symm.trans
    (((D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
      standardPlaneFourPortThetaSystem
      (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
      standardPlaneFourPortTheta_outer_decomposition).trans
        coveringPlaneCoordinates)

theorem centralHeightFlowFourPortHomeomorph_apply_completedThetaPath
    (b : D.ConnectorBandIndex) (i : Fin 3) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralHeightFlowCompletedThetaPath b i u) =
      standardFourPortThetaPath i u := by
  fin_cases i
  · change coveringPlaneCoordinates
        ((D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 0 u))) =
      standardFourPortThetaPath 0 u
    have h := (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph_apply_path0
      standardPlaneFourPortThetaSystem
      (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
      standardPlaneFourPortTheta_outer_decomposition u
    change
      (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 0 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 0 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
      congrArg coveringPlaneCoordinates h
  · change coveringPlaneCoordinates
        ((D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 1 u))) =
      standardFourPortThetaPath 1 u
    have h := (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph_apply_path1
      standardPlaneFourPortThetaSystem
      (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
      standardPlaneFourPortTheta_outer_decomposition u
    change
      (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 1 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 1 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
      congrArg coveringPlaneCoordinates h
  · change coveringPlaneCoordinates
        ((D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 2 u))) =
      standardFourPortThetaPath 2 u
    have h := (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph_apply_path2
      standardPlaneFourPortThetaSystem
      (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
      standardPlaneFourPortTheta_outer_decomposition u
    change
      (D.centralHeightFlowCompletedThetaSystem b).outer12AmbientHomeomorph
          standardPlaneFourPortThetaSystem
          (D.centralHeightFlowCanonicalFilledThetaSystemData b).outer_decomposition
          standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.centralHeightFlowCompletedThetaPath b 2 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 2 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
      congrArg coveringPlaneCoordinates h

theorem centralHeightFlowFourPortHomeomorph_fixes_seam
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b (bandSeamPath u) = bandSeamPath u := by
  simpa only [centralHeightFlowCompletedThetaPath, standardFourPortThetaPath] using
    D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 0 u

theorem centralHeightFlowFourPortHomeomorph_apply_leftLowerBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralLeftLowerHeightFlowBranchPath b u) =
      standardLeftLowerBranchPath (unitInterval.symm u) := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 1
    (Schoenflies.ThreePiecePath.firstCoordinate (unitInterval.symm u))
  rw [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowLowerThetaRoute_firstCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_firstCoordinate] at h
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using h

private theorem centralHeightFlowFourPortHomeomorph_apply_lowerConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b (D.centralHeightFlowLowerConnector b u) =
      bandBottomPath u := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 1
    (Schoenflies.ThreePiecePath.middleCoordinate u)
  simpa only [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowLowerThetaRoute_middleCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_middleCoordinate] using h

theorem centralHeightFlowFourPortHomeomorph_apply_rightLowerBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralRightLowerHeightFlowBranchPath b u) =
      standardRightLowerBranchPath u := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 1
    (Schoenflies.ThreePiecePath.thirdCoordinate u)
  simpa only [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowLowerThetaRoute_thirdCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_thirdCoordinate] using h

theorem centralHeightFlowFourPortHomeomorph_apply_leftUpperBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralLeftUpperHeightFlowBranchPath b u) =
      standardLeftUpperBranchPath u := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 2
    (Schoenflies.ThreePiecePath.firstCoordinate u)
  simpa only [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowUpperThetaRoute_firstCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_firstCoordinate] using h

private theorem centralHeightFlowFourPortHomeomorph_apply_upperConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b (D.centralHeightFlowUpperConnector b u) =
      bandTopPath u := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 2
    (Schoenflies.ThreePiecePath.middleCoordinate u)
  simpa only [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowUpperThetaRoute_middleCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_middleCoordinate] using h

theorem centralHeightFlowFourPortHomeomorph_apply_rightUpperBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowFourPortHomeomorph b
        (D.centralRightUpperHeightFlowBranchPath b u) =
      standardRightUpperBranchPath (unitInterval.symm u) := by
  have h := D.centralHeightFlowFourPortHomeomorph_apply_completedThetaPath b 2
    (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm u))
  rw [centralHeightFlowCompletedThetaPath,
    D.centralHeightFlowUpperThetaRoute_thirdCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_thirdCoordinate] at h
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using h

private theorem centralHeightFlowFourPortHomeomorph_symm_apply_leftLowerBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (standardLeftLowerBranchPath u) =
      D.centralLeftLowerHeightFlowBranchPath b (unitInterval.symm u) := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  symm
  simpa only [unitInterval.symm_symm] using
    D.centralHeightFlowFourPortHomeomorph_apply_leftLowerBranch b
      (unitInterval.symm u)

theorem centralHeightFlowFourPortHomeomorph_symm_apply_lowerConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (bandBottomPath u) =
      D.centralHeightFlowLowerConnector b u := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  exact (D.centralHeightFlowFourPortHomeomorph_apply_lowerConnector b u).symm

private theorem centralHeightFlowFourPortHomeomorph_symm_apply_rightLowerBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (standardRightLowerBranchPath u) =
      D.centralRightLowerHeightFlowBranchPath b u := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  exact (D.centralHeightFlowFourPortHomeomorph_apply_rightLowerBranch b u).symm

private theorem centralHeightFlowFourPortHomeomorph_symm_apply_leftUpperBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (standardLeftUpperBranchPath u) =
      D.centralLeftUpperHeightFlowBranchPath b u := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  exact (D.centralHeightFlowFourPortHomeomorph_apply_leftUpperBranch b u).symm

theorem centralHeightFlowFourPortHomeomorph_symm_apply_upperConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (bandTopPath u) =
      D.centralHeightFlowUpperConnector b u := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  exact (D.centralHeightFlowFourPortHomeomorph_apply_upperConnector b u).symm

private theorem centralHeightFlowFourPortHomeomorph_symm_apply_rightUpperBranch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (standardRightUpperBranchPath u) =
      D.centralRightUpperHeightFlowBranchPath b (unitInterval.symm u) := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  symm
  simpa only [unitInterval.symm_symm] using
    D.centralHeightFlowFourPortHomeomorph_apply_rightUpperBranch b
      (unitInterval.symm u)

private theorem centralHeightFlowFourPortHomeomorph_symm_apply_seam
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowFourPortHomeomorph b).symm (bandSeamPath u) = bandSeamPath u := by
  apply (D.centralHeightFlowFourPortHomeomorph b).injective
  rw [(D.centralHeightFlowFourPortHomeomorph b).apply_symm_apply]
  exact (D.centralHeightFlowFourPortHomeomorph_fixes_seam b u).symm

private theorem centralHeightFlowFourPort_local_carrier_iff
    (b : D.ConnectorBandIndex) (z : Plane) (hz : z ∈ standardBandPatchCarrier) :
    (D.canonicalBandMap b ((D.centralHeightFlowFourPortHomeomorph b).symm z) ∈
        D.centralGraph.carrier ↔ z ∈ standardBandSingularCarrier) := by
  rcases hz with ((((hleft | hright) | hbottom) | htop) | hseam)
  · rw [range_bandLeftPath_eq_standardHalves] at hleft
    rcases hleft with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inl ?_)
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inl ⟨u, rfl⟩
      · intro _
        rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_leftLowerBranch]
        exact D.canonicalBandMap_centralLeftLowerHeightFlowBranchPath_mem_carrier b _
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inl ?_)
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inr ⟨u, rfl⟩
      · intro _
        rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_leftUpperBranch]
        exact D.canonicalBandMap_centralLeftUpperHeightFlowBranchPath_mem_carrier b _
  · rw [range_bandRightPath_eq_standardHalves] at hright
    rcases hright with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inr ?_)
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inl ⟨u, rfl⟩
      · intro _
        rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_rightLowerBranch]
        exact D.canonicalBandMap_centralRightLowerHeightFlowBranchPath_mem_carrier b _
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inr ?_)
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inr ⟨u, rfl⟩
      · intro _
        rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_rightUpperBranch]
        exact D.canonicalBandMap_centralRightUpperHeightFlowBranchPath_mem_carrier b _
  · rcases hbottom with ⟨u, rfl⟩
    rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_lowerConnector,
      D.centralHeightFlowLowerConnector_mem_carrier_iff]
    exact (bandBottomPath_mem_standardSingularUnion_iff u).symm
  · rcases htop with ⟨u, rfl⟩
    rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_upperConnector,
      D.centralHeightFlowUpperConnector_mem_carrier_iff]
    exact (bandTopPath_mem_standardSingularUnion_iff u).symm
  · rcases hseam with ⟨u, rfl⟩
    constructor
    · intro _
      unfold standardBandSingularCarrier
      exact Or.inr ⟨u, rfl⟩
    · intro _
      rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_seam]
      exact D.canonicalBandMap_bandSeamPath_mem_carrier b u

/-- The selected-height filled theta reparametrizes one canonical open band exactly. -/
noncomputable def centralHeightFlowStraightenedBandData
    (b : D.ConnectorBandIndex) :
    GlobalBandTubularChartData D.centralCutOrder b := by
  let B := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  let e : Plane ≃ₜ B.surfacePatch :=
    (D.centralHeightFlowFourPortHomeomorph b).symm.trans B.strip
  apply GlobalBandTubularChartData.ofStrip B.surfacePatch e
  · rintro _ ⟨z, rfl⟩
    apply B.strip_mem_neighborhood
    exact ⟨(D.centralHeightFlowFourPortHomeomorph b).symm z, rfl⟩
  · intro u
    change (((B.strip ((D.centralHeightFlowFourPortHomeomorph b).symm
      (bandSeamPath u)) : B.surfacePatch) : transportedTorus Phi) : R3) = _
    rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_seam]
    exact B.core_alignment u

/-- The selected-height filled theta supplies exact charts in every canonical band. -/
noncomputable def centralHeightFlowStraightenedChartFamily :
    D.centralCutOrder.GlobalBandTubularChartFamily where
  band := D.centralHeightFlowStraightenedBandData

theorem centralHeightFlowStraightenedChart_leftLowerBranch_apply
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftLowerBranchPath u) =
      D.canonicalBandMap b
        (D.centralLeftLowerHeightFlowBranchPath b (unitInterval.symm u)) := by
  change D.canonicalBandMap b
      ((D.centralHeightFlowFourPortHomeomorph b).symm
        (standardLeftLowerBranchPath u)) = _
  rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_leftLowerBranch]

theorem centralHeightFlowStraightenedChart_rightLowerBranch_apply
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightLowerBranchPath u) =
      D.canonicalBandMap b (D.centralRightLowerHeightFlowBranchPath b u) := by
  change D.canonicalBandMap b
      ((D.centralHeightFlowFourPortHomeomorph b).symm
        (standardRightLowerBranchPath u)) = _
  rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_rightLowerBranch]

theorem centralHeightFlowStraightenedChart_leftUpperBranch_apply
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftUpperBranchPath u) =
      D.canonicalBandMap b (D.centralLeftUpperHeightFlowBranchPath b u) := by
  change D.canonicalBandMap b
      ((D.centralHeightFlowFourPortHomeomorph b).symm
        (standardLeftUpperBranchPath u)) = _
  rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_leftUpperBranch]

theorem centralHeightFlowStraightenedChart_rightUpperBranch_apply
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightUpperBranchPath u) =
      D.canonicalBandMap b
        (D.centralRightUpperHeightFlowBranchPath b (unitInterval.symm u)) := by
  change D.canonicalBandMap b
      ((D.centralHeightFlowFourPortHomeomorph b).symm
        (standardRightUpperBranchPath u)) = _
  rw [D.centralHeightFlowFourPortHomeomorph_symm_apply_rightUpperBranch]

private theorem centralHeightFlowPointwiseExactness :
    CanonicalGlobalBandChartPointwiseExactness D.centralGraph D.centralOuterOrder
      D.centralCutOrder D.centralHeightFlowStraightenedChartFamily where
  support_eq := fun _ ↦ rfl
  chart_mem_carrier_iff := fun b z hz ↦ by
    change D.canonicalBandMap b
        ((D.centralHeightFlowFourPortHomeomorph b).symm z) ∈
      D.centralGraph.carrier ↔ z ∈ standardBandSingularCarrier
    exact D.centralHeightFlowFourPort_local_carrier_iff b z hz

/-- Unconditional exact canonical band charts obtained from the filled height-flow sweep. -/
noncomputable def centralHeightFlowArcExactness :
    CanonicalCentralBarrierChartData.ArcExactness D where
  charts := D.centralHeightFlowStraightenedChartFamily
  exactness := D.centralHeightFlowPointwiseExactness.toCanonicalGlobalBandChartArcExactness
    (hR := D.scale_pos)

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
