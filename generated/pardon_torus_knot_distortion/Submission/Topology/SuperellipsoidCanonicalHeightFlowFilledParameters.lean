import Submission.Topology.SuperellipsoidCanonicalHeightFlowConnectors

/-!
# The compact filled parameter region between the canonical height-flow connectors

Inside the fixed probe-by-time rectangle, the nonpositive outer-defect locus is the closed
parameter strip bounded by the lower and upper connectors and the two outer branches.  This file
establishes its compactness and the exact alternatives for every parameter-frontier point.
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

private abbrev ConnectorFlowDomain := unitInterval × D.ConnectorFlowTimes

/-- The closed flow-time interval between the canonical lower and upper slices. -/
def centralConnectorSelectedTimes : Set D.ConnectorFlowTimes :=
  Icc D.centralLowerConnectorTime D.centralUpperConnectorTime

/-- The fixed compact probe-by-time rectangle containing the filled connector strip. -/
def centralConnectorParameterRectangle (b : D.ConnectorBandIndex) :
    Set D.ConnectorFlowDomain :=
  Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b) ×ˢ
    D.centralConnectorSelectedTimes

/-- The portion of the probe rectangle on or inside the outer superellipsoid level. -/
def centralConnectorFilledParameters (b : D.ConnectorBandIndex) :
    Set D.ConnectorFlowDomain :=
  D.centralConnectorParameterRectangle b ∩
    {p | D.centralHeightFlowOuterDefect b p.2 p.1 ≤ 0}

theorem continuous_centralHeightFlowOuterDefect_uncurry (b : D.ConnectorBandIndex) :
    Continuous (fun p : D.ConnectorFlowDomain ↦
      D.centralHeightFlowOuterDefect b p.2 p.1) :=
  D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
    D.centralHeightFlowData

private theorem frontier_centralConnectorSelectedTimes_subset :
    ∀ t ∈ frontier D.centralConnectorSelectedTimes,
      t = D.centralLowerConnectorTime ∨ t = D.centralUpperConnectorTime := by
  intro t ht
  have htIcc : t ∈ Icc D.centralLowerConnectorTime D.centralUpperConnectorTime := by
    rw [← closure_Icc]
    exact frontier_subset_closure ht
  have htNotIoo : t ∉ Ioo D.centralLowerConnectorTime D.centralUpperConnectorTime := by
    intro htIoo
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (interior_maximal Ioo_subset_Icc_self isOpen_Ioo htIoo) ht
  rcases eq_or_lt_of_le htIcc.1 with hleft | hleft
  · exact Or.inl hleft.symm
  · rcases eq_or_lt_of_le htIcc.2 with hright | hright
    · exact Or.inr hright
    · exact (htNotIoo ⟨hleft, hright⟩).elim

private theorem frontier_centralConnectorProbeInterval_subset
    (b : D.ConnectorBandIndex) :
    ∀ u ∈ frontier
      (Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b)),
      u = D.centralConnectorLeftProbe b ∨ u = D.centralConnectorRightProbe b := by
  intro u hu
  have huIcc : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorRightProbe b) := by
    rw [← closure_Icc]
    exact frontier_subset_closure hu
  have huNotIoo : u ∉ Ioo (D.centralConnectorLeftProbe b)
      (D.centralConnectorRightProbe b) := by
    intro huIoo
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (interior_maximal Ioo_subset_Icc_self isOpen_Ioo huIoo) hu
  rcases eq_or_lt_of_le huIcc.1 with hleft | hleft
  · exact Or.inl hleft.symm
  · rcases eq_or_lt_of_le huIcc.2 with hright | hright
    · exact Or.inr hright
    · exact (huNotIoo ⟨hleft, hright⟩).elim

theorem isCompact_centralConnectorParameterRectangle (b : D.ConnectorBandIndex) :
    IsCompact (D.centralConnectorParameterRectangle b) := by
  let _ : CompactSpace D.ConnectorFlowTimes :=
    isCompact_iff_compactSpace.mp <| by
      simpa only [ConnectorFlowTimes, globalBandFlowCollarTimes] using
        (isCompact_Icc : IsCompact
          (Icc (-D.ConnectorBand.ε) D.ConnectorBand.ε))
  exact isCompact_Icc.prod isClosed_Icc.isCompact

theorem isClosed_centralConnectorFilledParameters (b : D.ConnectorBandIndex) :
    IsClosed (D.centralConnectorFilledParameters b) := by
  exact (isClosed_Icc.prod isClosed_Icc).inter <|
    isClosed_le (D.continuous_centralHeightFlowOuterDefect_uncurry b) continuous_const

theorem isCompact_centralConnectorFilledParameters (b : D.ConnectorBandIndex) :
    IsCompact (D.centralConnectorFilledParameters b) := by
  exact (D.isCompact_centralConnectorParameterRectangle b).inter_right <|
    isClosed_le (D.continuous_centralHeightFlowOuterDefect_uncurry b) continuous_const

/-- The original inward excursion is the zero-time midline of the filled parameter region. -/
theorem centralConnectorCoreParameter_mem_filled
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
        (D.centralCutOrder.globalBandCoreRight b) u,
      globalBandFlowCollarZeroTime D.ConnectorBand) ∈
      D.centralConnectorFilledParameters b := by
  constructor
  · constructor
    · have hu : Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
          (D.centralCutOrder.globalBandCoreRight b) u ∈
          Icc (D.centralCutOrder.globalBandCoreLeft b)
            (D.centralCutOrder.globalBandCoreRight b) := by
        rw [← uIcc_of_le (D.centralCutOrder.globalBandCoreLeft_lt_coreRight b).le,
          ← Path.range_subpathAux]
        exact Set.mem_range_self u
      exact ⟨(D.centralConnectorLeftProbe_lt_coreLeft b).le.trans hu.1,
        hu.2.trans (D.centralConnectorCoreRight_lt_rightProbe b).le⟩
    · constructor
      · exact D.centralLowerConnectorTime_neg.le
      · exact D.centralUpperConnectorTime_pos.le
  · by_cases hu0 : (u : ℝ) = 0
    · have hu : u = 0 := Subtype.ext hu0
      subst u
      simpa only [Set.mem_ofPred_eq, Icc.convexComb_zero] using
        (D.centralHeightFlowOuterDefect_coreLeft_zero b).le
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = 1 := Subtype.ext hu1
        subst u
        simpa only [Set.mem_ofPred_eq, Icc.convexComb_one] using
          (D.centralHeightFlowOuterDefect_coreRight_zero b).le
      · exact (D.centralHeightFlowOuterDefect_core_zero_neg b u hu0 hu1).le

theorem abs_lt_uniformCentralConnectorTimeRadius
    {t : D.ConnectorFlowTimes} (ht : t ∈ D.centralConnectorSelectedTimes) :
    |(t : ℝ)| < D.uniformCentralConnectorTimeRadius := by
  rw [abs_lt]
  change -D.uniformCentralConnectorTimeRadius < (t : ℝ) ∧
    (t : ℝ) < D.uniformCentralConnectorTimeRadius
  change -D.uniformCentralConnectorTimeRadius / 2 ≤ (t : ℝ) ∧
    (t : ℝ) ≤ D.uniformCentralConnectorTimeRadius / 2 at ht
  constructor <;> linarith [D.uniformCentralConnectorTimeRadius_pos]

private theorem centralConnectorProbe_positive_of_mem_selectedTimes
    (b : D.ConnectorBandIndex) {t : D.ConnectorFlowTimes}
    (ht : t ∈ D.centralConnectorSelectedTimes) :
    0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b) := by
  apply D.centralConnectorPositiveProbeTimeRadius_spec b
  exact (D.abs_lt_uniformCentralConnectorTimeRadius ht).trans_le
    (D.uniformCentralConnectorTimeRadius_le_positive b)

/-- Every zero in the selected rectangle is the point on one of the two canonical moving outer
branches at the same flow time. -/
theorem centralConnector_zero_eq_outerArm
    (b : D.ConnectorBandIndex) {p : D.ConnectorFlowDomain}
    (hp : p ∈ D.centralConnectorParameterRectangle b)
    (hzero : D.centralHeightFlowOuterDefect b p.2 p.1 = 0) :
    D.centralHeightFlowSliceLift b p.2 p.1 =
        D.centralLeftOuterArmLift b (D.openChartNarrowedTime p.2) ∨
      D.centralHeightFlowSliceLift b p.2 p.1 =
        D.centralRightOuterArmLift b (D.openChartNarrowedTime p.2) := by
  have ht := D.abs_lt_uniformCentralConnectorTimeRadius hp.2
  by_cases hleft : p.1 ≤ D.centralConnectorLeftInnerProbe b
  · left
    apply D.centralConnectorLeftCrossing_eq_outerArm b p.2 ht p.1
    · exact ⟨hp.1.1, hleft⟩
    · exact hzero
  · by_cases hright : D.centralConnectorRightInnerProbe b ≤ p.1
    · right
      apply D.centralConnectorRightCrossing_eq_outerArm b p.2 ht p.1
      · exact ⟨hright, hp.1.2⟩
      · exact hzero
    · have hneg := D.centralConnectorFullNegativeTimeRadius_spec b p.2
        (ht.trans_le (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) p.1
        ⟨le_of_not_ge hleft, le_of_not_ge hright⟩
      exact (ne_of_lt hneg hzero).elim

/-- A frontier parameter is either on the lower slice, on the upper slice, or on the outer-level
zero locus.  The probe sides cannot occur because their defect is uniformly positive. -/
theorem frontier_centralConnectorFilledParameters_subset (b : D.ConnectorBandIndex) :
    frontier (D.centralConnectorFilledParameters b) ⊆
      {p | p.2 = D.centralLowerConnectorTime} ∪
        {p | p.2 = D.centralUpperConnectorTime} ∪
          {p | D.centralHeightFlowOuterDefect b p.2 p.1 = 0} := by
  intro p hpFrontier
  have hpFilled : p ∈ D.centralConnectorFilledParameters b := by
    have hpClosure := frontier_subset_closure hpFrontier
    simpa only [(D.isClosed_centralConnectorFilledParameters b).closure_eq] using hpClosure
  have hpSplit := frontier_inter_subset
    (D.centralConnectorParameterRectangle b)
    {p | D.centralHeightFlowOuterDefect b p.2 p.1 ≤ 0} hpFrontier
  rcases hpSplit with hpRectangle | hpDefect
  · rw [centralConnectorParameterRectangle, centralConnectorSelectedTimes,
      frontier_prod_eq,
      closure_Icc, closure_Icc] at hpRectangle
    rcases hpRectangle with ⟨_, ht⟩ | ⟨hu, ht⟩
    · have htEnds :=
        D.frontier_centralConnectorSelectedTimes_subset p.2 ht
      rcases htEnds with hLower | hUpper
      · exact Or.inl (Or.inl hLower)
      · exact Or.inl (Or.inr hUpper)
    · have huEnds :=
        D.frontier_centralConnectorProbeInterval_subset b p.1 hu
      rcases huEnds with hLeft | hRight
      · have hpos := (D.centralConnectorProbe_positive_of_mem_selectedTimes b ht).1
        have hnonpos : D.centralHeightFlowOuterDefect b p.2 p.1 ≤ 0 := by
          simpa only [Set.mem_ofPred_eq] using hpFilled.2
        rw [hLeft] at hnonpos
        exact (not_lt_of_ge hnonpos hpos).elim
      · have hpos := (D.centralConnectorProbe_positive_of_mem_selectedTimes b ht).2
        have hnonpos : D.centralHeightFlowOuterDefect b p.2 p.1 ≤ 0 := by
          simpa only [Set.mem_ofPred_eq] using hpFilled.2
        rw [hRight] at hnonpos
        exact (not_lt_of_ge hnonpos hpos).elim
  · apply Or.inr
    exact frontier_le_subset_eq
      (D.continuous_centralHeightFlowOuterDefect_uncurry b) continuous_const hpDefect.2

/-- On every selected slice there is a unique left outer-level crossing in the controlled seam
interval. -/
theorem existsUnique_centralConnectorLeftCrossing
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (ht : t ∈ D.centralConnectorSelectedTimes) :
    ∃! u : unitInterval,
      u ∈ Icc (D.centralConnectorLeftProbe b)
          (D.centralConnectorLeftInnerProbe b) ∧
        D.centralHeightFlowOuterDefect b t u = 0 := by
  have habs := D.abs_lt_uniformCentralConnectorTimeRadius ht
  have hnegative : ∀ u ∈ Icc (D.centralConnectorLeftInnerProbe b)
      (D.centralConnectorRightInnerProbe b),
      D.centralHeightFlowOuterDefect b t u < 0 := by
    intro u hu
    exact D.centralConnectorFullNegativeTimeRadius_spec b t
      (habs.trans_le (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) u hu
  obtain ⟨⟨u, hu, hzero⟩, _⟩ := D.exists_centralConnectorCrossings b t
    (D.centralConnectorProbe_positive_of_mem_selectedTimes b ht) hnegative
  refine ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩, ?_⟩
  intro v hv
  apply D.centralHeightFlowSliceLift_injective b t
  rw [D.centralConnectorLeftCrossing_eq_outerArm b t habs u
      ⟨hu.1.le, hu.2.le⟩ hzero,
    D.centralConnectorLeftCrossing_eq_outerArm b t habs v hv.1 hv.2]

/-- On every selected slice there is a unique right outer-level crossing in the controlled seam
interval. -/
theorem existsUnique_centralConnectorRightCrossing
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (ht : t ∈ D.centralConnectorSelectedTimes) :
    ∃! u : unitInterval,
      u ∈ Icc (D.centralConnectorRightInnerProbe b)
          (D.centralConnectorRightProbe b) ∧
        D.centralHeightFlowOuterDefect b t u = 0 := by
  have habs := D.abs_lt_uniformCentralConnectorTimeRadius ht
  have hnegative : ∀ u ∈ Icc (D.centralConnectorLeftInnerProbe b)
      (D.centralConnectorRightInnerProbe b),
      D.centralHeightFlowOuterDefect b t u < 0 := by
    intro u hu
    exact D.centralConnectorFullNegativeTimeRadius_spec b t
      (habs.trans_le (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) u hu
  obtain ⟨_, ⟨u, hu, hzero⟩⟩ := D.exists_centralConnectorCrossings b t
    (D.centralConnectorProbe_positive_of_mem_selectedTimes b ht) hnegative
  refine ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩, ?_⟩
  intro v hv
  apply D.centralHeightFlowSliceLift_injective b t
  rw [D.centralConnectorRightCrossing_eq_outerArm b t habs u
      ⟨hu.1.le, hu.2.le⟩ hzero,
    D.centralConnectorRightCrossing_eq_outerArm b t habs v hv.1 hv.2]

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
