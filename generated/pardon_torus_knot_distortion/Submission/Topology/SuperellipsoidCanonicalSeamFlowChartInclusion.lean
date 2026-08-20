import Submission.Topology.SuperellipsoidCanonicalSeamFlowArms

/-!
# Uniform inclusion of canonical seam-flow arms in open band charts

The canonical global band charts are open in the transported torus.  Every left and right
seam-flow arm starts at the corresponding endpoint of its chart core.  Continuity and finiteness
therefore give one positive flow-time radius on which all arms remain inside their charts.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev FlowTimes := globalBandFlowCollarTimes D.heightData.band

private abbrev BandIndex := Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private theorem centralOuterArmLift_mem_transportedTorus (uv : Plane) :
    transportedTorusPlaneMap Phi uv ∈ transportedTorus Phi := by
  rw [← range_transportedTorusPlaneMap Phi]
  exact Set.mem_range_self uv

/-- The left seam-flow arm, regarded as a curve in the transported torus. -/
def centralLeftOuterArmPoint (b : D.BandIndex) (t : D.FlowTimes) :
    transportedTorus Phi :=
  ⟨transportedTorusPlaneMap Phi (D.centralLeftOuterArmLift b t),
    centralOuterArmLift_mem_transportedTorus _⟩

/-- The right seam-flow arm, regarded as a curve in the transported torus. -/
def centralRightOuterArmPoint (b : D.BandIndex) (t : D.FlowTimes) :
    transportedTorus Phi :=
  ⟨transportedTorusPlaneMap Phi (D.centralRightOuterArmLift b t),
    centralOuterArmLift_mem_transportedTorus _⟩

theorem continuous_centralLeftOuterArmPoint (b : D.BandIndex) :
    Continuous (D.centralLeftOuterArmPoint b) := by
  apply Continuous.subtype_mk
  exact (transportedTorusPlaneMap_contDiff Phi).continuous.comp
    (D.continuous_centralLeftOuterArmLift b)

theorem continuous_centralRightOuterArmPoint (b : D.BandIndex) :
    Continuous (D.centralRightOuterArmPoint b) := by
  apply Continuous.subtype_mk
  exact (transportedTorusPlaneMap_contDiff Phi).continuous.comp
    (D.continuous_centralRightOuterArmLift b)

private theorem centralLeftOuterArmPoint_zero (b : D.BandIndex) :
    D.centralLeftOuterArmPoint b (globalBandFlowCollarZeroTime D.heightData.band) =
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip bandLeftVertex :
        transportedTorus Phi) := by
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (D.centralSeamFlowData.2.flow
        (D.centralCutOrder.globalBandLeftFlowSeamLift b) 0) = _
  rw [D.centralSeamFlowData.2.flow_zero]
  calc
    transportedTorusPlaneMap Phi (D.centralCutOrder.globalBandLeftFlowSeamLift b) =
        (D.centralCutOrder.toPairedSeamEnumeration.firstVertex b).1 :=
      D.centralCutOrder.transportedTorusPlaneMap_globalBandLeftFlowSeamLift b
    _ = ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b)
        |>.toPairedSeamBandChart).leftVertex :=
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b)
        |>.toPairedSeamBandChart_leftVertex).symm
    _ = (((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
        bandLeftVertex :
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch) :
            transportedTorus Phi) := rfl

private theorem centralRightOuterArmPoint_zero (b : D.BandIndex) :
    D.centralRightOuterArmPoint b (globalBandFlowCollarZeroTime D.heightData.band) =
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip bandRightVertex :
        transportedTorus Phi) := by
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (D.centralSeamFlowData.2.flow
        (D.centralCutOrder.globalBandRightFlowSeamLift b) 0) = _
  rw [D.centralSeamFlowData.2.flow_zero]
  calc
    transportedTorusPlaneMap Phi (D.centralCutOrder.globalBandRightFlowSeamLift b) =
        (D.centralCutOrder.toPairedSeamEnumeration.secondVertex b).1 :=
      D.centralCutOrder.transportedTorusPlaneMap_globalBandRightFlowSeamLift b
    _ = ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b)
        |>.toPairedSeamBandChart).rightVertex :=
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b)
        |>.toPairedSeamBandChart_rightVertex).symm
    _ = (((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
        bandRightVertex :
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch) :
            transportedTorus Phi) := rfl

private def centralSeamFlowOpenChartTimes : Set D.FlowTimes :=
  (⋂ b : D.BandIndex,
      D.centralLeftOuterArmPoint b ⁻¹'
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch) ∩
    ⋂ b : D.BandIndex,
      D.centralRightOuterArmPoint b ⁻¹'
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch

private theorem isOpen_centralSeamFlowOpenChartTimes :
    IsOpen D.centralSeamFlowOpenChartTimes := by
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro b
    exact (D.centralCutOrder.globalBandOpenTubularChartFamily_surfacePatch_open b).preimage
      (D.continuous_centralLeftOuterArmPoint b)
  · apply isOpen_iInter_of_finite
    intro b
    exact (D.centralCutOrder.globalBandOpenTubularChartFamily_surfacePatch_open b).preimage
      (D.continuous_centralRightOuterArmPoint b)

private theorem zero_mem_centralSeamFlowOpenChartTimes :
    globalBandFlowCollarZeroTime D.heightData.band ∈
      D.centralSeamFlowOpenChartTimes := by
  constructor
  · rw [Set.mem_iInter]
    intro b
    show D.centralLeftOuterArmPoint b (globalBandFlowCollarZeroTime D.heightData.band) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch
    rw [D.centralLeftOuterArmPoint_zero b]
    exact ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
      bandLeftVertex).property
  · rw [Set.mem_iInter]
    intro b
    show D.centralRightOuterArmPoint b (globalBandFlowCollarZeroTime D.heightData.band) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch
    rw [D.centralRightOuterArmPoint_zero b]
    exact ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
      bandRightVertex).property

/-- One positive flow-time radius works simultaneously for every left and right canonical arm. -/
theorem exists_uniform_openChartTimeRadius :
    ∃ η : ℝ, 0 < η ∧ ∀ (b : D.BandIndex) (t : D.FlowTimes), |(t : ℝ)| < η →
      D.centralLeftOuterArmPoint b t ∈
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch ∧
        D.centralRightOuterArmPoint b t ∈
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp
    D.isOpen_centralSeamFlowOpenChartTimes
    (globalBandFlowCollarZeroTime D.heightData.band)
    D.zero_mem_centralSeamFlowOpenChartTimes
  refine ⟨η, hη, fun b t ht ↦ ?_⟩
  have htBall : t ∈ Metric.ball (globalBandFlowCollarZeroTime D.heightData.band) η := by
    change dist (t : ℝ) 0 < η
    simpa only [Real.dist_eq, sub_zero] using ht
  have htGood := hball htBall
  exact ⟨Set.mem_iInter.mp htGood.1 b, Set.mem_iInter.mp htGood.2 b⟩

/-- A selected positive radius on which every canonical seam-flow arm stays in its chart. -/
noncomputable def openChartTimeRadius : ℝ :=
  Classical.choose D.exists_uniform_openChartTimeRadius

theorem openChartTimeRadius_pos : 0 < D.openChartTimeRadius :=
  (Classical.choose_spec D.exists_uniform_openChartTimeRadius).1

theorem openChartTimeRadius_spec (b : D.BandIndex) (t : D.FlowTimes)
    (ht : |(t : ℝ)| < D.openChartTimeRadius) :
    D.centralLeftOuterArmPoint b t ∈
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch ∧
      D.centralRightOuterArmPoint b t ∈
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch :=
  (Classical.choose_spec D.exists_uniform_openChartTimeRadius).2 b t ht

/-- Narrow the endpoint levels to half of the uniform open-chart radius.  The moving arms still
use the original complete seam flow. -/
def openChartNarrowedData : CanonicalEndpointRegularityData S :=
  D.narrow (D.openChartTimeRadius / 2) (half_pos D.openChartTimeRadius_pos)

theorem openChartNarrowed_epsilon_lt_radius :
    D.openChartNarrowedData.heightData.band.ε < D.openChartTimeRadius := by
  rw [openChartNarrowedData, D.narrow_epsilon]
  exact (min_le_right _ _).trans_lt (half_lt_self D.openChartTimeRadius_pos)

theorem openChartNarrowed_epsilon_le_original :
    D.openChartNarrowedData.heightData.band.ε ≤ D.heightData.band.ε := by
  rw [openChartNarrowedData, D.narrow_epsilon]
  exact min_le_left _ _

/-- Regard a time in the narrowed endpoint interval as a time for the original seam flow. -/
def openChartNarrowedTime
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) : D.FlowTimes :=
  ⟨t, by
    constructor
    · exact (neg_le_neg D.openChartNarrowed_epsilon_le_original).trans t.2.1
    · exact t.2.2.trans D.openChartNarrowed_epsilon_le_original⟩

theorem continuous_openChartNarrowedTime : Continuous D.openChartNarrowedTime :=
  Continuous.subtype_mk continuous_subtype_val _

theorem centralOuterArmPoint_mem_openChart_of_narrowed
    (b : D.BandIndex)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    D.centralLeftOuterArmPoint b (D.openChartNarrowedTime t) ∈
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch ∧
      D.centralRightOuterArmPoint b (D.openChartNarrowedTime t) ∈
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  apply D.openChartTimeRadius_spec b
  apply lt_of_le_of_lt _ D.openChartNarrowed_epsilon_lt_radius
  rw [abs_le]
  exact t.2

/-- Strip coordinates of the left moving outer arm throughout the narrowed time interval. -/
def centralLeftOuterArmCoordinate
    (b : D.BandIndex)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) : Plane :=
  (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    ⟨D.centralLeftOuterArmPoint b (D.openChartNarrowedTime t),
      (D.centralOuterArmPoint_mem_openChart_of_narrowed b t).1⟩

/-- Strip coordinates of the right moving outer arm throughout the narrowed time interval. -/
def centralRightOuterArmCoordinate
    (b : D.BandIndex)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) : Plane :=
  (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    ⟨D.centralRightOuterArmPoint b (D.openChartNarrowedTime t),
      (D.centralOuterArmPoint_mem_openChart_of_narrowed b t).2⟩

theorem continuous_centralLeftOuterArmCoordinate (b : D.BandIndex) :
    Continuous (D.centralLeftOuterArmCoordinate b) := by
  apply (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.continuous.comp
  apply Continuous.subtype_mk
  exact (D.continuous_centralLeftOuterArmPoint b).comp
    D.continuous_openChartNarrowedTime

theorem continuous_centralRightOuterArmCoordinate (b : D.BandIndex) :
    Continuous (D.centralRightOuterArmCoordinate b) := by
  apply (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.continuous.comp
  apply Continuous.subtype_mk
  exact (D.continuous_centralRightOuterArmPoint b).comp
    D.continuous_openChartNarrowedTime

theorem centralLeftOuterArmCoordinate_injective (b : D.BandIndex) :
    Function.Injective (D.centralLeftOuterArmCoordinate b) := by
  intro s t hst
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective hst
  have hpoint : D.centralLeftOuterArmPoint b (D.openChartNarrowedTime s) =
      D.centralLeftOuterArmPoint b (D.openChartNarrowedTime t) :=
    congrArg Subtype.val hsurface
  have hheight := congrArg (ambientCoordinate (frame 2)) (congrArg Subtype.val hpoint)
  change orientedCoordinateLift Phi frame 2
      (D.centralLeftOuterArmLift b (D.openChartNarrowedTime s)) =
    orientedCoordinateLift Phi frame 2
      (D.centralLeftOuterArmLift b (D.openChartNarrowedTime t)) at hheight
  rw [D.centralLeftOuterArmLift_height b, D.centralLeftOuterArmLift_height b] at hheight
  apply Subtype.ext
  change S.cut.height + (s : ℝ) = S.cut.height + (t : ℝ) at hheight
  exact add_left_cancel hheight

theorem centralRightOuterArmCoordinate_injective (b : D.BandIndex) :
    Function.Injective (D.centralRightOuterArmCoordinate b) := by
  intro s t hst
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective hst
  have hpoint : D.centralRightOuterArmPoint b (D.openChartNarrowedTime s) =
      D.centralRightOuterArmPoint b (D.openChartNarrowedTime t) :=
    congrArg Subtype.val hsurface
  have hheight := congrArg (ambientCoordinate (frame 2)) (congrArg Subtype.val hpoint)
  change orientedCoordinateLift Phi frame 2
      (D.centralRightOuterArmLift b (D.openChartNarrowedTime s)) =
    orientedCoordinateLift Phi frame 2
      (D.centralRightOuterArmLift b (D.openChartNarrowedTime t)) at hheight
  rw [D.centralRightOuterArmLift_height b, D.centralRightOuterArmLift_height b] at hheight
  apply Subtype.ext
  change S.cut.height + (s : ℝ) = S.cut.height + (t : ℝ) at hheight
  exact add_left_cancel hheight

private theorem centralOuterArmCoordinate_time_eq
    (b : D.BandIndex)
    {s t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band}
    (hst : D.centralLeftOuterArmCoordinate b s = D.centralRightOuterArmCoordinate b t) :
    s = t := by
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective hst
  have hpoint : D.centralLeftOuterArmPoint b (D.openChartNarrowedTime s) =
      D.centralRightOuterArmPoint b (D.openChartNarrowedTime t) :=
    congrArg Subtype.val hsurface
  have hheight := congrArg (ambientCoordinate (frame 2)) (congrArg Subtype.val hpoint)
  change orientedCoordinateLift Phi frame 2
      (D.centralLeftOuterArmLift b (D.openChartNarrowedTime s)) =
    orientedCoordinateLift Phi frame 2
      (D.centralRightOuterArmLift b (D.openChartNarrowedTime t)) at hheight
  rw [D.centralLeftOuterArmLift_height b, D.centralRightOuterArmLift_height b] at hheight
  apply Subtype.ext
  change S.cut.height + (s : ℝ) = S.cut.height + (t : ℝ) at hheight
  exact add_left_cancel hheight

private theorem centralOuterArmPoint_ne_sameTime
    (b : D.BandIndex) (t : D.FlowTimes) :
    D.centralLeftOuterArmPoint b t ≠ D.centralRightOuterArmPoint b t := by
  intro hpoint
  have hmap := congrArg Subtype.val hpoint
  have hexp : planeExpPair
      (D.centralSeamFlowData.2.flow
        (D.centralCutOrder.globalBandLeftFlowSeamLift b) t) =
      planeExpPair
        (D.centralSeamFlowData.2.flow
          (D.centralCutOrder.globalBandRightFlowSeamLift b) t) := by
    apply transportedTorusMap_injective Phi
    change transportedTorusPlaneMap Phi
        (D.centralSeamFlowData.2.flow
          (D.centralCutOrder.globalBandLeftFlowSeamLift b) t) =
      transportedTorusPlaneMap Phi
        (D.centralSeamFlowData.2.flow
          (D.centralCutOrder.globalBandRightFlowSeamLift b) t) at hmap
    rw [transportedTorusPlaneMap_eq_expPair, transportedTorusPlaneMap_eq_expPair] at hmap
    exact hmap
  obtain ⟨m, n, hdeck⟩ := eq_add_planeDeckVector_of_planeExpPair_eq hexp
  have hflow :
      D.centralSeamFlowData.2.flow
          (D.centralCutOrder.globalBandLeftFlowSeamLift b) t =
        D.centralSeamFlowData.2.flow
          (D.centralCutOrder.globalBandRightFlowSeamLift b + planeDeckVector m n) t := by
    rw [D.centralSeamFlowData.2.flow_add_planeDeckVector
      D.centralSeamFlowData.1.contDiff_completeField
      D.centralSeamFlowData.1.completeField_isPlaneDeckPeriodic]
    exact hdeck
  have hbase : D.centralCutOrder.globalBandLeftFlowSeamLift b =
      D.centralCutOrder.globalBandRightFlowSeamLift b + planeDeckVector m n :=
    (D.centralSeamFlowData.2.timeHomeomorph
      D.centralSeamFlowData.1.contDiff_completeField
      D.centralSeamFlowData.1.completeField_isPlaneDeckPeriodic t).injective hflow
  have hbaseExp : planeExpPair (D.centralCutOrder.globalBandLeftFlowSeamLift b) =
      planeExpPair (D.centralCutOrder.globalBandRightFlowSeamLift b) := by
    rw [hbase, planeExpPair_add_planeDeckVector]
  have hbaseMap :
      transportedTorusPlaneMap Phi (D.centralCutOrder.globalBandLeftFlowSeamLift b) =
        transportedTorusPlaneMap Phi
          (D.centralCutOrder.globalBandRightFlowSeamLift b) := by
    rw [transportedTorusPlaneMap_eq_expPair, transportedTorusPlaneMap_eq_expPair, hbaseExp]
  apply D.centralCutOrder.toPairedSeamEnumeration.paired_vertices_ne b
  apply Subtype.ext
  rw [← D.centralCutOrder.transportedTorusPlaneMap_globalBandLeftFlowSeamLift b,
    ← D.centralCutOrder.transportedTorusPlaneMap_globalBandRightFlowSeamLift b]
  exact hbaseMap

theorem centralLeftOuterArmCoordinate_disjoint_centralRightOuterArmCoordinate
    (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftOuterArmCoordinate b))
      (Set.range (D.centralRightOuterArmCoordinate b)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, rfl⟩ ⟨t, hst⟩
  have hsEqT := D.centralOuterArmCoordinate_time_eq b hst.symm
  subst t
  apply D.centralOuterArmPoint_ne_sameTime b (D.openChartNarrowedTime s)
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective hst.symm
  exact congrArg Subtype.val hsurface

@[simp]
theorem centralLeftOuterArmCoordinate_zero (b : D.BandIndex) :
    D.centralLeftOuterArmCoordinate b
        (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band) =
      bandLeftVertex := by
  unfold centralLeftOuterArmCoordinate
  have htime : D.openChartNarrowedTime
      (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band) =
        globalBandFlowCollarZeroTime D.heightData.band := rfl
  have hpoint :
      (⟨D.centralLeftOuterArmPoint b (D.openChartNarrowedTime
          (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band)),
        (D.centralOuterArmPoint_mem_openChart_of_narrowed b _).1⟩ :
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch) =
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
          bandLeftVertex := by
    apply Subtype.ext
    change D.centralLeftOuterArmPoint b (D.openChartNarrowedTime
        (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band)) =
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip bandLeftVertex :
        transportedTorus Phi)
    rw [htime, D.centralLeftOuterArmPoint_zero b]
  rw [hpoint]
  exact (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm_apply_apply _

@[simp]
theorem centralRightOuterArmCoordinate_zero (b : D.BandIndex) :
    D.centralRightOuterArmCoordinate b
        (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band) =
      bandRightVertex := by
  unfold centralRightOuterArmCoordinate
  have htime : D.openChartNarrowedTime
      (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band) =
        globalBandFlowCollarZeroTime D.heightData.band := rfl
  have hpoint :
      (⟨D.centralRightOuterArmPoint b (D.openChartNarrowedTime
          (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band)),
        (D.centralOuterArmPoint_mem_openChart_of_narrowed b _).2⟩ :
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch) =
        (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
          bandRightVertex := by
    apply Subtype.ext
    change D.centralRightOuterArmPoint b (D.openChartNarrowedTime
        (globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band)) =
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip bandRightVertex :
        transportedTorus Phi)
    rw [htime, D.centralRightOuterArmPoint_zero b]
  rw [hpoint]
  exact (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm_apply_apply _

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
