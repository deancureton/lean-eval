import Submission.Topology.SuperellipsoidCanonicalBooleanOutsidePaths
import Submission.Topology.SuperellipsoidOuterClosedGapPackage
import Submission.Topology.BooleanFourPortLocalIncidence
import Submission.Topology.BooleanFourPortOutsidePaths

/-!
# Canonical corner trimming of the central outer gaps

Each straightened four-port branch lies in one member of the finite disjoint closed-gap
partition of the central outer section.  Its seam endpoint identifies that member.  Hence both
four-port corners of an outside edge have canonical parameters on the same embedded outer gap,
and the subpath between those parameters removes the two chart branches without backtracking.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily
open FiniteSuperellipsoidBarrierGraph.OuterCircleTransverseHeightCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private theorem IsPreconnected.subset_or_subset_closed
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v)
    (huv : Disjoint u v) (hsub : s ⊆ u ∪ v) :
    s ⊆ u ∨ s ⊆ v := by
  by_contra h
  have hsu : ¬s ⊆ u := fun hsu ↦ h (Or.inl hsu)
  have hsv : ¬s ⊆ v := fun hsv ↦ h (Or.inr hsv)
  obtain ⟨x, hxs, hxu⟩ := Set.not_subset.mp hsu
  obtain ⟨y, hys, hyv⟩ := Set.not_subset.mp hsv
  have hxv : x ∈ v := (hsub hxs).resolve_left hxu
  have hyu : y ∈ u := (hsub hys).resolve_right hyv
  obtain ⟨z, _hzs, hzu, hzv⟩ :=
    isPreconnected_closed_iff.mp hs u v hu hv hsub
      ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  exact Set.disjoint_left.mp huv hzu hzv

private theorem IsConnected.subset_one_of_finite_disjoint_closed_iUnion
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    {s : Set X} (hs : IsConnected s) (u : ι → Set X)
    (hclosed : ∀ i, IsClosed (u i))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (u i) (u j))
    (hsub : s ⊆ ⋃ i, u i) :
    ∃ i, s ⊆ u i := by
  have hfinite (I : Finset ι)
      (hclosedI : ∀ i ∈ I, IsClosed (u i))
      (hdisjointI : ∀ {i}, i ∈ I → ∀ {j}, j ∈ I → i ≠ j →
        Disjoint (u i) (u j))
      (hsubI : s ⊆ ⋃ i ∈ I, u i) :
      ∃ i ∈ I, s ⊆ u i := by
    induction I using Finset.induction_on with
    | empty =>
        obtain ⟨x, hx⟩ := hs.nonempty
        simpa using hsubI hx
    | @insert i I hi ih =>
        let rest : Set X := ⋃ j ∈ I, u j
        have hrestClosed : IsClosed rest :=
          isClosed_biUnion_finset fun j hj ↦
            hclosedI j (Finset.mem_insert_of_mem hj)
        have hiClosed : IsClosed (u i) :=
          hclosedI i (Finset.mem_insert_self i I)
        have hiRest : Disjoint (u i) rest := by
          rw [Set.disjoint_left]
          intro x hxi hxrest
          simp only [rest, Set.mem_iUnion] at hxrest
          obtain ⟨j, hj, hxj⟩ := hxrest
          exact Set.disjoint_left.mp
            (hdisjointI (Finset.mem_insert_self i I)
              (Finset.mem_insert_of_mem hj)
              (Ne.symm <| fun hji ↦ hi (hji ▸ hj))) hxi hxj
        have hcover : s ⊆ u i ∪ rest := by
          simpa only [Finset.set_biUnion_insert] using hsubI
        rcases IsPreconnected.subset_or_subset_closed hs.isPreconnected
            hiClosed hrestClosed hiRest hcover with hsi | hsrest
        · exact ⟨i, Finset.mem_insert_self i I, hsi⟩
        · obtain ⟨j, hj, hsj⟩ := ih
            (fun j hj ↦ hclosedI j (Finset.mem_insert_of_mem hj))
            (fun {j} hj {k} hk hjk ↦ hdisjointI
              (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk)
            hsrest
          exact ⟨j, Finset.mem_insert_of_mem hj, hsj⟩
  obtain ⟨i, _, hi⟩ := hfinite Finset.univ
    (fun i _ ↦ hclosed i)
    (fun {_} _ {_} _ hij ↦ hdisjoint hij) (by simpa using hsub)
  exact ⟨i, hi⟩

private theorem canonicalBandMap_leftOuterArm
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b t) =
      D.centralLeftOuterArmPoint b (D.openChartNarrowedTime t) := by
  unfold canonicalBandMap centralLeftOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]

private theorem canonicalBandMap_rightOuterArm
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    D.canonicalBandMap b (D.centralRightOuterArmCoordinate b t) =
      D.centralRightOuterArmPoint b (D.openChartNarrowedTime t) := by
  unfold canonicalBandMap centralRightOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]

private theorem canonicalBandMap_leftOuterArm_mem_outerCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b t) ∈
      ⋃ i, Set.range (D.centralGraph.outer.circle i).circle := by
  rw [← D.centralGraph.outer.section_exact]
  rw [D.canonicalBandMap_leftOuterArm]
  constructor
  · exact (D.centralLeftOuterArmPoint b (D.openChartNarrowedTime t)).2
  · rw [mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ D.scale_pos.le]
    exact D.centralLeftOuterArmLift_level b (D.openChartNarrowedTime t)

private theorem canonicalBandMap_rightOuterArm_mem_outerCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    D.canonicalBandMap b (D.centralRightOuterArmCoordinate b t) ∈
      ⋃ i, Set.range (D.centralGraph.outer.circle i).circle := by
  rw [← D.centralGraph.outer.section_exact]
  rw [D.canonicalBandMap_rightOuterArm]
  constructor
  · exact (D.centralRightOuterArmPoint b (D.openChartNarrowedTime t)).2
  · rw [mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ D.scale_pos.le]
    exact D.centralRightOuterArmLift_level b (D.openChartNarrowedTime t)

private theorem canonicalBandMap_leftOuterArm_height
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    (D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b t)).ofLp (frame 2) =
      S.cut.height + t := by
  rw [D.canonicalBandMap_leftOuterArm]
  change orientedCoordinateLift Phi frame 2
      (D.centralLeftOuterArmLift b (D.openChartNarrowedTime t)) = _
  exact D.centralLeftOuterArmLift_height b (D.openChartNarrowedTime t)

private theorem canonicalBandMap_rightOuterArm_height
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    (t : globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band) :
    (D.canonicalBandMap b (D.centralRightOuterArmCoordinate b t)).ofLp (frame 2) =
      S.cut.height + t := by
  rw [D.canonicalBandMap_rightOuterArm]
  change orientedCoordinateLift Phi frame 2
      (D.centralRightOuterArmLift b (D.openChartNarrowedTime t)) = _
  exact D.centralRightOuterArmLift_height b (D.openChartNarrowedTime t)

private noncomputable def lowerPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :=
  seamToCornerPathOfBandSide D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily b side 0

private noncomputable def upperPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :=
  seamToCornerPathOfBandSide D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily b side 1

private theorem lowerPortBranch_range_subset_outerCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.lowerPortBranch b side) ⊆
      ⋃ i, Set.range (D.centralGraph.outer.circle i).circle := by
  fin_cases side
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftLowerBranchPath u) ∈ _
    rw [D.centralHeightFlowStraightenedChart_leftLowerBranch_apply]
    change D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b _) ∈ _
    exact D.canonicalBandMap_leftOuterArm_mem_outerCarrier _ _
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightLowerBranchPath (unitInterval.symm u)) ∈ _
    rw [D.centralHeightFlowStraightenedChart_rightLowerBranch_apply]
    change D.canonicalBandMap b (D.centralRightOuterArmCoordinate b _) ∈ _
    exact D.canonicalBandMap_rightOuterArm_mem_outerCarrier _ _

private theorem lowerPortBranch_range_subset_lowerHalfspace
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.lowerPortBranch b side) ⊆ lowerClosedHalfspace frame S.cut.height := by
  fin_cases side
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftLowerBranchPath u) ∈ _
    rw [D.centralHeightFlowStraightenedChart_leftLowerBranch_apply]
    change _ ≤ S.cut.height
    change (D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b _)).ofLp
        (frame 2) ≤ S.cut.height
    rw [D.canonicalBandMap_leftOuterArm_height, D.coe_connectorFlowTimeSegment]
    simp only [globalBandFlowCollarZeroTime]
    nlinarith [D.centralLowerConnectorTime_neg, (unitInterval.symm u).2.1,
      (unitInterval.symm u).2.2]
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightLowerBranchPath (unitInterval.symm u)) ∈ _
    rw [D.centralHeightFlowStraightenedChart_rightLowerBranch_apply]
    change _ ≤ S.cut.height
    change (D.canonicalBandMap b (D.centralRightOuterArmCoordinate b _)).ofLp
        (frame 2) ≤ S.cut.height
    rw [D.canonicalBandMap_rightOuterArm_height, D.coe_connectorFlowTimeSegment]
    simp only [globalBandFlowCollarZeroTime]
    nlinarith [D.centralLowerConnectorTime_neg, (unitInterval.symm u).2.1,
      (unitInterval.symm u).2.2]

private theorem upperPortBranch_range_subset_outerCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.upperPortBranch b side) ⊆
      ⋃ i, Set.range (D.centralGraph.outer.circle i).circle := by
  fin_cases side
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftUpperBranchPath u) ∈ _
    rw [D.centralHeightFlowStraightenedChart_leftUpperBranch_apply]
    change D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b _) ∈ _
    exact D.canonicalBandMap_leftOuterArm_mem_outerCarrier _ _
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightUpperBranchPath (unitInterval.symm u)) ∈ _
    rw [D.centralHeightFlowStraightenedChart_rightUpperBranch_apply]
    change D.canonicalBandMap b (D.centralRightOuterArmCoordinate b _) ∈ _
    exact D.canonicalBandMap_rightOuterArm_mem_outerCarrier _ _

private theorem upperPortBranch_range_subset_upperHalfspace
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.upperPortBranch b side) ⊆ upperClosedHalfspace frame S.cut.height := by
  fin_cases side
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftUpperBranchPath u) ∈ _
    rw [D.centralHeightFlowStraightenedChart_leftUpperBranch_apply]
    change S.cut.height ≤ _
    change S.cut.height ≤
      (D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b _)).ofLp (frame 2)
    rw [D.canonicalBandMap_leftOuterArm_height, D.coe_connectorFlowTimeSegment]
    simp only [globalBandFlowCollarZeroTime, mul_zero, zero_add]
    nlinarith [D.centralUpperConnectorTime_pos, u.2.1]
  · rintro _ ⟨u, rfl⟩
    change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightUpperBranchPath (unitInterval.symm u)) ∈ _
    rw [D.centralHeightFlowStraightenedChart_rightUpperBranch_apply]
    change S.cut.height ≤ _
    rw [unitInterval.symm_symm]
    change S.cut.height ≤
      (D.canonicalBandMap b (D.centralRightOuterArmCoordinate b _)).ofLp (frame 2)
    rw [D.canonicalBandMap_rightOuterArm_height, D.coe_connectorFlowTimeSegment]
    simp only [globalBandFlowCollarZeroTime, mul_zero, zero_add]
    nlinarith [D.centralUpperConnectorTime_pos, u.2.1]

/-- The lower chart branch attached to one endpoint of a selected lower outer gap. -/
noncomputable def lowerGapPortBranch
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :=
  seamToFourPortCornerPath D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily
    (D.centralOuterOrder.globalLowerEndpointEquiv (g, e)) 0

/-- The upper chart branch attached to one endpoint of a selected upper outer gap. -/
noncomputable def upperGapPortBranch
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :=
  seamToFourPortCornerPath D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily
    (D.centralOuterOrder.globalUpperEndpointEquiv (g, e)) 1

private theorem range_lowerGapPortBranch_eq
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerGapPortBranch g e) =
      Set.range (D.lowerPortBranch
        (seamBandSide D.centralCutOrder
          (D.centralOuterOrder.globalLowerEndpointEquiv (g, e))).1
        (seamBandSide D.centralCutOrder
          (D.centralOuterOrder.globalLowerEndpointEquiv (g, e))).2) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    unfold lowerGapPortBranch seamToFourPortCornerPath lowerPortBranch
    rw [Path.cast_coe]
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    unfold lowerGapPortBranch seamToFourPortCornerPath lowerPortBranch
    rw [Path.cast_coe]

private theorem range_upperGapPortBranch_eq
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperGapPortBranch g e) =
      Set.range (D.upperPortBranch
        (seamBandSide D.centralCutOrder
          (D.centralOuterOrder.globalUpperEndpointEquiv (g, e))).1
        (seamBandSide D.centralCutOrder
          (D.centralOuterOrder.globalUpperEndpointEquiv (g, e))).2) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    unfold upperGapPortBranch seamToFourPortCornerPath upperPortBranch
    rw [Path.cast_coe]
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    unfold upperGapPortBranch seamToFourPortCornerPath upperPortBranch
    rw [Path.cast_coe]

private theorem outerCircle_range_isClosed (i : D.centralOuterFamily.index) :
    IsClosed (Set.range (D.centralGraph.outer.circle i).circle) :=
  (isCompact_range (D.centralGraph.outer.circle i).isEmbedding.continuous).isClosed


private theorem exists_outerCircle_lowerGapPortBranch
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    ∃ i, Set.range (D.lowerGapPortBranch g e) ⊆
      Set.range (D.centralGraph.outer.circle i).circle := by
  classical
  apply IsConnected.subset_one_of_finite_disjoint_closed_iUnion
    (isConnected_range (D.lowerGapPortBranch g e).continuous)
    (fun i ↦ Set.range (D.centralGraph.outer.circle i).circle)
    D.outerCircle_range_isClosed D.centralGraph.outer.pairwise_disjoint
  rw [D.range_lowerGapPortBranch_eq g e]
  exact D.lowerPortBranch_range_subset_outerCarrier _ _

private theorem exists_outerCircle_upperGapPortBranch
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    ∃ i, Set.range (D.upperGapPortBranch g e) ⊆
      Set.range (D.centralGraph.outer.circle i).circle := by
  classical
  apply IsConnected.subset_one_of_finite_disjoint_closed_iUnion
    (isConnected_range (D.upperGapPortBranch g e).continuous)
    (fun i ↦ Set.range (D.centralGraph.outer.circle i).circle)
    D.outerCircle_range_isClosed D.centralGraph.outer.pairwise_disjoint
  rw [D.range_upperGapPortBranch_eq g e]
  exact D.upperPortBranch_range_subset_outerCarrier _ _


private theorem lowerGapPortBranch_range_subset_activeCarrier
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerGapPortBranch g e) ⊆
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  classical
  obtain ⟨i, hi⟩ := D.exists_outerCircle_lowerGapPortBranch g e
  let v := D.centralOuterOrder.globalLowerEndpointEquiv (g, e)
  have hvBranch : v.1 ∈ Set.range (D.lowerGapPortBranch g e) :=
    ⟨0, (D.lowerGapPortBranch g e).source⟩
  have hvGap : v.1 ∈ Set.range (D.centralGraph.outer.circle g.1.1).circle := by
    have hvGap' := D.centralOuterOrder.gapPath_mem_outerCircle
      (D.centralOuterOrder.lowerGapAsGlobalOuterGap g)
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e)
    have hvEq := D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g e
    exact hvEq.symm ▸ hvGap'
  have hiEq : i = g.1.1 := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.centralGraph.outer.pairwise_disjoint hne) (hi hvBranch) hvGap
  subst i
  intro x hx
  exact Set.mem_iUnion.mpr ⟨g.1, hi hx⟩


private theorem upperGapPortBranch_range_subset_activeCarrier
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperGapPortBranch g e) ⊆
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  classical
  obtain ⟨i, hi⟩ := D.exists_outerCircle_upperGapPortBranch g e
  let v := D.centralOuterOrder.globalUpperEndpointEquiv (g, e)
  have hvBranch : v.1 ∈ Set.range (D.upperGapPortBranch g e) :=
    ⟨0, (D.upperGapPortBranch g e).source⟩
  have hvGap : v.1 ∈ Set.range (D.centralGraph.outer.circle g.1.1).circle := by
    have hvGap' := D.centralOuterOrder.gapPath_mem_outerCircle
      (D.centralOuterOrder.upperGapAsGlobalOuterGap g)
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e)
    have hvEq := D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g e
    exact hvEq.symm ▸ hvGap'
  have hiEq : i = g.1.1 := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.centralGraph.outer.pairwise_disjoint hne) (hi hvBranch) hvGap
  subst i
  intro x hx
  exact Set.mem_iUnion.mpr ⟨g.1, hi hx⟩

theorem lowerGapPortBranch_range_subset_gap
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerGapPortBranch g e) ⊆
      Set.range fun u ↦
        ((D.centralOuterOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) := by
  classical
  have hUnion : Set.range (D.lowerGapPortBranch g e) ⊆
      ⋃ h : D.centralOuterOrder.GlobalLowerOuterGap,
        Set.range fun u ↦
          ((D.centralOuterOrder.globalLowerOuterPath h u : transportedTorus Phi) : R3) := by
    rw [D.centralOuterOrder.iUnion_range_globalLowerOuterPath_eq]
    intro x hx
    exact ⟨D.lowerGapPortBranch_range_subset_activeCarrier g e hx,
      D.lowerPortBranch_range_subset_lowerHalfspace _ _
        (D.range_lowerGapPortBranch_eq g e ▸ hx)⟩
  obtain ⟨h, hh⟩ := IsConnected.subset_one_of_finite_disjoint_closed_iUnion
    (isConnected_range (D.lowerGapPortBranch g e).continuous)
    (fun h ↦ Set.range fun u ↦
      ((D.centralOuterOrder.globalLowerOuterPath h u : transportedTorus Phi) : R3))
    (fun h ↦ (isCompact_range (continuous_subtype_val.comp
      (D.centralOuterOrder.globalLowerOuterPath h).continuous)).isClosed)
    D.centralOuterOrder.globalLowerOuterPath_ranges_pairwise_disjoint hUnion
  let v := D.centralOuterOrder.globalLowerEndpointEquiv (g, e)
  have hvBranch : v.1 ∈ Set.range (D.lowerGapPortBranch g e) :=
    ⟨0, (D.lowerGapPortBranch g e).source⟩
  have hvGap : v.1 ∈ Set.range fun u ↦
      ((D.centralOuterOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) := by
    refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e, ?_⟩
    exact (D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g e).symm
  have hhEq : h = g := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.centralOuterOrder.globalLowerOuterPath_ranges_pairwise_disjoint hne)
      (hh hvBranch) hvGap
  subst h
  exact hh

theorem upperGapPortBranch_range_subset_gap
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperGapPortBranch g e) ⊆
      Set.range fun u ↦
        ((D.centralOuterOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) := by
  classical
  have hUnion : Set.range (D.upperGapPortBranch g e) ⊆
      ⋃ h : D.centralOuterOrder.GlobalUpperOuterGap,
        Set.range fun u ↦
          ((D.centralOuterOrder.globalUpperOuterPath h u : transportedTorus Phi) : R3) := by
    rw [D.centralOuterOrder.iUnion_range_globalUpperOuterPath_eq]
    intro x hx
    exact ⟨D.upperGapPortBranch_range_subset_activeCarrier g e hx,
      D.upperPortBranch_range_subset_upperHalfspace _ _
        (D.range_upperGapPortBranch_eq g e ▸ hx)⟩
  obtain ⟨h, hh⟩ := IsConnected.subset_one_of_finite_disjoint_closed_iUnion
    (isConnected_range (D.upperGapPortBranch g e).continuous)
    (fun h ↦ Set.range fun u ↦
      ((D.centralOuterOrder.globalUpperOuterPath h u : transportedTorus Phi) : R3))
    (fun h ↦ (isCompact_range (continuous_subtype_val.comp
      (D.centralOuterOrder.globalUpperOuterPath h).continuous)).isClosed)
    D.centralOuterOrder.globalUpperOuterPath_ranges_pairwise_disjoint hUnion
  let v := D.centralOuterOrder.globalUpperEndpointEquiv (g, e)
  have hvBranch : v.1 ∈ Set.range (D.upperGapPortBranch g e) :=
    ⟨0, (D.upperGapPortBranch g e).source⟩
  have hvGap : v.1 ∈ Set.range fun u ↦
      ((D.centralOuterOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) := by
    refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e, ?_⟩
    exact (D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g e).symm
  have hhEq : h = g := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.centralOuterOrder.globalUpperOuterPath_ranges_pairwise_disjoint hne)
      (hh hvBranch) hvGap
  subst h
  exact hh

/-- Parameter of one lower four-port corner on its complete central outer gap. -/
noncomputable def lowerGapCornerParameter
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) : unitInterval :=
  Classical.choose (D.lowerGapPortBranch_range_subset_gap g e
    ⟨1, rfl⟩)

theorem lowerGapCornerParameter_spec
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    ((D.centralOuterOrder.globalLowerOuterPath g (D.lowerGapCornerParameter g e) :
      transportedTorus Phi) : R3) = D.lowerGapPortBranch g e 1 :=
  Classical.choose_spec (D.lowerGapPortBranch_range_subset_gap g e
    ⟨1, rfl⟩)

/-- Parameter of one upper four-port corner on its complete central outer gap. -/
noncomputable def upperGapCornerParameter
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) : unitInterval :=
  Classical.choose (D.upperGapPortBranch_range_subset_gap g e
    ⟨1, rfl⟩)

theorem upperGapCornerParameter_spec
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    ((D.centralOuterOrder.globalUpperOuterPath g (D.upperGapCornerParameter g e) :
      transportedTorus Phi) : R3) = D.upperGapPortBranch g e 1 :=
  Classical.choose_spec (D.upperGapPortBranch_range_subset_gap g e
    ⟨1, rfl⟩)

theorem lowerGapCorner_eq
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, e)) =
      ((D.centralOuterOrder.globalLowerOuterPath g (D.lowerGapCornerParameter g e) :
        transportedTorus Phi) : R3) := by
  rw [D.lowerGapCornerParameter_spec]
  exact (D.lowerGapPortBranch g e).target.symm

theorem upperGapCorner_eq
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, e)) =
      ((D.centralOuterOrder.globalUpperOuterPath g (D.upperGapCornerParameter g e) :
        transportedTorus Phi) : R3) := by
  rw [D.upperGapCornerParameter_spec]
  exact (D.upperGapPortBranch g e).target.symm

theorem lowerGapCornerParameter_injective
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Function.Injective (D.lowerGapCornerParameter g) := by
  intro e f hef
  have hpoint : fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
      (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
        (Sum.inl g, e)) =
    fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
      (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
        (Sum.inl g, f)) := by
    rw [D.lowerGapCorner_eq g e, D.lowerGapCorner_eq g f, hef]
  have hvert := D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
    |>.fourPortChartPoint_injective hpoint
  have hpair :=
    (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder).injective hvert
  exact congrArg Prod.snd hpair

theorem upperGapCornerParameter_injective
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Function.Injective (D.upperGapCornerParameter g) := by
  intro e f hef
  have hpoint : fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
      (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
        (Sum.inr g, e)) =
    fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
      (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
        (Sum.inr g, f)) := by
    rw [D.upperGapCorner_eq g e, D.upperGapCorner_eq g f, hef]
  have hvert := D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
    |>.fourPortChartPoint_injective hpoint
  have hpair :=
    (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder).injective hvert
  exact congrArg Prod.snd hpair

private theorem subpath_injective_of_ne
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (hp : Function.Injective p) (s t : unitInterval) (hst : s ≠ t) :
    Function.Injective (p.subpath s t) := by
  intro u v huv
  have hparameter := hp huv
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  apply Subtype.ext
  have hgap : (t : ℝ) - s ≠ 0 := sub_ne_zero.mpr fun h ↦ hst (Subtype.ext h.symm)
  have hmul : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hgap)

private noncomputable def ambientLowerOuterPath
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :=
  (D.centralOuterOrder.globalLowerOuterPath g).map continuous_subtype_val

private noncomputable def ambientUpperOuterPath
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :=
  (D.centralOuterOrder.globalUpperOuterPath g).map continuous_subtype_val

/-- The middle lower outer subarc between its two four-port corners. -/
noncomputable def lowerTrimmedOuterPath
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Path
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, 0)))
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, 1))) :=
  ((D.ambientLowerOuterPath g).subpath
    (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1)).cast
      (D.lowerGapCorner_eq g 0) (D.lowerGapCorner_eq g 1)

/-- The middle upper outer subarc between its two four-port corners. -/
noncomputable def upperTrimmedOuterPath
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Path
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, 0)))
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, 1))) :=
  ((D.ambientUpperOuterPath g).subpath
    (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1)).cast
      (D.upperGapCorner_eq g 0) (D.upperGapCorner_eq g 1)

theorem lowerTrimmedOuterPath_injective
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Function.Injective (D.lowerTrimmedOuterPath g) := by
  change Function.Injective ((D.ambientLowerOuterPath g).subpath
    (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1))
  apply subpath_injective_of_ne (D.ambientLowerOuterPath g)
  · exact D.centralOuterOrder.globalLowerOuterPath_injective g
  · intro h
    have he := D.lowerGapCornerParameter_injective g h
    norm_num at he

theorem upperTrimmedOuterPath_injective
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Function.Injective (D.upperTrimmedOuterPath g) := by
  change Function.Injective ((D.ambientUpperOuterPath g).subpath
    (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1))
  apply subpath_injective_of_ne (D.ambientUpperOuterPath g)
  · exact D.centralOuterOrder.globalUpperOuterPath_injective g
  · intro h
    have he := D.upperGapCornerParameter_injective g h
    norm_num at he

theorem lowerTrimmedOuterPath_range_subset_gap
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Set.range (D.lowerTrimmedOuterPath g) ⊆
      Set.range (D.ambientLowerOuterPath g) := by
  rintro _ ⟨u, rfl⟩
  refine ⟨Icc.convexComb (D.lowerGapCornerParameter g 0)
    (D.lowerGapCornerParameter g 1) u, ?_⟩
  unfold lowerTrimmedOuterPath
  change _ = (D.ambientLowerOuterPath g).subpath
    (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1) u
  rfl

theorem upperTrimmedOuterPath_range_subset_gap
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Set.range (D.upperTrimmedOuterPath g) ⊆
      Set.range (D.ambientUpperOuterPath g) := by
  rintro _ ⟨u, rfl⟩
  refine ⟨Icc.convexComb (D.upperGapCornerParameter g 0)
    (D.upperGapCornerParameter g 1) u, ?_⟩
  unfold upperTrimmedOuterPath
  change _ = (D.ambientUpperOuterPath g).subpath
    (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1) u
  rfl

/-- The fixed middle outside path represented by one lower or upper outer edge. -/
noncomputable def canonicalBooleanOutsidePath
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    Path
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        ((booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointEquiv
          (e, 0)))
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        ((booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointEquiv
          (e, 1))) := by
  rcases e with g | g
  · exact D.lowerTrimmedOuterPath g
  · exact D.upperTrimmedOuterPath g

/-- Canonical fixed outside paths for all central four-port endpoints. -/
noncomputable def canonicalBooleanOutsideEndpointPaths :
    FiniteAlternatingEndpointSystem.EndpointPathFamily
      (booleanOutsidePairing D.centralOuterOrder D.centralCutOrder)
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart) where
  path := D.canonicalBooleanOutsidePath

theorem canonicalBooleanOutsidePath_injective
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    Function.Injective (D.canonicalBooleanOutsidePath e) := by
  rcases e with g | g
  · exact D.lowerTrimmedOuterPath_injective g
  · exact D.upperTrimmedOuterPath_injective g

theorem canonicalBooleanOutsidePath_range_subset_transportedTorus
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    Set.range (D.canonicalBooleanOutsidePath e) ⊆ transportedTorus Phi := by
  rcases e with g | g
  · intro x hx
    obtain ⟨u, hu⟩ := D.lowerTrimmedOuterPath_range_subset_gap g hx
    rw [← hu]
    exact (D.centralOuterOrder.globalLowerOuterPath g u).2
  · intro x hx
    obtain ⟨u, hu⟩ := D.upperTrimmedOuterPath_range_subset_gap g hx
    rw [← hu]
    exact (D.centralOuterOrder.globalUpperOuterPath g u).2

private theorem lowerPortBranch_target_height_lt
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    (D.lowerPortBranch b side 1).ofLp (frame 2) < S.cut.height := by
  fin_cases side
  · change ((D.centralHeightFlowStraightenedChartFamily.chart b).chart
      (standardLeftLowerBranchPath 1)).ofLp (frame 2) < S.cut.height
    rw [D.centralHeightFlowStraightenedChart_leftLowerBranch_apply]
    rw [unitInterval.symm_one, (D.centralLeftLowerHeightFlowBranchPath b).source]
    rw [D.canonicalBandMap_leftOuterArm_height]
    linarith [D.centralLowerConnectorTime_neg]
  · change ((D.centralHeightFlowStraightenedChartFamily.chart b).chart
      (standardRightLowerBranchPath (unitInterval.symm 1))).ofLp
        (frame 2) < S.cut.height
    rw [unitInterval.symm_one]
    rw [D.centralHeightFlowStraightenedChart_rightLowerBranch_apply]
    rw [(D.centralRightLowerHeightFlowBranchPath b).source]
    rw [D.canonicalBandMap_rightOuterArm_height]
    linarith [D.centralLowerConnectorTime_neg]

private theorem upperPortBranch_target_height_gt
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    S.cut.height < (D.upperPortBranch b side 1).ofLp (frame 2) := by
  fin_cases side
  · change S.cut.height <
      ((D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardLeftUpperBranchPath 1)).ofLp (frame 2)
    rw [D.centralHeightFlowStraightenedChart_leftUpperBranch_apply]
    rw [(D.centralLeftUpperHeightFlowBranchPath b).target]
    rw [D.canonicalBandMap_leftOuterArm_height]
    linarith [D.centralUpperConnectorTime_pos]
  · change S.cut.height <
      ((D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (standardRightUpperBranchPath (unitInterval.symm 1))).ofLp (frame 2)
    rw [unitInterval.symm_one]
    rw [D.centralHeightFlowStraightenedChart_rightUpperBranch_apply]
    rw [unitInterval.symm_zero, (D.centralRightUpperHeightFlowBranchPath b).target]
    rw [D.canonicalBandMap_rightOuterArm_height]
    linarith [D.centralUpperConnectorTime_pos]

private theorem lowerGapPortBranch_target_height_lt
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    (D.lowerGapPortBranch g e 1).ofLp (frame 2) < S.cut.height := by
  change (D.lowerPortBranch
    (seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalLowerEndpointEquiv (g, e))).1
    (seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalLowerEndpointEquiv (g, e))).2 1).ofLp
      (frame 2) < S.cut.height
  exact D.lowerPortBranch_target_height_lt _ _

private theorem upperGapPortBranch_target_height_gt
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    S.cut.height < (D.upperGapPortBranch g e 1).ofLp (frame 2) := by
  change S.cut.height < (D.upperPortBranch
    (seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalUpperEndpointEquiv (g, e))).1
    (seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalUpperEndpointEquiv (g, e))).2 1).ofLp (frame 2)
  exact D.upperPortBranch_target_height_gt _ _

theorem lowerGapCornerParameter_ne_zero
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    D.lowerGapCornerParameter g e ≠ 0 := by
  intro hzero
  have hcorner := D.lowerGapCornerParameter_spec g e
  rw [hzero] at hcorner
  have hseam := D.centralOuterOrder.gapPath_endpoint_mem_seam
    (D.centralOuterOrder.lowerGapAsGlobalOuterGap g) 0
  have htargetSeam : D.lowerGapPortBranch g e 1 ∈
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
    have hseam' :
        ((D.centralOuterOrder.globalLowerOuterPath g 0 : transportedTorus Phi) : R3) ∈
          superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
      simpa only [globalLowerOuterPath,
        OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero] using hseam
    exact hcorner ▸ hseam'
  have hheight : (D.lowerGapPortBranch g e 1).ofLp (frame 2) = S.cut.height :=
    htargetSeam.2
  linarith [D.lowerGapPortBranch_target_height_lt g e]

theorem lowerGapCornerParameter_ne_one
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    D.lowerGapCornerParameter g e ≠ 1 := by
  intro hone
  have hcorner := D.lowerGapCornerParameter_spec g e
  rw [hone] at hcorner
  have hseam := D.centralOuterOrder.gapPath_endpoint_mem_seam
    (D.centralOuterOrder.lowerGapAsGlobalOuterGap g) 1
  have htargetSeam : D.lowerGapPortBranch g e 1 ∈
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
    have hseam' :
        ((D.centralOuterOrder.globalLowerOuterPath g 1 : transportedTorus Phi) : R3) ∈
          superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
      simpa only [globalLowerOuterPath,
        OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one] using hseam
    exact hcorner ▸ hseam'
  have hheight : (D.lowerGapPortBranch g e 1).ofLp (frame 2) = S.cut.height :=
    htargetSeam.2
  linarith [D.lowerGapPortBranch_target_height_lt g e]

theorem upperGapCornerParameter_ne_zero
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    D.upperGapCornerParameter g e ≠ 0 := by
  intro hzero
  have hcorner := D.upperGapCornerParameter_spec g e
  rw [hzero] at hcorner
  have hseam := D.centralOuterOrder.gapPath_endpoint_mem_seam
    (D.centralOuterOrder.upperGapAsGlobalOuterGap g) 0
  have htargetSeam : D.upperGapPortBranch g e 1 ∈
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
    have hseam' :
        ((D.centralOuterOrder.globalUpperOuterPath g 0 : transportedTorus Phi) : R3) ∈
          superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
      simpa only [globalUpperOuterPath,
        OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero] using hseam
    exact hcorner ▸ hseam'
  have hheight : (D.upperGapPortBranch g e 1).ofLp (frame 2) = S.cut.height :=
    htargetSeam.2
  linarith [D.upperGapPortBranch_target_height_gt g e]

theorem upperGapCornerParameter_ne_one
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    D.upperGapCornerParameter g e ≠ 1 := by
  intro hone
  have hcorner := D.upperGapCornerParameter_spec g e
  rw [hone] at hcorner
  have hseam := D.centralOuterOrder.gapPath_endpoint_mem_seam
    (D.centralOuterOrder.upperGapAsGlobalOuterGap g) 1
  have htargetSeam : D.upperGapPortBranch g e 1 ∈
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
    have hseam' :
        ((D.centralOuterOrder.globalUpperOuterPath g 1 : transportedTorus Phi) : R3) ∈
          superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
      simpa only [globalUpperOuterPath,
        OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one] using hseam
    exact hcorner ▸ hseam'
  have hheight : (D.upperGapPortBranch g e 1).ofLp (frame 2) = S.cut.height :=
    htargetSeam.2
  linarith [D.upperGapPortBranch_target_height_gt g e]

private theorem convexComb_mem_Ioo_of_ne_endpoints
    (x y u : unitInterval) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    ((Icc.convexComb x y u : unitInterval) : ℝ) ∈ Set.Ioo 0 1 := by
  have hx0' : (0 : ℝ) < x := by
    apply lt_of_le_of_ne x.2.1
    exact fun h ↦ hx0 (Subtype.ext h.symm)
  have hx1' : (x : ℝ) < 1 := by
    apply lt_of_le_of_ne x.2.2
    exact fun h ↦ hx1 (Subtype.ext h)
  have hy0' : (0 : ℝ) < y := by
    apply lt_of_le_of_ne y.2.1
    exact fun h ↦ hy0 (Subtype.ext h.symm)
  have hy1' : (y : ℝ) < 1 := by
    apply lt_of_le_of_ne y.2.2
    exact fun h ↦ hy1 (Subtype.ext h)
  rw [Icc.coe_convexComb]
  constructor
  · by_cases hu0 : (u : ℝ) = 0
    · simpa only [hu0, sub_zero, mul_zero, zero_mul, add_zero, one_mul] using hx0'
    · have hut : (0 : ℝ) < u := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr u.2.2) hx0'.le) (mul_pos hut hy0')
  · by_cases hu1 : (u : ℝ) = 1
    · simpa only [hu1, sub_self, zero_mul, one_mul, zero_add] using hy1'
    · have hut : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu1
      have hleft : 0 < (1 - (u : ℝ)) * (1 - (x : ℝ)) :=
        mul_pos (sub_pos.mpr hut) (sub_pos.mpr hx1')
      have hright : 0 ≤ (u : ℝ) * (1 - (y : ℝ)) :=
        mul_nonneg u.2.1 (sub_nonneg.mpr hy1'.le)
      nlinarith

private theorem lowerTrimmedOuterPath_parameter_mem_Ioo
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (u : unitInterval) :
    ((Icc.convexComb (D.lowerGapCornerParameter g 0)
      (D.lowerGapCornerParameter g 1) u : unitInterval) : ℝ) ∈ Set.Ioo 0 1 :=
  convexComb_mem_Ioo_of_ne_endpoints _ _ _
    (D.lowerGapCornerParameter_ne_zero g 0)
    (D.lowerGapCornerParameter_ne_one g 0)
    (D.lowerGapCornerParameter_ne_zero g 1)
    (D.lowerGapCornerParameter_ne_one g 1)

private theorem upperTrimmedOuterPath_parameter_mem_Ioo
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (u : unitInterval) :
    ((Icc.convexComb (D.upperGapCornerParameter g 0)
      (D.upperGapCornerParameter g 1) u : unitInterval) : ℝ) ∈ Set.Ioo 0 1 :=
  convexComb_mem_Ioo_of_ne_endpoints _ _ _
    (D.upperGapCornerParameter_ne_zero g 0)
    (D.upperGapCornerParameter_ne_one g 0)
    (D.upperGapCornerParameter_ne_zero g 1)
    (D.upperGapCornerParameter_ne_one g 1)

theorem lowerTrimmedOuterPath_not_mem_seam
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (u : unitInterval) :
    D.lowerTrimmedOuterPath g u ∉
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
  let q := Icc.convexComb (D.lowerGapCornerParameter g 0)
    (D.lowerGapCornerParameter g 1) u
  have hq := D.lowerTrimmedOuterPath_parameter_mem_Ioo g u
  have hnot := D.centralOuterOrder.gapPath_interior_not_mem_seam
    (D.centralOuterOrder.lowerGapAsGlobalOuterGap g) q hq.1.ne' hq.2.ne
  change ((D.centralOuterOrder.globalLowerOuterPath g q : transportedTorus Phi) : R3) ∉
    superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height at hnot
  change ((D.centralOuterOrder.globalLowerOuterPath g q : transportedTorus Phi) : R3) ∉
    superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height
  exact hnot

theorem upperTrimmedOuterPath_not_mem_seam
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (u : unitInterval) :
    D.upperTrimmedOuterPath g u ∉
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
  let q := Icc.convexComb (D.upperGapCornerParameter g 0)
    (D.upperGapCornerParameter g 1) u
  have hq := D.upperTrimmedOuterPath_parameter_mem_Ioo g u
  have hnot := D.centralOuterOrder.gapPath_interior_not_mem_seam
    (D.centralOuterOrder.upperGapAsGlobalOuterGap g) q hq.1.ne' hq.2.ne
  change ((D.centralOuterOrder.globalUpperOuterPath g q : transportedTorus Phi) : R3) ∉
    superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height at hnot
  change ((D.centralOuterOrder.globalUpperOuterPath g q : transportedTorus Phi) : R3) ∉
    superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height
  exact hnot

theorem lowerTrimmedOuterPath_ranges_pairwise_disjoint :
    Pairwise fun g h : D.centralOuterOrder.GlobalLowerOuterGap ↦
      Disjoint (Set.range (D.lowerTrimmedOuterPath g))
        (Set.range (D.lowerTrimmedOuterPath h)) := by
  intro g h hgh
  exact (D.centralOuterOrder.globalLowerOuterPath_ranges_pairwise_disjoint hgh).mono
    (D.lowerTrimmedOuterPath_range_subset_gap g)
    (D.lowerTrimmedOuterPath_range_subset_gap h)

theorem upperTrimmedOuterPath_ranges_pairwise_disjoint :
    Pairwise fun g h : D.centralOuterOrder.GlobalUpperOuterGap ↦
      Disjoint (Set.range (D.upperTrimmedOuterPath g))
        (Set.range (D.upperTrimmedOuterPath h)) := by
  intro g h hgh
  exact (D.centralOuterOrder.globalUpperOuterPath_ranges_pairwise_disjoint hgh).mono
    (D.upperTrimmedOuterPath_range_subset_gap g)
    (D.upperTrimmedOuterPath_range_subset_gap h)

theorem lowerTrimmedOuterPath_disjoint_upperTrimmedOuterPath
    (g : D.centralOuterOrder.GlobalLowerOuterGap)
    (h : D.centralOuterOrder.GlobalUpperOuterGap) :
    Disjoint (Set.range (D.lowerTrimmedOuterPath g))
      (Set.range (D.upperTrimmedOuterPath h)) := by
  rw [Set.disjoint_left]
  intro x hxLower hxUpper
  have hxLowerGap := D.lowerTrimmedOuterPath_range_subset_gap g hxLower
  have hxUpperGap := D.upperTrimmedOuterPath_range_subset_gap h hxUpper
  obtain ⟨u, hu⟩ := hxLower
  obtain ⟨q, hq⟩ := hxLowerGap
  obtain ⟨v, hv⟩ := hxUpperGap
  have hxLowerHalf : x ∈ lowerClosedHalfspace frame S.cut.height := by
    have hmem := D.centralOuterOrder.lowerGapPath_mem
      (D.centralOuterOrder.lowerGapAsLowerGap g) q
    exact hq ▸ hmem
  have hxUpperHalf : x ∈ upperClosedHalfspace frame S.cut.height := by
    have hmem := D.centralOuterOrder.upperGapPath_mem
      (D.centralOuterOrder.upperGapAsUpperGap h) v
    exact hv ▸ hmem
  have hxPlane : x.ofLp (frame 2) = S.cut.height :=
    le_antisymm hxLowerHalf hxUpperHalf
  have hxOuter := D.centralOuterOrder.gapPath_mem_outerCircle
    (D.centralOuterOrder.lowerGapAsGlobalOuterGap g) q
  have hxOuter' : x ∈ Set.range (D.centralGraph.outer.circle g.1.1).circle :=
    hq ▸ hxOuter
  have hxSection := D.centralGraph.outer.circle_mem_section g.1.1 hxOuter'
  have hxSeam : x ∈
      superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height := by
    exact ⟨⟨hxSection.1, hxSection.2⟩, hxPlane⟩
  exact D.lowerTrimmedOuterPath_not_mem_seam g u (hu.symm ▸ hxSeam)

theorem canonicalBooleanOutsidePath_ranges_pairwise_disjoint :
    Pairwise fun e f : BooleanOutsideEdge D.centralOuterOrder ↦
      Disjoint (Set.range (D.canonicalBooleanOutsidePath e))
        (Set.range (D.canonicalBooleanOutsidePath f)) := by
  rintro (g | g) (h | h) hne
  · exact D.lowerTrimmedOuterPath_ranges_pairwise_disjoint
      (fun hgh ↦ hne (congrArg Sum.inl hgh))
  · exact D.lowerTrimmedOuterPath_disjoint_upperTrimmedOuterPath g h
  · exact (D.lowerTrimmedOuterPath_disjoint_upperTrimmedOuterPath h g).symm
  · exact D.upperTrimmedOuterPath_ranges_pairwise_disjoint
      (fun hgh ↦ hne (congrArg Sum.inr hgh))

private theorem range_eq_subpath_zero_of_range_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b : X}
    (p : Path a b) (hp : Function.Injective p) (c : unitInterval)
    (q : Path (p 0) (p c)) (hq : Function.Injective q)
    (hsub : Set.range q ⊆ Set.range p) :
    Set.range q = Set.range (p.subpath 0 c) := by
  let E : unitInterval ≃ₜ Set.range p :=
    (p.continuous.isClosedEmbedding hp).isEmbedding.toHomeomorph
  let s : unitInterval → unitInterval := fun u ↦
    E.symm ⟨q u, hsub ⟨u, rfl⟩⟩
  have hs_apply (u : unitInterval) : p (s u) = q u := by
    change (E (E.symm ⟨q u, hsub ⟨u, rfl⟩⟩)).1 = q u
    rw [E.apply_symm_apply]
  have hs_continuous : Continuous s := by
    apply E.symm.continuous.comp
    exact continuous_induced_rng.mpr q.continuous
  have hs_injective : Function.Injective s := by
    intro u v huv
    apply hq
    rw [← hs_apply u, ← hs_apply v, huv]
  have hs_zero : s 0 = 0 := by
    apply hp
    rw [hs_apply, q.source, p.source]
  have hs_one : s 1 = c := by
    apply hp
    rw [hs_apply, q.target]
  have hs_mono : StrictMono s := by
    rcases hs_continuous.strictMono_of_inj_boundedOrder' hs_injective with hmono | hanti
    · exact hmono
    · exfalso
      have hbad := hanti (show (0 : unitInterval) < 1 by norm_num)
      rw [hs_zero] at hbad
      exact (not_lt_of_ge (show (0 : unitInterval) ≤ s 1 from bot_le)) hbad
  rw [Path.range_subpath_of_le p 0 c bot_le]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨s u, ⟨?_, ?_⟩, hs_apply u⟩
    · rw [← hs_zero]
      exact hs_mono.monotone bot_le
    · rw [← hs_one]
      exact hs_mono.monotone le_top
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc (s 0) (s 1) := by simpa only [hs_zero, hs_one]
    obtain ⟨u, _hu, hut⟩ :=
      intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
        hs_continuous.continuousOn ht'
    exact ⟨u, by rw [← hs_apply u, hut]⟩

private theorem range_eq_subpath_one_of_range_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b : X}
    (p : Path a b) (hp : Function.Injective p) (c : unitInterval)
    (q : Path (p 1) (p c)) (hq : Function.Injective q)
    (hsub : Set.range q ⊆ Set.range p) :
    Set.range q = Set.range (p.subpath 1 c) := by
  let E : unitInterval ≃ₜ Set.range p :=
    (p.continuous.isClosedEmbedding hp).isEmbedding.toHomeomorph
  let s : unitInterval → unitInterval := fun u ↦
    E.symm ⟨q u, hsub ⟨u, rfl⟩⟩
  have hs_apply (u : unitInterval) : p (s u) = q u := by
    change (E (E.symm ⟨q u, hsub ⟨u, rfl⟩⟩)).1 = q u
    rw [E.apply_symm_apply]
  have hs_continuous : Continuous s := by
    apply E.symm.continuous.comp
    exact continuous_induced_rng.mpr q.continuous
  have hs_injective : Function.Injective s := by
    intro u v huv
    apply hq
    rw [← hs_apply u, ← hs_apply v, huv]
  have hs_zero : s 0 = 1 := by
    apply hp
    rw [hs_apply, q.source, p.target]
  have hs_one : s 1 = c := by
    apply hp
    rw [hs_apply, q.target]
  have hs_anti : StrictAnti s := by
    rcases hs_continuous.strictMono_of_inj_boundedOrder' hs_injective with hmono | hanti
    · exfalso
      have hbad := hmono (show (0 : unitInterval) < 1 by norm_num)
      rw [hs_zero] at hbad
      exact (not_lt_of_ge (show s 1 ≤ (1 : unitInterval) from le_top)) hbad
    · exact hanti
  rw [Path.range_subpath_of_ge p 1 c le_top]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨s u, ⟨?_, ?_⟩, hs_apply u⟩
    · rw [← hs_one]
      exact hs_anti.antitone le_top
    · rw [← hs_zero]
      exact hs_anti.antitone bot_le
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc (s 1) (s 0) := by simpa only [hs_zero, hs_one]
    obtain ⟨u, _hu, hut⟩ :=
      intermediate_value_Icc' (show (0 : unitInterval) ≤ 1 from bot_le)
        hs_continuous.continuousOn ht'
    exact ⟨u, by rw [← hs_apply u, hut]⟩

private noncomputable def lowerGapPortBranchOnGap
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Path (D.ambientLowerOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e))
      (D.ambientLowerOuterPath g (D.lowerGapCornerParameter g e)) :=
  (D.lowerGapPortBranch g e).cast
    (D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g e).symm
    (D.lowerGapCorner_eq g e).symm

private noncomputable def upperGapPortBranchOnGap
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Path (D.ambientUpperOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e))
      (D.ambientUpperOuterPath g (D.upperGapCornerParameter g e)) :=
  (D.upperGapPortBranch g e).cast
    (D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g e).symm
    (D.upperGapCorner_eq g e).symm

private theorem range_lowerGapPortBranchOnGap
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerGapPortBranchOnGap g e) =
      Set.range (D.lowerGapPortBranch g e) := by
  exact congrArg Set.range <|
    Path.cast_coe (D.lowerGapPortBranch g e)
      (D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g e).symm
      (D.lowerGapCorner_eq g e).symm

private theorem range_upperGapPortBranchOnGap
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperGapPortBranchOnGap g e) =
      Set.range (D.upperGapPortBranch g e) := by
  exact congrArg Set.range <|
    Path.cast_coe (D.upperGapPortBranch g e)
      (D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g e).symm
      (D.upperGapCorner_eq g e).symm

private theorem range_lowerGapPortBranch_zero_eq_subpath
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Set.range (D.lowerGapPortBranch g 0) =
      Set.range ((D.ambientLowerOuterPath g).subpath 0
        (D.lowerGapCornerParameter g 0)) := by
  have hp : Function.Injective (D.ambientLowerOuterPath g) := by
    intro u v huv
    exact D.centralOuterOrder.globalLowerOuterPath_injective g huv
  have hsource : D.ambientLowerOuterPath g 0 =
      (D.centralOuterOrder.globalLowerEndpointEquiv (g, 0)).1 := by
    change ((D.centralOuterOrder.globalLowerOuterPath g 0 : transportedTorus Phi) : R3) = _
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero]
      using (D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g 0).symm
  have htarget : D.ambientLowerOuterPath g (D.lowerGapCornerParameter g 0) =
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, 0)) := (D.lowerGapCorner_eq g 0).symm
  let q : Path (D.ambientLowerOuterPath g 0)
      (D.ambientLowerOuterPath g (D.lowerGapCornerParameter g 0)) :=
    (D.lowerGapPortBranch g 0).cast hsource htarget
  have hqCoe : (q : unitInterval → R3) = D.lowerGapPortBranch g 0 := Path.cast_coe _ _ _
  have hqInj : Function.Injective q := by
    rw [hqCoe]
    exact seamToFourPortCornerPath_injective D.centralCutOrder
      D.centralHeightFlowStraightenedChartFamily _ _
  have hqSub : Set.range q ⊆ Set.range (D.ambientLowerOuterPath g) := by
    rw [hqCoe]
    exact D.lowerGapPortBranch_range_subset_gap g 0
  have hresult := range_eq_subpath_zero_of_range_subset
    (D.ambientLowerOuterPath g) hp (D.lowerGapCornerParameter g 0) q hqInj hqSub
  rwa [hqCoe] at hresult

private theorem range_lowerGapPortBranch_one_eq_subpath
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Set.range (D.lowerGapPortBranch g 1) =
      Set.range ((D.ambientLowerOuterPath g).subpath 1
        (D.lowerGapCornerParameter g 1)) := by
  have hp : Function.Injective (D.ambientLowerOuterPath g) := by
    intro u v huv
    exact D.centralOuterOrder.globalLowerOuterPath_injective g huv
  have hsource : D.ambientLowerOuterPath g 1 =
      (D.centralOuterOrder.globalLowerEndpointEquiv (g, 1)).1 := by
    change ((D.centralOuterOrder.globalLowerOuterPath g 1 : transportedTorus Phi) : R3) = _
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one]
      using (D.centralOuterOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g 1).symm
  have htarget : D.ambientLowerOuterPath g (D.lowerGapCornerParameter g 1) =
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, 1)) := (D.lowerGapCorner_eq g 1).symm
  let q : Path (D.ambientLowerOuterPath g 1)
      (D.ambientLowerOuterPath g (D.lowerGapCornerParameter g 1)) :=
    (D.lowerGapPortBranch g 1).cast hsource htarget
  have hqCoe : (q : unitInterval → R3) = D.lowerGapPortBranch g 1 := Path.cast_coe _ _ _
  have hqInj : Function.Injective q := by
    rw [hqCoe]
    exact seamToFourPortCornerPath_injective D.centralCutOrder
      D.centralHeightFlowStraightenedChartFamily _ _
  have hqSub : Set.range q ⊆ Set.range (D.ambientLowerOuterPath g) := by
    rw [hqCoe]
    exact D.lowerGapPortBranch_range_subset_gap g 1
  have hresult := range_eq_subpath_one_of_range_subset
    (D.ambientLowerOuterPath g) hp (D.lowerGapCornerParameter g 1) q hqInj hqSub
  rwa [hqCoe] at hresult

theorem range_lowerGapPortBranch_eq_subpath
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerGapPortBranch g e) =
      Set.range ((D.ambientLowerOuterPath g).subpath
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e)
        (D.lowerGapCornerParameter g e)) := by
  refine Fin.cases ?_ (fun e ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) e) e
  · rw [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero]
    exact D.range_lowerGapPortBranch_zero_eq_subpath g
  · rw [show (Fin.succ 0 : Fin 2) = 1 from rfl,
      OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one]
    exact D.range_lowerGapPortBranch_one_eq_subpath g

private theorem range_upperGapPortBranch_zero_eq_subpath
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Set.range (D.upperGapPortBranch g 0) =
      Set.range ((D.ambientUpperOuterPath g).subpath 0
        (D.upperGapCornerParameter g 0)) := by
  have hp : Function.Injective (D.ambientUpperOuterPath g) := by
    intro u v huv
    exact D.centralOuterOrder.globalUpperOuterPath_injective g huv
  have hsource : D.ambientUpperOuterPath g 0 =
      (D.centralOuterOrder.globalUpperEndpointEquiv (g, 0)).1 := by
    change ((D.centralOuterOrder.globalUpperOuterPath g 0 : transportedTorus Phi) : R3) = _
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero]
      using (D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g 0).symm
  have htarget : D.ambientUpperOuterPath g (D.upperGapCornerParameter g 0) =
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, 0)) := (D.upperGapCorner_eq g 0).symm
  let q : Path (D.ambientUpperOuterPath g 0)
      (D.ambientUpperOuterPath g (D.upperGapCornerParameter g 0)) :=
    (D.upperGapPortBranch g 0).cast hsource htarget
  have hqCoe : (q : unitInterval → R3) = D.upperGapPortBranch g 0 := Path.cast_coe _ _ _
  have hqInj : Function.Injective q := by
    rw [hqCoe]
    exact seamToFourPortCornerPath_injective D.centralCutOrder
      D.centralHeightFlowStraightenedChartFamily _ _
  have hqSub : Set.range q ⊆ Set.range (D.ambientUpperOuterPath g) := by
    rw [hqCoe]
    exact D.upperGapPortBranch_range_subset_gap g 0
  have hresult := range_eq_subpath_zero_of_range_subset
    (D.ambientUpperOuterPath g) hp (D.upperGapCornerParameter g 0) q hqInj hqSub
  rwa [hqCoe] at hresult

private theorem range_upperGapPortBranch_one_eq_subpath
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Set.range (D.upperGapPortBranch g 1) =
      Set.range ((D.ambientUpperOuterPath g).subpath 1
        (D.upperGapCornerParameter g 1)) := by
  have hp : Function.Injective (D.ambientUpperOuterPath g) := by
    intro u v huv
    exact D.centralOuterOrder.globalUpperOuterPath_injective g huv
  have hsource : D.ambientUpperOuterPath g 1 =
      (D.centralOuterOrder.globalUpperEndpointEquiv (g, 1)).1 := by
    change ((D.centralOuterOrder.globalUpperOuterPath g 1 : transportedTorus Phi) : R3) = _
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one]
      using (D.centralOuterOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g 1).symm
  have htarget : D.ambientUpperOuterPath g (D.upperGapCornerParameter g 1) =
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, 1)) := (D.upperGapCorner_eq g 1).symm
  let q : Path (D.ambientUpperOuterPath g 1)
      (D.ambientUpperOuterPath g (D.upperGapCornerParameter g 1)) :=
    (D.upperGapPortBranch g 1).cast hsource htarget
  have hqCoe : (q : unitInterval → R3) = D.upperGapPortBranch g 1 := Path.cast_coe _ _ _
  have hqInj : Function.Injective q := by
    rw [hqCoe]
    exact seamToFourPortCornerPath_injective D.centralCutOrder
      D.centralHeightFlowStraightenedChartFamily _ _
  have hqSub : Set.range q ⊆ Set.range (D.ambientUpperOuterPath g) := by
    rw [hqCoe]
    exact D.upperGapPortBranch_range_subset_gap g 1
  have hresult := range_eq_subpath_one_of_range_subset
    (D.ambientUpperOuterPath g) hp (D.upperGapCornerParameter g 1) q hqInj hqSub
  rwa [hqCoe] at hresult

theorem range_upperGapPortBranch_eq_subpath
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperGapPortBranch g e) =
      Set.range ((D.ambientUpperOuterPath g).subpath
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e)
        (D.upperGapCornerParameter g e)) := by
  refine Fin.cases ?_ (fun e ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) e) e
  · rw [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero]
    exact D.range_upperGapPortBranch_zero_eq_subpath g
  · rw [show (Fin.succ 0 : Fin 2) = 1 from rfl,
      OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one]
    exact D.range_upperGapPortBranch_one_eq_subpath g

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
