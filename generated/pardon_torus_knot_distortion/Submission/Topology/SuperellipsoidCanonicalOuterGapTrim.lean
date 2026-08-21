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

noncomputable def lowerPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :=
  seamToCornerPathOfBandSide D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily b side 0

noncomputable def upperPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :=
  seamToCornerPathOfBandSide D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily b side 1

theorem leftPath_range_eq_portBranches
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath =
      Set.range (D.lowerPortBranch b 0) ∪ Set.range (D.upperPortBranch b 0) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hu : bandLeftPath u ∈
        Set.range standardLeftLowerBranchPath ∪
          Set.range standardLeftUpperBranchPath := by
      rw [← range_bandLeftPath_eq_standardHalves]
      exact ⟨u, rfl⟩
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact Or.inl ⟨v,
        congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
    · exact Or.inr ⟨v,
        congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · have hu : standardLeftLowerBranchPath u ∈ Set.range bandLeftPath := by
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inl ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
    · have hu : standardLeftUpperBranchPath u ∈ Set.range bandLeftPath := by
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inr ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

theorem rightPath_range_eq_portBranches
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).rightPath =
      Set.range (D.lowerPortBranch b 1) ∪ Set.range (D.upperPortBranch b 1) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hu : bandRightPath u ∈
        Set.range standardRightLowerBranchPath ∪
          Set.range standardRightUpperBranchPath := by
      rw [← range_bandRightPath_eq_standardHalves]
      exact ⟨u, rfl⟩
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact Or.inl ⟨unitInterval.symm v, by
        change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
            (standardRightLowerBranchPath (unitInterval.symm (unitInterval.symm v))) = _
        rw [unitInterval.symm_symm]
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
    · exact Or.inr ⟨unitInterval.symm v, by
        change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
            (standardRightUpperBranchPath (unitInterval.symm (unitInterval.symm v))) = _
        rw [unitInterval.symm_symm]
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · have hu : standardRightLowerBranchPath (unitInterval.symm u) ∈
          Set.range bandRightPath := by
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inl ⟨unitInterval.symm u, rfl⟩
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩
    · have hu : standardRightUpperBranchPath (unitInterval.symm u) ∈
          Set.range bandRightPath := by
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inr ⟨unitInterval.symm u, rfl⟩
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

/-- At the all-false resolution, one local edge is exactly the two incident outer port
branches. -/
theorem range_booleanFourPortLocalPath_false_eq_portBranches
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path (b, side)) =
      Set.range (D.lowerPortBranch b side) ∪ Set.range (D.upperPortBranch b side) := by
  refine Fin.cases ?_ (fun side : Fin 1 ↦
    Fin.cases ?_ (fun z : Fin 0 ↦ Fin.elim0 z) side) side
  · change Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path
          (b, (0 : Fin 2))) =
      Set.range (D.lowerPortBranch b 0) ∪ Set.range (D.upperPortBranch b 0)
    change Set.range (booleanFourPortLocalPath
      D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false) (b, 0)) = _
    simpa only [booleanFourPortLocalPath, Bool.false_eq_true, ↓reduceDIte,
      Fin.cases_zero, Path.cast_coe] using D.leftPath_range_eq_portBranches b
  · change Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path
          (b, Fin.succ 0)) =
      Set.range (D.lowerPortBranch b (Fin.succ 0)) ∪
        Set.range (D.upperPortBranch b (Fin.succ 0))
    change Set.range (booleanFourPortLocalPath
      D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)
        (b, Fin.succ 0)) = _
    unfold booleanFourPortLocalPath
    simp only
    rw [dif_neg (by simp)]
    simp only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe]
    exact D.rightPath_range_eq_portBranches b

private theorem lowerPortBranch_zero_range_subset_leftPath
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.lowerPortBranch b 0) ⊆
      Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath := by
  rintro _ ⟨u, rfl⟩
  change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
    (standardLeftLowerBranchPath u) ∈ _
  have hz : standardLeftLowerBranchPath u ∈ Set.range bandLeftPath := by
    rw [range_bandLeftPath_eq_standardHalves]
    exact Or.inl ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

private theorem lowerPortBranch_one_range_subset_rightPath
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.lowerPortBranch b 1) ⊆
      Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).rightPath := by
  rintro _ ⟨u, rfl⟩
  change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
    (standardRightLowerBranchPath (unitInterval.symm u)) ∈ _
  have hz : standardRightLowerBranchPath (unitInterval.symm u) ∈
      Set.range bandRightPath := by
    rw [range_bandRightPath_eq_standardHalves]
    exact Or.inl ⟨unitInterval.symm u, rfl⟩
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

private theorem upperPortBranch_zero_range_subset_leftPath
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.upperPortBranch b 0) ⊆
      Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath := by
  rintro _ ⟨u, rfl⟩
  change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
    (standardLeftUpperBranchPath u) ∈ _
  have hz : standardLeftUpperBranchPath u ∈ Set.range bandLeftPath := by
    rw [range_bandLeftPath_eq_standardHalves]
    exact Or.inr ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

private theorem upperPortBranch_one_range_subset_rightPath
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.upperPortBranch b 1) ⊆
      Set.range (D.centralHeightFlowStraightenedChartFamily.chart b).rightPath := by
  rintro _ ⟨u, rfl⟩
  change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
    (standardRightUpperBranchPath (unitInterval.symm u)) ∈ _
  have hz : standardRightUpperBranchPath (unitInterval.symm u) ∈
      Set.range bandRightPath := by
    rw [range_bandRightPath_eq_standardHalves]
    exact Or.inr ⟨unitInterval.symm u, rfl⟩
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv⟩

private theorem lowerPortBranch_ranges_pairwise_disjoint :
    Pairwise fun p q :
        Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount × Fin 2 ↦
      Disjoint (Set.range (D.lowerPortBranch p.1 p.2))
        (Set.range (D.lowerPortBranch q.1 q.2)) := by
  rintro ⟨b, side⟩ ⟨b', side'⟩ hne
  by_cases hbb' : b = b'
  · subst b'
    have hside : side ≠ side' := fun h ↦ hne (Prod.ext rfl h)
    fin_cases side <;> fin_cases side'
    · exact (hside rfl).elim
    · exact (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath_disjoint_rightPath
        |>.mono (D.lowerPortBranch_zero_range_subset_leftPath b)
          (D.lowerPortBranch_one_range_subset_rightPath b)
    · exact (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath_disjoint_rightPath.symm
        |>.mono (D.lowerPortBranch_one_range_subset_rightPath b)
          (D.lowerPortBranch_zero_range_subset_leftPath b)
    · exact (hside rfl).elim
  · exact (D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
        |>.support_pairwise hbb').mono
      (seamToCornerPathOfBandSide_range_subset_support D.centralCutOrder
        D.centralHeightFlowStraightenedChartFamily b side 0)
      (seamToCornerPathOfBandSide_range_subset_support D.centralCutOrder
        D.centralHeightFlowStraightenedChartFamily b' side' 0)

private theorem upperPortBranch_ranges_pairwise_disjoint :
    Pairwise fun p q :
        Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount × Fin 2 ↦
      Disjoint (Set.range (D.upperPortBranch p.1 p.2))
        (Set.range (D.upperPortBranch q.1 q.2)) := by
  rintro ⟨b, side⟩ ⟨b', side'⟩ hne
  by_cases hbb' : b = b'
  · subst b'
    have hside : side ≠ side' := fun h ↦ hne (Prod.ext rfl h)
    fin_cases side <;> fin_cases side'
    · exact (hside rfl).elim
    · exact (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath_disjoint_rightPath
        |>.mono (D.upperPortBranch_zero_range_subset_leftPath b)
          (D.upperPortBranch_one_range_subset_rightPath b)
    · exact (D.centralHeightFlowStraightenedChartFamily.chart b).leftPath_disjoint_rightPath.symm
        |>.mono (D.upperPortBranch_one_range_subset_rightPath b)
          (D.upperPortBranch_zero_range_subset_leftPath b)
    · exact (hside rfl).elim
  · exact (D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
        |>.support_pairwise hbb').mono
      (seamToCornerPathOfBandSide_range_subset_support D.centralCutOrder
        D.centralHeightFlowStraightenedChartFamily b side 1)
      (seamToCornerPathOfBandSide_range_subset_support D.centralCutOrder
        D.centralHeightFlowStraightenedChartFamily b' side' 1)

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

theorem lowerTrimmedOuterPath_height_lt
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (u : unitInterval) :
    (D.lowerTrimmedOuterPath g u).ofLp (frame 2) < S.cut.height := by
  obtain ⟨q, hq⟩ := D.lowerTrimmedOuterPath_range_subset_gap g ⟨u, rfl⟩
  have hle := D.centralOuterOrder.lowerGapPath_mem
    (D.centralOuterOrder.lowerGapAsLowerGap g) q
  have houter := D.centralOuterOrder.gapPath_mem_outerCircle
    (D.centralOuterOrder.lowerGapAsGlobalOuterGap g) q
  have hsection := D.centralGraph.outer.circle_mem_section g.1.1 houter
  have hne : (D.lowerTrimmedOuterPath g u).ofLp (frame 2) ≠ S.cut.height := by
    intro heq
    apply D.lowerTrimmedOuterPath_not_mem_seam g u
    exact ⟨⟨hq ▸ hsection.1, hq ▸ hsection.2⟩, heq⟩
  have hle' : (D.lowerTrimmedOuterPath g u).ofLp (frame 2) ≤ S.cut.height :=
    hq ▸ hle
  exact lt_of_le_of_ne hle' hne

theorem upperTrimmedOuterPath_height_gt
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (u : unitInterval) :
    S.cut.height < (D.upperTrimmedOuterPath g u).ofLp (frame 2) := by
  obtain ⟨q, hq⟩ := D.upperTrimmedOuterPath_range_subset_gap g ⟨u, rfl⟩
  have hge := D.centralOuterOrder.upperGapPath_mem
    (D.centralOuterOrder.upperGapAsUpperGap g) q
  have houter := D.centralOuterOrder.gapPath_mem_outerCircle
    (D.centralOuterOrder.upperGapAsGlobalOuterGap g) q
  have hsection := D.centralGraph.outer.circle_mem_section g.1.1 houter
  have hne : S.cut.height ≠ (D.upperTrimmedOuterPath g u).ofLp (frame 2) := by
    intro heq
    apply D.upperTrimmedOuterPath_not_mem_seam g u
    exact ⟨⟨hq ▸ hsection.1, hq ▸ hsection.2⟩, heq.symm⟩
  have hge' : S.cut.height ≤ (D.upperTrimmedOuterPath g u).ofLp (frame 2) :=
    hq ▸ hge
  exact lt_of_le_of_ne hge' hne

private theorem lowerTrimmedOuterPath_mem_support_exists_port
    (g : D.centralOuterOrder.GlobalLowerOuterGap)
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    {x : R3} (hx : x ∈ Set.range (D.lowerTrimmedOuterPath g))
    (hxs : x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).support) :
    ∃ side : Fin 2, x ∈ Set.range (D.lowerPortBranch b side) := by
  obtain ⟨q, hq⟩ := D.lowerTrimmedOuterPath_range_subset_gap g hx
  obtain ⟨u, hu⟩ := hx
  have hxHeight : x.ofLp (frame 2) < S.cut.height :=
    hu ▸ D.lowerTrimmedOuterPath_height_lt g u
  have hxCarrier : x ∈ D.centralGraph.carrier := by
    rw [← hq]
    exact canonicalBarrierPath_mem_carrier D.centralGraph D.centralOuterOrder
      D.centralCutOrder D.scale_pos (Sum.inl g) q
  have hxSingular :
      x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).singularPatch := by
    change x ∈ (D.centralHeightFlowArcExactness.charts.chart b).singularPatch
    have hxs' : x ∈ (D.centralHeightFlowArcExactness.charts.chart b).support := hxs
    rw [← D.centralHeightFlowArcExactness.exactness.local_arc_union_exact b,
      ← carrier_inter_eq_iUnion D.centralGraph D.centralOuterOrder
        D.centralCutOrder D.scale_pos]
    exact ⟨hxCarrier, hxs'⟩
  rcases hxSingular with (hleft | hright) | hseam
  · obtain ⟨t, rfl⟩ := hleft
    have ht : bandLeftPath t ∈
        Set.range standardLeftLowerBranchPath ∪
          Set.range standardLeftUpperBranchPath := by
      rw [← range_bandLeftPath_eq_standardHalves]
      exact ⟨t, rfl⟩
    rcases ht with ⟨v, hv⟩ | ⟨v, hv⟩
    · refine ⟨0, v, ?_⟩
      change _ = (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (bandLeftPath t)
      exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
    · have hupper :
          (D.centralHeightFlowStraightenedChartFamily.chart b).chart
              (bandLeftPath t) ∈ Set.range (D.upperPortBranch b 0) := by
        refine ⟨v, ?_⟩
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
      have hge := D.upperPortBranch_range_subset_upperHalfspace b 0 hupper
      exact (not_lt_of_ge hge hxHeight).elim
  · obtain ⟨t, rfl⟩ := hright
    have ht : bandRightPath t ∈
        Set.range standardRightLowerBranchPath ∪
          Set.range standardRightUpperBranchPath := by
      rw [← range_bandRightPath_eq_standardHalves]
      exact ⟨t, rfl⟩
    rcases ht with ⟨v, hv⟩ | ⟨v, hv⟩
    · refine ⟨1, unitInterval.symm v, ?_⟩
      change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
          (standardRightLowerBranchPath (unitInterval.symm (unitInterval.symm v))) = _
      rw [unitInterval.symm_symm]
      exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
    · have hupper :
          (D.centralHeightFlowStraightenedChartFamily.chart b).chart
              (bandRightPath t) ∈ Set.range (D.upperPortBranch b 1) := by
        refine ⟨unitInterval.symm v, ?_⟩
        change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
            (standardRightUpperBranchPath (unitInterval.symm (unitInterval.symm v))) = _
        rw [unitInterval.symm_symm]
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
      have hge := D.upperPortBranch_range_subset_upperHalfspace b 1 hupper
      exact (not_lt_of_ge hge hxHeight).elim
  · obtain ⟨t, rfl⟩ := hseam
    have hcircle := D.centralCutOrder.globalInwardExcursionPath_mem_cutCircle
      (D.centralCutOrder.globalGapOfBand b) t
    have hsection := D.centralGraph.cut.circle_mem_section
      (D.centralCutOrder.globalGapOfBand b).1.1 hcircle
    have hheight :
        ((D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t).ofLp
          (frame 2) = S.cut.height := by
      have hcore :
          (D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t =
            ((D.centralCutOrder.globalBandPath b t : transportedTorus Phi) : R3) :=
        (D.centralHeightFlowStraightenedBandData b).core_alignment t
      rw [hcore]
      exact hsection.2
    rw [hheight] at hxHeight
    exact (lt_irrefl _ hxHeight).elim

private theorem upperTrimmedOuterPath_mem_support_exists_port
    (g : D.centralOuterOrder.GlobalUpperOuterGap)
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    {x : R3} (hx : x ∈ Set.range (D.upperTrimmedOuterPath g))
    (hxs : x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).support) :
    ∃ side : Fin 2, x ∈ Set.range (D.upperPortBranch b side) := by
  obtain ⟨q, hq⟩ := D.upperTrimmedOuterPath_range_subset_gap g hx
  obtain ⟨u, hu⟩ := hx
  have hxHeight : S.cut.height < x.ofLp (frame 2) :=
    hu ▸ D.upperTrimmedOuterPath_height_gt g u
  have hxCarrier : x ∈ D.centralGraph.carrier := by
    rw [← hq]
    exact canonicalBarrierPath_mem_carrier D.centralGraph D.centralOuterOrder
      D.centralCutOrder D.scale_pos (Sum.inr (Sum.inl g)) q
  have hxSingular :
      x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).singularPatch := by
    change x ∈ (D.centralHeightFlowArcExactness.charts.chart b).singularPatch
    have hxs' : x ∈ (D.centralHeightFlowArcExactness.charts.chart b).support := hxs
    rw [← D.centralHeightFlowArcExactness.exactness.local_arc_union_exact b,
      ← carrier_inter_eq_iUnion D.centralGraph D.centralOuterOrder
        D.centralCutOrder D.scale_pos]
    exact ⟨hxCarrier, hxs'⟩
  rcases hxSingular with (hleft | hright) | hseam
  · obtain ⟨t, rfl⟩ := hleft
    have ht : bandLeftPath t ∈
        Set.range standardLeftLowerBranchPath ∪
          Set.range standardLeftUpperBranchPath := by
      rw [← range_bandLeftPath_eq_standardHalves]
      exact ⟨t, rfl⟩
    rcases ht with ⟨v, hv⟩ | ⟨v, hv⟩
    · have hlower :
          (D.centralHeightFlowStraightenedChartFamily.chart b).chart
              (bandLeftPath t) ∈ Set.range (D.lowerPortBranch b 0) := by
        refine ⟨v, ?_⟩
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
      have hle := D.lowerPortBranch_range_subset_lowerHalfspace b 0 hlower
      exact (not_lt_of_ge hle hxHeight).elim
    · refine ⟨0, v, ?_⟩
      change _ = (D.centralHeightFlowStraightenedChartFamily.chart b).chart
        (bandLeftPath t)
      exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
  · obtain ⟨t, rfl⟩ := hright
    have ht : bandRightPath t ∈
        Set.range standardRightLowerBranchPath ∪
          Set.range standardRightUpperBranchPath := by
      rw [← range_bandRightPath_eq_standardHalves]
      exact ⟨t, rfl⟩
    rcases ht with ⟨v, hv⟩ | ⟨v, hv⟩
    · have hlower :
          (D.centralHeightFlowStraightenedChartFamily.chart b).chart
              (bandRightPath t) ∈ Set.range (D.lowerPortBranch b 1) := by
        refine ⟨unitInterval.symm v, ?_⟩
        change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
            (standardRightLowerBranchPath (unitInterval.symm (unitInterval.symm v))) = _
        rw [unitInterval.symm_symm]
        exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
      have hle := D.lowerPortBranch_range_subset_lowerHalfspace b 1 hlower
      exact (not_lt_of_ge hle hxHeight).elim
    · refine ⟨1, unitInterval.symm v, ?_⟩
      change (D.centralHeightFlowStraightenedChartFamily.chart b).chart
          (standardRightUpperBranchPath (unitInterval.symm (unitInterval.symm v))) = _
      rw [unitInterval.symm_symm]
      exact congrArg (D.centralHeightFlowStraightenedChartFamily.chart b).chart hv
  · obtain ⟨t, rfl⟩ := hseam
    have hcircle := D.centralCutOrder.globalInwardExcursionPath_mem_cutCircle
      (D.centralCutOrder.globalGapOfBand b) t
    have hsection := D.centralGraph.cut.circle_mem_section
      (D.centralCutOrder.globalGapOfBand b).1.1 hcircle
    have hheight :
        ((D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t).ofLp
          (frame 2) = S.cut.height := by
      have hcore :
          (D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t =
            ((D.centralCutOrder.globalBandPath b t : transportedTorus Phi) : R3) :=
        (D.centralHeightFlowStraightenedBandData b).core_alignment t
      rw [hcore]
      exact hsection.2
    rw [hheight] at hxHeight
    exact (lt_irrefl _ hxHeight).elim

private theorem lowerPortBranch_eq_incidentGapPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    let ge := D.centralOuterOrder.globalLowerEndpointEquiv.symm
      (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
    Set.range (D.lowerPortBranch b side) =
      Set.range (D.lowerGapPortBranch ge.1 ge.2) := by
  dsimp only
  let ge := D.centralOuterOrder.globalLowerEndpointEquiv.symm
    (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
  have hglobal : D.centralOuterOrder.globalLowerEndpointEquiv ge =
      D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side) :=
    D.centralOuterOrder.globalLowerEndpointEquiv.apply_symm_apply _
  have hside : seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalLowerEndpointEquiv ge) = (b, side) := by
    rw [hglobal]
    exact D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm_apply_apply _
  rw [D.range_lowerGapPortBranch_eq ge.1 ge.2, hside]

private theorem upperPortBranch_eq_incidentGapPortBranch
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    let ge := D.centralOuterOrder.globalUpperEndpointEquiv.symm
      (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
    Set.range (D.upperPortBranch b side) =
      Set.range (D.upperGapPortBranch ge.1 ge.2) := by
  dsimp only
  let ge := D.centralOuterOrder.globalUpperEndpointEquiv.symm
    (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
  have hglobal : D.centralOuterOrder.globalUpperEndpointEquiv ge =
      D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side) :=
    D.centralOuterOrder.globalUpperEndpointEquiv.apply_symm_apply _
  have hside : seamBandSide D.centralCutOrder
      (D.centralOuterOrder.globalUpperEndpointEquiv ge) = (b, side) := by
    rw [hglobal]
    exact D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm_apply_apply _
  rw [D.range_upperGapPortBranch_eq ge.1 ge.2, hside]

theorem lowerPortBranch_range_subset_activeCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.lowerPortBranch b side) ⊆
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  let ge := D.centralOuterOrder.globalLowerEndpointEquiv.symm
    (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
  intro x hx
  apply D.lowerGapPortBranch_range_subset_activeCarrier ge.1 ge.2
  rw [← D.lowerPortBranch_eq_incidentGapPortBranch b side]
  exact hx

theorem upperPortBranch_range_subset_activeCarrier
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) (side : Fin 2) :
    Set.range (D.upperPortBranch b side) ⊆
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  let ge := D.centralOuterOrder.globalUpperEndpointEquiv.symm
    (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
  intro x hx
  apply D.upperGapPortBranch_range_subset_activeCarrier ge.1 ge.2
  rw [← D.upperPortBranch_eq_incidentGapPortBranch b side]
  exact hx

theorem canonicalBooleanOutsidePath_range_subset_activeCarrier
    (e : BooleanOutsideEdge D.centralOuterOrder) :
    Set.range (D.canonicalBooleanOutsidePath e) ⊆
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  rcases e with g | g
  · intro x hx
    have hxGap := D.lowerTrimmedOuterPath_range_subset_gap g hx
    have hxUnion : x ∈ ⋃ h : D.centralOuterOrder.GlobalLowerOuterGap,
        Set.range fun u ↦
          ((D.centralOuterOrder.globalLowerOuterPath h u : transportedTorus Phi) : R3) :=
      Set.mem_iUnion.mpr ⟨g, hxGap⟩
    rw [D.centralOuterOrder.iUnion_range_globalLowerOuterPath_eq] at hxUnion
    exact hxUnion.1
  · intro x hx
    have hxGap := D.upperTrimmedOuterPath_range_subset_gap g hx
    have hxUnion : x ∈ ⋃ h : D.centralOuterOrder.GlobalUpperOuterGap,
        Set.range fun u ↦
          ((D.centralOuterOrder.globalUpperOuterPath h u : transportedTorus Phi) : R3) :=
      Set.mem_iUnion.mpr ⟨g, hxGap⟩
    rw [D.centralOuterOrder.iUnion_range_globalUpperOuterPath_eq] at hxUnion
    exact hxUnion.1

private theorem activeOuterCarrier_disjoint_inactiveOuterCircle
    (i : D.centralOuterOrder.InactiveOuterCircle) :
    Disjoint
      (⋃ a : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle a.1).circle)
      (Set.range (D.centralGraph.outer.circle i.1).circle) := by
  rw [Set.disjoint_left]
  intro x hxActive hxInactive
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxActive
  have hai : a.1 ≠ i.1 := by
    intro h
    exact i.2 (h ▸ a.2)
  exact Set.disjoint_left.mp (D.centralGraph.outer.pairwise_disjoint hai) ha hxInactive

private theorem inactiveOuterCircle_range_disjoint_seam
    (i : D.centralOuterOrder.InactiveOuterCircle) :
    Disjoint (Set.range (D.centralGraph.outer.circle i.1).circle)
      (superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height) := by
  rw [Set.disjoint_left]
  intro x hxCircle hxSeam
  obtain ⟨z, rfl⟩ := hxCircle
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  apply D.centralOuterOrder.inactiveOuter_height_ne_zero i t
  unfold windingLoopCutHeight
  rw [← (D.centralGraph.outer.circle i.1).parametrization]
  exact sub_eq_zero.mpr hxSeam.2

theorem inactiveOuterCircle_range_disjoint_support
    (i : D.centralOuterOrder.InactiveOuterCircle)
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Disjoint (Set.range (D.centralGraph.outer.circle i.1).circle)
      (D.centralHeightFlowStraightenedChartFamily.chart b).support := by
  rw [Set.disjoint_left]
  intro x hxCircle hxSupport
  have hxCarrier : x ∈ D.centralGraph.carrier :=
    Or.inl (Set.mem_iUnion.mpr ⟨i.1, hxCircle⟩)
  have hxSingular :
      x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).singularPatch := by
    change x ∈ (D.centralHeightFlowArcExactness.charts.chart b).singularPatch
    rw [← D.centralHeightFlowArcExactness.exactness.local_arc_union_exact b,
      ← carrier_inter_eq_iUnion D.centralGraph D.centralOuterOrder
        D.centralCutOrder D.scale_pos]
    exact ⟨hxCarrier, hxSupport⟩
  rcases hxSingular with (hxLeft | hxRight) | hxSeam
  · rw [D.leftPath_range_eq_portBranches b] at hxLeft
    have hxActive : x ∈ ⋃ a : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle a.1).circle := by
      rcases hxLeft with hxLeft | hxLeft
      · exact D.lowerPortBranch_range_subset_activeCarrier b 0 hxLeft
      · exact D.upperPortBranch_range_subset_activeCarrier b 0 hxLeft
    exact Set.disjoint_left.mp
      (D.activeOuterCarrier_disjoint_inactiveOuterCircle i) hxActive hxCircle
  · rw [D.rightPath_range_eq_portBranches b] at hxRight
    have hxActive : x ∈ ⋃ a : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle a.1).circle := by
      rcases hxRight with hxRight | hxRight
      · exact D.lowerPortBranch_range_subset_activeCarrier b 1 hxRight
      · exact D.upperPortBranch_range_subset_activeCarrier b 1 hxRight
    exact Set.disjoint_left.mp
      (D.activeOuterCarrier_disjoint_inactiveOuterCircle i) hxActive hxCircle
  · obtain ⟨t, rfl⟩ := hxSeam
    have hcircle := D.centralCutOrder.globalInwardExcursionPath_mem_cutCircle
      (D.centralCutOrder.globalGapOfBand b) t
    have hsection := D.centralGraph.cut.circle_mem_section
      (D.centralCutOrder.globalGapOfBand b).1.1 hcircle
    have hheight :
        ((D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t).ofLp
          (frame 2) = S.cut.height := by
      have hcore :
          (D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t =
            ((D.centralCutOrder.globalBandPath b t : transportedTorus Phi) : R3) :=
        (D.centralHeightFlowStraightenedBandData b).core_alignment t
      rw [hcore]
      exact hsection.2
    have hxGeometricSeam :
        (D.centralHeightFlowStraightenedChartFamily.chart b).seamPath t ∈
          superellipsoidTorusSeam Phi frame c S.outer.scale S.cut.height :=
      ⟨D.centralGraph.outer.circle_mem_section i.1 hxCircle, hheight⟩
    exact Set.disjoint_left.mp (D.inactiveOuterCircle_range_disjoint_seam i)
      hxCircle hxGeometricSeam

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

private theorem lowerGapPortBranches_disjoint
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Disjoint (Set.range (D.lowerGapPortBranch g 0))
      (Set.range (D.lowerGapPortBranch g 1)) := by
  let bs0 := seamBandSide D.centralCutOrder
    (D.centralOuterOrder.globalLowerEndpointEquiv (g, 0))
  let bs1 := seamBandSide D.centralCutOrder
    (D.centralOuterOrder.globalLowerEndpointEquiv (g, 1))
  have hbs : bs0 ≠ bs1 := by
    intro h
    have hv : D.centralOuterOrder.globalLowerEndpointEquiv (g, 0) =
        D.centralOuterOrder.globalLowerEndpointEquiv (g, 1) := by
      apply D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm.injective
      exact h
    have hpair := D.centralOuterOrder.globalLowerEndpointEquiv.injective hv
    have he := congrArg Prod.snd hpair
    norm_num at he
  have hdis := D.lowerPortBranch_ranges_pairwise_disjoint hbs
  rw [D.range_lowerGapPortBranch_eq g 0, D.range_lowerGapPortBranch_eq g 1]
  exact hdis

private theorem upperGapPortBranches_disjoint
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Disjoint (Set.range (D.upperGapPortBranch g 0))
      (Set.range (D.upperGapPortBranch g 1)) := by
  let bs0 := seamBandSide D.centralCutOrder
    (D.centralOuterOrder.globalUpperEndpointEquiv (g, 0))
  let bs1 := seamBandSide D.centralCutOrder
    (D.centralOuterOrder.globalUpperEndpointEquiv (g, 1))
  have hbs : bs0 ≠ bs1 := by
    intro h
    have hv : D.centralOuterOrder.globalUpperEndpointEquiv (g, 0) =
        D.centralOuterOrder.globalUpperEndpointEquiv (g, 1) := by
      apply D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm.injective
      exact h
    have hpair := D.centralOuterOrder.globalUpperEndpointEquiv.injective hv
    have he := congrArg Prod.snd hpair
    norm_num at he
  have hdis := D.upperPortBranch_ranges_pairwise_disjoint hbs
  rw [D.range_upperGapPortBranch_eq g 0, D.range_upperGapPortBranch_eq g 1]
  exact hdis

theorem lowerGapCornerParameter_zero_lt_one
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    D.lowerGapCornerParameter g 0 < D.lowerGapCornerParameter g 1 := by
  rcases lt_trichotomy (D.lowerGapCornerParameter g 0)
      (D.lowerGapCornerParameter g 1) with hlt | heq | hgt
  · exact hlt
  · have h01 := D.lowerGapCornerParameter_injective g heq
    norm_num at h01
  · obtain ⟨t, ht1, ht0⟩ := exists_between hgt
    let p := D.ambientLowerOuterPath g
    have htPort0 : D.ambientLowerOuterPath g t ∈
        Set.range (D.lowerGapPortBranch g 0) := by
      rw [D.range_lowerGapPortBranch_zero_eq_subpath]
      change p t ∈ Set.range (p.subpath 0 (D.lowerGapCornerParameter g 0))
      rw [Path.range_subpath_of_le p 0 _ bot_le]
      exact ⟨t, ⟨bot_le, ht0.le⟩, rfl⟩
    have htPort1 : D.ambientLowerOuterPath g t ∈
        Set.range (D.lowerGapPortBranch g 1) := by
      rw [D.range_lowerGapPortBranch_one_eq_subpath]
      change p t ∈ Set.range (p.subpath 1 (D.lowerGapCornerParameter g 1))
      rw [Path.range_subpath_of_ge p 1 _ le_top]
      exact ⟨t, ⟨ht1.le, le_top⟩, rfl⟩
    exact (Set.disjoint_left.mp (D.lowerGapPortBranches_disjoint g)
      htPort0 htPort1).elim

theorem upperGapCornerParameter_zero_lt_one
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    D.upperGapCornerParameter g 0 < D.upperGapCornerParameter g 1 := by
  rcases lt_trichotomy (D.upperGapCornerParameter g 0)
      (D.upperGapCornerParameter g 1) with hlt | heq | hgt
  · exact hlt
  · have h01 := D.upperGapCornerParameter_injective g heq
    norm_num at h01
  · obtain ⟨t, ht1, ht0⟩ := exists_between hgt
    let p := D.ambientUpperOuterPath g
    have htPort0 : D.ambientUpperOuterPath g t ∈
        Set.range (D.upperGapPortBranch g 0) := by
      rw [D.range_upperGapPortBranch_zero_eq_subpath]
      change p t ∈ Set.range (p.subpath 0 (D.upperGapCornerParameter g 0))
      rw [Path.range_subpath_of_le p 0 _ bot_le]
      exact ⟨t, ⟨bot_le, ht0.le⟩, rfl⟩
    have htPort1 : D.ambientUpperOuterPath g t ∈
        Set.range (D.upperGapPortBranch g 1) := by
      rw [D.range_upperGapPortBranch_one_eq_subpath]
      change p t ∈ Set.range (p.subpath 1 (D.upperGapCornerParameter g 1))
      rw [Path.range_subpath_of_ge p 1 _ le_top]
      exact ⟨t, ⟨ht1.le, le_top⟩, rfl⟩
    exact (Set.disjoint_left.mp (D.upperGapPortBranches_disjoint g)
      htPort0 htPort1).elim

private theorem range_eq_three_subpaths {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (s t : unitInterval) (hst : s ≤ t) :
    Set.range p =
      (Set.range (p.subpath 0 s) ∪ Set.range (p.subpath s t)) ∪
        Set.range (p.subpath 1 t) := by
  rw [Path.range_subpath_of_le p 0 s bot_le,
    Path.range_subpath_of_le p s t hst,
    Path.range_subpath_of_ge p 1 t le_top]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hus : u ≤ s
    · exact Or.inl (Or.inl ⟨u, ⟨bot_le, hus⟩, rfl⟩)
    · by_cases hut : u ≤ t
      · exact Or.inl (Or.inr ⟨u, ⟨le_of_not_ge hus, hut⟩, rfl⟩)
      · exact Or.inr ⟨u, ⟨le_of_not_ge hut, le_top⟩, rfl⟩
  · rintro ((⟨u, _hu, rfl⟩ | ⟨u, _hu, rfl⟩) | ⟨u, _hu, rfl⟩) <;>
      exact ⟨u, rfl⟩

/-- A lower outer gap is exactly its two port branches and trimmed middle arc. -/
theorem range_globalLowerOuterPath_eq_portBranches_union_trimmed
    (g : D.centralOuterOrder.GlobalLowerOuterGap) :
    Set.range (fun u ↦
        ((D.centralOuterOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3)) =
      (Set.range (D.lowerGapPortBranch g 0) ∪ Set.range (D.lowerTrimmedOuterPath g)) ∪
        Set.range (D.lowerGapPortBranch g 1) := by
  have htrim : Set.range (D.lowerTrimmedOuterPath g) =
      Set.range ((D.ambientLowerOuterPath g).subpath
        (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1)) :=
    congrArg Set.range (Path.cast_coe _ _ _)
  change Set.range (D.ambientLowerOuterPath g) = _
  rw [D.range_lowerGapPortBranch_zero_eq_subpath, htrim,
    D.range_lowerGapPortBranch_one_eq_subpath]
  exact range_eq_three_subpaths (D.ambientLowerOuterPath g)
    (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1)
    (D.lowerGapCornerParameter_zero_lt_one g).le

/-- An upper outer gap is exactly its two port branches and trimmed middle arc. -/
theorem range_globalUpperOuterPath_eq_portBranches_union_trimmed
    (g : D.centralOuterOrder.GlobalUpperOuterGap) :
    Set.range (fun u ↦
        ((D.centralOuterOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3)) =
      (Set.range (D.upperGapPortBranch g 0) ∪ Set.range (D.upperTrimmedOuterPath g)) ∪
        Set.range (D.upperGapPortBranch g 1) := by
  have htrim : Set.range (D.upperTrimmedOuterPath g) =
      Set.range ((D.ambientUpperOuterPath g).subpath
        (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1)) :=
    congrArg Set.range (Path.cast_coe _ _ _)
  change Set.range (D.ambientUpperOuterPath g) = _
  rw [D.range_upperGapPortBranch_zero_eq_subpath, htrim,
    D.range_upperGapPortBranch_one_eq_subpath]
  exact range_eq_three_subpaths (D.ambientUpperOuterPath g)
    (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1)
    (D.upperGapCornerParameter_zero_lt_one g).le

private theorem range_adjacent_subpaths_inter {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (hp : Function.Injective p)
    (s t u : unitInterval) (hst : s ≤ t) (htu : t ≤ u) :
    Set.range (p.subpath s t) ∩ Set.range (p.subpath t u) = {p t} := by
  rw [Path.range_subpath_of_le p s t hst,
    Path.range_subpath_of_le p t u htu]
  ext x
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, ⟨w, hw, hwv⟩⟩
    have hvw : v = w := hp hwv.symm
    subst w
    have hvt : v = t := le_antisymm hv.2 hw.1
    subst v
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨t, ⟨hst, le_rfl⟩, rfl⟩, ⟨t, ⟨le_rfl, htu⟩, rfl⟩⟩

private theorem range_middle_subpath_inter_reversed_right {X : Type*}
    [TopologicalSpace X] {a b : X} (p : Path a b) (hp : Function.Injective p)
    (s t u : unitInterval) (hst : s ≤ t) (htu : t ≤ u) :
    Set.range (p.subpath s t) ∩ Set.range (p.subpath u t) = {p t} := by
  have hreverse : Set.range (p.subpath u t) = Set.range (p.subpath t u) := by
    rw [Path.range_subpath_of_ge p u t htu,
      Path.range_subpath_of_le p t u htu]
  rw [hreverse]
  exact range_adjacent_subpaths_inter p hp s t u hst htu

theorem lowerTrimmedOuterPath_inter_lowerGapPortBranch
    (g : D.centralOuterOrder.GlobalLowerOuterGap) (e : Fin 2) :
    Set.range (D.lowerTrimmedOuterPath g) ∩
        Set.range (D.lowerGapPortBranch g e) =
      {fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inl g, e))} := by
  have htrim : (D.lowerTrimmedOuterPath g : unitInterval → R3) =
      (D.ambientLowerOuterPath g).subpath
        (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1) := by
    funext u
    unfold lowerTrimmedOuterPath
    exact congrFun (Path.cast_coe _ _ _) u
  refine Fin.cases ?_ (fun e ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) e) e
  · rw [htrim, D.range_lowerGapPortBranch_zero_eq_subpath, Set.inter_comm,
      D.lowerGapCorner_eq g 0]
    exact range_adjacent_subpaths_inter (D.ambientLowerOuterPath g)
      (D.centralOuterOrder.globalLowerOuterPath_injective g) 0
      (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1) bot_le
      (D.lowerGapCornerParameter_zero_lt_one g).le
  · rw [show (Fin.succ 0 : Fin 2) = 1 from rfl, htrim,
      D.range_lowerGapPortBranch_one_eq_subpath, D.lowerGapCorner_eq g 1]
    exact range_middle_subpath_inter_reversed_right (D.ambientLowerOuterPath g)
      (D.centralOuterOrder.globalLowerOuterPath_injective g)
      (D.lowerGapCornerParameter g 0) (D.lowerGapCornerParameter g 1) 1
      (D.lowerGapCornerParameter_zero_lt_one g).le le_top

theorem upperTrimmedOuterPath_inter_upperGapPortBranch
    (g : D.centralOuterOrder.GlobalUpperOuterGap) (e : Fin 2) :
    Set.range (D.upperTrimmedOuterPath g) ∩
        Set.range (D.upperGapPortBranch g e) =
      {fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
        (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder
          (Sum.inr g, e))} := by
  have htrim : (D.upperTrimmedOuterPath g : unitInterval → R3) =
      (D.ambientUpperOuterPath g).subpath
        (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1) := by
    funext u
    unfold upperTrimmedOuterPath
    exact congrFun (Path.cast_coe _ _ _) u
  refine Fin.cases ?_ (fun e ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) e) e
  · rw [htrim, D.range_upperGapPortBranch_zero_eq_subpath, Set.inter_comm,
      D.upperGapCorner_eq g 0]
    exact range_adjacent_subpaths_inter (D.ambientUpperOuterPath g)
      (D.centralOuterOrder.globalUpperOuterPath_injective g) 0
      (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1) bot_le
      (D.upperGapCornerParameter_zero_lt_one g).le
  · rw [show (Fin.succ 0 : Fin 2) = 1 from rfl, htrim,
      D.range_upperGapPortBranch_one_eq_subpath, D.upperGapCorner_eq g 1]
    exact range_middle_subpath_inter_reversed_right (D.ambientUpperOuterPath g)
      (D.centralOuterOrder.globalUpperOuterPath_injective g)
      (D.upperGapCornerParameter g 0) (D.upperGapCornerParameter g 1) 1
      (D.upperGapCornerParameter_zero_lt_one g).le le_top

theorem canonicalBooleanOutsidePath_mem_support_exists_endpoint
    (e : BooleanOutsideEdge D.centralOuterOrder)
    (b : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount)
    {x : R3} (hx : x ∈ Set.range (D.canonicalBooleanOutsidePath e))
    (hxs : x ∈ (D.centralHeightFlowStraightenedChartFamily.chart b).support) :
    ∃ j : Fin 2,
      (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder (e, j)).1 = b ∧
        x = fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart
          (booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder (e, j)) := by
  rcases e with g | g
  · obtain ⟨side, hxPort⟩ :=
      D.lowerTrimmedOuterPath_mem_support_exists_port g b hx hxs
    let ge := D.centralOuterOrder.globalLowerEndpointEquiv.symm
      (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
    have hxGapPort : x ∈ Set.range (D.lowerGapPortBranch ge.1 ge.2) := by
      rw [← D.lowerPortBranch_eq_incidentGapPortBranch b side]
      exact hxPort
    have hge : ge.1 = g := by
      by_contra hne
      exact Set.disjoint_left.mp
        (D.centralOuterOrder.globalLowerOuterPath_ranges_pairwise_disjoint hne)
        (D.lowerGapPortBranch_range_subset_gap ge.1 ge.2 hxGapPort)
        (D.lowerTrimmedOuterPath_range_subset_gap g hx)
    subst g
    have hxInter : x ∈ Set.range (D.lowerTrimmedOuterPath ge.1) ∩
        Set.range (D.lowerGapPortBranch ge.1 ge.2) := ⟨hx, hxGapPort⟩
    rw [D.lowerTrimmedOuterPath_inter_lowerGapPortBranch ge.1 ge.2] at hxInter
    have hxCorner := Set.mem_singleton_iff.mp hxInter
    refine ⟨ge.2, ?_, hxCorner⟩
    have hglobal : D.centralOuterOrder.globalLowerEndpointEquiv ge =
        D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side) :=
      D.centralOuterOrder.globalLowerEndpointEquiv.apply_symm_apply _
    simp only [booleanOutsideEndpointEquiv_lower]
    rw [show seamBandSide D.centralCutOrder
        (D.centralOuterOrder.globalLowerEndpointEquiv ge) = (b, side) by
      rw [hglobal]
      exact D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm_apply_apply _]
  · obtain ⟨side, hxPort⟩ :=
      D.upperTrimmedOuterPath_mem_support_exists_port g b hx hxs
    let ge := D.centralOuterOrder.globalUpperEndpointEquiv.symm
      (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
    have hxGapPort : x ∈ Set.range (D.upperGapPortBranch ge.1 ge.2) := by
      rw [← D.upperPortBranch_eq_incidentGapPortBranch b side]
      exact hxPort
    have hge : ge.1 = g := by
      by_contra hne
      exact Set.disjoint_left.mp
        (D.centralOuterOrder.globalUpperOuterPath_ranges_pairwise_disjoint hne)
        (D.upperGapPortBranch_range_subset_gap ge.1 ge.2 hxGapPort)
        (D.upperTrimmedOuterPath_range_subset_gap g hx)
    subst g
    have hxInter : x ∈ Set.range (D.upperTrimmedOuterPath ge.1) ∩
        Set.range (D.upperGapPortBranch ge.1 ge.2) := ⟨hx, hxGapPort⟩
    rw [D.upperTrimmedOuterPath_inter_upperGapPortBranch ge.1 ge.2] at hxInter
    have hxCorner := Set.mem_singleton_iff.mp hxInter
    refine ⟨ge.2, ?_, hxCorner⟩
    have hglobal : D.centralOuterOrder.globalUpperEndpointEquiv ge =
        D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side) :=
      D.centralOuterOrder.globalUpperEndpointEquiv.apply_symm_apply _
    simp only [booleanOutsideEndpointEquiv_upper]
    rw [show seamBandSide D.centralCutOrder
        (D.centralOuterOrder.globalUpperEndpointEquiv ge) = (b, side) by
      rw [hglobal]
      exact D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv.symm_apply_apply _]

theorem point_mem_path_of_mem_endpointSet
    {vertex X : Type*} [Fintype vertex] [TopologicalSpace X]
    (P : FiniteEndpointPairing vertex) (point : vertex → X)
    (paths : FiniteAlternatingEndpointSystem.EndpointPathFamily P point)
    {e : P.edge} {v : vertex} (hv : v ∈ P.endpointSet e) :
    point v ∈ Set.range (paths.path e) := by
  obtain ⟨j, hj⟩ := hv
  fin_cases j
  · refine ⟨0, ?_⟩
    rw [(paths.path e).source]
    exact congrArg point (by simpa using hj)
  · refine ⟨1, ?_⟩
    rw [(paths.path e).target]
    exact congrArg point (by simpa using hj)

theorem mem_endpointSet_of_point_mem_path
    {vertex X : Type*} [Fintype vertex] [TopologicalSpace X]
    (P : FiniteEndpointPairing vertex) (point : vertex → X)
    (paths : FiniteAlternatingEndpointSystem.EndpointPathFamily P point)
    (hpairwise : Pairwise fun e f : P.edge ↦
      Disjoint (Set.range (paths.path e)) (Set.range (paths.path f)))
    {e : P.edge} {v : vertex} (hv : point v ∈ Set.range (paths.path e)) :
    v ∈ P.endpointSet e := by
  let ej := P.endpointEquiv.symm v
  have hev : P.endpointEquiv ej = v := P.endpointEquiv.apply_symm_apply v
  have hvOwn : point v ∈ Set.range (paths.path ej.1) :=
    point_mem_path_of_mem_endpointSet P point paths ⟨ej.2, hev⟩
  have he : e = ej.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (hpairwise hne) hv hvOwn
  subst e
  exact ⟨ej.2, hev⟩

theorem canonicalBooleanOutsidePath_cross_intersection_subset
    (choice : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount → Bool)
    (e : BooleanOutsideEdge D.centralOuterOrder)
    (f : FourPortLocalEdge D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.canonicalBooleanOutsidePath e) ∩
        Set.range ((booleanFourPortLocalEndpointPaths
          D.centralHeightFlowStraightenedChartFamily.chart choice).path f) ⊆
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart ''
        ((booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointSet e ∩
          (fourPortLocalPairing choice).endpointSet f) := by
  rintro x ⟨hxOutside, hxLocal⟩
  have hxSupport := D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
    |>.booleanFourPortLocalEndpointPaths_range_subset_support choice f hxLocal
  obtain ⟨j, _hband, hxPoint⟩ :=
    D.canonicalBooleanOutsidePath_mem_support_exists_endpoint e f.1
      hxOutside hxSupport
  let v := booleanOutsideEndpointEquiv D.centralOuterOrder D.centralCutOrder (e, j)
  have hvOutside :
      v ∈ (booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointSet e :=
    ⟨j, rfl⟩
  have hvLocal : v ∈ (fourPortLocalPairing choice).endpointSet f := by
    apply mem_endpointSet_of_point_mem_path (fourPortLocalPairing choice)
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart)
      (booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart choice)
      (D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
        |>.booleanFourPortLocalEndpointPaths_pairwise choice)
    exact hxPoint ▸ hxLocal
  exact ⟨v, ⟨hvOutside, hvLocal⟩, hxPoint.symm⟩

theorem canonicalBooleanOutsidePath_cross_intersection_superset
    (choice : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount → Bool)
    (e : BooleanOutsideEdge D.centralOuterOrder)
    (f : FourPortLocalEdge D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart ''
        ((booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointSet e ∩
          (fourPortLocalPairing choice).endpointSet f) ⊆
      Set.range (D.canonicalBooleanOutsidePath e) ∩
        Set.range ((booleanFourPortLocalEndpointPaths
          D.centralHeightFlowStraightenedChartFamily.chart choice).path f) := by
  rintro _ ⟨v, ⟨hvOutside, hvLocal⟩, rfl⟩
  constructor
  · exact point_mem_path_of_mem_endpointSet
      (booleanOutsidePairing D.centralOuterOrder D.centralCutOrder)
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart)
      D.canonicalBooleanOutsideEndpointPaths hvOutside
  · exact point_mem_path_of_mem_endpointSet (fourPortLocalPairing choice)
      (fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart)
      (booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart choice) hvLocal

theorem canonicalBooleanOutsidePath_cross_intersection
    (choice : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount → Bool)
    (e : BooleanOutsideEdge D.centralOuterOrder)
    (f : FourPortLocalEdge D.centralCutOrder.toPairedSeamEnumeration.bandCount) :
    Set.range (D.canonicalBooleanOutsidePath e) ∩
        Set.range ((booleanFourPortLocalEndpointPaths
          D.centralHeightFlowStraightenedChartFamily.chart choice).path f) =
      fourPortChartPoint D.centralHeightFlowStraightenedChartFamily.chart ''
        ((booleanOutsidePairing D.centralOuterOrder D.centralCutOrder).endpointSet e ∩
          (fourPortLocalPairing choice).endpointSet f) := by
  apply Set.Subset.antisymm
  · exact D.canonicalBooleanOutsidePath_cross_intersection_subset choice e f
  · exact D.canonicalBooleanOutsidePath_cross_intersection_superset choice e f

/-- The canonical trimmed outer gaps satisfy exact incidence with every Boolean four-port
resolution. -/
noncomputable def canonicalBooleanOutsidePathData :
    BooleanFourPortOutsidePathData Phi
      D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts where
  outside := booleanOutsidePairing D.centralOuterOrder D.centralCutOrder
  paths := D.canonicalBooleanOutsideEndpointPaths
  chart_mem_torus := chart_mem_transportedTorus D.centralCutOrder
    D.centralHeightFlowStraightenedChartFamily
  paths_mem_torus := D.canonicalBooleanOutsidePath_range_subset_transportedTorus
  paths_injective := D.canonicalBooleanOutsidePath_injective
  paths_pairwise := D.canonicalBooleanOutsidePath_ranges_pairwise_disjoint
  cross_intersection := D.canonicalBooleanOutsidePath_cross_intersection

/-- The fixed seam-free outer circles, which do not participate in any four-port move. -/
def canonicalInactiveOuterCarrier : Set R3 :=
  ⋃ i : D.centralOuterOrder.InactiveOuterCircle,
    Set.range (D.centralGraph.outer.circle i.1).circle

theorem superellipsoidOuterTorusSection_eq_active_union_inactive :
    superellipsoidOuterTorusSection Phi frame c S.outer.scale =
      (⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle) ∪
        D.canonicalInactiveOuterCarrier := by
  classical
  calc
    superellipsoidOuterTorusSection Phi frame c S.outer.scale =
        ⋃ i, Set.range (D.centralGraph.outer.circle i).circle :=
      D.centralGraph.outer.section_exact
    _ = _ := by
      ext x
      simp only [canonicalInactiveOuterCarrier, Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        by_cases hactive : (D.centralOuterOrder.regular i).crossings.Nonempty
        · exact Or.inl ⟨⟨i, hactive⟩, hi⟩
        · exact Or.inr ⟨⟨i, hactive⟩, hi⟩
      · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
        · exact ⟨i.1, hi⟩
        · exact ⟨i.1, hi⟩

theorem canonicalBooleanOutsidePathData_ambientSection_disjoint_inactiveOuterCircle
    (choice : Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount → Bool)
    (i : D.centralOuterOrder.InactiveOuterCircle) :
    Disjoint (D.canonicalBooleanOutsidePathData.ambientSection choice)
      (Set.range (D.centralGraph.outer.circle i.1).circle) := by
  rw [Set.disjoint_left]
  intro x hxSection hxInactive
  rw [D.canonicalBooleanOutsidePathData.ambientSection_eq_iUnion_ranges] at hxSection
  rcases hxSection with hxOutside | hxLocal
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxOutside
    have hxActive := D.canonicalBooleanOutsidePath_range_subset_activeCarrier e he
    exact Set.disjoint_left.mp
      (D.activeOuterCarrier_disjoint_inactiveOuterCircle i) hxActive hxInactive
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxLocal
    have hxSupport := D.centralHeightFlowArcExactness.charts.toFinitePairedSeamBandCharts
      |>.booleanFourPortLocalEndpointPaths_range_subset_support choice e he
    exact Set.disjoint_left.mp (D.inactiveOuterCircle_range_disjoint_support i e.1)
      hxInactive hxSupport

/-- The all-vertical Boolean resolution reconstructs exactly the active outer circles. -/
theorem canonicalBooleanOutsidePathData_ambientSection_false_eq_activeOuterCarrier :
    D.canonicalBooleanOutsidePathData.ambientSection (fun _ ↦ false) =
      ⋃ i : D.centralOuterOrder.ActiveOuterCircle,
        Set.range (D.centralGraph.outer.circle i.1).circle := by
  classical
  rw [D.canonicalBooleanOutsidePathData.ambientSection_eq_iUnion_ranges]
  ext x
  constructor
  · rintro (hxOutside | hxLocal)
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxOutside
      rcases e with g | g
      · have hxGap := D.lowerTrimmedOuterPath_range_subset_gap g he
        have hxUnion : x ∈ ⋃ h : D.centralOuterOrder.GlobalLowerOuterGap,
            Set.range fun u ↦
              ((D.centralOuterOrder.globalLowerOuterPath h u : transportedTorus Phi) : R3) :=
          Set.mem_iUnion.mpr ⟨g, hxGap⟩
        rw [D.centralOuterOrder.iUnion_range_globalLowerOuterPath_eq] at hxUnion
        exact hxUnion.1
      · have hxGap := D.upperTrimmedOuterPath_range_subset_gap g he
        have hxUnion : x ∈ ⋃ h : D.centralOuterOrder.GlobalUpperOuterGap,
            Set.range fun u ↦
              ((D.centralOuterOrder.globalUpperOuterPath h u : transportedTorus Phi) : R3) :=
          Set.mem_iUnion.mpr ⟨g, hxGap⟩
        rw [D.centralOuterOrder.iUnion_range_globalUpperOuterPath_eq] at hxUnion
        exact hxUnion.1
    · obtain ⟨⟨b, side⟩, he⟩ := Set.mem_iUnion.mp hxLocal
      change x ∈ Set.range ((booleanFourPortLocalEndpointPaths
        D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path
          (b, side)) at he
      rw [D.range_booleanFourPortLocalPath_false_eq_portBranches b side] at he
      rcases he with he | he
      · let ge := D.centralOuterOrder.globalLowerEndpointEquiv.symm
          (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
        have he' : x ∈ Set.range (D.lowerGapPortBranch ge.1 ge.2) := by
          rw [← D.lowerPortBranch_eq_incidentGapPortBranch b side]
          exact he
        exact D.lowerGapPortBranch_range_subset_activeCarrier ge.1 ge.2 he'
      · let ge := D.centralOuterOrder.globalUpperEndpointEquiv.symm
          (D.centralCutOrder.toPairedSeamEnumeration.endpointEquiv (b, side))
        have he' : x ∈ Set.range (D.upperGapPortBranch ge.1 ge.2) := by
          rw [← D.upperPortBranch_eq_incidentGapPortBranch b side]
          exact he
        exact D.upperGapPortBranch_range_subset_activeCarrier ge.1 ge.2 he'
  · intro hx
    rcases le_total (x.ofLp (frame 2)) S.cut.height with hxLower | hxUpper
    · have hxHalf : x ∈
          (⋃ i : D.centralOuterOrder.ActiveOuterCircle,
            Set.range (D.centralGraph.outer.circle i.1).circle) ∩
              lowerClosedHalfspace frame S.cut.height := ⟨hx, hxLower⟩
      rw [← D.centralOuterOrder.iUnion_range_globalLowerOuterPath_eq] at hxHalf
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxHalf
      rw [D.range_globalLowerOuterPath_eq_portBranches_union_trimmed g] at hg
      rcases hg with (hg | hg) | hg
      · refine Or.inr (Set.mem_iUnion.mpr ⟨?_, ?_⟩)
        · exact seamBandSide D.centralCutOrder
            (D.centralOuterOrder.globalLowerEndpointEquiv (g, 0))
        · change x ∈ Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path _)
          rw [D.range_booleanFourPortLocalPath_false_eq_portBranches]
          exact Or.inl (D.range_lowerGapPortBranch_eq g 0 ▸ hg)
      · exact Or.inl (Set.mem_iUnion.mpr ⟨Sum.inl g, hg⟩)
      · refine Or.inr (Set.mem_iUnion.mpr ⟨?_, ?_⟩)
        · exact seamBandSide D.centralCutOrder
            (D.centralOuterOrder.globalLowerEndpointEquiv (g, 1))
        · change x ∈ Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path _)
          rw [D.range_booleanFourPortLocalPath_false_eq_portBranches]
          exact Or.inl (D.range_lowerGapPortBranch_eq g 1 ▸ hg)
    · have hxHalf : x ∈
          (⋃ i : D.centralOuterOrder.ActiveOuterCircle,
            Set.range (D.centralGraph.outer.circle i.1).circle) ∩
              upperClosedHalfspace frame S.cut.height := ⟨hx, hxUpper⟩
      rw [← D.centralOuterOrder.iUnion_range_globalUpperOuterPath_eq] at hxHalf
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxHalf
      rw [D.range_globalUpperOuterPath_eq_portBranches_union_trimmed g] at hg
      rcases hg with (hg | hg) | hg
      · refine Or.inr (Set.mem_iUnion.mpr ⟨?_, ?_⟩)
        · exact seamBandSide D.centralCutOrder
            (D.centralOuterOrder.globalUpperEndpointEquiv (g, 0))
        · change x ∈ Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path _)
          rw [D.range_booleanFourPortLocalPath_false_eq_portBranches]
          exact Or.inr (D.range_upperGapPortBranch_eq g 0 ▸ hg)
      · exact Or.inl (Set.mem_iUnion.mpr ⟨Sum.inr g, hg⟩)
      · refine Or.inr (Set.mem_iUnion.mpr ⟨?_, ?_⟩)
        · exact seamBandSide D.centralCutOrder
            (D.centralOuterOrder.globalUpperEndpointEquiv (g, 1))
        · change x ∈ Set.range ((booleanFourPortLocalEndpointPaths
            D.centralHeightFlowStraightenedChartFamily.chart (fun _ ↦ false)).path _)
          rw [D.range_booleanFourPortLocalPath_false_eq_portBranches]
          exact Or.inr (D.range_upperGapPortBranch_eq g 1 ▸ hg)

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
