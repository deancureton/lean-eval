import Submission.Topology.SuperellipsoidGlobalFourPortMorseGraph

/-!
# Exact endpoint carriers for the global four-port Morse graph

This adapter identifies the zero- and one-time transported-torus intersections of the global
Morse graph with the vertical and horizontal path carriers in its paired seam-band chart.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-! ## The standard planar carriers as path ranges -/

theorem bandLeftPath_snd_eq (u : unitInterval) :
    (bandLeftPath u).2 = 2 * (u : ℝ) - 1 := by
  rw [bandLeftPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (u : ℝ)) * (-1) + (u : ℝ) * 1 = 2 * (u : ℝ) - 1
  ring

theorem bandRightPath_snd_eq (u : unitInterval) :
    (bandRightPath u).2 = 2 * (u : ℝ) - 1 := by
  rw [bandRightPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (u : ℝ)) * (-1) + (u : ℝ) * 1 = 2 * (u : ℝ) - 1
  ring

theorem bandBottomPath_fst_eq (u : unitInterval) :
    (bandBottomPath u).1 = 2 * (u : ℝ) - 1 := by
  rw [bandBottomPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (u : ℝ)) * (-1) + (u : ℝ) * 1 = 2 * (u : ℝ) - 1
  ring

theorem bandTopPath_fst_eq (u : unitInterval) :
    (bandTopPath u).1 = 2 * (u : ℝ) - 1 := by
  rw [bandTopPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (u : ℝ)) * (-1) + (u : ℝ) * 1 = 2 * (u : ℝ) - 1
  ring

private theorem exists_unitInterval_eq_two_mul_sub_one {x : ℝ}
    (hx : x ∈ Icc (-(1 : ℝ)) 1) :
    ∃ u : unitInterval, 2 * (u : ℝ) - 1 = x := by
  let u : unitInterval := ⟨(x + 1) / 2, by
    constructor <;> linarith [hx.1, hx.2]⟩
  exact ⟨u, by dsimp [u]; ring⟩

theorem fourPortVerticalCarrier_eq_pathRanges :
    fourPortVerticalCarrier = Set.range bandLeftPath ∪ Set.range bandRightPath := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨u, hu⟩ := exists_unitInterval_eq_two_mul_sub_one hy
    rcases hx with hx | hx
    · right
      refine ⟨u, Prod.ext ?_ ?_⟩
      · simpa [hx] using bandRightPath_fst u
      · simpa [hu] using bandRightPath_snd_eq u
    · left
      refine ⟨u, Prod.ext ?_ ?_⟩
      · simpa [hx] using bandLeftPath_fst u
      · simpa [hu] using bandLeftPath_snd_eq u
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨Or.inr (bandLeftPath_fst u), ?_⟩
      rw [bandLeftPath_snd_eq, mem_Icc]
      constructor <;> linarith [u.2.1, u.2.2]
    · refine ⟨Or.inl (bandRightPath_fst u), ?_⟩
      rw [bandRightPath_snd_eq, mem_Icc]
      constructor <;> linarith [u.2.1, u.2.2]

theorem fourPortHorizontalCarrier_eq_pathRanges :
    fourPortHorizontalCarrier = Set.range bandBottomPath ∪ Set.range bandTopPath := by
  ext x
  constructor
  · rintro ⟨hy, hx⟩
    obtain ⟨u, hu⟩ := exists_unitInterval_eq_two_mul_sub_one hx
    rcases hy with hy | hy
    · right
      refine ⟨u, Prod.ext ?_ ?_⟩
      · simpa [hu] using bandTopPath_fst_eq u
      · simpa [hy] using bandTopPath_snd u
    · left
      refine ⟨u, Prod.ext ?_ ?_⟩
      · simpa [hu] using bandBottomPath_fst_eq u
      · simpa [hy] using bandBottomPath_snd u
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨Or.inr (bandBottomPath_snd u), ?_⟩
      rw [bandBottomPath_fst_eq, mem_Icc]
      constructor <;> linarith [u.2.1, u.2.2]
    · refine ⟨Or.inl (bandTopPath_snd u), ?_⟩
      rw [bandTopPath_fst_eq, mem_Icc]
      constructor <;> linarith [u.2.1, u.2.2]

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace CutCircleTransverseCyclicOrderFamily

variable {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

private theorem image_chart_range_path
    (T : GlobalBandTubularChartData F b) {x y : Plane} (p : Path x y) :
    T.toPairedSeamBandChart.chart '' Set.range p =
      Set.range (p.map T.toPairedSeamBandChart.chartEmbedding.continuous) := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨p u, ⟨u, rfl⟩, rfl⟩

/-- On the zero normal slice, the ambient graph point is literally the chart point. -/
theorem globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) (hu : fourPortMorseHeight t u.1 = 0) :
    globalBandFourPortMorseGraph T t u = T.toPairedSeamBandChart.chart u.1 := by
  have hnormal : fourPortNormalCoordinate t u = standardTorusNormalZero := by
    apply Subtype.ext
    change (1 / 4 : ℝ) * fourPortMorseHeight t u.1 = 0
    rw [hu]
    norm_num
  rw [globalBandFourPortMorseGraph, globalBandFourPortTubeCoordinates, hnormal,
    transportedTorusNormalTubeMap_zero]
  change transportedTorusMap Phi ((transportedTorusHomeomorph Phi).symm
      ((T.strip u.1 : T.surfacePatch) : transportedTorus Phi)) =
    (((T.strip u.1 : T.surfacePatch) : transportedTorus Phi) : R3)
  exact congrArg Subtype.val <|
    (transportedTorusHomeomorph Phi).apply_symm_apply
      ((T.strip u.1 : T.surfacePatch) : transportedTorus Phi)

/-- The chart image of the vertical planar carrier is its parallel path patch. -/
theorem image_chart_fourPortVerticalCarrier
    (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.chart '' fourPortVerticalCarrier =
      T.toPairedSeamBandChart.parallelPatch := by
  rw [fourPortVerticalCarrier_eq_pathRanges, image_union]
  rw [image_chart_range_path T bandLeftPath, image_chart_range_path T bandRightPath]
  rfl

/-- The chart image of the horizontal planar carrier is its surgery path patch. -/
theorem image_chart_fourPortHorizontalCarrier
    (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.chart '' fourPortHorizontalCarrier =
      T.toPairedSeamBandChart.surgeryPatch := by
  rw [fourPortHorizontalCarrier_eq_pathRanges, image_union]
  rw [image_chart_range_path T bandBottomPath, image_chart_range_path T bandTopPath]
  rfl

/-- Exact time-zero transported-torus intersection: the two vertical chart paths. -/
theorem range_globalBandFourPortMorseGraph_zero_inter_transportedTorus
    (T : GlobalBandTubularChartData F b) :
    Set.range (globalBandFourPortMorseGraph T ⟨0, by norm_num⟩) ∩
        transportedTorus Phi = T.toPairedSeamBandChart.parallelPatch := by
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, huTorus⟩
    have huCarrier :=
      (globalBandFourPortMorseGraph_zero_mem_transportedTorus_iff T u).mp huTorus
    rw [← image_chart_fourPortVerticalCarrier T]
    refine ⟨u.1, huCarrier, ?_⟩
    symm
    exact globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
      (⟨0, by norm_num⟩ : FourPortMorseTime) u <| by
        rw [fourPortMorseHeight_zero]
        exact ((mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u.1).mpr
          huCarrier).2
  · intro hx
    rw [← image_chart_fourPortVerticalCarrier T] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzRegion : z ∈ fourPortQuadraticRegion :=
      ((mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff z).mpr hz).1
    let u : FourPortQuadraticDisk := ⟨z, hzRegion⟩
    have huZero : fourPortMorseHeight (⟨0, by norm_num⟩ : FourPortMorseTime) z = 0 := by
      rw [fourPortMorseHeight_zero]
      exact ((mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff z).mpr hz).2
    have hgraph := globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
      (⟨0, by norm_num⟩ : FourPortMorseTime) u huZero
    refine ⟨⟨u, hgraph⟩, ?_⟩
    change (((T.strip z : T.surfacePatch) : transportedTorus Phi) : R3) ∈
      transportedTorus Phi
    exact ((T.strip z : T.surfacePatch) : transportedTorus Phi).2

/-- Exact time-one transported-torus intersection: the two horizontal chart paths. -/
theorem range_globalBandFourPortMorseGraph_one_inter_transportedTorus
    (T : GlobalBandTubularChartData F b) :
    Set.range (globalBandFourPortMorseGraph T ⟨1, by norm_num⟩) ∩
        transportedTorus Phi = T.toPairedSeamBandChart.surgeryPatch := by
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, huTorus⟩
    have huCarrier :=
      (globalBandFourPortMorseGraph_one_mem_transportedTorus_iff T u).mp huTorus
    rw [← image_chart_fourPortHorizontalCarrier T]
    refine ⟨u.1, huCarrier, ?_⟩
    symm
    exact globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
      (⟨1, by norm_num⟩ : FourPortMorseTime) u <| by
        rw [fourPortMorseHeight_one]
        exact ((mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u.1).mpr
          huCarrier).2
  · intro hx
    rw [← image_chart_fourPortHorizontalCarrier T] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzRegion : z ∈ fourPortQuadraticRegion :=
      ((mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff z).mpr hz).1
    let u : FourPortQuadraticDisk := ⟨z, hzRegion⟩
    have huZero : fourPortMorseHeight (⟨1, by norm_num⟩ : FourPortMorseTime) z = 0 := by
      rw [fourPortMorseHeight_one]
      exact ((mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff z).mpr hz).2
    have hgraph := globalBandFourPortMorseGraph_eq_chart_of_height_eq_zero T
      (⟨1, by norm_num⟩ : FourPortMorseTime) u huZero
    refine ⟨⟨u, hgraph⟩, ?_⟩
    change (((T.strip z : T.surfacePatch) : transportedTorus Phi) : R3) ∈
      transportedTorus Phi
    exact ((T.strip z : T.surfacePatch) : transportedTorus Phi).2

end CutCircleTransverseCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
