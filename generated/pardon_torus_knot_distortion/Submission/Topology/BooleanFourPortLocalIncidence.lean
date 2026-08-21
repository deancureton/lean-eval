import Submission.Topology.BooleanFourPortLocalPaths

/-!
# Closed-arc incidence inside disjoint four-port charts

The Boolean local paths are embedded and pairwise disjoint, and their four labelled endpoints are
distinct.  These facts follow from the embedded charts and their pairwise-disjoint supports; no
outside-path geometry is used here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

namespace FinitePairedSeamBandCharts

variable {n : ℕ} (F : FinitePairedSeamBandCharts n)

private theorem finTwo_one_eq_succ_zero : (1 : Fin 2) = Fin.succ 0 := rfl

theorem fourPortChartPoint_mem_support (v : FourPortVertex n) :
    fourPortChartPoint F.band v ∈ (F.band v.1).support := by
  rcases v with ⟨b, side, level⟩
  fin_cases side <;> fin_cases level
  · change (F.band b).leftBottom ∈ (F.band b).support
    exact (F.band b).leftPath_range_subset_support ⟨0, (F.band b).leftPath.source⟩
  · change (F.band b).leftTop ∈ (F.band b).support
    exact (F.band b).leftPath_range_subset_support ⟨1, (F.band b).leftPath.target⟩
  · change (F.band b).rightBottom ∈ (F.band b).support
    exact (F.band b).rightPath_range_subset_support ⟨0, (F.band b).rightPath.source⟩
  · change (F.band b).rightTop ∈ (F.band b).support
    exact (F.band b).rightPath_range_subset_support ⟨1, (F.band b).rightPath.target⟩

theorem fourPortChartPoint_injective : Function.Injective (fourPortChartPoint F.band) := by
  rintro ⟨b, side, level⟩ ⟨c, side', level'⟩ hpoint
  by_cases hbc : b = c
  · subst c
    have hcorner := (F.band b).chartEmbedding.injective hpoint
    have hlabels : (side, level) = (side', level') :=
      fourPortCorner_pair_injective hcorner
    exact Prod.ext rfl hlabels
  · have hdisjoint := Set.disjoint_left.mp (F.support_pairwise hbc)
    have hbmem := F.fourPortChartPoint_mem_support (b, side, level)
    have hcmem := F.fourPortChartPoint_mem_support (c, side', level')
    exact False.elim <| hdisjoint hbmem (hpoint.symm ▸ hcmem)

theorem booleanFourPortLocalEndpointPaths_injective
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Function.Injective
      ((booleanFourPortLocalEndpointPaths F.band choice).path e) := by
  rcases e with ⟨b, edge⟩
  change Function.Injective (booleanFourPortLocalPath F.band choice (b, edge))
  unfold booleanFourPortLocalPath
  simp only
  by_cases hb : choice b = true
  · rw [dif_pos hb]
    exact Fin.cases
      (by simpa only [Fin.cases_zero, Path.cast_coe] using
        (F.band b).bottomPath_injective)
      (fun edge : Fin 1 ↦ Fin.cases
        (by simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using
          (F.band b).topPath_injective)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge
  · rw [dif_neg hb]
    exact Fin.cases
      (by simpa only [Fin.cases_zero, Path.cast_coe] using
        (F.band b).leftPath_injective)
      (fun edge : Fin 1 ↦ Fin.cases
        (by simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using
          (F.band b).rightPath_injective)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge

theorem booleanFourPortLocalEndpointPaths_range_subset_support
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) ⊆
      (F.band e.1).support := by
  rcases e with ⟨b, edge⟩
  change Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path
      ((b, edge) : FourPortLocalEdge n)) ⊆ (F.band b).support
  change Set.range (booleanFourPortLocalPath F.band choice (b, edge)) ⊆
    (F.band b).support
  unfold booleanFourPortLocalPath
  simp only
  by_cases hb : choice b = true
  · rw [dif_pos hb]
    exact Fin.cases
      (by simpa only [Fin.cases_zero, Path.cast_coe] using
        (F.band b).bottomPath_range_subset_support)
      (fun edge : Fin 1 ↦ Fin.cases
        (by simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using
          (F.band b).topPath_range_subset_support)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge
  · rw [dif_neg hb]
    exact Fin.cases
      (by simpa only [Fin.cases_zero, Path.cast_coe] using
        (F.band b).leftPath_range_subset_support)
      (fun edge : Fin 1 ↦ Fin.cases
        (by simpa only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe] using
          (F.band b).rightPath_range_subset_support)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge

/-- If every chart lies on the transported torus, then so does every selected local path. -/
theorem booleanFourPortLocalEndpointPaths_range_subset_transportedTorus
    {Phi : AmbientIsotopy}
    (hchart : ∀ b z, (F.band b).chart z ∈ transportedTorus Phi)
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) ⊆
      transportedTorus Phi := by
  rcases e with ⟨b, edge⟩
  change Set.range (booleanFourPortLocalPath F.band choice (b, edge)) ⊆
    transportedTorus Phi
  unfold booleanFourPortLocalPath
  simp only
  by_cases hb : choice b = true
  · rw [dif_pos hb]
    exact Fin.cases
      (by
        rintro x ⟨t, rfl⟩
        simp only [Fin.cases_zero]
        rw [Path.cast_coe]
        change (F.band b).chart (bandBottomPath t) ∈ transportedTorus Phi
        exact hchart b (bandBottomPath t))
      (fun edge : Fin 1 ↦ Fin.cases
        (by
          rintro x ⟨t, rfl⟩
          simp only [Fin.cases_succ, Fin.cases_zero]
          rw [Path.cast_coe]
          change (F.band b).chart (bandTopPath t) ∈ transportedTorus Phi
          exact hchart b (bandTopPath t))
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge
  · rw [dif_neg hb]
    exact Fin.cases
      (by
        rintro x ⟨t, rfl⟩
        simp only [Fin.cases_zero]
        rw [Path.cast_coe]
        change (F.band b).chart (bandLeftPath t) ∈ transportedTorus Phi
        exact hchart b (bandLeftPath t))
      (fun edge : Fin 1 ↦ Fin.cases
        (by
          rintro x ⟨t, rfl⟩
          simp only [Fin.cases_succ, Fin.cases_zero]
          rw [Path.cast_coe]
          change (F.band b).chart (bandRightPath t) ∈ transportedTorus Phi
          exact hchart b (bandRightPath t))
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge

theorem booleanFourPortLocalEndpointPaths_pairwise
    (choice : Fin n → Bool) : Pairwise fun e f : FourPortLocalEdge n ↦
    Disjoint
      (Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e))
      (Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path f)) := by
  rintro ⟨b, edge⟩ ⟨c, edge'⟩ hedge
  by_cases hbc : b = c
  · subst c
    have he : edge ≠ edge' := fun h ↦ hedge (Prod.ext rfl h)
    fin_cases edge <;> fin_cases edge'
    · exact False.elim (he rfl)
    · by_cases hb : choice b = true
      · change Disjoint
          (Set.range (booleanFourPortLocalPath F.band choice (b, 0)))
          (Set.range (booleanFourPortLocalPath F.band choice (b, 1)))
        unfold booleanFourPortLocalPath
        simpa only [Prod.casesOn, dif_pos hb, finTwo_one_eq_succ_zero,
          Fin.cases_zero,
          Fin.cases_succ, Path.cast_coe] using
          (F.band b).bottomPath_disjoint_topPath
      · change Disjoint
          (Set.range (booleanFourPortLocalPath F.band choice (b, 0)))
          (Set.range (booleanFourPortLocalPath F.band choice (b, 1)))
        unfold booleanFourPortLocalPath
        simpa only [Prod.casesOn, dif_neg hb, finTwo_one_eq_succ_zero,
          Fin.cases_zero,
          Fin.cases_succ, Path.cast_coe] using
          (F.band b).leftPath_disjoint_rightPath
    · by_cases hb : choice b = true
      · change Disjoint
          (Set.range (booleanFourPortLocalPath F.band choice (b, 1)))
          (Set.range (booleanFourPortLocalPath F.band choice (b, 0)))
        unfold booleanFourPortLocalPath
        simpa only [Prod.casesOn, dif_pos hb, finTwo_one_eq_succ_zero,
          Fin.cases_zero,
          Fin.cases_succ, Path.cast_coe] using
          (F.band b).bottomPath_disjoint_topPath.symm
      · change Disjoint
          (Set.range (booleanFourPortLocalPath F.band choice (b, 1)))
          (Set.range (booleanFourPortLocalPath F.band choice (b, 0)))
        unfold booleanFourPortLocalPath
        simpa only [Prod.casesOn, dif_neg hb, finTwo_one_eq_succ_zero,
          Fin.cases_zero,
          Fin.cases_succ, Path.cast_coe] using
          (F.band b).leftPath_disjoint_rightPath.symm
    · exact False.elim (he rfl)
  · exact (F.support_pairwise hbc).mono
      (F.booleanFourPortLocalEndpointPaths_range_subset_support choice (b, edge))
      (F.booleanFourPortLocalEndpointPaths_range_subset_support choice (c, edge'))

end FinitePairedSeamBandCharts
end Submission.Topology
