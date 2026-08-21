import Submission.Topology.BooleanFourPortCrossIncidence
import Submission.Topology.BooleanFourPortCycleCut

/-!
# Incidence of vertical sides with distinct horizontal child cycles

If the two horizontal local edges belong to distinct quotient cycles, each vertical side meets
each complete child carrier only at their labelled common corner.
-/

open Set

noncomputable section

namespace Submission.Topology
namespace BooleanFourPortOutsidePathData

open FiniteAlternatingEndpointSystem
open LeanEval.KnotTheory.PardonDistortion

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}
  (D : BooleanFourPortOutsidePathData Phi F)

private theorem trueLocalEndpoint_cycle_eq_start
    (choice : Fin n → Bool) {b : Fin n} (hb : choice b = true)
    (side level : Fin 2) :
    (D.localFirstSystem choice).cycleOfVertex (b, side, level) =
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, level)) := by
  fin_cases side
  · simp [localEdgeStart, fourPortLocalEndpointEquiv_true hb]
  · have hedge := (D.localFirstSystem choice).first_edge_endpoints_same_cycle (b, level)
    change (D.localFirstSystem choice).cycleOfVertex
        (fourPortLocalEndpointEquiv choice ((b, level), 1)) =
      (D.localFirstSystem choice).cycleOfVertex
        (fourPortLocalEndpointEquiv choice ((b, level), 0)) at hedge
    simpa [localEdgeStart, fourPortLocalEndpointEquiv_true hb] using hedge

private theorem localEdge_cycle_ne_of_other
    (choice : Fin n → Bool) {b : Fin n}
    (hdistinct :
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 0)) ≠
        (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 1)))
    {j level : Fin 2}
    (hne : j ≠ level) :
    (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, j)) ≠
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, level)) := by
  fin_cases j <;> fin_cases level
  · exact (hne rfl).elim
  · exact hdistinct
  · exact hdistinct.symm
  · exact (hne rfl).elim

/-- A vertical side meets one distinct horizontal child carrier at exactly their common port. -/
theorem range_falseLocalPath_inter_trueCycleEdgeCarrier
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1)))
    (side level : Fin 2) :
    Set.range ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, side)) ∩
        ClosedArcIncidenceData.cycleEdgeCarrier
          (D.localFirstSystem trueChoice) (fourPortChartPoint F.band)
          (booleanFourPortLocalEndpointPaths F.band trueChoice) D.paths
          ((D.localFirstSystem trueChoice).cycleOfVertex
            (localEdgeStart trueChoice (b, level))) =
      {fourPortChartPoint F.band (b, side, level)} := by
  classical
  let A := D.localFirstSystem trueChoice
  let point := fourPortChartPoint F.band
  let q := A.cycleOfVertex (localEdgeStart trueChoice (b, level))
  let vertical := (booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, side)
  apply Set.Subset.antisymm
  · rintro x ⟨hxVertical, hxCarrier⟩
    change x ∈ ClosedArcIncidenceData.cycleEdgeCarrier A point
      (booleanFourPortLocalEndpointPaths F.band trueChoice) D.paths q at hxCarrier
    simp only [ClosedArcIncidenceData.cycleEdgeCarrier, Set.mem_union,
      Set.mem_iUnion] at hxCarrier
    rcases hxCarrier with ⟨⟨c, edge⟩, hxLocal⟩ | ⟨e, hxOutside⟩
    · by_cases hcycle : A.cycleOfVertex
          (A.first.endpointEquiv ((c, edge), 0)) = q
      · rw [if_pos hcycle] at hxLocal
        by_cases hcb : c = b
        · subst c
          have hedge : edge = level := by
            by_contra hne
            apply D.localEdge_cycle_ne_of_other trueChoice hdistinct hne
            have hstart : A.first.endpointEquiv ((b, edge), 0) =
                localEdgeStart trueChoice (b, edge) := rfl
            rwa [hstart] at hcycle
          subst edge
          have hx := Set.mem_inter hxVertical hxLocal
          change x ∈ Set.range (booleanFourPortLocalPath F.band falseChoice (b, side)) ∩
            Set.range (booleanFourPortLocalPath F.band trueChoice (b, level)) at hx
          rw [range_falseLocalPath_inter_trueLocalPath F.band falseChoice trueChoice
            b hfalse htrue side level] at hx
          exact hx
        · have hxFalseSupport := F.booleanFourPortLocalEndpointPaths_range_subset_support
            falseChoice (b, side) hxVertical
          have hxTrueSupport := F.booleanFourPortLocalEndpointPaths_range_subset_support
            trueChoice (c, edge) hxLocal
          exact False.elim <| Set.disjoint_left.mp (F.support_pairwise hcb)
            hxTrueSupport hxFalseSupport
      · rw [if_neg hcycle] at hxLocal
        exact hxLocal.elim
    · by_cases hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
      · rw [if_pos hcycle] at hxOutside
        change D.outside.edge at e
        change A.cycleOfVertex (D.outside.endpointEquiv (e, 0)) = q at hcycle
        have hxCross := Set.mem_inter hxOutside hxVertical
        change x ∈ Set.range (D.paths.path e) ∩
          Set.range (booleanFourPortLocalPath F.band falseChoice (b, side)) at hxCross
        have hcross := D.cross_intersection falseChoice
          e (b, side)
        change Set.range (D.paths.path e) ∩
          Set.range (booleanFourPortLocalPath F.band falseChoice (b, side)) = _ at hcross
        rw [hcross] at hxCross
        obtain ⟨v, hv, rfl⟩ := hxCross
        obtain ⟨j, hj⟩ := hv.2
        have hvValue : v = (b, side, j) := by
          calc
            v = (fourPortLocalPairing falseChoice).endpointEquiv ((b, side), j) := hj.symm
            _ = (b, side, j) := fourPortLocalEndpointEquiv_false hfalse side j
        subst v
        obtain ⟨k, hk⟩ := hv.1
        have houtsideCycle : A.cycleOfVertex (b, side, j) = q := by
          calc
            A.cycleOfVertex (b, side, j) =
                A.cycleOfVertex (D.outside.endpointEquiv (e, 0)) := by
              fin_cases k
              · have hk0 : D.outside.endpointEquiv (e, (0 : Fin 2)) =
                    (fourPortLocalPairing falseChoice).endpointEquiv
                      ((b, side), j) := by
                  convert hk using 1
                  apply congrArg (fun z : Fin 2 ↦ D.outside.endpointEquiv (e, z))
                  apply Fin.ext
                  rfl
                simpa only [fourPortLocalEndpointEquiv_false hfalse] using
                  congrArg A.cycleOfVertex hk0.symm
              · have hedge := A.second_edge_endpoints_same_cycle e
                change A.cycleOfVertex (D.outside.endpointEquiv (e, 1)) =
                  A.cycleOfVertex (D.outside.endpointEquiv (e, 0)) at hedge
                have hk1 : D.outside.endpointEquiv (e, (1 : Fin 2)) =
                    (fourPortLocalPairing falseChoice).endpointEquiv
                      ((b, side), j) := by
                  convert hk using 1
                  apply congrArg (fun z : Fin 2 ↦ D.outside.endpointEquiv (e, z))
                  apply Fin.ext
                  rfl
                exact (by
                  simpa only [fourPortLocalEndpointEquiv_false hfalse] using
                    (congrArg A.cycleOfVertex hk1).symm.trans hedge)
            _ = q := hcycle
        have hjLevel : j = level := by
          by_contra hne
          apply D.localEdge_cycle_ne_of_other trueChoice hdistinct hne
          calc
            A.cycleOfVertex (localEdgeStart trueChoice (b, j)) =
                A.cycleOfVertex (b, side, j) :=
              (D.trueLocalEndpoint_cycle_eq_start trueChoice htrue side j).symm
            _ = q := houtsideCycle
            _ = A.cycleOfVertex (localEdgeStart trueChoice (b, level)) := rfl
        subst j
        rw [hvValue]
        exact Set.mem_singleton _
      · rw [if_neg hcycle] at hxOutside
        exact hxOutside.elim
  · rintro x rfl
    constructor
    · change fourPortChartPoint F.band (b, side, level) ∈ Set.range vertical
      fin_cases level
      · refine ⟨0, ?_⟩
        simp [vertical, fourPortLocalEndpointEquiv_false hfalse]
      · refine ⟨1, ?_⟩
        simp [vertical, fourPortLocalEndpointEquiv_false hfalse]
    · change fourPortChartPoint F.band (b, side, level) ∈
        ClosedArcIncidenceData.cycleEdgeCarrier A point
          (booleanFourPortLocalEndpointPaths F.band trueChoice) D.paths q
      simp only [ClosedArcIncidenceData.cycleEdgeCarrier, Set.mem_union,
        Set.mem_iUnion]
      left
      refine ⟨(b, level), ?_⟩
      have hcycle : A.cycleOfVertex (A.first.endpointEquiv ((b, level), 0)) = q := by
        simp only [A, q, localFirstSystem]
        rfl
      rw [if_pos hcycle]
      fin_cases side
      · refine ⟨0, ?_⟩
        calc
          (booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, level) 0 =
              fourPortChartPoint F.band
                ((fourPortLocalPairing trueChoice).endpointEquiv ((b, level), 0)) :=
            ((booleanFourPortLocalEndpointPaths F.band trueChoice).path
              (b, level)).source
          _ = fourPortChartPoint F.band (b, 0, level) := by
            rw [fourPortLocalEndpointEquiv_true htrue]
      · refine ⟨1, ?_⟩
        calc
          (booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, level) 1 =
              fourPortChartPoint F.band
                ((fourPortLocalPairing trueChoice).endpointEquiv ((b, level), 1)) :=
            ((booleanFourPortLocalEndpointPaths F.band trueChoice).path
              (b, level)).target
          _ = fourPortChartPoint F.band (b, 1, level) := by
            rw [fourPortLocalEndpointEquiv_true htrue]

/-- A vertical side meets the complete horizontal child circle only at their common port. -/
theorem range_falseLocalPath_inter_trueLocalEdgeCircle
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1)))
    (side level : Fin 2) :
    Set.range ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, side)) ∩
        Set.range (D.localEdgeCircle trueChoice (b, level)) =
      {fourPortChartPoint F.band (b, side, level)} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxCarrier : x ∈
        ClosedArcIncidenceData.cycleEdgeCarrier
          (D.localFirstSystem trueChoice) (fourPortChartPoint F.band)
          (booleanFourPortLocalEndpointPaths F.band trueChoice) D.paths
          ((D.localFirstSystem trueChoice).cycleOfVertex
            (localEdgeStart trueChoice (b, level))) :=
      D.range_localEdgeCircle_subset_cycleEdgeCarrier trueChoice (b, level) hx.2
    have hx' := Set.mem_inter hx.1 hxCarrier
    rwa [D.range_falseLocalPath_inter_trueCycleEdgeCarrier falseChoice trueChoice
      b hfalse htrue hdistinct side level] at hx'
  · rw [← range_falseLocalPath_inter_trueLocalPath F.band falseChoice trueChoice
      b hfalse htrue side level]
    rintro x ⟨hxFalse, hxTrue⟩
    refine ⟨hxFalse, ?_⟩
    rw [D.range_localEdgeCircle trueChoice (b, level)]
    exact Or.inl hxTrue

end BooleanFourPortOutsidePathData
end Submission.Topology
