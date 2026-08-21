import Submission.Topology.BooleanFourPortOutsidePaths
import Submission.Topology.FiniteAlternatingArcCycleCut

/-!
# Cutting a Boolean four-port component at one local edge

Swapping the two colours makes a selected local four-port edge the first edge of its alternating
component.  The specified-edge cut then returns the complete outside route complementary to that
local edge, with embedded-circle data derived from the existing exact incidence package.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}

namespace BooleanFourPortOutsidePathData

variable (D : BooleanFourPortOutsidePathData Phi F)

/-- Orient the local matching first and the fixed outside matching second. -/
abbrev localFirstSystem (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem (FourPortVertex n) :=
  (D.system choice).swap

/-- The local paths and fixed outside paths retain exact incidence after exchanging colours. -/
theorem localFirstIncidence (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData
      (D.localFirstSystem choice) (fourPortChartPoint F.band)
        (booleanFourPortLocalEndpointPaths F.band choice) D.paths :=
  (D.incidence choice).swap

/-- The zero endpoint of one selected local edge. -/
def localEdgeStart (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    FourPortVertex n :=
  (fourPortLocalPairing choice).endpointEquiv (e, 0)

/-- The full outside route complementary to one selected local edge. -/
def localEdgeComplementPath (choice : Fin n → Bool) (e : FourPortLocalEdge n) :=
  (FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (A := D.localFirstSystem choice)
      (booleanFourPortLocalEndpointPaths F.band choice) D.paths).complementPathAt
    (localEdgeStart choice e)

/-- The canonically oriented selected local edge. -/
def localEdgePath (choice : Fin n → Bool) (e : FourPortLocalEdge n) :=
  (FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (A := D.localFirstSystem choice)
      (booleanFourPortLocalEndpointPaths F.band choice) D.paths).firstPathAt
    (localEdgeStart choice e)

@[simp] theorem localEdgePath_apply
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) (t : unitInterval) :
    D.localEdgePath choice e t =
      (booleanFourPortLocalEndpointPaths F.band choice).path e t := by
  change (booleanFourPortLocalEndpointPaths F.band choice).orientedPath
      ((fourPortLocalPairing choice).endpointEquiv (e, 0)) t = _
  exact
    FiniteAlternatingEndpointSystem.EndpointPathFamily.orientedPath_endpointEquiv_zero_apply
      (booleanFourPortLocalEndpointPaths F.band choice) e t

theorem range_localEdgePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgePath choice e) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) := by
  exact congrArg Set.range (funext (D.localEdgePath_apply choice e))

/-- One local edge glued to its entire outside complement. -/
def localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) : Circle → R3 :=
  TwoArcCircle.circleMap (D.localEdgePath choice e) (D.localEdgeComplementPath choice e)

/-- Exact constituent incidence makes the cut local-edge circle embedded. -/
theorem localEdgeTwoArcData (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    TwoArcCircle.Data (D.localEdgePath choice e) (D.localEdgeComplementPath choice e) := by
  exact (D.localFirstIncidence choice).twoArcDataAt (localEdgeStart choice e)

theorem continuous_localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Continuous (D.localEdgeCircle choice e) :=
  TwoArcCircle.continuous_circleMap _ _

theorem localEdgeCircle_injective (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Function.Injective (D.localEdgeCircle choice e) :=
  (D.localEdgeTwoArcData choice e).injective

/-- The cut circle has exactly the selected local edge and its complementary outside route. -/
theorem range_localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) ∪
        Set.range (D.localEdgeComplementPath choice e) := by
  rw [localEdgeCircle, TwoArcCircle.range_circleMap, D.range_localEdgePath]

/-- A specified-edge circle is contained in its quotient-cycle edge carrier. -/
theorem range_localEdgeCircle_subset_cycleEdgeCarrier
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) ⊆
      FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
        (D.localFirstSystem choice) (fourPortChartPoint F.band)
        (booleanFourPortLocalEndpointPaths F.band choice) D.paths
        ((D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)) := by
  rw [D.range_localEdgeCircle choice e, ← D.range_localEdgePath choice e]
  exact (D.localFirstIncidence choice)
    |>.range_firstPathAt_union_complementPathAt_subset_cycleEdgeCarrier
      (localEdgeStart choice e)

/-- The same cut circle lies in the corresponding quotient carrier before swapping edge
colours. -/
theorem range_localEdgeCircle_subset_originalCycleEdgeCarrier
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) ⊆
      FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
        (D.system choice) (fourPortChartPoint F.band) D.paths
        (booleanFourPortLocalEndpointPaths F.band choice)
        ((D.system choice).swapCycleEquiv <|
          (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)) := by
  rw [← (D.incidence choice).cycleEdgeCarrier_swap]
  exact D.range_localEdgeCircle_subset_cycleEdgeCarrier choice e

/-- The specified-edge circle is contained in the canonical quotient circle of the unswapped
finite section. -/
theorem range_localEdgeCircle_subset_circleSection
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) ⊆
      Set.range ((D.circleSection choice).circle
        ((D.system choice).swapCycleEquiv <|
          (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e))).circle := by
  intro x hx
  have hx' := D.range_localEdgeCircle_subset_originalCycleEdgeCarrier choice e hx
  rw [← (D.incidence choice).range_circleMap_eq_cycleEdgeCarrier] at hx'
  obtain ⟨z, rfl⟩ := hx'
  exact ⟨z, (D.circleSection_circle_apply choice _ z).symm⟩

/-- The selected edge meets its complementary route only at its two endpoints. -/
theorem range_localEdgePath_inter_complementPath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgePath choice e) ∩
        Set.range (D.localEdgeComplementPath choice e) =
      {fourPortChartPoint F.band (localEdgeStart choice e),
        fourPortChartPoint F.band
          ((D.localFirstSystem choice).first.endpointMate (localEdgeStart choice e))} := by
  exact (D.localFirstIncidence choice).firstPathAt_inter_complementPathAt
    (localEdgeStart choice e)

/-- Updating a different band does not change a local path. -/
theorem localPath_update_of_ne
    (choice : Fin n → Bool) {b c : Fin n} (hcb : c ≠ b) (edge : Fin 2) :
    ∀ t, (booleanFourPortLocalEndpointPaths F.band (Function.update choice b true)).path
        (c, edge) t =
      (booleanFourPortLocalEndpointPaths F.band choice).path (c, edge) t := by
  intro t
  unfold booleanFourPortLocalEndpointPaths booleanFourPortLocalPath
  simp only [Function.update_of_ne hcb]
  by_cases hc : choice c = true
  · rw [dif_pos hc, dif_pos hc]
    exact Fin.cases
      (by simp only [Fin.cases_zero, Path.cast_coe])
      (fun edge1 : Fin 1 ↦ Fin.cases
        (by simp only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe])
        (fun edge0 : Fin 0 ↦ Fin.elim0 edge0) edge1)
      edge
  · rw [dif_neg hc, dif_neg hc]
    exact Fin.cases
      (by simp only [Fin.cases_zero, Path.cast_coe])
      (fun edge1 : Fin 1 ↦ Fin.cases
        (by simp only [Fin.cases_succ, Fin.cases_zero, Path.cast_coe])
        (fun edge0 : Fin 0 ↦ Fin.elim0 edge0) edge1)
      edge

/-- Every labelled corner lies on the vertical resolution when the bit is false. -/
theorem chartPoint_mem_ambientSection_of_false
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = false)
    (side level : Fin 2) :
    fourPortChartPoint F.band (b, side, level) ∈ D.ambientSection choice := by
  rw [D.ambientSection_eq_iUnion_ranges choice]
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨(b, side), ?_⟩
  fin_cases level
  · refine ⟨0, ?_⟩
    simp [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb]
  · refine ⟨1, ?_⟩
    simp [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb]

/-- Every labelled corner lies on the horizontal resolution when the bit is true. -/
theorem chartPoint_mem_ambientSection_of_true
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = true)
    (side level : Fin 2) :
    fourPortChartPoint F.band (b, side, level) ∈ D.ambientSection choice := by
  rw [D.ambientSection_eq_iUnion_ranges choice]
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨(b, level), ?_⟩
  fin_cases side
  · refine ⟨0, ?_⟩
    simp [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb]
  · refine ⟨1, ?_⟩
    simp [booleanFourPortLocalEndpointPaths, booleanFourPortLocalPath, hb]

private theorem update_localEdge_eq_of_cycle_eq
    (choice : Fin n → Bool) (b : Fin n)
    (hdistinct :
      (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          (localEdgeStart (Function.update choice b true) (b, 0)) ≠
        (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          (localEdgeStart (Function.update choice b true) (b, 1)))
    {edge level : Fin 2}
    (hcycle :
      (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          ((D.localFirstSystem (Function.update choice b true)).first.endpointEquiv
            ((b, edge), 0)) =
        (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          (localEdgeStart (Function.update choice b true) (b, level))) :
    edge = level := by
  fin_cases edge <;> fin_cases level
  · rfl
  · exact False.elim (hdistinct hcycle)
  · exact False.elim (hdistinct hcycle.symm)
  · rfl

/-- If the two post-flip local edges lie in distinct cycles, either complementary post route
already belongs to the pre-flip carrier. -/
theorem range_update_localEdgeComplementPath_subset_ambientSection
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = false)
    (hdistinct :
      (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          (localEdgeStart (Function.update choice b true) (b, 0)) ≠
        (D.localFirstSystem (Function.update choice b true)).cycleOfVertex
          (localEdgeStart (Function.update choice b true) (b, 1)))
    (level : Fin 2) :
    Set.range (D.localEdgeComplementPath (Function.update choice b true) (b, level)) ⊆
      D.ambientSection choice := by
  classical
  let next := Function.update choice b true
  let A := D.localFirstSystem next
  let q := A.cycleOfVertex (localEdgeStart next (b, level))
  intro x hx
  change x ∈ Set.range (D.localEdgeComplementPath next (b, level)) at hx
  have hxCarrier : x ∈
      FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier A
      (fourPortChartPoint F.band) (booleanFourPortLocalEndpointPaths F.band next)
      D.paths q := by
    apply D.range_localEdgeCircle_subset_cycleEdgeCarrier next (b, level)
    rw [D.range_localEdgeCircle]
    exact Or.inr hx
  simp only [FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier,
    Set.mem_union, Set.mem_iUnion] at hxCarrier
  rcases hxCarrier with ⟨⟨c, edge⟩, hxLocal⟩ | ⟨e, hxOutside⟩
  · by_cases hcycle : A.cycleOfVertex
        (A.first.endpointEquiv ((c, edge), 0)) = q
    · rw [if_pos hcycle] at hxLocal
      by_cases hcb : c = b
      · subst c
        have hedge : edge = level :=
          D.update_localEdge_eq_of_cycle_eq choice b hdistinct hcycle
        subst edge
        have hxFirst : x ∈ Set.range (D.localEdgePath next (b, level)) := by
          rw [D.range_localEdgePath]
          exact hxLocal
        have hxEndpoints := Set.mem_inter hxFirst hx
        rw [D.range_localEdgePath_inter_complementPath] at hxEndpoints
        rcases hxEndpoints with hxStart | hxMate
        · have hvalue : x = fourPortChartPoint F.band (b, 0, level) := by
            simpa [next, localEdgeStart, fourPortLocalEndpointEquiv_true] using hxStart
          rw [hvalue]
          exact D.chartPoint_mem_ambientSection_of_false choice b hb 0 level
        · have hvalue : x = fourPortChartPoint F.band (b, 1, level) := by
            change x = fourPortChartPoint F.band
              ((fourPortLocalPairing next).endpointMate
                ((fourPortLocalPairing next).endpointEquiv ((b, level), 0))) at hxMate
            rw [(fourPortLocalPairing next).endpointMate_endpointEquiv,
              fourPortLocalEndpointEquiv_true (by simp [next])] at hxMate
            exact hxMate
          rw [hvalue]
          exact D.chartPoint_mem_ambientSection_of_false choice b hb 1 level
      · rw [D.ambientSection_eq_iUnion_ranges choice]
        apply Or.inr
        refine Set.mem_iUnion.mpr ⟨(c, edge), ?_⟩
        obtain ⟨t, rfl⟩ := hxLocal
        exact ⟨t, (localPath_update_of_ne (F := F) choice hcb edge t).symm⟩
    · rw [if_neg hcycle] at hxLocal
      exact hxLocal.elim
  · by_cases hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
    · rw [if_pos hcycle] at hxOutside
      rw [D.ambientSection_eq_iUnion_ranges choice]
      exact Or.inl (Set.mem_iUnion.mpr ⟨e, hxOutside⟩)
    · rw [if_neg hcycle] at hxOutside
      exact hxOutside.elim

/-- If the two pre-flip local edges lie in distinct cycles, either complementary pre route
already belongs to the post-flip carrier. -/
theorem range_localEdgeComplementPath_subset_update_ambientSection
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = false)
    (hdistinct :
      (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 0)) ≠
        (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice (b, 1)))
    (side : Fin 2) :
    Set.range (D.localEdgeComplementPath choice (b, side)) ⊆
      D.ambientSection (Function.update choice b true) := by
  classical
  let next := Function.update choice b true
  let A := D.localFirstSystem choice
  let q := A.cycleOfVertex (localEdgeStart choice (b, side))
  intro x hx
  have hxCarrier : x ∈
      FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier A
      (fourPortChartPoint F.band) (booleanFourPortLocalEndpointPaths F.band choice)
      D.paths q := by
    apply D.range_localEdgeCircle_subset_cycleEdgeCarrier choice (b, side)
    rw [D.range_localEdgeCircle]
    exact Or.inr hx
  simp only [FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier,
    Set.mem_union, Set.mem_iUnion] at hxCarrier
  rcases hxCarrier with ⟨⟨c, edge⟩, hxLocal⟩ | ⟨e, hxOutside⟩
  · by_cases hcycle : A.cycleOfVertex
        (A.first.endpointEquiv ((c, edge), 0)) = q
    · rw [if_pos hcycle] at hxLocal
      by_cases hcb : c = b
      · subst c
        have hedge : edge = side := by
          fin_cases edge <;> fin_cases side
          · rfl
          · exact False.elim (hdistinct hcycle)
          · exact False.elim (hdistinct hcycle.symm)
          · rfl
        subst edge
        have hxFirst : x ∈ Set.range (D.localEdgePath choice (b, side)) := by
          rw [D.range_localEdgePath]
          exact hxLocal
        have hxEndpoints := Set.mem_inter hxFirst hx
        rw [D.range_localEdgePath_inter_complementPath] at hxEndpoints
        rcases hxEndpoints with hxStart | hxMate
        · have hvalue : x = fourPortChartPoint F.band (b, side, 0) := by
            simpa [localEdgeStart, fourPortLocalEndpointEquiv_false hb] using hxStart
          rw [hvalue]
          exact D.chartPoint_mem_ambientSection_of_true next b (by simp [next]) side 0
        · have hvalue : x = fourPortChartPoint F.band (b, side, 1) := by
            change x = fourPortChartPoint F.band
              ((fourPortLocalPairing choice).endpointMate
                ((fourPortLocalPairing choice).endpointEquiv ((b, side), 0))) at hxMate
            rw [(fourPortLocalPairing choice).endpointMate_endpointEquiv,
              fourPortLocalEndpointEquiv_false hb] at hxMate
            exact hxMate
          rw [hvalue]
          exact D.chartPoint_mem_ambientSection_of_true next b (by simp [next]) side 1
      · rw [D.ambientSection_eq_iUnion_ranges next]
        apply Or.inr
        refine Set.mem_iUnion.mpr ⟨(c, edge), ?_⟩
        obtain ⟨t, rfl⟩ := hxLocal
        exact ⟨t, localPath_update_of_ne (F := F) choice hcb edge t⟩
    · rw [if_neg hcycle] at hxLocal
      exact hxLocal.elim
  · by_cases hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
    · rw [if_pos hcycle] at hxOutside
      rw [D.ambientSection_eq_iUnion_ranges next]
      exact Or.inl (Set.mem_iUnion.mpr ⟨e, hxOutside⟩)
    · rw [if_neg hcycle] at hxOutside
      exact hxOutside.elim
end BooleanFourPortOutsidePathData
end Submission.Topology
