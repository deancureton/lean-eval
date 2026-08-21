import Submission.Topology.BooleanFourPortChildCarrierIncidence
import Submission.Topology.FourPortSixEdgePathSystemConstructor
import Submission.Topology.FourPortSixEdgeSubtype

/-!
# The conditional six-edge graph of one Boolean four-port flip

When the two horizontal edges of the resolved endpoint lie in distinct quotient cycles, the
vertical unresolved edges and the two complete horizontal child circles form the canonical
six-edge split graph.
-/

open Set

noncomputable section

namespace Submission.Topology
namespace BooleanFourPortOutsidePathData

open FiniteAlternatingEndpointSystem
open LeanEval.KnotTheory.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}
  (D : BooleanFourPortOutsidePathData Phi F)

private theorem falseLeft_source_eq
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing falseChoice).endpointEquiv ((b, 0), 0) =
      localEdgeStart trueChoice (b, 0) := by
  simp [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem falseLeft_target_eq
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing falseChoice).endpointEquiv ((b, 0), 1) =
      localEdgeStart trueChoice (b, 1) := by
  simp [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem falseRight_source_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing falseChoice).endpointEquiv ((b, 1), 0) =
      (D.localFirstSystem trueChoice).first.endpointMate
        (localEdgeStart trueChoice (b, 0)) := by
  change _ = (fourPortLocalPairing trueChoice).endpointMate
    (localEdgeStart trueChoice (b, 0))
  rw [localEdgeStart, (fourPortLocalPairing trueChoice).endpointMate_endpointEquiv]
  simp [fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem falseRight_target_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing falseChoice).endpointEquiv ((b, 1), 1) =
      (D.localFirstSystem trueChoice).first.endpointMate
        (localEdgeStart trueChoice (b, 1)) := by
  change _ = (fourPortLocalPairing trueChoice).endpointMate
    (localEdgeStart trueChoice (b, 1))
  rw [localEdgeStart, (fourPortLocalPairing trueChoice).endpointMate_endpointEquiv]
  simp [fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem trueRightPoint_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (trueChoice : Fin n → Bool) (b : Fin n) (htrue : trueChoice b = true)
    (level : Fin 2) :
    (D.localFirstSystem trueChoice).first.endpointMate
        (localEdgeStart trueChoice (b, level)) = (b, 1, level) := by
  change (fourPortLocalPairing trueChoice).endpointMate
      ((fourPortLocalPairing trueChoice).endpointEquiv ((b, level), 0)) = _
  rw [(fourPortLocalPairing trueChoice).endpointMate_endpointEquiv]
  simpa using fourPortLocalEndpointEquiv_true htrue level 1

private def falseLeftPath
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Path
      (fourPortChartPoint F.band (localEdgeStart trueChoice (b, 0)))
      (fourPortChartPoint F.band (localEdgeStart trueChoice (b, 1))) :=
  ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, 0)).cast
    (congrArg (fourPortChartPoint F.band)
      (falseLeft_source_eq falseChoice trueChoice b hfalse htrue).symm)
    (congrArg (fourPortChartPoint F.band)
      (falseLeft_target_eq falseChoice trueChoice b hfalse htrue).symm)

private def falseRightPath
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Path
      (fourPortChartPoint F.band
        ((D.localFirstSystem trueChoice).first.endpointMate
          (localEdgeStart trueChoice (b, 0))))
      (fourPortChartPoint F.band
        ((D.localFirstSystem trueChoice).first.endpointMate
          (localEdgeStart trueChoice (b, 1)))) :=
  ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, 1)).cast
    (congrArg (fourPortChartPoint F.band)
      (D.falseRight_source_eq falseChoice trueChoice b hfalse htrue).symm)
    (congrArg (fourPortChartPoint F.band)
      (D.falseRight_target_eq falseChoice trueChoice b hfalse htrue).symm)

private theorem range_falseLeftPath
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Set.range (falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, 0)) :=
  congrArg Set.range (Path.cast_coe _ _ _)

private theorem range_falseRightPath
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Set.range (D.falseRightPath falseChoice trueChoice b hfalse htrue) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band falseChoice).path (b, 1)) :=
  congrArg Set.range (Path.cast_coe _ _ _)

/-- The canonical six-edge split graph at one false-to-true Boolean band flip. -/
noncomputable def sixEdgeConstituentData
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1))) :
    FourPortSixEdgeConstituentData (X := R3) where
  leftBottom := fourPortChartPoint F.band (localEdgeStart trueChoice (b, 0))
  leftTop := fourPortChartPoint F.band (localEdgeStart trueChoice (b, 1))
  rightBottom := fourPortChartPoint F.band
    ((D.localFirstSystem trueChoice).first.endpointMate
      (localEdgeStart trueChoice (b, 0)))
  rightTop := fourPortChartPoint F.band
    ((D.localFirstSystem trueChoice).first.endpointMate
      (localEdgeStart trueChoice (b, 1)))
  left := falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue
  right := D.falseRightPath falseChoice trueChoice b hfalse htrue
  bottom := D.localEdgePath trueChoice (b, 0)
  top := D.localEdgePath trueChoice (b, 1)
  bottomOutside := D.localEdgeComplementPath trueChoice (b, 0)
  topOutside := D.localEdgeComplementPath trueChoice (b, 1)
  bottomData := D.localEdgeTwoArcData trueChoice (b, 0)
  topData := D.localEdgeTwoArcData trueChoice (b, 1)
  left_injective := by
    simpa only [falseLeftPath, Path.cast_coe] using
      F.booleanFourPortLocalEndpointPaths_injective falseChoice (b, 0)
  right_injective := by
    simpa only [falseRightPath, Path.cast_coe] using
      F.booleanFourPortLocalEndpointPaths_injective falseChoice (b, 1)
  left_disjoint_right := by
    rw [range_falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_falseRightPath falseChoice trueChoice b hfalse htrue]
    exact F.booleanFourPortLocalEndpointPaths_pairwise falseChoice (by simp)
  children_disjoint := by
    rw [D.range_localEdgePath trueChoice (b, 0),
      D.range_localEdgePath trueChoice (b, 1),
      ← D.range_localEdgeCircle trueChoice (b, 0),
      ← D.range_localEdgeCircle trueChoice (b, 1)]
    have hcarrier := (D.localFirstIncidence trueChoice).cycleEdgeCarrier_disjoint hdistinct
    exact hcarrier.mono
      (D.range_localEdgeCircle_subset_cycleEdgeCarrier trueChoice (b, 0))
      (D.range_localEdgeCircle_subset_cycleEdgeCarrier trueChoice (b, 1))
  left_inter_bottom := by
    rw [range_falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath trueChoice (b, 0),
      ← D.range_localEdgeCircle trueChoice (b, 0)]
    simpa [localEdgeStart, fourPortLocalEndpointEquiv_true htrue] using
      D.range_falseLocalPath_inter_trueLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 0 0
  right_inter_bottom := by
    rw [D.range_falseRightPath falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath trueChoice (b, 0),
      ← D.range_localEdgeCircle trueChoice (b, 0)]
    simpa only [D.trueRightPoint_eq trueChoice b htrue 0] using
      D.range_falseLocalPath_inter_trueLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 1 0
  left_inter_top := by
    rw [range_falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath trueChoice (b, 1),
      ← D.range_localEdgeCircle trueChoice (b, 1)]
    simpa [localEdgeStart, fourPortLocalEndpointEquiv_true htrue] using
      D.range_falseLocalPath_inter_trueLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 0 1
  right_inter_top := by
    rw [D.range_falseRightPath falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath trueChoice (b, 1),
      ← D.range_localEdgeCircle trueChoice (b, 1)]
    simpa only [D.trueRightPoint_eq trueChoice b htrue 1] using
      D.range_falseLocalPath_inter_trueLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 1 1

/-- The canonical six-edge path system at one split flip. -/
noncomputable def sixEdgePathSystem
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1))) :
    FourPortSixEdgePathSystem R3 :=
  (D.sixEdgeConstituentData falseChoice trueChoice b hfalse htrue hdistinct)
    |>.toFourPortSixEdgePathSystem

private theorem trueBottom_source_eq
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing trueChoice).endpointEquiv ((b, 0), 0) =
      localEdgeStart falseChoice (b, 0) := by
  simp [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem trueBottom_target_eq
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing trueChoice).endpointEquiv ((b, 0), 1) =
      localEdgeStart falseChoice (b, 1) := by
  simp [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse,
    fourPortLocalEndpointEquiv_true htrue]

private theorem falseUpperPoint_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice : Fin n → Bool) (b : Fin n) (hfalse : falseChoice b = false)
    (side : Fin 2) :
    (D.localFirstSystem falseChoice).first.endpointMate
        (localEdgeStart falseChoice (b, side)) = (b, side, 1) := by
  change (fourPortLocalPairing falseChoice).endpointMate
      ((fourPortLocalPairing falseChoice).endpointEquiv ((b, side), 0)) = _
  rw [(fourPortLocalPairing falseChoice).endpointMate_endpointEquiv]
  simpa using fourPortLocalEndpointEquiv_false hfalse side 1

private theorem trueTop_source_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing trueChoice).endpointEquiv ((b, 1), 0) =
      (D.localFirstSystem falseChoice).first.endpointMate
        (localEdgeStart falseChoice (b, 0)) := by
  rw [D.falseUpperPoint_eq falseChoice b hfalse 0]
  exact fourPortLocalEndpointEquiv_true htrue 1 0

private theorem trueTop_target_eq
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    (fourPortLocalPairing trueChoice).endpointEquiv ((b, 1), 1) =
      (D.localFirstSystem falseChoice).first.endpointMate
        (localEdgeStart falseChoice (b, 1)) := by
  rw [D.falseUpperPoint_eq falseChoice b hfalse 1]
  exact fourPortLocalEndpointEquiv_true htrue 1 1

private def trueBottomPath
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Path
      (fourPortChartPoint F.band (localEdgeStart falseChoice (b, 0)))
      (fourPortChartPoint F.band (localEdgeStart falseChoice (b, 1))) :=
  ((booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, 0)).cast
    (congrArg (fourPortChartPoint F.band)
      (trueBottom_source_eq falseChoice trueChoice b hfalse htrue).symm)
    (congrArg (fourPortChartPoint F.band)
      (trueBottom_target_eq falseChoice trueChoice b hfalse htrue).symm)

private def trueTopPath
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Path
      (fourPortChartPoint F.band
        ((D.localFirstSystem falseChoice).first.endpointMate
          (localEdgeStart falseChoice (b, 0))))
      (fourPortChartPoint F.band
        ((D.localFirstSystem falseChoice).first.endpointMate
          (localEdgeStart falseChoice (b, 1)))) :=
  ((booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, 1)).cast
    (congrArg (fourPortChartPoint F.band)
      (D.trueTop_source_eq falseChoice trueChoice b hfalse htrue).symm)
    (congrArg (fourPortChartPoint F.band)
      (D.trueTop_target_eq falseChoice trueChoice b hfalse htrue).symm)

private theorem range_trueBottomPath
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Set.range (trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, 0)) :=
  congrArg Set.range (Path.cast_coe _ _ _)

private theorem range_trueTopPath
    (D : BooleanFourPortOutsidePathData Phi F)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true) :
    Set.range (D.trueTopPath falseChoice trueChoice b hfalse htrue) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band trueChoice).path (b, 1)) :=
  congrArg Set.range (Path.cast_coe _ _ _)

/-- The canonical six-edge merge graph when the two vertical pre-flip cycles are distinct. -/
noncomputable def mergeSixEdgeConstituentData
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 0)) ≠
        (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 1))) :
    FourPortSixEdgeConstituentData (X := R3) where
  leftBottom := fourPortChartPoint F.band (localEdgeStart falseChoice (b, 0))
  leftTop := fourPortChartPoint F.band (localEdgeStart falseChoice (b, 1))
  rightBottom := fourPortChartPoint F.band
    ((D.localFirstSystem falseChoice).first.endpointMate
      (localEdgeStart falseChoice (b, 0)))
  rightTop := fourPortChartPoint F.band
    ((D.localFirstSystem falseChoice).first.endpointMate
      (localEdgeStart falseChoice (b, 1)))
  left := trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue
  right := D.trueTopPath falseChoice trueChoice b hfalse htrue
  bottom := D.localEdgePath falseChoice (b, 0)
  top := D.localEdgePath falseChoice (b, 1)
  bottomOutside := D.localEdgeComplementPath falseChoice (b, 0)
  topOutside := D.localEdgeComplementPath falseChoice (b, 1)
  bottomData := D.localEdgeTwoArcData falseChoice (b, 0)
  topData := D.localEdgeTwoArcData falseChoice (b, 1)
  left_injective := by
    simpa only [trueBottomPath, Path.cast_coe] using
      F.booleanFourPortLocalEndpointPaths_injective trueChoice (b, 0)
  right_injective := by
    simpa only [trueTopPath, Path.cast_coe] using
      F.booleanFourPortLocalEndpointPaths_injective trueChoice (b, 1)
  left_disjoint_right := by
    rw [range_trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_trueTopPath falseChoice trueChoice b hfalse htrue]
    exact F.booleanFourPortLocalEndpointPaths_pairwise trueChoice (by simp)
  children_disjoint := by
    rw [D.range_localEdgePath falseChoice (b, 0),
      D.range_localEdgePath falseChoice (b, 1),
      ← D.range_localEdgeCircle falseChoice (b, 0),
      ← D.range_localEdgeCircle falseChoice (b, 1)]
    have hcarrier := (D.localFirstIncidence falseChoice).cycleEdgeCarrier_disjoint hdistinct
    exact hcarrier.mono
      (D.range_localEdgeCircle_subset_cycleEdgeCarrier falseChoice (b, 0))
      (D.range_localEdgeCircle_subset_cycleEdgeCarrier falseChoice (b, 1))
  left_inter_bottom := by
    rw [range_trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath falseChoice (b, 0),
      ← D.range_localEdgeCircle falseChoice (b, 0)]
    simpa [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse] using
      D.range_trueLocalPath_inter_falseLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 0 0
  right_inter_bottom := by
    rw [D.range_trueTopPath falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath falseChoice (b, 0),
      ← D.range_localEdgeCircle falseChoice (b, 0)]
    simpa only [D.falseUpperPoint_eq falseChoice b hfalse 0] using
      D.range_trueLocalPath_inter_falseLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 1 0
  left_inter_top := by
    rw [range_trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath falseChoice (b, 1),
      ← D.range_localEdgeCircle falseChoice (b, 1)]
    simpa [localEdgeStart, fourPortLocalEndpointEquiv_false hfalse] using
      D.range_trueLocalPath_inter_falseLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 0 1
  right_inter_top := by
    rw [D.range_trueTopPath falseChoice trueChoice b hfalse htrue,
      D.range_localEdgePath falseChoice (b, 1),
      ← D.range_localEdgeCircle falseChoice (b, 1)]
    simpa only [D.falseUpperPoint_eq falseChoice b hfalse 1] using
      D.range_trueLocalPath_inter_falseLocalEdgeCircle falseChoice trueChoice
        b hfalse htrue hdistinct 1 1

/-- The canonical six-edge path system at one merge flip. -/
noncomputable def mergeSixEdgePathSystem
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 0)) ≠
        (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 1))) :
    FourPortSixEdgePathSystem R3 :=
  (D.mergeSixEdgeConstituentData falseChoice trueChoice b hfalse htrue hdistinct)
    |>.toFourPortSixEdgePathSystem

theorem range_localEdgeComplementPath_subset_transportedTorus
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeComplementPath choice e) ⊆ transportedTorus Phi := by
  let q := (D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)
  have hcanonical := (D.localFirstIncidence choice).range_circleMap_subset_transportedTorus
    (D.localPaths_mem_torus choice) D.paths_mem_torus q
  rw [(D.localFirstIncidence choice).range_circleMap_eq_cycleEdgeCarrier] at hcanonical
  intro x hx
  apply hcanonical
  apply D.range_localEdgeCircle_subset_cycleEdgeCarrier choice e
  rw [D.range_localEdgeCircle choice e]
  exact Or.inr hx

/-- Every path of the conditional split graph lies on the transported torus. -/
theorem sixEdgeCarrierData
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1))) :
    FourPortSixEdgeCarrierData
      (D.sixEdgePathSystem falseChoice trueChoice b hfalse htrue hdistinct)
      (transportedTorus Phi) where
  left := by
    change Set.range (falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue) ⊆ _
    rw [range_falseLeftPath (F := F) falseChoice trueChoice b hfalse htrue]
    exact D.localPaths_mem_torus falseChoice (b, 0)
  right := by
    change Set.range (D.falseRightPath falseChoice trueChoice b hfalse htrue) ⊆ _
    rw [D.range_falseRightPath falseChoice trueChoice b hfalse htrue]
    exact D.localPaths_mem_torus falseChoice (b, 1)
  bottom := by
    change Set.range (D.localEdgePath trueChoice (b, 0)) ⊆ _
    rw [D.range_localEdgePath trueChoice (b, 0)]
    exact D.localPaths_mem_torus trueChoice (b, 0)
  top := by
    change Set.range (D.localEdgePath trueChoice (b, 1)) ⊆ _
    rw [D.range_localEdgePath trueChoice (b, 1)]
    exact D.localPaths_mem_torus trueChoice (b, 1)
  bottomOutside := D.range_localEdgeComplementPath_subset_transportedTorus trueChoice (b, 0)
  topOutside := D.range_localEdgeComplementPath_subset_transportedTorus trueChoice (b, 1)

/-- Every path of the conditional merge graph lies on the transported torus. -/
theorem mergeSixEdgeCarrierData
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 0)) ≠
        (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 1))) :
    FourPortSixEdgeCarrierData
      (D.mergeSixEdgePathSystem falseChoice trueChoice b hfalse htrue hdistinct)
      (transportedTorus Phi) where
  left := by
    change Set.range (trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue) ⊆ _
    rw [range_trueBottomPath (F := F) falseChoice trueChoice b hfalse htrue]
    exact D.localPaths_mem_torus trueChoice (b, 0)
  right := by
    change Set.range (D.trueTopPath falseChoice trueChoice b hfalse htrue) ⊆ _
    rw [D.range_trueTopPath falseChoice trueChoice b hfalse htrue]
    exact D.localPaths_mem_torus trueChoice (b, 1)
  bottom := by
    change Set.range (D.localEdgePath falseChoice (b, 0)) ⊆ _
    rw [D.range_localEdgePath falseChoice (b, 0)]
    exact D.localPaths_mem_torus falseChoice (b, 0)
  top := by
    change Set.range (D.localEdgePath falseChoice (b, 1)) ⊆ _
    rw [D.range_localEdgePath falseChoice (b, 1)]
    exact D.localPaths_mem_torus falseChoice (b, 1)
  bottomOutside := D.range_localEdgeComplementPath_subset_transportedTorus falseChoice (b, 0)
  topOutside := D.range_localEdgeComplementPath_subset_transportedTorus falseChoice (b, 1)

/-- The conditional split graph as a transported-torus path system. -/
noncomputable def sixEdgeTorusPathSystem
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 0)) ≠
        (D.localFirstSystem trueChoice).cycleOfVertex
          (localEdgeStart trueChoice (b, 1))) :
    FourPortSixEdgePathSystem (transportedTorus Phi) :=
  (D.sixEdgeCarrierData falseChoice trueChoice b hfalse htrue hdistinct).toSubtypeGraph

/-- The conditional merge graph as a transported-torus path system. -/
noncomputable def mergeSixEdgeTorusPathSystem
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (hdistinct :
      (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 0)) ≠
        (D.localFirstSystem falseChoice).cycleOfVertex
          (localEdgeStart falseChoice (b, 1))) :
    FourPortSixEdgePathSystem (transportedTorus Phi) :=
  (D.mergeSixEdgeCarrierData falseChoice trueChoice b hfalse htrue hdistinct)
    |>.toSubtypeGraph

end BooleanFourPortOutsidePathData
end Submission.Topology
