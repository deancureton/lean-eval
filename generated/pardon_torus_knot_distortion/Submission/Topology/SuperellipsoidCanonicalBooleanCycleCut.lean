import Submission.Topology.BooleanFourPortCycleCut
import Submission.Topology.SuperellipsoidCanonicalReducedRegions

/-!
# Specified-edge cuts of the canonical Boolean four-port family

The two local edges at one band are exactly the analytic vertical or horizontal patch selected
by the Boolean bit.  Cutting either edge at its prescribed endpoint retains this exact local
carrier while constructing the complementary global outside route.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  (D : CanonicalEndpointRegularityData S)

abbrev CanonicalCycleCutBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private theorem iUnion_finTwo_eq_union {X : Type*} (s : Fin 2 → Set X) :
    (⋃ i, s i) = s 0 ∪ s 1 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hx | hx)
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩

/-- The two specified local-edge cuts retain exactly the selected analytic band patch. -/
theorem range_localEdgePath_zero_union_one
    (choice : D.CanonicalCycleCutBandIndex → Bool)
    (b : D.CanonicalCycleCutBandIndex) :
    Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 0)) ∪
        Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 1)) =
      if choice b then
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch
      else (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  rw [D.canonicalBooleanOutsidePathData.range_localEdgePath,
    D.canonicalBooleanOutsidePathData.range_localEdgePath]
  have h := D.iUnion_range_canonicalBooleanLocalPaths_at_band choice b
  rw [iUnion_finTwo_eq_union] at h
  exact h

/-- At a false bit the two specified-edge cuts retain exactly the vertical patch. -/
theorem range_false_localEdgePaths_eq_parallelPatch
    (choice : D.CanonicalCycleCutBandIndex → Bool)
    (b : D.CanonicalCycleCutBandIndex)
    (hb : choice b = false) :
    Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 0)) ∪
        Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 1)) =
      (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch := by
  simpa [hb] using D.range_localEdgePath_zero_union_one choice b

/-- At a true bit the two specified-edge cuts retain exactly the horizontal patch. -/
theorem range_true_localEdgePaths_eq_surgeryPatch
    (choice : D.CanonicalCycleCutBandIndex → Bool)
    (b : D.CanonicalCycleCutBandIndex)
    (hb : choice b = true) :
    Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 0)) ∪
        Set.range (D.canonicalBooleanOutsidePathData.localEdgePath choice (b, 1)) =
      (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch := by
  simpa [hb] using D.range_localEdgePath_zero_union_one choice b

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
