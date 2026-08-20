import Submission.Topology.SuperellipsoidCanonicalBarrierArcPresentation

/-!
# Pointwise criterion for canonical band exactness

The canonical band carrier equality follows from two local chart facts: every barrier point in
the selected neighborhood has a chart coordinate, and the pullback of the barrier is the standard
three-branch `T`.  This isolates the remaining analytic endpoint-straightening calculation.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

/-- The standard singular `T` in the planar band coordinates. -/
def standardBandSingularCarrier : Set Submission.SurfaceRegularValue.Plane :=
  Set.range bandLeftPath ∪ Set.range bandRightPath ∪ Set.range bandSeamPath

namespace PairedSeamBandChart

/-- The ambient singular patch is exactly the chart image of the standard planar `T`. -/
theorem singularPatch_eq_image_standardBandSingularCarrier (B : PairedSeamBandChart) :
    B.singularPatch = B.chart '' standardBandSingularCarrier := by
  have hleft : Set.range B.leftPath = B.chart '' Set.range bandLeftPath := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨bandLeftPath t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hright : Set.range B.rightPath = B.chart '' Set.range bandRightPath := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨bandRightPath t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hseam : Set.range B.seamPath = B.chart '' Set.range bandSeamPath := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨bandSeamPath t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  rw [singularPatch, standardBandSingularCarrier, hleft, hright, hseam,
    Set.image_union, Set.image_union]

end PairedSeamBandChart

namespace FiniteSuperellipsoidBarrierGraph

universe u

/-- Local analytic facts sufficient for exactness of every canonical band chart.

The first field is a genuine chart-coverage statement.  The second is the signed local equation
in coordinates; it is the form supplied by a relative endpoint straightener and the seam IFT.
-/
structure CanonicalGlobalBandChartPointwiseExactness
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (T : cutOrder.GlobalBandTubularChartFamily) where
  local_carrier_subset_chart : ∀ b,
    G.carrier ∩ cutOrder.globalBandOpenNeighborhood b ⊆ Set.range (T.chart b).chart
  chart_mem_carrier_iff : ∀ b u,
    (T.chart b).chart u ∈ G.carrier ↔ u ∈ standardBandSingularCarrier

namespace CanonicalGlobalBandChartPointwiseExactness

/-- Pointwise chart exactness implies the set-level exactness consumed by the canonical
paired-band construction. -/
theorem toCanonicalGlobalBandChartArcExactness
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily}
    {cutOrder : G.CutCircleTransverseCyclicOrderFamily} {hR : 0 < R}
    {T : cutOrder.GlobalBandTubularChartFamily}
    (X : CanonicalGlobalBandChartPointwiseExactness G outerOrder cutOrder T) :
    CanonicalGlobalBandChartArcExactness G outerOrder cutOrder T where
  local_arc_union_exact := by
    intro b
    rw [← carrier_inter_globalBandOpenNeighborhood_eq_iUnion
      G outerOrder cutOrder hR b]
    let B := T.chart b
    rw [B.singularPatch_eq_image_standardBandSingularCarrier]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨u, hu⟩ := X.local_carrier_subset_chart b hx
      refine ⟨u, (X.chart_mem_carrier_iff b u).mp ?_, hu⟩
      simpa only [hu] using hx.1
    · rintro x ⟨u, hu, rfl⟩
      refine ⟨(X.chart_mem_carrier_iff b u).mpr hu, ?_⟩
      exact (B.singularPatch_subset_support
        (B.singularPatch_eq_image_standardBandSingularCarrier.symm ▸ ⟨u, hu, rfl⟩))

end CanonicalGlobalBandChartPointwiseExactness
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
