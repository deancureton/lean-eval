import Submission.Topology.SuperellipsoidCanonicalBarrierArcPresentation

/-!
# Pointwise criterion for compact canonical band exactness

The canonical compact-patch carrier equality follows from an exact support description and the
pullback equation on that patch.  The surrounding open band remains available for isolation and
event charging without incorrectly asserting that a circle terminates inside an open chart.
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

/-- Local analytic facts sufficient for exactness of every compact canonical band patch. -/
structure CanonicalGlobalBandChartPointwiseExactness
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (T : cutOrder.GlobalBandTubularChartFamily) where
  support_eq : ∀ b,
    (T.chart b).support = (T.chart b).chart '' standardBandPatchCarrier
  chart_mem_carrier_iff : ∀ b u, u ∈ standardBandPatchCarrier →
    ((T.chart b).chart u ∈ G.carrier ↔ u ∈ standardBandSingularCarrier)

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
    rw [← carrier_inter_eq_iUnion G outerOrder cutOrder hR (T.chart b).support]
    let B := T.chart b
    rw [B.singularPatch_eq_image_standardBandSingularCarrier]
    apply Set.Subset.antisymm
    · intro x hx
      rw [X.support_eq b] at hx
      obtain ⟨u, huPatch, rfl⟩ := hx.2
      have hiff := X.chart_mem_carrier_iff b u
      exact ⟨u, (hiff huPatch).mp hx.1, rfl⟩
    · rintro x ⟨u, hu, rfl⟩
      have huPatch : u ∈ standardBandPatchCarrier := by
        rcases hu with (hu | hu) | hu
        · exact range_bandLeftPath_subset_standardBandPatchCarrier hu
        · exact range_bandRightPath_subset_standardBandPatchCarrier hu
        · exact range_bandSeamPath_subset_standardBandPatchCarrier hu
      have hiff := X.chart_mem_carrier_iff b u
      refine ⟨(hiff huPatch).mpr hu, ?_⟩
      rw [X.support_eq b]
      exact ⟨u, huPatch, rfl⟩

end CanonicalGlobalBandChartPointwiseExactness
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
