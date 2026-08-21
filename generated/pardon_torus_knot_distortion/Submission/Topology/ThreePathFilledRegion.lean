import Submission.PlaneSchoenflies.Schoenflies.JordanRegionRecognition
import Submission.Topology.CoherentThetaOuterCycle
import Submission.Topology.SuperellipsoidCanonicalFourPortThetaCompletion

/-!
# Recognizing the outer cycle of a three-path system

A compact planar region whose frontier lies on the cycle formed by paths one and two identifies
that cycle as the outer cycle, provided the remaining path lies in the region.  This packages the
exact planar recognition step needed by the canonical Pardon four-port theta.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

namespace ThreePathSystem

variable {a b : Plane} {path : Fin 3 → Path a b} (G : ThreePathSystem path)

/-- A compact planar filling whose frontier lies on the cycle formed by paths one and two and
which also contains path zero. -/
structure FilledOuterRegionData where
  region : Set Plane
  region_isCompact : IsCompact region
  region_frontier_subset : frontier region ⊆ G.circle12.carrier
  path0_subset_region : Set.range (path 0) ⊆ region

namespace FilledOuterRegionData

private theorem frontier_image_subset_image_frontier
    {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X} {f : X → Plane}
    (hC : IsCompact C) (hf : Continuous f)
    (hinterior : f '' interior C ⊆ interior (f '' C)) :
    frontier (f '' C) ⊆ f '' frontier C := by
  intro x hx
  have hxImage : x ∈ f '' C := by
    have hxClosure := frontier_subset_closure hx
    simpa only [(hC.image hf).isClosed.closure_eq] using hxClosure
  obtain ⟨y, hyC, rfl⟩ := hxImage
  refine ⟨y, ?_, rfl⟩
  rw [frontier, hC.isClosed.closure_eq]
  refine ⟨hyC, ?_⟩
  intro hyInterior
  exact Set.disjoint_left.mp disjoint_interior_frontier
    (hinterior ⟨y, hyInterior, rfl⟩) hx

/-- Build a filled-region certificate from a compact parameter region whose interior maps into
the interior of its image and whose parameter frontier maps into the outer cycle. -/
def ofImage {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) (f : X → Plane)
    (hC : IsCompact C) (hf : Continuous f)
    (hinterior : f '' interior C ⊆ interior (f '' C))
    (hfrontier : f '' frontier C ⊆ G.circle12.carrier)
    (hpath0 : Set.range (path 0) ⊆ f '' C) : G.FilledOuterRegionData where
  region := f '' C
  region_isCompact := hC.image hf
  region_frontier_subset :=
    (frontier_image_subset_image_frontier hC hf hinterior).trans hfrontier
  path0_subset_region := hpath0

variable (D : G.FilledOuterRegionData)

theorem region_subset_closure_inside :
    D.region ⊆ closure G.circle12.inside :=
  G.circle12.subset_closure_inside_of_isCompact_frontier_subset
    D.region_isCompact D.region_frontier_subset

private theorem circle12_carrier_subset_closure_inside :
    G.circle12.carrier ⊆ closure G.circle12.inside := by
  rw [G.circle12.closure_inside]
  exact Set.subset_union_right

private theorem path1_subset_closure_inside :
    Set.range (path 1) ⊆ closure G.circle12.inside := by
  intro x hx
  apply circle12_carrier_subset_closure_inside G
  rw [G.carrier_circle12]
  exact Or.inl hx

private theorem path2_subset_closure_inside :
    Set.range (path 2) ⊆ closure G.circle12.inside := by
  intro x hx
  apply circle12_carrier_subset_closure_inside G
  rw [G.carrier_circle12]
  exact Or.inr hx

include D in
private theorem circle01_carrier_subset_closure_inside :
    G.circle01.carrier ⊆ closure G.circle12.inside := by
  rw [G.carrier_circle01]
  exact Set.union_subset
    (Set.Subset.trans D.path0_subset_region (region_subset_closure_inside G D))
    (path1_subset_closure_inside G)

include D in
private theorem circle02_carrier_subset_closure_inside :
    G.circle02.carrier ⊆ closure G.circle12.inside := by
  rw [G.carrier_circle02]
  exact Set.union_subset
    (Set.Subset.trans D.path0_subset_region (region_subset_closure_inside G D))
    (path2_subset_closure_inside G)

include D in
/-- The prescribed filled region forces the paths-one-and-two cycle to be the outer theta cycle. -/
theorem outer_decomposition :
    closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside := by
  apply JordanThetaRegions.closure_inside_eq_union_of_common_interior
    (Q := G.circle12) (K₀ := G.circle01) (K₁ := G.circle02)
    (B := Set.range (path 0)) (A₀ := Set.range (path 1))
    (A₁ := Set.range (path 2))
  · rw [← G.circle12.closure_inside]
    exact circle01_carrier_subset_closure_inside G D
  · rw [← G.circle12.closure_inside]
    exact circle02_carrier_subset_closure_inside G D
  · exact G.carrier_circle12
  · exact G.carrier_circle01
  · exact G.carrier_circle02
  · rw [G.carrier_circle02]
    exact G.toTopologicalPlanarJordanThetaData.private1_nonempty
  · rw [G.carrier_circle01]
    exact G.toTopologicalPlanarJordanThetaData.private2_nonempty
  · exact G.toTopologicalPlanarJordanThetaData.exceptional_finite
  · intro p hp
    apply (G.toTopologicalPlanarJordanThetaData.local0 p hp).mem_interior
    apply JordanThetaRegions.disjoint_inside
      (Q := G.circle12) (K₀ := G.circle01) (K₁ := G.circle02)
      (B := Set.range (path 0)) (A₀ := Set.range (path 1))
      (A₁ := Set.range (path 2))
    · rw [← G.circle12.closure_inside]
      exact circle01_carrier_subset_closure_inside G D
    · rw [← G.circle12.closure_inside]
      exact circle02_carrier_subset_closure_inside G D
    · exact G.carrier_circle12
    · exact G.carrier_circle01
    · exact G.carrier_circle02
    · rw [G.carrier_circle02]
      exact G.toTopologicalPlanarJordanThetaData.private1_nonempty
    · rw [G.carrier_circle01]
      exact G.toTopologicalPlanarJordanThetaData.private2_nonempty

include D in
/-- Turn a filled-region certificate into the theta package consumed by the relative ambient
straightener. -/
def toFilledThetaSystemData : FilledThetaSystemData path where
  system := G
  outer_decomposition := outer_decomposition G D

end FilledOuterRegionData
end ThreePathSystem
end Submission.Topology
