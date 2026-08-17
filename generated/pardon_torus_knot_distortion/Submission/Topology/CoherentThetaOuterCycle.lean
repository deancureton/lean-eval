import Submission.PlaneSchoenflies.Schoenflies.JordanThetaRegions
import Submission.Topology.CoherentThetaCoveringNeighborhood

/-!
# The outer cycle of a planar theta graph

Three arcs with two common endpoints determine three Jordan circles.  Exactly one of their
bounded closed disks contains the third arc; its disk is the union of the other two disks.  This
module derives that choice rather than storing a permutation of the three cycles.

The only local hypothesis is the one used by `JordanThetaRegions`: away from a finite exceptional
set, the two cycle carriers sharing an edge have the same local straight-line germ.  This holds for
the piecewise smooth and piecewise polygonal theta graphs used by the four-port construction.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

/-- Carrier-level data for three planar arcs forming a locally straight Jordan theta graph. -/
structure PlanarJordanThetaData where
  source : Plane
  target : Plane
  edge0 : Set Plane
  edge1 : Set Plane
  edge2 : Set Plane
  circle01 : JordanCircle
  circle02 : JordanCircle
  circle12 : JordanCircle
  endpoints_subset_edge0 : ({source, target} : Set Plane) ⊆ edge0
  endpoints_subset_edge1 : ({source, target} : Set Plane) ⊆ edge1
  endpoints_subset_edge2 : ({source, target} : Set Plane) ⊆ edge2
  edge0_inter_edge1 : edge0 ∩ edge1 = {source, target}
  edge0_inter_edge2 : edge0 ∩ edge2 = {source, target}
  edge1_inter_edge2 : edge1 ∩ edge2 = {source, target}
  carrier01 : circle01.carrier = edge0 ∪ edge1
  carrier02 : circle02.carrier = edge0 ∪ edge2
  carrier12 : circle12.carrier = edge1 ∪ edge2
  private0_preconnected : IsPreconnected (edge0 \ {source, target})
  private1_preconnected : IsPreconnected (edge1 \ {source, target})
  private2_preconnected : IsPreconnected (edge2 \ {source, target})
  private0_nonempty : (edge0 \ (edge1 ∪ edge2)).Nonempty
  private1_nonempty : (edge1 \ (edge0 ∪ edge2)).Nonempty
  private2_nonempty : (edge2 \ (edge0 ∪ edge1)).Nonempty
  exceptional : Set Plane
  exceptional_finite : exceptional.Finite
  local0 : ∀ p ∈ edge0 \ exceptional,
    ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      Metric.ball p r ∩ circle01.carrier =
        Metric.ball p r ∩ determinantLine p d ∧
      Metric.ball p r ∩ circle02.carrier =
        Metric.ball p r ∩ determinantLine p d
  local1 : ∀ p ∈ edge1 \ exceptional,
    ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      Metric.ball p r ∩ circle01.carrier =
        Metric.ball p r ∩ determinantLine p d ∧
      Metric.ball p r ∩ circle12.carrier =
        Metric.ball p r ∩ determinantLine p d
  local2 : ∀ p ∈ edge2 \ exceptional,
    ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      Metric.ball p r ∩ circle02.carrier =
        Metric.ball p r ∩ determinantLine p d ∧
      Metric.ball p r ∩ circle12.carrier =
        Metric.ball p r ∩ determinantLine p d

namespace PlanarJordanThetaData

variable (G : PlanarJordanThetaData)

private theorem private0_disjoint_circle12 :
    G.edge0 \ {G.source, G.target} ⊆ G.circle12.carrierᶜ := by
  rintro x ⟨hx0, hxEnds⟩
  rw [G.carrier12]
  rintro (hx1 | hx2)
  · exact hxEnds (by rw [← G.edge0_inter_edge1]; exact ⟨hx0, hx1⟩)
  · exact hxEnds (by rw [← G.edge0_inter_edge2]; exact ⟨hx0, hx2⟩)

private theorem private1_disjoint_circle02 :
    G.edge1 \ {G.source, G.target} ⊆ G.circle02.carrierᶜ := by
  rintro x ⟨hx1, hxEnds⟩
  rw [G.carrier02]
  rintro (hx0 | hx2)
  · exact hxEnds (by rw [← G.edge0_inter_edge1]; exact ⟨hx0, hx1⟩)
  · exact hxEnds (by rw [← G.edge1_inter_edge2]; exact ⟨hx1, hx2⟩)

private theorem private2_disjoint_circle01 :
    G.edge2 \ {G.source, G.target} ⊆ G.circle01.carrierᶜ := by
  rintro x ⟨hx2, hxEnds⟩
  rw [G.carrier01]
  rintro (hx0 | hx1)
  · exact hxEnds (by rw [← G.edge0_inter_edge2]; exact ⟨hx0, hx2⟩)
  · exact hxEnds (by rw [← G.edge1_inter_edge2]; exact ⟨hx1, hx2⟩)

private theorem private0_side :
    G.edge0 \ {G.source, G.target} ⊆ G.circle12.inside ∨
      G.edge0 \ {G.source, G.target} ⊆ G.circle12.outside := by
  apply G.private0_preconnected.subset_or_subset
      G.circle12.inside_isOpen G.circle12.outside_isOpen
      G.circle12.inside_disjoint_outside
  rw [G.circle12.inside_union_outside]
  exact G.private0_disjoint_circle12

private theorem private1_side :
    G.edge1 \ {G.source, G.target} ⊆ G.circle02.inside ∨
      G.edge1 \ {G.source, G.target} ⊆ G.circle02.outside := by
  apply G.private1_preconnected.subset_or_subset
      G.circle02.inside_isOpen G.circle02.outside_isOpen
      G.circle02.inside_disjoint_outside
  rw [G.circle02.inside_union_outside]
  exact G.private1_disjoint_circle02

private theorem private2_side :
    G.edge2 \ {G.source, G.target} ⊆ G.circle01.inside ∨
      G.edge2 \ {G.source, G.target} ⊆ G.circle01.outside := by
  apply G.private2_preconnected.subset_or_subset
      G.circle01.inside_isOpen G.circle01.outside_isOpen
      G.circle01.inside_disjoint_outside
  rw [G.circle01.inside_union_outside]
  exact G.private2_disjoint_circle01

private theorem edge_subset_closed_of_private_subset_inside
    {J : JordanCircle} {E : Set Plane}
    (hend : ({G.source, G.target} : Set Plane) ⊆ J.carrier)
    (hprivate : E \ {G.source, G.target} ⊆ J.inside) :
    E ⊆ J.inside ∪ J.carrier := by
  intro x hx
  by_cases hends : x ∈ ({G.source, G.target} : Set Plane)
  · exact Or.inr (hend hends)
  · exact Or.inl (hprivate ⟨hx, hends⟩)

private theorem edge0_endpoints_circle12 :
    ({G.source, G.target} : Set Plane) ⊆ G.circle12.carrier := by
  rw [G.carrier12]
  exact G.endpoints_subset_edge1.trans Set.subset_union_left

private theorem edge1_endpoints_circle02 :
    ({G.source, G.target} : Set Plane) ⊆ G.circle02.carrier := by
  rw [G.carrier02]
  exact G.endpoints_subset_edge0.trans Set.subset_union_left

private theorem edge2_endpoints_circle01 :
    ({G.source, G.target} : Set Plane) ⊆ G.circle01.carrier := by
  rw [G.carrier01]
  exact G.endpoints_subset_edge0.trans Set.subset_union_left

private theorem disjoint_inside_of_shared_boundary
    {J K : JordanCircle} {B A C : Set Plane}
    (hJ : J.carrier = B ∪ A) (hK : K.carrier = B ∪ C)
    (hAoutside : A \ B ⊆ K.outside)
    (hCoutside : C \ B ⊆ J.outside)
    (hprivate : (A \ (B ∪ C)).Nonempty) :
    Disjoint J.inside K.inside := by
  have hJdisjointKcarrier : Disjoint J.inside K.carrier := by
    rw [Set.disjoint_left]
    intro x hxJ hxK
    rw [hK] at hxK
    rcases hxK with hxB | hxC
    · exact J.inside_subset_compl hxJ (by rw [hJ]; exact Or.inl hxB)
    · by_cases hxB : x ∈ B
      · exact J.inside_subset_compl hxJ (by rw [hJ]; exact Or.inl hxB)
      · exact Set.disjoint_left.mp J.inside_disjoint_outside hxJ
          (hCoutside ⟨hxC, hxB⟩)
  have hregions : J.inside ⊆ K.inside ∪ K.outside := by
    rw [K.inside_union_outside]
    intro x hxJ hxK
    exact Set.disjoint_left.mp hJdisjointKcarrier hxJ hxK
  rcases J.inside_isConnected.isPreconnected.subset_or_subset
      K.inside_isOpen K.outside_isOpen K.inside_disjoint_outside hregions with
      hinside | houtside
  · obtain ⟨x, hxA, hxNot⟩ := hprivate
    have hxNotB : x ∉ B := fun hxB ↦ hxNot (Or.inl hxB)
    have hxKoutside : x ∈ K.outside := hAoutside ⟨hxA, hxNotB⟩
    have hxClosureJ : x ∈ closure J.inside := by
      rw [J.closure_inside, hJ]
      exact Or.inr (Or.inr hxA)
    have hxInterClosure : x ∈ closure (K.outside ∩ J.inside) :=
      K.outside_isOpen.inter_closure ⟨hxKoutside, hxClosureJ⟩
    obtain ⟨y, hyKoutside, hyJinside⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      (hinside hyJinside) hyKoutside
  · exact Set.disjoint_left.mpr fun _ hxJ hxK ↦
      Set.disjoint_left.mp K.inside_disjoint_outside hxK (houtside hxJ)

private theorem frontier_threeClosed_subset_carriers
    (J K L : JordanCircle) :
    frontier (closure J.inside ∪ closure K.inside ∪ closure L.inside) ⊆
      J.carrier ∪ K.carrier ∪ L.carrier := by
  intro x hx
  rcases frontier_union_subset _ _ hx with hxJK | hxL
  · rcases frontier_union_subset _ _ hxJK.1 with hxJ | hxK
    · exact Or.inl (Or.inl <|
        (frontier_closure_subset.trans <| by rw [J.frontier_inside]) hxJ.1)
    · exact Or.inl (Or.inr <|
        (frontier_closure_subset.trans <| by rw [K.frontier_inside]) hxK.2)
  · exact Or.inr <|
      (frontier_closure_subset.trans <| by rw [L.frontier_inside]) hxL.2

private theorem closure_interior_closure_inside (J : JordanCircle) :
    closure (interior (closure J.inside)) = closure J.inside := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact interior_maximal subset_closure J.inside_isOpen

/-- At least one two-edge cycle contains the third edge in its closed bounded disk. -/
theorem exists_outer_carrier :
    G.edge2 ⊆ G.circle01.inside ∪ G.circle01.carrier ∨
      G.edge1 ⊆ G.circle02.inside ∪ G.circle02.carrier ∨
        G.edge0 ⊆ G.circle12.inside ∪ G.circle12.carrier := by
  by_contra hnone
  push Not at hnone
  have hout2 : G.edge2 \ {G.source, G.target} ⊆ G.circle01.outside := by
    rcases G.private2_side with hin | hout
    · exact False.elim <| hnone.1 <|
        G.edge_subset_closed_of_private_subset_inside G.edge2_endpoints_circle01 hin
    · exact hout
  have hout1 : G.edge1 \ {G.source, G.target} ⊆ G.circle02.outside := by
    rcases G.private1_side with hin | hout
    · exact False.elim <| hnone.2.1 <|
        G.edge_subset_closed_of_private_subset_inside G.edge1_endpoints_circle02 hin
    · exact hout
  have hout0 : G.edge0 \ {G.source, G.target} ⊆ G.circle12.outside := by
    rcases G.private0_side with hin | hout
    · exact False.elim <| hnone.2.2 <|
        G.edge_subset_closed_of_private_subset_inside G.edge0_endpoints_circle12 hin
    · exact hout
  have hd01_02 : Disjoint G.circle01.inside G.circle02.inside := by
    apply disjoint_inside_of_shared_boundary
      (B := G.edge0) (A := G.edge1) (C := G.edge2)
      G.carrier01 G.carrier02
    · intro x hx
      exact hout1 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge0 hends)⟩
    · intro x hx
      exact hout2 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge0 hends)⟩
    · exact G.private1_nonempty
  have hd01_12 : Disjoint G.circle01.inside G.circle12.inside := by
    apply disjoint_inside_of_shared_boundary
      (B := G.edge1) (A := G.edge0) (C := G.edge2)
      (by rw [G.carrier01, Set.union_comm]) G.carrier12
    · intro x hx
      exact hout0 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge1 hends)⟩
    · intro x hx
      exact hout2 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge1 hends)⟩
    · exact G.private0_nonempty
  have hd02_12 : Disjoint G.circle02.inside G.circle12.inside := by
    apply disjoint_inside_of_shared_boundary
      (B := G.edge2) (A := G.edge0) (C := G.edge1)
      (by rw [G.carrier02, Set.union_comm])
      (by rw [G.carrier12, Set.union_comm])
    · intro x hx
      exact hout0 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge2 hends)⟩
    · intro x hx
      exact hout1 ⟨hx.1, fun hends ↦ hx.2 (G.endpoints_subset_edge2 hends)⟩
    · simpa only [Set.union_comm] using G.private0_nonempty
  let S := closure G.circle01.inside ∪ closure G.circle02.inside ∪
    closure G.circle12.inside
  have hSclosed : IsClosed S :=
    (isClosed_closure.union isClosed_closure).union isClosed_closure
  have hScompact : IsCompact S :=
    (G.circle01.isCompact_closure_inside.union
      G.circle02.isCompact_closure_inside).union
        G.circle12.isCompact_closure_inside
  have hSregular : closure (interior S) = S := by
    apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hSclosed
    · rintro x ((hx | hx) | hx)
      · rw [← closure_interior_closure_inside G.circle01] at hx
        exact closure_mono (interior_mono <| Set.subset_union_left.trans
          Set.subset_union_left) hx
      · rw [← closure_interior_closure_inside G.circle02] at hx
        exact closure_mono (interior_mono <| Set.subset_union_right.trans
          Set.subset_union_left) hx
      · rw [← closure_interior_closure_inside G.circle12] at hx
        exact closure_mono (interior_mono Set.subset_union_right) hx
  have hfrontierFinite : frontier S ⊆ G.exceptional := by
    intro x hxFrontier
    have hxCarrier := frontier_threeClosed_subset_carriers
      G.circle01 G.circle02 G.circle12 hxFrontier
    rcases hxCarrier with hx01 | hx12
    · rcases hx01 with hxCircle01 | hxCircle02
      · rw [G.carrier01] at hxCircle01
        rcases hxCircle01 with hx0 | hx1
        · by_cases hxF : x ∈ G.exceptional
          · exact hxF
          · obtain ⟨d, r, hr, hlocal01, hlocal02⟩ := G.local0 x ⟨hx0, hxF⟩
            have hxInterior :=
              JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
                hd01_02 hr (by rw [G.carrier01]; exact Or.inl hx0)
                hlocal01 hlocal02
            exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
              (interior_mono Set.subset_union_left hxInterior) hxFrontier
        · by_cases hxF : x ∈ G.exceptional
          · exact hxF
          · obtain ⟨d, r, hr, hlocal01, hlocal12⟩ := G.local1 x ⟨hx1, hxF⟩
            have hxInterior :=
              JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
                hd01_12 hr (by rw [G.carrier01]; exact Or.inr hx1)
                hlocal01 hlocal12
            have hsub : closure G.circle01.inside ∪ closure G.circle12.inside ⊆ S :=
              Set.union_subset
                (Set.subset_union_left.trans Set.subset_union_left)
                Set.subset_union_right
            exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
              (interior_mono hsub hxInterior) hxFrontier
      · rw [G.carrier02] at hxCircle02
        rcases hxCircle02 with hx0 | hx2
        · by_cases hxF : x ∈ G.exceptional
          · exact hxF
          · obtain ⟨d, r, hr, hlocal01, hlocal02⟩ := G.local0 x ⟨hx0, hxF⟩
            have hxInterior :=
              JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
                hd01_02 hr (by rw [G.carrier01]; exact Or.inl hx0)
                hlocal01 hlocal02
            exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
              (interior_mono Set.subset_union_left hxInterior) hxFrontier
        · by_cases hxF : x ∈ G.exceptional
          · exact hxF
          · obtain ⟨d, r, hr, hlocal02, hlocal12⟩ := G.local2 x ⟨hx2, hxF⟩
            have hxInterior :=
              JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
                hd02_12 hr (by rw [G.carrier02]; exact Or.inr hx2)
                hlocal02 hlocal12
            have hsub : closure G.circle02.inside ∪ closure G.circle12.inside ⊆ S :=
              Set.union_subset (Set.subset_union_right.trans Set.subset_union_left)
                Set.subset_union_right
            exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
              (interior_mono hsub hxInterior) hxFrontier
    · by_cases hxF : x ∈ G.exceptional
      · exact hxF
      · rw [G.carrier12] at hx12
        rcases hx12 with hx1 | hx2
        · obtain ⟨d, r, hr, hlocal01, hlocal12⟩ := G.local1 x ⟨hx1, hxF⟩
          have hxInterior :=
            JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
              hd01_12 hr (by rw [G.carrier01]; exact Or.inr hx1)
              hlocal01 hlocal12
          have hsub : closure G.circle01.inside ∪ closure G.circle12.inside ⊆ S :=
            Set.union_subset
              (Set.subset_union_left.trans Set.subset_union_left)
              Set.subset_union_right
          exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
            (interior_mono hsub hxInterior) hxFrontier
        · obtain ⟨d, r, hr, hlocal02, hlocal12⟩ := G.local2 x ⟨hx2, hxF⟩
          have hxInterior :=
            JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
              hd02_12 hr (by rw [G.carrier02]; exact Or.inr hx2)
              hlocal02 hlocal12
          have hsub : closure G.circle02.inside ∪ closure G.circle12.inside ⊆ S :=
            Set.union_subset (Set.subset_union_right.trans Set.subset_union_left)
              Set.subset_union_right
          exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
            (interior_mono hsub hxInterior) hxFrontier
  have hfrontierEmpty : frontier S = ∅ := by
    apply Set.Subset.antisymm
    · intro x hxFrontier
      have hxClosure :=
        frontier_subset_closure_sdiff_finite_of_regularClosed
          hSclosed hSregular G.exceptional_finite hxFrontier
      have hdiff : frontier S \ G.exceptional = ∅ :=
        Set.sdiff_eq_empty.mpr hfrontierFinite
      rw [hdiff, closure_empty] at hxClosure
      exact hxClosure.elim
    · exact Set.empty_subset _
  have hclopen : IsClopen S := isClopen_iff_frontier_eq_empty.mpr hfrontierEmpty
  rcases isClopen_iff.mp hclopen with hSempty | hSuniv
  · have : G.circle01.insidePoint ∈ S := by
      exact Or.inl (Or.inl (subset_closure G.circle01.insidePoint_mem_inside))
    rw [hSempty] at this
    exact this
  · have hbounded : Bornology.IsBounded (Set.univ : Set Plane) := by
      rw [← hSuniv]
      exact hScompact.isBounded
    exact hbounded.ediam_ne_top Metric.ediam_univ_of_noncompact

/-- One of the three cycles is the outer cycle, and its closed disk is exactly the union of the
other two closed disks. -/
theorem exists_outer_cycle_decomposition :
    closure G.circle01.inside =
        closure G.circle02.inside ∪ closure G.circle12.inside ∨
      closure G.circle02.inside =
        closure G.circle01.inside ∪ closure G.circle12.inside ∨
      closure G.circle12.inside =
        closure G.circle01.inside ∪ closure G.circle02.inside := by
  rcases G.exists_outer_carrier with h01 | h02 | h12
  · left
    apply JordanThetaRegions.closure_inside_eq_union
      (Q := G.circle01) (K₀ := G.circle02) (K₁ := G.circle12)
      (B := G.edge2) (A₀ := G.edge0) (A₁ := G.edge1)
    · rw [G.carrier02]
      exact Set.union_subset
        (by rw [G.carrier01]; exact fun _ hx ↦ Or.inr (Or.inl hx)) h01
    · rw [G.carrier12]
      exact Set.union_subset
        (by rw [G.carrier01]; exact fun _ hx ↦ Or.inr (Or.inr hx)) h01
    · exact G.carrier01
    · rw [G.carrier02, Set.union_comm]
    · rw [G.carrier12, Set.union_comm]
    · simpa only [G.carrier12] using G.private0_nonempty
    · simpa only [G.carrier02] using G.private1_nonempty
    · exact G.exceptional_finite
    · exact G.local2
  · right; left
    apply JordanThetaRegions.closure_inside_eq_union
      (Q := G.circle02) (K₀ := G.circle01) (K₁ := G.circle12)
      (B := G.edge1) (A₀ := G.edge0) (A₁ := G.edge2)
    · rw [G.carrier01]
      exact Set.union_subset
        (by rw [G.carrier02]; exact fun _ hx ↦ Or.inr (Or.inl hx)) h02
    · rw [G.carrier12]
      exact Set.union_subset h02
        (by rw [G.carrier02]; exact fun _ hx ↦ Or.inr (Or.inr hx))
    · exact G.carrier02
    · rw [G.carrier01, Set.union_comm]
    · exact G.carrier12
    · simpa only [G.carrier12] using G.private0_nonempty
    · simpa only [G.carrier01] using G.private2_nonempty
    · exact G.exceptional_finite
    · exact G.local1
  · right; right
    apply JordanThetaRegions.closure_inside_eq_union
      (Q := G.circle12) (K₀ := G.circle01) (K₁ := G.circle02)
      (B := G.edge0) (A₀ := G.edge1) (A₁ := G.edge2)
    · rw [G.carrier01]
      exact Set.union_subset h12
        (by rw [G.carrier12]; exact fun _ hx ↦ Or.inr (Or.inl hx))
    · rw [G.carrier02]
      exact Set.union_subset h12
        (by rw [G.carrier12]; exact fun _ hx ↦ Or.inr (Or.inr hx))
    · exact G.carrier12
    · exact G.carrier01
    · exact G.carrier02
    · simpa only [G.carrier02] using G.private1_nonempty
    · simpa only [G.carrier01] using G.private2_nonempty
    · exact G.exceptional_finite
    · exact G.local0

end PlanarJordanThetaData
end Submission.Topology
