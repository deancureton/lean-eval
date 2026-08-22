import Submission.PlaneSchoenflies.Schoenflies.JordanThetaAmbientExtension
import Submission.Topology.TwoArcCommonLocalStraightening

/-!
# The planar obstruction to two alternating exterior crosscuts

Three pairwise endpoint-intersecting arcs form a theta graph.  If the cycle made from the
first two arcs is outer, a fourth arc cannot join private points of the second and third arcs
while remaining outside their cycle and avoiding the theta graph.  This is the topological
obstruction needed to exclude the diagonal four-port connectivity.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

namespace ThreePathSystem

variable {a b : Plane} {path : Fin 3 → Path a b}

/-- A fourth path joins private points of edges one and two, misses edge zero, and otherwise
stays off both incident edges. -/
structure AlternatingCrosscutData (G : ThreePathSystem path) where
  x : Plane
  y : Plane
  crosscut : Path x y
  crosscut_injective : Function.Injective crosscut
  x_mem_edge1 : x ∈ Set.range (path 1)
  y_mem_edge2 : y ∈ Set.range (path 2)
  x_not_endpoint : x ∉ ({a, b} : Set Plane)
  y_not_endpoint : y ∉ ({a, b} : Set Plane)
  crosscut_inter_edge0 : Set.range crosscut ∩ Set.range (path 0) = ∅
  crosscut_inter_edge1 : Set.range crosscut ∩ Set.range (path 1) = {x}
  crosscut_inter_edge2 : Set.range crosscut ∩ Set.range (path 2) = {y}
  edge0_private_subset_rectangleOutside :
    Set.range (path 0) \ ({a, b} : Set Plane) ⊆ G.circle12.outside
  crosscut_private_subset_rectangleOutside :
    Set.range crosscut \ ({x, y} : Set Plane) ⊆ G.circle12.outside

namespace AlternatingCrosscutData

variable {G : ThreePathSystem path} (D : AlternatingCrosscutData G)

private theorem x_not_mem_edge0 : D.x ∉ Set.range (path 0) := by
  intro hx0
  exact D.x_not_endpoint (by
    rw [← G.range_inter (show (0 : Fin 3) ≠ 1 by decide)]
    exact ⟨hx0, D.x_mem_edge1⟩)

private theorem x_not_mem_edge2 : D.x ∉ Set.range (path 2) := by
  intro hx2
  exact D.x_not_endpoint (by
    rw [← G.range_inter (show (1 : Fin 3) ≠ 2 by decide)]
    exact ⟨D.x_mem_edge1, hx2⟩)

private theorem y_not_mem_edge0 : D.y ∉ Set.range (path 0) := by
  intro hy0
  exact D.y_not_endpoint (by
    rw [← G.range_inter (show (0 : Fin 3) ≠ 2 by decide)]
    exact ⟨hy0, D.y_mem_edge2⟩)

private theorem y_not_mem_edge1 : D.y ∉ Set.range (path 1) := by
  intro hy1
  exact D.y_not_endpoint (by
    rw [← G.range_inter (show (1 : Fin 3) ≠ 2 by decide)]
    exact ⟨hy1, D.y_mem_edge2⟩)

private theorem x_not_mem_circle02 : D.x ∉ G.circle02.carrier := by
  rw [G.carrier_circle02]
  exact fun hx ↦ hx.elim D.x_not_mem_edge0 D.x_not_mem_edge2

private theorem y_not_mem_circle01 : D.y ∉ G.circle01.carrier := by
  rw [G.carrier_circle01]
  exact fun hy ↦ hy.elim D.y_not_mem_edge0 D.y_not_mem_edge1

private theorem crosscut_Ioc_subset_circle01_compl :
    D.crosscut '' Ioc (0 : unitInterval) 1 ⊆ G.circle01.carrierᶜ := by
  rintro z ⟨t, ht, rfl⟩ hz
  rw [G.carrier_circle01] at hz
  rcases hz with hz0 | hz1
  · have hempty : D.crosscut t ∈ (∅ : Set Plane) := by
      rw [← D.crosscut_inter_edge0]
      exact ⟨⟨t, rfl⟩, hz0⟩
    exact hempty.elim
  · have hx : D.crosscut t = D.x := by
      rw [← Set.mem_singleton_iff, ← D.crosscut_inter_edge1]
      exact ⟨⟨t, rfl⟩, hz1⟩
    have ht0 : t = 0 := D.crosscut_injective (hx.trans D.crosscut.source.symm)
    exact (ne_of_gt ht.1) ht0

private theorem crosscut_Ioc_preconnected :
    IsPreconnected (D.crosscut '' Ioc (0 : unitInterval) 1) :=
  Set.ordConnected_Ioc.isPreconnected.image D.crosscut D.crosscut.continuous.continuousOn

private theorem y_mem_crosscut_Ioc :
    D.y ∈ D.crosscut '' Ioc (0 : unitInterval) 1 := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, D.crosscut.target⟩

private theorem child_closed_inter_rectangleClosed_eq_edge2
    (hdisjoint : Disjoint G.circle02.inside G.circle12.inside) :
    closure G.circle02.inside ∩ closure G.circle12.inside = Set.range (path 2) := by
  apply JordanThetaAmbientExtension.closure_inside_inter_eq_of_disjoint_inside_of_carrier_inter
    G.circle02 G.circle12 hdisjoint
  rw [G.carrier_circle02, G.carrier_circle12]
  apply Set.Subset.antisymm
  · rintro z ⟨hz0 | hz2, hz1 | hz2'⟩
    · have hzEnd : z ∈ ({a, b} : Set Plane) := by
        rw [← G.range_inter (show (0 : Fin 3) ≠ 1 by decide)]
        exact ⟨hz0, hz1⟩
      exact (G.toTopologicalPlanarJordanThetaData.endpoints_subset_edge2 hzEnd)
    · exact hz2'
    · exact hz2
    · exact hz2
  · intro z hz2
    exact ⟨Or.inr hz2, Or.inr hz2⟩

private theorem child_inside_disjoint_of_circle01_outer
    (houter : closure G.circle01.inside =
      closure G.circle02.inside ∪ closure G.circle12.inside) :
    Disjoint G.circle02.inside G.circle12.inside := by
  have h02 : G.circle02.carrier ⊆ G.circle01.inside ∪ G.circle01.carrier := by
    rw [← G.circle01.closure_inside, houter]
    intro z hz
    exact Or.inl (by rw [G.circle02.closure_inside]; exact Or.inr hz)
  have h12 : G.circle12.carrier ⊆ G.circle01.inside ∪ G.circle01.carrier := by
    rw [← G.circle01.closure_inside, houter]
    intro z hz
    exact Or.inr (by rw [G.circle12.closure_inside]; exact Or.inr hz)
  apply Schoenflies.JordanThetaRegions.disjoint_inside
    (Q := G.circle01) (K₀ := G.circle02) (K₁ := G.circle12)
    (B := Set.range (path 2)) (A₀ := Set.range (path 0))
    (A₁ := Set.range (path 1)) h02 h12
  · exact G.carrier_circle01
  · rw [G.carrier_circle02, Set.union_comm]
  · rw [G.carrier_circle12, Set.union_comm]
  · simpa only [ThreePathSystem.toTopologicalPlanarJordanThetaData,
      G.carrier_circle12] using
      G.toTopologicalPlanarJordanThetaData.private0_nonempty
  · simpa only [ThreePathSystem.toTopologicalPlanarJordanThetaData,
      G.carrier_circle02] using
      G.toTopologicalPlanarJordanThetaData.private1_nonempty

private theorem y_mem_circle01_inside
    (houter : closure G.circle01.inside =
      closure G.circle02.inside ∪ closure G.circle12.inside) :
    D.y ∈ G.circle01.inside := by
  have hyClosed : D.y ∈ closure G.circle01.inside := by
    rw [houter]
    left
    rw [G.circle02.closure_inside, G.carrier_circle02]
    exact Or.inr (Or.inr D.y_mem_edge2)
  rw [G.circle01.closure_inside] at hyClosed
  exact hyClosed.resolve_right D.y_not_mem_circle01

private theorem crosscut_Ioc_subset_circle01_inside
    (houter : closure G.circle01.inside =
      closure G.circle02.inside ∪ closure G.circle12.inside) :
    D.crosscut '' Ioc (0 : unitInterval) 1 ⊆ G.circle01.inside := by
  intro z hz
  have hsides := G.circle01.preconnected_subset_same_side
    D.crosscut_Ioc_preconnected D.crosscut_Ioc_subset_circle01_compl
    hz D.y_mem_crosscut_Ioc
  rcases hsides with hinside | houtside
  · exact hinside.1
  · exact False.elim <| Set.disjoint_left.mp G.circle01.inside_disjoint_outside
      (D.y_mem_circle01_inside houter) houtside.2

private theorem crosscut_Ioc_subset_circle02_closed
    (houter : closure G.circle01.inside =
      closure G.circle02.inside ∪ closure G.circle12.inside) :
    D.crosscut '' Ioc (0 : unitInterval) 1 ⊆ closure G.circle02.inside := by
  rintro z ⟨t, ht, rfl⟩
  by_cases hty : D.crosscut t = D.y
  · rw [hty, G.circle02.closure_inside, G.carrier_circle02]
    exact Or.inr (Or.inr D.y_mem_edge2)
  have htx : D.crosscut t ≠ D.x := by
    intro htx
    have ht0 : t = 0 := D.crosscut_injective (htx.trans D.crosscut.source.symm)
    exact (ne_of_gt ht.1) ht0
  have houtside : D.crosscut t ∈ G.circle12.outside :=
    D.crosscut_private_subset_rectangleOutside
      ⟨⟨t, rfl⟩, fun hends ↦ hends.elim htx hty⟩
  have hclosed : D.crosscut t ∈ closure G.circle01.inside :=
    subset_closure (D.crosscut_Ioc_subset_circle01_inside houter ⟨t, ht, rfl⟩)
  rw [houter] at hclosed
  rcases hclosed with h02 | h12
  · exact h02
  · rw [G.circle12.closure_inside] at h12
    rcases h12 with hinside | hcarrier
    · exact False.elim <| Set.disjoint_left.mp G.circle12.inside_disjoint_outside
        hinside houtside
    · exact False.elim <| G.circle12.outside_subset_compl houtside hcarrier

include D in
/-- If cycle `01` is outer, the alternating fourth exterior crosscut cannot exist. -/
theorem false_of_circle01_outer
    (houter : closure G.circle01.inside =
      closure G.circle02.inside ∪ closure G.circle12.inside) : False := by
  have hdisjoint := child_inside_disjoint_of_circle01_outer (G := G) houter
  have hclosedInter := child_closed_inter_rectangleClosed_eq_edge2 (G := G) hdisjoint
  have hxRectangleClosed : D.x ∈ closure G.circle12.inside := by
    rw [G.circle12.closure_inside, G.carrier_circle12]
    exact Or.inr (Or.inl D.x_mem_edge1)
  have hxClosureCrosscut : D.x ∈ closure (D.crosscut '' Ioc (0 : unitInterval) 1) := by
    have hsource : D.crosscut 0 ∈ closure (D.crosscut '' Ioc (0 : unitInterval) 1) := by
      apply map_mem_closure D.crosscut.continuous
      · rw [closure_Ioc (by norm_num : (0 : unitInterval) ≠ 1)]
        exact ⟨le_rfl, zero_le_one⟩
      · exact Set.mapsTo_image D.crosscut (Ioc (0 : unitInterval) 1)
    simpa only [D.crosscut.source] using hsource
  have hxChildClosed : D.x ∈ closure G.circle02.inside :=
    (closure_minimal (D.crosscut_Ioc_subset_circle02_closed houter) isClosed_closure)
      hxClosureCrosscut
  have hxEdge2 : D.x ∈ Set.range (path 2) := by
    rw [← hclosedInter]
    exact ⟨hxChildClosed, hxRectangleClosed⟩
  exact D.x_not_mem_edge2 hxEdge2

include D in
/-- Cycle `12` cannot be outer because a private point of edge zero is required to lie outside
that cycle. -/
theorem false_of_circle12_outer
    (houter : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside) : False := by
  have hprivate :
      (Set.range (path 0) \ (Set.range (path 1) ∪ Set.range (path 2))).Nonempty := by
    simpa only [ThreePathSystem.toTopologicalPlanarJordanThetaData] using
      G.toTopologicalPlanarJordanThetaData.private0_nonempty
  obtain ⟨z, hz0, hzPrivate⟩ := hprivate
  have hzNotEndpoint : z ∉ ({a, b} : Set Plane) := by
    intro hzEndpoint
    exact hzPrivate (Or.inl
      (G.toTopologicalPlanarJordanThetaData.endpoints_subset_edge1 hzEndpoint))
  have hzOutside : z ∈ G.circle12.outside :=
    D.edge0_private_subset_rectangleOutside ⟨hz0, hzNotEndpoint⟩
  have hzChildClosed : z ∈ closure G.circle01.inside := by
    rw [G.circle01.closure_inside, G.carrier_circle01]
    exact Or.inr (Or.inl hz0)
  have hzOuterClosed : z ∈ closure G.circle12.inside := by
    rw [houter]
    exact Or.inl hzChildClosed
  rw [G.circle12.closure_inside] at hzOuterClosed
  rcases hzOuterClosed with hzInside | hzCarrier
  · exact Set.disjoint_left.mp G.circle12.inside_disjoint_outside hzInside hzOutside
  · exact G.circle12.outside_subset_compl hzOutside hzCarrier

private theorem crosscut_Ico_subset_circle02_compl :
    D.crosscut '' Ico (0 : unitInterval) 1 ⊆ G.circle02.carrierᶜ := by
  rintro z ⟨t, ht, rfl⟩ hz
  rw [G.carrier_circle02] at hz
  rcases hz with hz0 | hz2
  · have hempty : D.crosscut t ∈ (∅ : Set Plane) := by
      rw [← D.crosscut_inter_edge0]
      exact ⟨⟨t, rfl⟩, hz0⟩
    exact hempty.elim
  · have hy : D.crosscut t = D.y := by
      rw [← Set.mem_singleton_iff, ← D.crosscut_inter_edge2]
      exact ⟨⟨t, rfl⟩, hz2⟩
    have ht1 : t = 1 := D.crosscut_injective (hy.trans D.crosscut.target.symm)
    exact (ne_of_lt ht.2) ht1

private theorem crosscut_Ico_preconnected :
    IsPreconnected (D.crosscut '' Ico (0 : unitInterval) 1) :=
  Set.ordConnected_Ico.isPreconnected.image D.crosscut D.crosscut.continuous.continuousOn

private theorem x_mem_crosscut_Ico :
    D.x ∈ D.crosscut '' Ico (0 : unitInterval) 1 := by
  refine ⟨0, ⟨le_rfl, by norm_num⟩, D.crosscut.source⟩

private theorem child_closed_inter_rectangleClosed_eq_edge1
    (hdisjoint : Disjoint G.circle01.inside G.circle12.inside) :
    closure G.circle01.inside ∩ closure G.circle12.inside = Set.range (path 1) := by
  apply JordanThetaAmbientExtension.closure_inside_inter_eq_of_disjoint_inside_of_carrier_inter
    G.circle01 G.circle12 hdisjoint
  rw [G.carrier_circle01, G.carrier_circle12]
  apply Set.Subset.antisymm
  · rintro z ⟨hz0 | hz1, hz1' | hz2⟩
    · exact hz1'
    · have hzEnd : z ∈ ({a, b} : Set Plane) := by
        rw [← G.range_inter (show (0 : Fin 3) ≠ 2 by decide)]
        exact ⟨hz0, hz2⟩
      exact G.toTopologicalPlanarJordanThetaData.endpoints_subset_edge1 hzEnd
    · exact hz1
    · exact hz1
  · intro z hz1
    exact ⟨Or.inr hz1, Or.inl hz1⟩

private theorem child_inside_disjoint_of_circle02_outer
    (houter : closure G.circle02.inside =
      closure G.circle01.inside ∪ closure G.circle12.inside) :
    Disjoint G.circle01.inside G.circle12.inside := by
  have h01 : G.circle01.carrier ⊆ G.circle02.inside ∪ G.circle02.carrier := by
    rw [← G.circle02.closure_inside, houter]
    intro z hz
    exact Or.inl (by rw [G.circle01.closure_inside]; exact Or.inr hz)
  have h12 : G.circle12.carrier ⊆ G.circle02.inside ∪ G.circle02.carrier := by
    rw [← G.circle02.closure_inside, houter]
    intro z hz
    exact Or.inr (by rw [G.circle12.closure_inside]; exact Or.inr hz)
  apply Schoenflies.JordanThetaRegions.disjoint_inside
    (Q := G.circle02) (K₀ := G.circle01) (K₁ := G.circle12)
    (B := Set.range (path 1)) (A₀ := Set.range (path 0))
    (A₁ := Set.range (path 2)) h01 h12
  · exact G.carrier_circle02
  · rw [G.carrier_circle01, Set.union_comm]
  · exact G.carrier_circle12
  · simpa only [ThreePathSystem.toTopologicalPlanarJordanThetaData,
      G.carrier_circle12] using
      G.toTopologicalPlanarJordanThetaData.private0_nonempty
  · simpa only [ThreePathSystem.toTopologicalPlanarJordanThetaData,
      G.carrier_circle01] using
      G.toTopologicalPlanarJordanThetaData.private2_nonempty

private theorem x_mem_circle02_inside
    (houter : closure G.circle02.inside =
      closure G.circle01.inside ∪ closure G.circle12.inside) :
    D.x ∈ G.circle02.inside := by
  have hxClosed : D.x ∈ closure G.circle02.inside := by
    rw [houter]
    left
    rw [G.circle01.closure_inside, G.carrier_circle01]
    exact Or.inr (Or.inr D.x_mem_edge1)
  rw [G.circle02.closure_inside] at hxClosed
  exact hxClosed.resolve_right D.x_not_mem_circle02

private theorem crosscut_Ico_subset_circle02_inside
    (houter : closure G.circle02.inside =
      closure G.circle01.inside ∪ closure G.circle12.inside) :
    D.crosscut '' Ico (0 : unitInterval) 1 ⊆ G.circle02.inside := by
  intro z hz
  have hsides := G.circle02.preconnected_subset_same_side
    D.crosscut_Ico_preconnected D.crosscut_Ico_subset_circle02_compl
    hz D.x_mem_crosscut_Ico
  rcases hsides with hinside | houtside
  · exact hinside.1
  · exact False.elim <| Set.disjoint_left.mp G.circle02.inside_disjoint_outside
      (D.x_mem_circle02_inside houter) houtside.2

private theorem crosscut_Ico_subset_circle01_closed
    (houter : closure G.circle02.inside =
      closure G.circle01.inside ∪ closure G.circle12.inside) :
    D.crosscut '' Ico (0 : unitInterval) 1 ⊆ closure G.circle01.inside := by
  rintro z ⟨t, ht, rfl⟩
  by_cases htx : D.crosscut t = D.x
  · rw [htx, G.circle01.closure_inside, G.carrier_circle01]
    exact Or.inr (Or.inr D.x_mem_edge1)
  have hty : D.crosscut t ≠ D.y := by
    intro hty
    have ht1 : t = 1 := D.crosscut_injective (hty.trans D.crosscut.target.symm)
    exact (ne_of_lt ht.2) ht1
  have houtside : D.crosscut t ∈ G.circle12.outside :=
    D.crosscut_private_subset_rectangleOutside
      ⟨⟨t, rfl⟩, fun hends ↦ hends.elim htx hty⟩
  have hclosed : D.crosscut t ∈ closure G.circle02.inside :=
    subset_closure (D.crosscut_Ico_subset_circle02_inside houter ⟨t, ht, rfl⟩)
  rw [houter] at hclosed
  rcases hclosed with h01 | h12
  · exact h01
  · rw [G.circle12.closure_inside] at h12
    rcases h12 with hinside | hcarrier
    · exact False.elim <| Set.disjoint_left.mp G.circle12.inside_disjoint_outside
        hinside houtside
    · exact False.elim <| G.circle12.outside_subset_compl houtside hcarrier

include D in
/-- If cycle `02` is outer, the alternating fourth exterior crosscut cannot exist. -/
theorem false_of_circle02_outer
    (houter : closure G.circle02.inside =
      closure G.circle01.inside ∪ closure G.circle12.inside) : False := by
  have hdisjoint := child_inside_disjoint_of_circle02_outer (G := G) houter
  have hclosedInter := child_closed_inter_rectangleClosed_eq_edge1 (G := G) hdisjoint
  have hyRectangleClosed : D.y ∈ closure G.circle12.inside := by
    rw [G.circle12.closure_inside, G.carrier_circle12]
    exact Or.inr (Or.inr D.y_mem_edge2)
  have hyClosureCrosscut : D.y ∈ closure (D.crosscut '' Ico (0 : unitInterval) 1) := by
    have htarget : D.crosscut 1 ∈ closure (D.crosscut '' Ico (0 : unitInterval) 1) := by
      apply map_mem_closure D.crosscut.continuous
      · rw [closure_Ico (by norm_num : (0 : unitInterval) ≠ 1)]
        exact ⟨zero_le_one, le_rfl⟩
      · exact Set.mapsTo_image D.crosscut (Ico (0 : unitInterval) 1)
    simpa only [D.crosscut.target] using htarget
  have hyChildClosed : D.y ∈ closure G.circle01.inside :=
    (closure_minimal (D.crosscut_Ico_subset_circle01_closed houter) isClosed_closure)
      hyClosureCrosscut
  have hyEdge1 : D.y ∈ Set.range (path 1) := by
    rw [← hclosedInter]
    exact ⟨hyChildClosed, hyRectangleClosed⟩
  exact D.y_not_mem_edge1 hyEdge1

include D in
/-- No planar alternating exterior crosscut satisfies the four-path incidence data. -/
theorem false : False := by
  rcases G.exists_outer_cycle_decomposition with h01 | h02 | h12
  · exact D.false_of_circle01_outer h01
  · exact D.false_of_circle02_outer h02
  · exact D.false_of_circle12_outer h12

end AlternatingCrosscutData
end ThreePathSystem
end Submission.Topology
