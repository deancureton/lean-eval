import Submission.Topology.PlanarAlternatingCrosscutObstruction

/-!
# The planar obstruction to a diagonal four-port graph

Four local rectangle sides and two crossed exterior routes form a subdivision of `K₄`.  The
upper exterior route together with the two local rectangle routes is a theta graph, while the
lower exterior route is an alternating crosscut.  This file derives that theta data from exact
six-edge incidence and then applies the planar alternating-crosscut obstruction.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

variable (X : Type) [TopologicalSpace X]

/-- Six injective paths with the exact incidence of the diagonal four-port `K₄` graph. -/
structure FourPortDiagonalPathSystem where
  leftBottom : X
  leftTop : X
  rightBottom : X
  rightTop : X
  left : Path leftBottom leftTop
  right : Path rightBottom rightTop
  bottom : Path leftBottom rightBottom
  top : Path leftTop rightTop
  lower : Path leftTop rightBottom
  upper : Path rightTop leftBottom
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  bottom_injective : Function.Injective bottom
  top_injective : Function.Injective top
  lower_injective : Function.Injective lower
  upper_injective : Function.Injective upper
  upper_inter_left : Set.range upper ∩ Set.range left = {leftBottom}
  upper_inter_top : Set.range upper ∩ Set.range top = {rightTop}
  upper_inter_bottom : Set.range upper ∩ Set.range bottom = {leftBottom}
  upper_inter_right : Set.range upper ∩ Set.range right = {rightTop}
  left_inter_top : Set.range left ∩ Set.range top = {leftTop}
  bottom_inter_right : Set.range bottom ∩ Set.range right = {rightBottom}
  left_inter_bottom : Set.range left ∩ Set.range bottom = {leftBottom}
  left_inter_right : Set.range left ∩ Set.range right = ∅
  top_inter_bottom : Set.range top ∩ Set.range bottom = ∅
  top_inter_right : Set.range top ∩ Set.range right = {rightTop}
  lower_inter_upper : Set.range lower ∩ Set.range upper = ∅
  lower_inter_left : Set.range lower ∩ Set.range left = {leftTop}
  lower_inter_top : Set.range lower ∩ Set.range top = {leftTop}
  lower_inter_bottom : Set.range lower ∩ Set.range bottom = {rightBottom}
  lower_inter_right : Set.range lower ∩ Set.range right = {rightBottom}
  leftTop_ne_leftBottom : leftTop ≠ leftBottom
  leftTop_ne_rightTop : leftTop ≠ rightTop
  rightBottom_ne_leftBottom : rightBottom ≠ leftBottom
  rightBottom_ne_rightTop : rightBottom ≠ rightTop

namespace FourPortDiagonalPathSystem

variable {X} (G : FourPortDiagonalPathSystem X)

private theorem left_trans_top_injective : Function.Injective (G.left.trans G.top) :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    G.left G.top G.left_injective G.top_injective G.left_inter_top

private theorem bottom_trans_right_injective :
    Function.Injective (G.bottom.trans G.right) :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    G.bottom G.right G.bottom_injective G.right_injective G.bottom_inter_right

/-- The three paths from the lower-left to the upper-right port. -/
def thetaPath : Fin 3 → Path G.leftBottom G.rightTop
  | 0 => G.upper.symm
  | 1 => G.left.trans G.top
  | 2 => G.bottom.trans G.right

private theorem upper_inter_left_trans_top :
    Set.range G.upper ∩ Set.range (G.left.trans G.top) =
      {G.leftBottom, G.rightTop} := by
  rw [Path.trans_range, Set.inter_union_distrib_left, G.upper_inter_left,
    G.upper_inter_top]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

private theorem upper_inter_bottom_trans_right :
    Set.range G.upper ∩ Set.range (G.bottom.trans G.right) =
      {G.leftBottom, G.rightTop} := by
  rw [Path.trans_range, Set.inter_union_distrib_left, G.upper_inter_bottom,
    G.upper_inter_right]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

private theorem left_trans_top_inter_bottom_trans_right :
    Set.range (G.left.trans G.top) ∩ Set.range (G.bottom.trans G.right) =
      {G.leftBottom, G.rightTop} := by
  rw [Path.trans_range, Path.trans_range, Set.union_inter_distrib_right,
    Set.inter_union_distrib_left, Set.inter_union_distrib_left,
    G.left_inter_bottom, G.left_inter_right, G.top_inter_bottom,
    G.top_inter_right, Set.union_empty, Set.empty_union]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- The upper exterior route and the two local rectangle routes form a theta graph. -/
theorem thetaSystem (H : FourPortDiagonalPathSystem Plane) : ThreePathSystem H.thetaPath where
  injective := by
    intro i
    fin_cases i
    · intro s t hst
      apply unitInterval.symm_bijective.injective
      apply H.upper_injective
      simpa only [thetaPath, Path.symm_apply, Function.comp_apply] using hst
    · exact H.left_trans_top_injective
    · exact H.bottom_trans_right_injective
  range_inter := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [thetaPath, Path.symm_range] using H.upper_inter_left_trans_top
    · simpa only [thetaPath, Path.symm_range] using H.upper_inter_bottom_trans_right
    · rw [Set.inter_comm]
      simpa only [thetaPath, Path.symm_range] using H.upper_inter_left_trans_top
    · exact (hij rfl).elim
    · simpa only [thetaPath] using H.left_trans_top_inter_bottom_trans_right
    · rw [Set.inter_comm]
      simpa only [thetaPath, Path.symm_range] using H.upper_inter_bottom_trans_right
    · rw [Set.inter_comm]
      simpa only [thetaPath] using H.left_trans_top_inter_bottom_trans_right
    · exact (hij rfl).elim

private theorem lower_inter_left_trans_top :
    Set.range G.lower ∩ Set.range (G.left.trans G.top) = {G.leftTop} := by
  rw [Path.trans_range, Set.inter_union_distrib_left, G.lower_inter_left,
    G.lower_inter_top, Set.union_self]

private theorem lower_inter_bottom_trans_right :
    Set.range G.lower ∩ Set.range (G.bottom.trans G.right) = {G.rightBottom} := by
  rw [Path.trans_range, Set.inter_union_distrib_left, G.lower_inter_bottom,
    G.lower_inter_right, Set.union_self]

private theorem leftTop_mem_left_trans_top :
    G.leftTop ∈ Set.range (G.left.trans G.top) := by
  rw [Path.trans_range]
  exact Or.inl ⟨1, G.left.target⟩

private theorem rightBottom_mem_bottom_trans_right :
    G.rightBottom ∈ Set.range (G.bottom.trans G.right) := by
  rw [Path.trans_range]
  exact Or.inl ⟨1, G.bottom.target⟩

variable {G : FourPortDiagonalPathSystem Plane}

/-- Exterior-side data for the two crossed routes relative to the local rectangle cycle. -/
structure ExteriorSideData (G : FourPortDiagonalPathSystem Plane) where
  upper_private_subset_rectangleOutside :
    Set.range G.upper \ {G.rightTop, G.leftBottom} ⊆ G.thetaSystem.circle12.outside
  lower_private_subset_rectangleOutside :
    Set.range G.lower \ {G.leftTop, G.rightBottom} ⊆ G.thetaSystem.circle12.outside

namespace ExteriorSideData

variable (D : G.ExteriorSideData)

/-- Exact six-edge incidence and exterior sidedness produce the alternating crosscut. -/
def alternatingCrosscutData : ThreePathSystem.AlternatingCrosscutData G.thetaSystem where
  x := G.leftTop
  y := G.rightBottom
  crosscut := G.lower
  crosscut_injective := G.lower_injective
  x_mem_edge1 := by
    change G.leftTop ∈ Set.range (G.left.trans G.top)
    exact G.leftTop_mem_left_trans_top
  y_mem_edge2 := by
    change G.rightBottom ∈ Set.range (G.bottom.trans G.right)
    exact G.rightBottom_mem_bottom_trans_right
  x_not_endpoint := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨G.leftTop_ne_leftBottom, G.leftTop_ne_rightTop⟩
  y_not_endpoint := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨G.rightBottom_ne_leftBottom, G.rightBottom_ne_rightTop⟩
  crosscut_inter_edge0 := by
    change Set.range G.lower ∩ Set.range G.upper.symm = ∅
    simpa only [Path.symm_range] using G.lower_inter_upper
  crosscut_inter_edge1 := by
    change Set.range G.lower ∩ Set.range (G.left.trans G.top) = {G.leftTop}
    exact G.lower_inter_left_trans_top
  crosscut_inter_edge2 := by
    change Set.range G.lower ∩ Set.range (G.bottom.trans G.right) = {G.rightBottom}
    exact G.lower_inter_bottom_trans_right
  edge0_private_subset_rectangleOutside := by
    change Set.range G.upper.symm \ {G.leftBottom, G.rightTop} ⊆
      G.thetaSystem.circle12.outside
    simpa only [Path.symm_range, Set.pair_comm] using
      D.upper_private_subset_rectangleOutside
  crosscut_private_subset_rectangleOutside :=
    D.lower_private_subset_rectangleOutside

/-- A planar diagonal four-port graph with both exterior routes outside is impossible. -/
theorem false (D : G.ExteriorSideData) : False :=
  ThreePathSystem.AlternatingCrosscutData.false D.alternatingCrosscutData

end ExteriorSideData
end FourPortDiagonalPathSystem
end Submission.Topology
