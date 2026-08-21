import Submission.Topology.FourPortSixEdgeGraph

/-!
# Constructing a six-edge system from its two child circles

The two child cycles and exact endpoint incidence of the vertical sides determine the embedded
central cycle.  This packages the set algebra and path-concatenation argument once.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X]

/-- Constituent data sufficient to construct the full six-edge path system. -/
structure FourPortSixEdgeConstituentData where
  leftBottom : X
  leftTop : X
  rightBottom : X
  rightTop : X
  left : Path leftBottom leftTop
  right : Path rightBottom rightTop
  bottom : Path leftBottom rightBottom
  top : Path leftTop rightTop
  bottomOutside : Path rightBottom leftBottom
  topOutside : Path rightTop leftTop
  bottomData : TwoArcCircle.Data bottom bottomOutside
  topData : TwoArcCircle.Data top topOutside
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  left_disjoint_right : Disjoint (Set.range left) (Set.range right)
  children_disjoint :
    Disjoint (Set.range bottom ∪ Set.range bottomOutside)
      (Set.range top ∪ Set.range topOutside)
  left_inter_bottom :
    Set.range left ∩ (Set.range bottom ∪ Set.range bottomOutside) = {leftBottom}
  right_inter_bottom :
    Set.range right ∩ (Set.range bottom ∪ Set.range bottomOutside) = {rightBottom}
  left_inter_top :
    Set.range left ∩ (Set.range top ∪ Set.range topOutside) = {leftTop}
  right_inter_top :
    Set.range right ∩ (Set.range top ∪ Set.range topOutside) = {rightTop}

namespace FourPortSixEdgeConstituentData

variable (D : FourPortSixEdgeConstituentData (X := X))

private theorem left_inter_topOutside :
    Set.range D.left ∩ Set.range D.topOutside = {D.leftTop} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ Set.range D.left ∩
        (Set.range D.top ∪ Set.range D.topOutside) := ⟨hx.1, Or.inr hx.2⟩
    rwa [D.left_inter_top] at hx'
  · rintro x rfl
    exact ⟨⟨1, D.left.target⟩, ⟨1, D.topOutside.target⟩⟩

private theorem topOutside_inter_right :
    Set.range D.topOutside ∩ Set.range D.right = {D.rightTop} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ Set.range D.right ∩
        (Set.range D.top ∪ Set.range D.topOutside) := ⟨hx.2, Or.inr hx.1⟩
    rw [D.right_inter_top] at hx'
    exact hx'
  · rintro x rfl
    exact ⟨⟨0, D.topOutside.source⟩, ⟨1, D.right.target⟩⟩

private theorem leftTopOutsidePath_injective :
    Function.Injective (D.left.trans D.topOutside.symm) := by
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
  · exact D.left_injective
  · exact D.topData.second_injective.comp unitInterval.symm_bijective.injective
  · simpa only [Path.symm_range] using D.left_inter_topOutside

private theorem leftTopOutside_inter_right :
    Set.range (D.left.trans D.topOutside.symm) ∩ Set.range D.right = {D.rightTop} := by
  rw [Path.trans_range, Path.symm_range, union_inter_distrib_right,
    Set.disjoint_iff_inter_eq_empty.mp D.left_disjoint_right,
    D.topOutside_inter_right, Set.empty_union]

private theorem centralUpper_injective :
    Function.Injective
      (fourPortCentralUpperPath D.left D.topOutside D.right) := by
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
  · exact D.leftTopOutsidePath_injective
  · exact D.right_injective.comp unitInterval.symm_bijective.injective
  · simpa only [Path.symm_range] using D.leftTopOutside_inter_right

private theorem topOutside_disjoint_bottomCarrier :
    Disjoint (Set.range D.topOutside)
      (Set.range D.bottom ∪ Set.range D.bottomOutside) :=
  D.children_disjoint.symm.mono Set.subset_union_right Set.Subset.rfl

private theorem bottomOutside_disjoint_topCarrier :
    Disjoint (Set.range D.bottomOutside)
      (Set.range D.top ∪ Set.range D.topOutside) :=
  D.children_disjoint.mono Set.subset_union_right Set.Subset.rfl

private theorem centralUpper_inter_bottomOutside :
    Set.range (fourPortCentralUpperPath D.left D.topOutside D.right) ∩
        Set.range D.bottomOutside = {D.leftBottom, D.rightBottom} := by
  rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
    Path.symm_range, Path.symm_range, union_inter_distrib_right,
    union_inter_distrib_right]
  have hleft : Set.range D.left ∩ Set.range D.bottomOutside = {D.leftBottom} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ Set.range D.left ∩
          (Set.range D.bottom ∪ Set.range D.bottomOutside) := ⟨hx.1, Or.inr hx.2⟩
      rwa [D.left_inter_bottom] at hx'
    · rintro x rfl
      exact ⟨⟨0, D.left.source⟩, ⟨1, D.bottomOutside.target⟩⟩
  have hright : Set.range D.right ∩ Set.range D.bottomOutside = {D.rightBottom} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ Set.range D.right ∩
          (Set.range D.bottom ∪ Set.range D.bottomOutside) := ⟨hx.1, Or.inr hx.2⟩
      rwa [D.right_inter_bottom] at hx'
    · rintro x rfl
      exact ⟨⟨0, D.right.source⟩, ⟨0, D.bottomOutside.source⟩⟩
  have hdis : Disjoint (Set.range D.topOutside) (Set.range D.bottomOutside) :=
    D.topOutside_disjoint_bottomCarrier.mono_right Set.subset_union_right
  rw [hleft, hright, Set.disjoint_iff_inter_eq_empty.mp hdis, Set.union_empty]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

private theorem centralData :
    TwoArcCircle.Data
      (fourPortCentralUpperPath D.left D.topOutside D.right) D.bottomOutside where
  first_injective := D.centralUpper_injective
  second_injective := D.bottomData.second_injective
  range_inter := D.centralUpper_inter_bottomOutside

private theorem central_inter_bottom :
    (Set.range (fourPortCentralUpperPath D.left D.topOutside D.right) ∪
        Set.range D.bottomOutside) ∩
      (Set.range D.bottom ∪ Set.range D.bottomOutside) = Set.range D.bottomOutside := by
  apply Set.Subset.antisymm
  · rintro x ⟨hcentral, hbottom⟩
    rcases hcentral with hupper | houtside
    · rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
        Path.symm_range, Path.symm_range] at hupper
      rcases hupper with (hleft | htopOutside) | hright
      · have hx := Set.mem_inter hleft hbottom
        rw [D.left_inter_bottom] at hx
        rcases hx with rfl
        exact ⟨1, D.bottomOutside.target⟩
      · exact False.elim <|
          Set.disjoint_left.mp D.topOutside_disjoint_bottomCarrier htopOutside hbottom
      · have hx := Set.mem_inter hright hbottom
        rw [D.right_inter_bottom] at hx
        rcases hx with rfl
        exact ⟨0, D.bottomOutside.source⟩
    · exact houtside
  · intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩

private theorem central_inter_top :
    (Set.range (fourPortCentralUpperPath D.left D.topOutside D.right) ∪
        Set.range D.bottomOutside) ∩
      (Set.range D.top ∪ Set.range D.topOutside) = Set.range D.topOutside := by
  apply Set.Subset.antisymm
  · rintro x ⟨hcentral, htop⟩
    rcases hcentral with hupper | hbottomOutside
    · rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
        Path.symm_range, Path.symm_range] at hupper
      rcases hupper with (hleft | htopOutside) | hright
      · have hx := Set.mem_inter hleft htop
        rw [D.left_inter_top] at hx
        rcases hx with rfl
        exact ⟨1, D.topOutside.target⟩
      · exact htopOutside
      · have hx := Set.mem_inter hright htop
        rw [D.right_inter_top] at hx
        rcases hx with rfl
        exact ⟨0, D.topOutside.source⟩
    · exact False.elim <|
        Set.disjoint_left.mp D.bottomOutside_disjoint_topCarrier hbottomOutside htop
  · intro x hx
    exact ⟨Or.inl (by
      rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range, Path.symm_range]
      exact Or.inl (Or.inr hx)), Or.inr hx⟩

/-- Assemble the honest six-edge system from its constituent incidence. -/
def toFourPortSixEdgePathSystem : FourPortSixEdgePathSystem X where
  leftBottom := D.leftBottom
  leftTop := D.leftTop
  rightBottom := D.rightBottom
  rightTop := D.rightTop
  left := D.left
  right := D.right
  bottom := D.bottom
  top := D.top
  bottomOutside := D.bottomOutside
  topOutside := D.topOutside
  bottomData := D.bottomData
  topData := D.topData
  centralData := D.centralData
  central_inter_bottom := D.central_inter_bottom
  central_inter_top := D.central_inter_top
  bottom_disjoint_top := D.children_disjoint

end FourPortSixEdgeConstituentData
end Submission.Topology
