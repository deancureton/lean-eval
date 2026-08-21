import Submission.Topology.FourPortSixEdgeGraph

/-!
# Restricting a six-edge graph to a carrier subtype

A six-edge graph whose constituent paths lie in one set canonically restricts to a graph in that
set.  Exact path incidence is preserved because subtype inclusion is injective.
-/

open Set

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X] {s : Set X}

private def pathToSubtype {a b : X} (p : Path a b) (hp : Set.range p ⊆ s) :
    Path (⟨a, hp (Path.source_mem_range p)⟩ : s)
      (⟨b, hp (Path.target_mem_range p)⟩ : s) where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] private theorem pathToSubtype_apply
    {a b : X} (p : Path a b) (hp : Set.range p ⊆ s) (t : unitInterval) :
    ((pathToSubtype p hp t : s) : X) = p t :=
  rfl

private theorem range_pathToSubtype
    {a b : X} (p : Path a b) (hp : Set.range p ⊆ s) :
    Set.range (pathToSubtype p hp) = Subtype.val ⁻¹' Set.range p := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, Subtype.ext ?_⟩
    exact ht

/-- Proof that all six constituent paths of a graph lie in one carrier. -/
structure FourPortSixEdgeCarrierData (G : FourPortSixEdgePathSystem X) (s : Set X) : Prop where
  left : Set.range G.left ⊆ s
  right : Set.range G.right ⊆ s
  bottom : Set.range G.bottom ⊆ s
  top : Set.range G.top ⊆ s
  bottomOutside : Set.range G.bottomOutside ⊆ s
  topOutside : Set.range G.topOutside ⊆ s

namespace FourPortSixEdgeCarrierData

variable {G : FourPortSixEdgePathSystem X} (H : FourPortSixEdgeCarrierData G s)

omit [TopologicalSpace X] in
private theorem preimage_singleton (x : s) :
    Subtype.val ⁻¹' ({(x : X)} : Set X) = {x} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact Subtype.coe_injective.eq_iff

private theorem lifted_twoArcData
    {a b : X} (p : Path a b) (q : Path b a)
    (hp : Set.range p ⊆ s) (hq : Set.range q ⊆ s)
    (D : TwoArcCircle.Data p q) :
    TwoArcCircle.Data (pathToSubtype p hp) (pathToSubtype q hq) where
  first_injective := fun _ _ h ↦ D.first_injective (congrArg Subtype.val h)
  second_injective := fun _ _ h ↦ D.second_injective (congrArg Subtype.val h)
  range_inter := by
    rw [range_pathToSubtype, range_pathToSubtype, ← Set.preimage_inter,
      D.range_inter]
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext hx)
    · rintro (hx | hx)
      · exact Or.inl (congrArg Subtype.val hx)
      · exact Or.inr (congrArg Subtype.val hx)

private theorem lifted_disjoint
    {a b c d : X} (p : Path a b) (q : Path c d)
    (hp : Set.range p ⊆ s) (hq : Set.range q ⊆ s)
    (hdisjoint : Disjoint (Set.range p) (Set.range q)) :
    Disjoint (Set.range (pathToSubtype p hp)) (Set.range (pathToSubtype q hq)) := by
  rw [Set.disjoint_iff_inter_eq_empty, range_pathToSubtype, range_pathToSubtype,
    ← Set.preimage_inter, Set.disjoint_iff_inter_eq_empty.mp hdisjoint,
    Set.preimage_empty]

/-- Restrict the entire six-edge graph to its carrier subtype. -/
noncomputable def toSubtypeGraph : FourPortSixEdgePathSystem s where
  leftBottom := ⟨G.leftBottom, H.left (Path.source_mem_range G.left)⟩
  leftTop := ⟨G.leftTop, H.left (Path.target_mem_range G.left)⟩
  rightBottom := ⟨G.rightBottom, H.right (Path.source_mem_range G.right)⟩
  rightTop := ⟨G.rightTop, H.right (Path.target_mem_range G.right)⟩
  left := pathToSubtype G.left H.left
  right := pathToSubtype G.right H.right
  bottom := pathToSubtype G.bottom H.bottom
  top := pathToSubtype G.top H.top
  bottomOutside := pathToSubtype G.bottomOutside H.bottomOutside
  topOutside := pathToSubtype G.topOutside H.topOutside
  bottomData := lifted_twoArcData G.bottom G.bottomOutside
    H.bottom H.bottomOutside G.bottomData
  topData := lifted_twoArcData G.top G.topOutside H.top H.topOutside G.topData
  centralData := by
    let hcentral : Set.range
        (fourPortCentralUpperPath G.left G.topOutside G.right) ⊆ s := by
      rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
        Path.symm_range, Path.symm_range]
      exact Set.union_subset (Set.union_subset H.left H.topOutside) H.right
    have hpath :
        fourPortCentralUpperPath (pathToSubtype G.left H.left)
            (pathToSubtype G.topOutside H.topOutside)
            (pathToSubtype G.right H.right) =
          pathToSubtype (fourPortCentralUpperPath G.left G.topOutside G.right)
            hcentral := by
      apply Path.ext
      funext t
      apply Subtype.ext
      change ((fourPortCentralUpperPath (pathToSubtype G.left H.left)
          (pathToSubtype G.topOutside H.topOutside)
          (pathToSubtype G.right H.right) t : s) : X) =
        fourPortCentralUpperPath G.left G.topOutside G.right t
      simp only [fourPortCentralUpperPath, Path.trans_apply, Path.symm_apply,
        Function.comp_apply]
      split
      · split <;> rfl
      · rfl
    rw [hpath]
    exact lifted_twoArcData
      (fourPortCentralUpperPath G.left G.topOutside G.right) G.bottomOutside
      hcentral H.bottomOutside G.centralData
  central_inter_bottom := by
    simp only [fourPortCentralUpperPath, Path.trans_range, Path.symm_range]
    simp only [range_pathToSubtype]
    have h := congrArg (Set.preimage (Subtype.val : s → X)) G.central_inter_bottom
    rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
      Path.symm_range, Path.symm_range] at h
    simpa only [Set.preimage_inter, Set.preimage_union] using h
  central_inter_top := by
    simp only [fourPortCentralUpperPath, Path.trans_range, Path.symm_range]
    simp only [range_pathToSubtype]
    have h := congrArg (Set.preimage (Subtype.val : s → X)) G.central_inter_top
    rw [fourPortCentralUpperPath, Path.trans_range, Path.trans_range,
      Path.symm_range, Path.symm_range] at h
    simpa only [Set.preimage_inter, Set.preimage_union] using h
  bottom_disjoint_top := by
    simp only [Set.disjoint_iff_inter_eq_empty, range_pathToSubtype]
    have h := congrArg (Set.preimage (Subtype.val : s → X))
      (Set.disjoint_iff_inter_eq_empty.mp G.bottom_disjoint_top)
    simpa only [Set.preimage_inter, Set.preimage_union, Set.preimage_empty] using h

@[simp] theorem range_toSubtypeGraph_left :
    Set.range H.toSubtypeGraph.left = Subtype.val ⁻¹' Set.range G.left :=
  range_pathToSubtype G.left H.left

@[simp] theorem range_toSubtypeGraph_right :
    Set.range H.toSubtypeGraph.right = Subtype.val ⁻¹' Set.range G.right :=
  range_pathToSubtype G.right H.right

@[simp] theorem range_toSubtypeGraph_bottom :
    Set.range H.toSubtypeGraph.bottom = Subtype.val ⁻¹' Set.range G.bottom :=
  range_pathToSubtype G.bottom H.bottom

@[simp] theorem range_toSubtypeGraph_top :
    Set.range H.toSubtypeGraph.top = Subtype.val ⁻¹' Set.range G.top :=
  range_pathToSubtype G.top H.top

@[simp] theorem coe_toSubtypeGraph_centralCircle (z : Circle) :
    ((H.toSubtypeGraph.centralCircle z : s) : X) = G.centralCircle z := by
  apply TwoArcCircle.map_circleMap_of_pointwise
  · intro t
    simp only [fourPortCentralUpperPath, Path.trans_apply, Path.symm_apply,
      Function.comp_apply]
    split
    · split <;> rfl
    · rfl
  · intro t
    rfl

@[simp] theorem coe_toSubtypeGraph_bottomCircle (z : Circle) :
    ((H.toSubtypeGraph.bottomCircle z : s) : X) = G.bottomCircle z := by
  apply TwoArcCircle.map_circleMap_of_pointwise <;> intro t <;> rfl

@[simp] theorem coe_toSubtypeGraph_topCircle (z : Circle) :
    ((H.toSubtypeGraph.topCircle z : s) : X) = G.topCircle z := by
  apply TwoArcCircle.map_circleMap_of_pointwise <;> intro t <;> rfl

end FourPortSixEdgeCarrierData
end Submission.Topology
