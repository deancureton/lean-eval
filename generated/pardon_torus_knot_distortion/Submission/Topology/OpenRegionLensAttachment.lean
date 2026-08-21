import Mathlib.Topology.Sets.Opens

/-!
# Updating an open region by one lens

The reduced Pardon stages change one torus parity cell by attaching an open four-port lens.
For two open sets, the frontier of their union consists exactly of the part of each old frontier
not swallowed by the other open set.  This elementary identity is the set-theoretic core of the
prefix-stage construction.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X]

/-- The exact frontier of the union of two open regions. -/
theorem frontier_union_eq_sdiff_of_isOpen {a b : Set X}
    (ha : IsOpen a) (hb : IsOpen b) :
    frontier (a ∪ b) = (frontier a \ b) ∪ (frontier b \ a) := by
  rw [(ha.union hb).frontier_eq, closure_union, ha.frontier_eq, hb.frontier_eq]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

/-- Attaching an open lens preserves precisely the unabsorbed old face and exposes precisely the
unabsorbed lens face. -/
theorem frontier_union_eq_preserved_union_introduced {a lens preserved introduced : Set X}
    (ha : IsOpen a) (hlens : IsOpen lens)
    (hpreserved : frontier a \ lens = preserved)
    (hintroduced : frontier lens \ a = introduced) :
    frontier (a ∪ lens) = preserved ∪ introduced := by
  rw [frontier_union_eq_sdiff_of_isOpen ha hlens, hpreserved, hintroduced]

omit [TopologicalSpace X] in
/-- Membership can change when an open lens is attached only inside that lens. -/
theorem labelChange_union_subset_right (a lens : Set X) :
    {x | (x ∈ a) ≠ (x ∈ a ∪ lens)} ⊆ lens := by
  intro x hx
  by_contra hxlens
  apply hx
  simp only [Set.mem_union, hxlens, or_false]

/-- Removing a closed lens from an open region leaves an open region. -/
theorem isOpen_sdiff_of_isOpen_isClosed {a lens : Set X}
    (ha : IsOpen a) (hlens : IsClosed lens) : IsOpen (a \ lens) :=
  ha.inter hlens.isOpen_compl

omit [TopologicalSpace X] in
/-- Membership can change when a closed lens is removed only inside that lens. -/
theorem labelChange_sdiff_subset_right (a lens : Set X) :
    {x | (x ∈ a) ≠ (x ∈ a \ lens)} ⊆ lens := by
  intro x hx
  by_contra hxlens
  apply hx
  simp only [Set.mem_sdiff, hxlens, not_false_eq_true, and_true]

/-- Removing a closed lens introduces no frontier away from the old frontier or the lens
frontier. -/
theorem frontier_sdiff_subset_union {a lens : Set X} :
    frontier (a \ lens) ⊆ frontier a ∪ frontier lens := by
  change frontier (a ∩ lensᶜ) ⊆ frontier a ∪ frontier lens
  intro x hx
  rcases frontier_inter_subset a lensᶜ hx with hx | hx
  · exact Or.inl hx.1
  · exact Or.inr (by simpa only [frontier_compl] using hx.2)

end Submission.Topology
