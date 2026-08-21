import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Connected.Basic

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

/-- The interior of a finite union of pairwise-disjoint closed sets is the union of their
interiors. -/
theorem interior_iUnion_eq_iUnion_interior_of_pairwise_disjoint
    {ι : Type*} [Fintype ι] {s : ι → Set X}
    (hsClosed : ∀ i, IsClosed (s i))
    (hsDisjoint : Pairwise fun i j ↦ Disjoint (s i) (s j)) :
    interior (⋃ i, s i) = ⋃ i, interior (s i) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (interior_subset hx)
    let other : Set X := ⋃ j : {j : ι // j ≠ i}, s j.1
    have hotherClosed : IsClosed other := by
      apply isClosed_iUnion_of_finite
      exact fun j ↦ hsClosed j.1
    have hxOther : x ∉ other := by
      intro hxOther
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxOther
      exact Set.disjoint_left.mp (hsDisjoint j.2) hxj hxi
    have hopen : IsOpen (interior (⋃ i, s i) ∩ otherᶜ) :=
      isOpen_interior.inter hotherClosed.isOpen_compl
    have hsubset : interior (⋃ i, s i) ∩ otherᶜ ⊆ s i := by
      intro y hy
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (interior_subset hy.1)
      by_cases hji : j = i
      · simpa only [hji] using hyj
      · exact False.elim <| hy.2 (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
    exact Set.mem_iUnion.mpr ⟨i,
      interior_maximal hsubset hopen ⟨hx, hxOther⟩⟩
  · exact iUnion_subset fun i ↦ interior_mono (subset_iUnion s i)

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

/-- The boundary faces which are visibly active after removing a closed lens. -/
def sdiffActiveFrontier (a lens : Set X) : Set X :=
  (frontier a \ lens) ∪ (frontier lens ∩ a)

/-- The set `s` has arbitrarily small preconnected traces near `x`. -/
def IsLocallyPreconnectedWithinAt (s : Set X) (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (V ∩ s)

/-- Every visibly active old or lens face remains in the new frontier. -/
theorem sdiffActiveFrontier_subset_frontier_sdiff
    {a lens : Set X} (ha : IsOpen a) (hlens : IsClosed lens) :
    sdiffActiveFrontier a lens ⊆ frontier (a \ lens) := by
  intro x hx
  rw [sdiffActiveFrontier] at hx
  rcases hx with hx | hx
  · have hxa : x ∈ closure a := frontier_subset_closure hx.1
    have hxlensCompl : x ∈ lensᶜ := hx.2
    have hxClosure : x ∈ closure (a ∩ lensᶜ) :=
      (by simpa only [inter_comm] using
        hlens.isOpen_compl.inter_closure ⟨hxlensCompl, hxa⟩)
    have hxaNot : x ∉ a := by
      rw [ha.frontier_eq] at hx
      exact hx.1.2
    rw [ha.sdiff hlens |>.frontier_eq]
    exact ⟨hxClosure, fun hxNew ↦ hxaNot hxNew.1⟩
  · have hxLensClosure : x ∈ closure lensᶜ := by
      apply frontier_subset_closure
      simpa only [frontier_compl] using hx.1
    have hxClosure : x ∈ closure (a ∩ lensᶜ) :=
      ha.inter_closure ⟨hx.2, hxLensClosure⟩
    have hxLensMem : x ∈ lens := by
      rw [hlens.frontier_eq] at hx
      exact hx.1.1
    rw [ha.sdiff hlens |>.frontier_eq]
    exact ⟨hxClosure, fun hxNew ↦ hxNew.2 hxLensMem⟩

/-- Local preconnectedness of the old open side forces every surviving shared face to be
approached by an active face. -/
theorem shared_frontier_subset_closure_active_of_locallyPreconnected
    {a lens : Set X} (hlens : IsClosed lens)
    (hinterior : interior lens ⊆ a) (hlensRegular : lens ⊆ closure (interior lens))
    (hlocal : ∀ x ∈ frontier a ∩ frontier lens,
      IsLocallyPreconnectedWithinAt a x) :
    frontier (a \ lens) ∩ frontier a ∩ frontier lens ⊆
      closure (sdiffActiveFrontier a lens) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hV, hVU, hVconnected⟩ := hlocal x ⟨hx.1.2, hx.2⟩ U hU
  have hxNewClosure : x ∈ closure (a \ lens) := frontier_subset_closure hx.1.1
  obtain ⟨r, hrV, hrNew⟩ := mem_closure_iff_nhds.mp hxNewClosure V hV
  have hxLens : x ∈ lens := by
    rw [hlens.frontier_eq] at hx
    exact hx.2.1
  obtain ⟨l, hlV, hlInterior⟩ :=
    mem_closure_iff_nhds.mp (hlensRegular hxLens) V hV
  by_contra hactive
  have hcover : V ∩ a ⊆ interior lens ∪ lensᶜ := by
    intro y hy
    by_cases hyLens : y ∈ lens
    · apply Or.inl
      by_contra hyInterior
      apply hactive
      refine ⟨y, hVU hy.1, Or.inr ⟨?_, hy.2⟩⟩
      rw [hlens.frontier_eq]
      exact ⟨hyLens, hyInterior⟩
    · exact Or.inr hyLens
  have hleft : ((V ∩ a) ∩ interior lens).Nonempty :=
    ⟨l, ⟨hlV, hinterior hlInterior⟩, hlInterior⟩
  have hright : ((V ∩ a) ∩ lensᶜ).Nonempty :=
    ⟨r, ⟨hrV, hrNew.1⟩, hrNew.2⟩
  obtain ⟨y, _, hyInterior, hyOutside⟩ := hVconnected
    (interior lens) lensᶜ isOpen_interior hlens.isOpen_compl hcover hleft hright
  exact hyOutside (interior_subset hyInterior)

/-- Apart from coincident old and lens faces, the active-face formula is exact. -/
theorem frontier_sdiff_eq_closure_active_of_shared_subset
    {a lens : Set X} (ha : IsOpen a) (hlens : IsClosed lens)
    (hinterior : interior lens ⊆ a) (hlensClosure : lens ⊆ closure a)
    (hshared : frontier (a \ lens) ∩ frontier a ∩ frontier lens ⊆
      closure (sdiffActiveFrontier a lens)) :
    frontier (a \ lens) = closure (sdiffActiveFrontier a lens) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases frontier_sdiff_subset_union hx with hxa | hxLens
    · by_cases hxNotLens : x ∉ lens
      · exact subset_closure <| Or.inl ⟨hxa, hxNotLens⟩
      · apply hshared
        refine ⟨⟨hx, hxa⟩, ?_⟩
        have hxaNot : x ∉ a := by
          rw [ha.frontier_eq] at hxa
          exact hxa.2
        rw [hlens.frontier_eq]
        exact ⟨not_not.mp hxNotLens, fun hxInterior ↦
          hxaNot (hinterior hxInterior)⟩
    · by_cases hxaMem : x ∈ a
      · exact subset_closure <| Or.inr ⟨hxLens, hxaMem⟩
      · apply hshared
        refine ⟨⟨hx, ?_⟩, hxLens⟩
        have hxLensMem : x ∈ lens := by
          rw [hlens.frontier_eq] at hxLens
          exact hxLens.1
        rw [ha.frontier_eq]
        exact ⟨hlensClosure hxLensMem, hxaMem⟩
  · exact closure_minimal
      (sdiffActiveFrontier_subset_frontier_sdiff ha hlens) isClosed_frontier

/-- Removing a regular closed lens from a locally one-sided open region has exactly the closure
of the visible old and new faces as frontier. -/
theorem frontier_sdiff_eq_closure_active_of_locallyPreconnected
    {a lens : Set X} (ha : IsOpen a) (hlens : IsClosed lens)
    (hinterior : interior lens ⊆ a) (hlensRegular : lens ⊆ closure (interior lens))
    (hlocal : ∀ x ∈ frontier a ∩ frontier lens,
      IsLocallyPreconnectedWithinAt a x) :
    frontier (a \ lens) = closure (sdiffActiveFrontier a lens) := by
  apply frontier_sdiff_eq_closure_active_of_shared_subset ha hlens hinterior
    (hlensRegular.trans <| closure_mono hinterior)
  exact shared_frontier_subset_closure_active_of_locallyPreconnected hlens hinterior
    hlensRegular hlocal

end Submission.Topology
