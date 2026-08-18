import Mathlib.Topology.LocallyFinite

/-!
# Pasting maps on a finite closed cover

This file packages the finite closed-cover pasting argument in a form suited to the
innermost-circle construction.  The input maps are defined on the corresponding subtypes, so no
arbitrary extension away from a cover piece is required.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

/-- Compatible continuous maps on a finite closed cover. -/
structure FiniteClosedCoverPastingData
    (ι X Y : Type*) [Finite ι] [TopologicalSpace X] [TopologicalSpace Y] where
  piece : ι → Set X
  isClosed_piece : ∀ i, IsClosed (piece i)
  cover : ⋃ i, piece i = univ
  value : ∀ i, piece i → Y
  continuous_value : ∀ i, Continuous (value i)
  compatible : ∀ i j x (hxi : x ∈ piece i) (hxj : x ∈ piece j),
    value i ⟨x, hxi⟩ = value j ⟨x, hxj⟩

namespace FiniteClosedCoverPastingData

variable {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
  (D : FiniteClosedCoverPastingData ι X Y)

private theorem exists_piece (x : X) : ∃ i, x ∈ D.piece i := by
  have hx : x ∈ ⋃ i, D.piece i := by
    rw [D.cover]
    exact mem_univ x
  simpa only [mem_iUnion] using hx

/-- A chosen cover piece containing a point.  Compatibility makes the final glued value
independent of this choice. -/
def chosenIndex (x : X) : ι :=
  Classical.choose (D.exists_piece x)

theorem chosenIndex_mem (x : X) : x ∈ D.piece (D.chosenIndex x) :=
  Classical.choose_spec (D.exists_piece x)

/-- The globally pasted map. -/
def glued (x : X) : Y :=
  D.value (D.chosenIndex x) ⟨x, D.chosenIndex_mem x⟩

/-- On each cover piece, the pasted map is the prescribed map. -/
theorem glued_eq (i : ι) (x : X) (hx : x ∈ D.piece i) :
    D.glued x = D.value i ⟨x, hx⟩ :=
  D.compatible (D.chosenIndex x) i x (D.chosenIndex_mem x) hx

/-- Finite closed-cover pasting. -/
theorem continuous_glued : Continuous D.glued := by
  apply (locallyFinite_of_finite D.piece).continuous D.cover D.isClosed_piece
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  convert D.continuous_value i using 1
  funext x
  exact D.glued_eq i x x.property

end FiniteClosedCoverPastingData
end Submission.Topology
