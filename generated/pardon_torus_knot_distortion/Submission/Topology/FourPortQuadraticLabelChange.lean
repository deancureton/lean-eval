import Submission.Topology.FourPortMorseGraphPatch
import Submission.PlaneSchoenflies.Schoenflies.JordanHomeomorphRegions
import Submission.Topology.TorusPlaneCircleLiftAlignment

/-!
# Label change in the quadratic four-port model

On the supporting disk, the vertical height is everywhere at most the horizontal height.  Thus
two consistently oriented endpoint inside predicates can differ only in the central closed
rectangle bounded by the four port arcs.  This is the algebraic core of the remaining geometric
label-change containment theorem.
-/

open Set

noncomputable section

namespace Submission.Topology

open EmbeddedTorusIntersectionCircle

/-- A regular closed bounded body whose frontier is a Jordan carrier lies in the closed bounded
Jordan region. -/
theorem subset_closure_inside_of_carrier_eq_frontier
    (J : Schoenflies.JordanCircle) {K : Set Schoenflies.Plane}
    (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hregular : closure (interior K) = K) (hcarrier : J.carrier = frontier K) :
    K ⊆ closure J.inside := by
  have hpartition : J.inside ∪ J.outside = interior K ∪ Kᶜ := by
    rw [J.inside_union_outside, hcarrier, compl_frontier_eq_union_interior,
      hclosed.isOpen_compl.interior_eq]
  have houtsideCover : J.outside ⊆ interior K ∪ Kᶜ := by
    rw [← hpartition]
    exact subset_union_right
  have hdisjoint : Disjoint (interior K) Kᶜ := by
    rw [Set.disjoint_left]
    intro x hxInterior hxCompl
    exact hxCompl (interior_subset hxInterior)
  have houtside : J.outside ⊆ Kᶜ := by
    rcases J.outside_isConnected.isPreconnected.subset_or_subset
        isOpen_interior hclosed.isOpen_compl hdisjoint houtsideCover with
      houtsideInterior | houtsideCompl
    · exact False.elim <|
        J.outside_unbounded (hbounded.subset (houtsideInterior.trans interior_subset))
    · exact houtsideCompl
  have hinterior : interior K ⊆ J.inside := by
    intro x hxInterior
    have hxNotCarrier : x ∉ J.carrier := by
      rw [hcarrier]
      exact Set.disjoint_left.mp disjoint_interior_frontier hxInterior
    rcases J.mem_inside_or_outside hxNotCarrier with hxInside | hxOutside
    · exact hxInside
    · exact False.elim (houtside hxOutside (interior_subset hxInterior))
  rw [← hregular]
  exact closure_mono hinterior

/-- The closed coordinate rectangle bounded by the four standard port paths. -/
def fourPortClosedRectangle : Set FourPortPlane :=
  Icc (-(1 : ℝ)) 1 ×ˢ Icc (-(1 : ℝ)) 1

theorem isClosed_fourPortClosedRectangle : IsClosed fourPortClosedRectangle :=
  isClosed_Icc.prod isClosed_Icc

theorem isCompact_fourPortClosedRectangle : IsCompact fourPortClosedRectangle :=
  isCompact_Icc.prod isCompact_Icc

theorem isBounded_fourPortClosedRectangle :
    Bornology.IsBounded fourPortClosedRectangle :=
  isCompact_fourPortClosedRectangle.isBounded

theorem closure_interior_fourPortClosedRectangle :
    closure (interior fourPortClosedRectangle) = fourPortClosedRectangle := by
  simp only [fourPortClosedRectangle, interior_prod_eq, interior_Icc,
    closure_prod_eq, closure_Ioo (by norm_num : (-(1 : ℝ)) ≠ 1)]

/-- The four standard port segments are exactly the frontier of the closed coordinate
rectangle. -/
theorem frontier_fourPortClosedRectangle :
    frontier fourPortClosedRectangle =
      fourPortVerticalCarrier ∪ fourPortHorizontalCarrier := by
  rw [frontier, isClosed_fourPortClosedRectangle.closure_eq]
  ext u
  rcases u with ⟨x, y⟩
  simp only [fourPortClosedRectangle, mem_sdiff, mem_prod, mem_Icc,
    interior_prod_eq, interior_Icc, mem_Ioo, fourPortVerticalCarrier,
    fourPortHorizontalCarrier, Set.mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨⟨⟨hxLower, hxUpper⟩, ⟨hyLower, hyUpper⟩⟩, hnotInterior⟩
    by_cases hxLowerEq : x = -1
    · exact Or.inl ⟨Or.inr hxLowerEq, hyLower, hyUpper⟩
    by_cases hxUpperEq : x = 1
    · exact Or.inl ⟨Or.inl hxUpperEq, hyLower, hyUpper⟩
    by_cases hyLowerEq : y = -1
    · exact Or.inr ⟨Or.inr hyLowerEq, hxLower, hxUpper⟩
    by_cases hyUpperEq : y = 1
    · exact Or.inr ⟨Or.inl hyUpperEq, hxLower, hxUpper⟩
    exfalso
    apply hnotInterior
    exact ⟨⟨lt_of_le_of_ne hxLower (Ne.symm hxLowerEq),
      lt_of_le_of_ne hxUpper hxUpperEq⟩,
      lt_of_le_of_ne hyLower (Ne.symm hyLowerEq),
      lt_of_le_of_ne hyUpper hyUpperEq⟩
  · rintro (⟨hx | hx, hyLower, hyUpper⟩ | ⟨hy | hy, hxLower, hxUpper⟩)
    · subst x
      refine ⟨⟨⟨by norm_num, by norm_num⟩, ⟨hyLower, hyUpper⟩⟩, ?_⟩
      norm_num
    · subst x
      refine ⟨⟨⟨by norm_num, by norm_num⟩, ⟨hyLower, hyUpper⟩⟩, ?_⟩
      norm_num
    · subst y
      refine ⟨⟨⟨hxLower, hxUpper⟩, ⟨by norm_num, by norm_num⟩⟩, ?_⟩
      norm_num
    · subst y
      refine ⟨⟨⟨hxLower, hxUpper⟩, ⟨by norm_num, by norm_num⟩⟩, ?_⟩
      norm_num

/-- The coordinate rectangle transported to the Euclidean torus covering plane. -/
def fourPortClosedRectangleInCoveringPlane : Set TorusCoveringPlane :=
  coveringPlaneCoordinates.symm '' fourPortClosedRectangle

theorem isClosed_fourPortClosedRectangleInCoveringPlane :
    IsClosed fourPortClosedRectangleInCoveringPlane := by
  exact coveringPlaneCoordinates.symm.isClosed_image.mpr
    isClosed_fourPortClosedRectangle

theorem isBounded_fourPortClosedRectangleInCoveringPlane :
    Bornology.IsBounded fourPortClosedRectangleInCoveringPlane := by
  exact (isCompact_fourPortClosedRectangle.image
    coveringPlaneCoordinates.symm.continuous).isBounded

theorem closure_interior_fourPortClosedRectangleInCoveringPlane :
    closure (interior fourPortClosedRectangleInCoveringPlane) =
      fourPortClosedRectangleInCoveringPlane := by
  rw [fourPortClosedRectangleInCoveringPlane,
    ← coveringPlaneCoordinates.symm.image_interior,
    ← coveringPlaneCoordinates.symm.image_closure,
    closure_interior_fourPortClosedRectangle]

/-- The coordinate change carries the four-port rectangle frontier to the frontier in the
Euclidean covering plane. -/
theorem frontier_fourPortClosedRectangleInCoveringPlane :
    frontier fourPortClosedRectangleInCoveringPlane =
      coveringPlaneCoordinates.symm ''
        (fourPortVerticalCarrier ∪ fourPortHorizontalCarrier) := by
  rw [fourPortClosedRectangleInCoveringPlane,
    ← coveringPlaneCoordinates.symm.image_frontier,
    frontier_fourPortClosedRectangle]

/-- Any Jordan parametrization of the four standard port edges has the coordinate square as a
subset of its closed bounded side. -/
theorem fourPortClosedRectangle_subset_closure_inside
    (J : Schoenflies.JordanCircle)
    (hcarrier : J.carrier = frontier fourPortClosedRectangleInCoveringPlane) :
    fourPortClosedRectangleInCoveringPlane ⊆ closure J.inside :=
  subset_closure_inside_of_carrier_eq_frontier J
    isClosed_fourPortClosedRectangleInCoveringPlane
    isBounded_fourPortClosedRectangleInCoveringPlane
    closure_interior_fourPortClosedRectangleInCoveringPlane hcarrier

/-- On the supporting disk the vertical endpoint graph lies below the horizontal endpoint
graph. -/
theorem fourPortVerticalHeight_le_horizontalHeight_of_mem_region
    {u : FourPortPlane} (hu : u ∈ fourPortQuadraticRegion) :
    fourPortVerticalHeight u ≤ fourPortHorizontalHeight u := by
  change u.1 ^ 2 + u.2 ^ 2 ≤ 2 at hu
  simp only [fourPortVerticalHeight, fourPortHorizontalHeight]
  linarith

/-- If the two negative-side labels differ on the supporting disk, the point lies in the
central closed rectangle. -/
theorem mem_fourPortClosedRectangle_of_negative_labels_ne
    {u : FourPortPlane} (hu : u ∈ fourPortQuadraticRegion)
    (hchange : (fourPortVerticalHeight u < 0) ≠
      (fourPortHorizontalHeight u < 0)) :
    u ∈ fourPortClosedRectangle := by
  have hle := fourPortVerticalHeight_le_horizontalHeight_of_mem_region hu
  have hnotiff : ¬ (fourPortVerticalHeight u < 0 ↔
      fourPortHorizontalHeight u < 0) := by
    intro h
    exact hchange (propext h)
  have himp : fourPortHorizontalHeight u < 0 →
      fourPortVerticalHeight u < 0 := fun hs ↦ lt_of_le_of_lt hle hs
  have hp : fourPortVerticalHeight u < 0 := by tauto
  have hs : ¬ fourPortHorizontalHeight u < 0 := by tauto
  change u.1 ∈ Icc (-(1 : ℝ)) 1 ∧ u.2 ∈ Icc (-(1 : ℝ)) 1
  simp only [mem_Icc, fourPortVerticalHeight, fourPortHorizontalHeight] at hp hs ⊢
  constructor <;> constructor <;> nlinarith [sq_nonneg u.1, sq_nonneg u.2]

/-- The same containment holds when both endpoint insides use the positive side of their graph.
-/
theorem mem_fourPortClosedRectangle_of_positive_labels_ne
    {u : FourPortPlane} (hu : u ∈ fourPortQuadraticRegion)
    (hchange : (0 < fourPortVerticalHeight u) ≠
      (0 < fourPortHorizontalHeight u)) :
    u ∈ fourPortClosedRectangle := by
  have hle := fourPortVerticalHeight_le_horizontalHeight_of_mem_region hu
  have hnotiff : ¬ (0 < fourPortVerticalHeight u ↔
      0 < fourPortHorizontalHeight u) := by
    intro h
    exact hchange (propext h)
  have himp : 0 < fourPortVerticalHeight u →
      0 < fourPortHorizontalHeight u := fun hp ↦ lt_of_lt_of_le hp hle
  have hp : ¬ 0 < fourPortVerticalHeight u := by tauto
  have hs : 0 < fourPortHorizontalHeight u := by tauto
  change u.1 ∈ Icc (-(1 : ℝ)) 1 ∧ u.2 ∈ Icc (-(1 : ℝ)) 1
  simp only [mem_Icc, fourPortVerticalHeight, fourPortHorizontalHeight] at hp hs ⊢
  constructor <;> constructor <;> nlinarith [sq_nonneg u.1, sq_nonneg u.2]

end Submission.Topology
