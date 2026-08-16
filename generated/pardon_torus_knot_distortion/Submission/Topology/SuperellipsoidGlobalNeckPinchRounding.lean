import Submission.Topology.SuperellipsoidThreePageAttachment
import Submission.Topology.SuperellipsoidAnalyticSphere

/-!
# Explicit separated-truncation neck-pinch rounding

Truncating the convex superellipsoid at the separated levels `d - ε` and `d + ε` gives
two disjoint closed convex bodies.  Their interiors and frontier spheres provide the honest
two-component regular stage required by `SuperellipsoidGlobalNeckPinchRoundingData`.  Outside
the strip `|height - d| < 2ε`, the new boundary and inside label agree with the original convex
outer sphere.

This module constructs only the geometric rounding datum.  It makes no disk-cover assertion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε : ℝ}

/-- The two separated closed convex child bodies. -/
def separatedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d ε : ℝ) : Set R3 :=
  closedLowerSuperellipsoidTruncation frame c R (d - ε)

def separatedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d ε : ℝ) : Set R3 :=
  closedUpperSuperellipsoidTruncation frame c R (d + ε)

/-- The open rounded-child regions are the interiors of the separated truncations. -/
def separatedLowerSuperellipsoidInside
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d ε : ℝ) : Set R3 :=
  interior (separatedLowerSuperellipsoidTruncation frame c R d ε)

def separatedUpperSuperellipsoidInside
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d ε : ℝ) : Set R3 :=
  interior (separatedUpperSuperellipsoidTruncation frame c R d ε)

theorem isClosed_separatedLowerSuperellipsoidTruncation :
    IsClosed (separatedLowerSuperellipsoidTruncation frame c R d ε) :=
  isClosed_closedLowerSuperellipsoidTruncation frame c R (d - ε)

theorem isClosed_separatedUpperSuperellipsoidTruncation :
    IsClosed (separatedUpperSuperellipsoidTruncation frame c R d ε) :=
  isClosed_closedUpperSuperellipsoidTruncation frame c R (d + ε)

theorem convex_separatedLowerSuperellipsoidTruncation :
    Convex ℝ (separatedLowerSuperellipsoidTruncation frame c R d ε) :=
  convex_closedLowerSuperellipsoidTruncation frame c R (d - ε)

theorem convex_separatedUpperSuperellipsoidTruncation :
    Convex ℝ (separatedUpperSuperellipsoidTruncation frame c R d ε) :=
  convex_closedUpperSuperellipsoidTruncation frame c R (d + ε)

theorem closure_separatedLowerInside
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε) :
    closure (separatedLowerSuperellipsoidInside frame c R d ε) =
      separatedLowerSuperellipsoidTruncation frame c R d ε := by
  rw [separatedLowerSuperellipsoidInside,
    (convex_separatedLowerSuperellipsoidTruncation (frame := frame) (c := c)
      (R := R) (d := d) (ε := ε)).closure_interior_eq_closure_of_nonempty_interior
        (nonempty_interior_closedLowerSuperellipsoidTruncation
          frame c R (d - ε) hlower),
    isClosed_separatedLowerSuperellipsoidTruncation.closure_eq]

theorem closure_separatedUpperInside
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) :
    closure (separatedUpperSuperellipsoidInside frame c R d ε) =
      separatedUpperSuperellipsoidTruncation frame c R d ε := by
  rw [separatedUpperSuperellipsoidInside,
    (convex_separatedUpperSuperellipsoidTruncation (frame := frame) (c := c)
      (R := R) (d := d) (ε := ε)).closure_interior_eq_closure_of_nonempty_interior
        (nonempty_interior_closedUpperSuperellipsoidTruncation
          frame c R (d + ε) hupper),
    isClosed_separatedUpperSuperellipsoidTruncation.closure_eq]

theorem separatedTruncations_disjoint (hε : 0 < ε) :
    Disjoint (separatedLowerSuperellipsoidTruncation frame c R d ε)
      (separatedUpperSuperellipsoidTruncation frame c R d ε) := by
  rw [Set.disjoint_left]
  intro x hxLower hxUpper
  exact (by
    change x ∈ closedSuperellipsoidBody frame c R ∧
      x.ofLp (frame 2) ≤ d - ε at hxLower
    change x ∈ closedSuperellipsoidBody frame c R ∧
      d + ε ≤ x.ofLp (frame 2) at hxUpper
    linarith [hxLower.2, hxUpper.2])

theorem separatedInsides_disjoint (hε : 0 < ε) :
    Disjoint (separatedLowerSuperellipsoidInside frame c R d ε)
      (separatedUpperSuperellipsoidInside frame c R d ε) :=
  (separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
    (d := d) hε).mono interior_subset interior_subset

/-- Interior points of the closed outer body have strict superellipsoid gauge. -/
theorem interior_closedSuperellipsoidBody_subset_superellipsoidBody
    (hR : 0 < R) :
    interior (closedSuperellipsoidBody frame c R) ⊆ superellipsoidBody frame c R := by
  intro x hx
  have hxClosed : x ∈ closedSuperellipsoidBody frame c R := interior_subset hx
  change superellipsoidGauge frame c x ≤ R at hxClosed
  have hxNotFrontier : x ∉ frontier (closedSuperellipsoidBody frame c R) := by
    rw [frontier, Set.mem_sdiff]
    exact fun h ↦ h.2 hx
  have hxNe : superellipsoidGauge frame c x ≠ R := by
    intro hxEq
    apply hxNotFrontier
    rw [frontier_closedSuperellipsoidBody_eq_boundary frame c hR]
    exact hxEq
  exact lt_of_le_of_ne hxClosed hxNe

theorem separatedLowerInside_subset_halfBody (hR : 0 < R) (hε : 0 < ε) :
    separatedLowerSuperellipsoidInside frame c R d ε ⊆
      superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d} := by
  intro x hx
  have hxTrunc := interior_subset hx
  have hxOuterInterior : x ∈ interior (closedSuperellipsoidBody frame c R) :=
    interior_mono inter_subset_left hx
  constructor
  · exact interior_closedSuperellipsoidBody_subset_superellipsoidBody hR hxOuterInterior
  · change x ∈ closedSuperellipsoidBody frame c R ∧
      x.ofLp (frame 2) ≤ d - ε at hxTrunc
    exact hxTrunc.2.trans (sub_le_self d hε.le)

theorem separatedUpperInside_subset_halfBody (hR : 0 < R) (hε : 0 < ε) :
    separatedUpperSuperellipsoidInside frame c R d ε ⊆
      superellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)} := by
  intro x hx
  have hxTrunc := interior_subset hx
  have hxOuterInterior : x ∈ interior (closedSuperellipsoidBody frame c R) :=
    interior_mono inter_subset_left hx
  constructor
  · exact interior_closedSuperellipsoidBody_subset_superellipsoidBody hR hxOuterInterior
  · change x ∈ closedSuperellipsoidBody frame c R ∧
      d + ε ≤ x.ofLp (frame 2) at hxTrunc
    exact (le_add_of_nonneg_right hε.le).trans hxTrunc.2

/-- The explicit two-sphere family bounding the separated truncations. -/
def separatedTruncationSphereFamily (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2))
    (hε : 0 < ε) : FiniteEmbeddedTopologicalSphereFamilyInR3 where
  count := 2
  sphere
    | ⟨0, _⟩ => (lowerTruncatedSuperellipsoidSphereData frame c hR hlower).sphere
    | ⟨1, _⟩ => (upperTruncatedSuperellipsoidSphereData frame c hR hupper).sphere
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact (separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
        (d := d) hε).mono
          (ConvexBodySphereData.sphere_carrier_eq_frontier _ ▸
            isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset)
          (ConvexBodySphereData.sphere_carrier_eq_frontier _ ▸
            isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset)
    · exact ((separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
        (d := d) hε).mono
          (ConvexBodySphereData.sphere_carrier_eq_frontier _ ▸
            isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset)
          (ConvexBodySphereData.sphere_carrier_eq_frontier _ ▸
            isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset)).symm
    · exact False.elim (hij rfl)

@[simp] theorem separatedTruncationSphereFamily_count (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (separatedTruncationSphereFamily hR hlower hupper hε).count = 2 := rfl

/-- The neck support is the open strip of double the separation width. -/
def separatedTruncationNeckSupport
    (frame : Equiv.Perm (Fin 3)) (d ε : ℝ) : Set R3 :=
  {x | |x.ofLp (frame 2) - d| < 2 * ε}

theorem isOpen_separatedTruncationNeckSupport :
    IsOpen (separatedTruncationNeckSupport frame d ε) := by
  exact isOpen_Iio.preimage <| continuous_abs.comp <|
    (coordinateCLM (frame 2)).continuous.sub continuous_const

private theorem frontier_interior_eq_frontier_separatedLower
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε) :
    frontier (separatedLowerSuperellipsoidInside frame c R d ε) =
      frontier (separatedLowerSuperellipsoidTruncation frame c R d ε) := by
  rw [frontier, closure_separatedLowerInside hlower]
  change separatedLowerSuperellipsoidTruncation frame c R d ε \
      interior (interior (separatedLowerSuperellipsoidTruncation frame c R d ε)) = _
  rw [interior_interior]
  symm
  exact isClosed_separatedLowerSuperellipsoidTruncation.frontier_eq

private theorem frontier_interior_eq_frontier_separatedUpper
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) :
    frontier (separatedUpperSuperellipsoidInside frame c R d ε) =
      frontier (separatedUpperSuperellipsoidTruncation frame c R d ε) := by
  rw [frontier, closure_separatedUpperInside hupper]
  change separatedUpperSuperellipsoidTruncation frame c R d ε \
      interior (interior (separatedUpperSuperellipsoidTruncation frame c R d ε)) = _
  rw [interior_interior]
  symm
  exact isClosed_separatedUpperSuperellipsoidTruncation.frontier_eq

private theorem frontier_union_eq_union_frontier_of_open_closure_disjoint
    {A B : Set R3} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint (closure A) (closure B)) :
    frontier (A ∪ B) = frontier A ∪ frontier B := by
  apply Subset.antisymm
  · exact (frontier_union_subset A B).trans <|
      union_subset (inter_subset_left.trans subset_union_left)
        (inter_subset_right.trans subset_union_right)
  · intro x hx
    rcases hx with hxA | hxB
    · have hxA' : x ∈ closure A ∧ x ∉ A := by
        simpa [hA.frontier_eq] using hxA
      rw [(hA.union hB).frontier_eq]
      refine ⟨closure_mono subset_union_left hxA'.1, ?_⟩
      intro hxUnion
      rcases hxUnion with hxInA | hxInB
      · exact hxA'.2 hxInA
      · exact Set.disjoint_left.mp hdisj hxA'.1 (subset_closure hxInB)
    · have hxB' : x ∈ closure B ∧ x ∉ B := by
        simpa [hB.frontier_eq] using hxB
      rw [(hA.union hB).frontier_eq]
      refine ⟨closure_mono subset_union_right hxB'.1, ?_⟩
      intro hxUnion
      rcases hxUnion with hxInA | hxInB
      · exact Set.disjoint_left.mp hdisj.symm hxB'.1 (subset_closure hxInA)
      · exact hxB'.2 hxInB

theorem separatedTruncationSphereFamily_carrier
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (separatedTruncationSphereFamily hR hlower hupper hε).carrier =
      frontier (separatedLowerSuperellipsoidTruncation frame c R d ε) ∪
        frontier (separatedUpperSuperellipsoidTruncation frame c R d ε) := by
  change (⋃ i : Fin 2,
      ((separatedTruncationSphereFamily hR hlower hupper hε).sphere i).carrier) = _
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · left
      simpa [separatedTruncationSphereFamily,
        separatedLowerSuperellipsoidTruncation] using
          (ConvexBodySphereData.sphere_carrier_eq_frontier
            (lowerTruncatedSuperellipsoidSphereData frame c hR hlower) ▸ hi)
    · right
      simpa [separatedTruncationSphereFamily,
        separatedUpperSuperellipsoidTruncation] using
          (ConvexBodySphereData.sphere_carrier_eq_frontier
            (upperTruncatedSuperellipsoidSphereData frame c hR hupper) ▸ hi)
  · intro hx
    rcases hx with hx | hx
    · refine ⟨0, ?_⟩
      simpa [separatedTruncationSphereFamily,
        separatedLowerSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hx
    · refine ⟨1, ?_⟩
      simpa [separatedTruncationSphereFamily,
        separatedUpperSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hx

theorem separatedTruncationSphereFamily_is_boundary
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (separatedTruncationSphereFamily hR hlower hupper hε).carrier =
      frontier (separatedLowerSuperellipsoidInside frame c R d ε ∪
        separatedUpperSuperellipsoidInside frame c R d ε) := by
  rw [separatedTruncationSphereFamily_carrier hR hlower hupper hε,
    ← frontier_interior_eq_frontier_separatedLower hlower,
    ← frontier_interior_eq_frontier_separatedUpper hupper]
  symm
  have hdisj : Disjoint
      (closure (separatedLowerSuperellipsoidInside frame c R d ε))
      (closure (separatedUpperSuperellipsoidInside frame c R d ε)) := by
    rw [closure_separatedLowerInside hlower, closure_separatedUpperInside hupper]
    exact separatedTruncations_disjoint hε
  exact frontier_union_eq_union_frontier_of_open_closure_disjoint
    isOpen_interior isOpen_interior hdisj

private theorem frontier_lowerTruncation_subset_outer_of_not_mem_neck
    (hε : 0 < ε) :
    frontier (separatedLowerSuperellipsoidTruncation frame c R d ε) \
        separatedTruncationNeckSupport frame d ε ⊆
      frontier (closedSuperellipsoidBody frame c R) := by
  rintro x ⟨hxFrontier, hxNeck⟩
  have hxSplit := frontier_inter_subset
    (closedSuperellipsoidBody frame c R)
    {x : R3 | x.ofLp (frame 2) ≤ d - ε} hxFrontier
  rcases hxSplit with hxOuter | hxCut
  · exact hxOuter.1
  · exfalso
    have hxCutFrontier := hxCut.2
    have hxLe : x.ofLp (frame 2) ≤ d - ε := by
      exact (isClosed_Iic.preimage
        (coordinateCLM (frame 2)).continuous).frontier_subset hxCutFrontier
    have hxNotLt : ¬x.ofLp (frame 2) < d - ε := by
      intro hxLt
      have hxInterior : x ∈ interior {y : R3 | y.ofLp (frame 2) ≤ d - ε} :=
        interior_maximal (fun y hy ↦ show y.ofLp (frame 2) ≤ d - ε from hy.le)
          (isOpen_Iio.preimage (coordinateCLM (frame 2)).continuous) hxLt
      exact hxCutFrontier.2 hxInterior
    apply hxNeck
    change |x.ofLp (frame 2) - d| < 2 * ε
    have hxEq : x.ofLp (frame 2) = d - ε := le_antisymm hxLe (le_of_not_gt hxNotLt)
    rw [hxEq]
    have : |d - ε - d| = ε := by rw [show d - ε - d = -ε by ring, abs_neg, abs_of_pos hε]
    linarith

private theorem frontier_upperTruncation_subset_outer_of_not_mem_neck
    (hε : 0 < ε) :
    frontier (separatedUpperSuperellipsoidTruncation frame c R d ε) \
        separatedTruncationNeckSupport frame d ε ⊆
      frontier (closedSuperellipsoidBody frame c R) := by
  rintro x ⟨hxFrontier, hxNeck⟩
  have hxSplit := frontier_inter_subset
    (closedSuperellipsoidBody frame c R)
    {x : R3 | d + ε ≤ x.ofLp (frame 2)} hxFrontier
  rcases hxSplit with hxOuter | hxCut
  · exact hxOuter.1
  · exfalso
    have hxCutFrontier := hxCut.2
    have hxGe : d + ε ≤ x.ofLp (frame 2) := by
      exact (isClosed_Ici.preimage
        (coordinateCLM (frame 2)).continuous).frontier_subset hxCutFrontier
    have hxNotGt : ¬d + ε < x.ofLp (frame 2) := by
      intro hxGt
      have hxInterior : x ∈ interior {y : R3 | d + ε ≤ y.ofLp (frame 2)} :=
        interior_maximal (fun y hy ↦ show d + ε ≤ y.ofLp (frame 2) from hy.le)
          (isOpen_Ioi.preimage (coordinateCLM (frame 2)).continuous) hxGt
      exact hxCutFrontier.2 hxInterior
    apply hxNeck
    change |x.ofLp (frame 2) - d| < 2 * ε
    have hxEq : x.ofLp (frame 2) = d + ε := le_antisymm (le_of_not_gt hxNotGt) hxGe
    rw [hxEq]
    have : |d + ε - d| = ε := by rw [show d + ε - d = ε by ring, abs_of_pos hε]
    linarith

theorem separatedTruncationSphereFamily_off_neck_subset_outer
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (separatedTruncationSphereFamily hR hlower hupper hε).carrier \
        separatedTruncationNeckSupport frame d ε ⊆
      (outerSuperellipsoidSphereFamily frame c hR).carrier := by
  rw [separatedTruncationSphereFamily_carrier hR hlower hupper hε,
    outerSuperellipsoidSphereFamily_carrier frame c hR]
  rintro x ⟨hx, hxNeck⟩
  rcases hx with hxLower | hxUpper
  · exact frontier_lowerTruncation_subset_outer_of_not_mem_neck hε ⟨hxLower, hxNeck⟩
  · exact frontier_upperTruncation_subset_outer_of_not_mem_neck hε ⟨hxUpper, hxNeck⟩

theorem outerSphere_off_neck_subset_separatedTruncationSphereFamily
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (outerSuperellipsoidSphereFamily frame c hR).carrier \
        separatedTruncationNeckSupport frame d ε ⊆
      (separatedTruncationSphereFamily hR hlower hupper hε).carrier := by
  rw [outerSuperellipsoidSphereFamily_carrier frame c hR,
    separatedTruncationSphereFamily_carrier hR hlower hupper hε]
  rintro x ⟨hxOuter, hxNeck⟩
  have hxClosed : x ∈ closedSuperellipsoidBody frame c R :=
    (isClosed_closedSuperellipsoidBody_convexSphere frame c R).frontier_subset hxOuter
  have hxNotInterior : x ∉ interior (closedSuperellipsoidBody frame c R) := by
    have hxPair : x ∈ closedSuperellipsoidBody frame c R \
        interior (closedSuperellipsoidBody frame c R) := by
      rw [← (isClosed_closedSuperellipsoidBody_convexSphere frame c R).frontier_eq]
      exact hxOuter
    exact hxPair.2
  have hxAbs : 2 * ε ≤ |x.ofLp (frame 2) - d| := le_of_not_gt hxNeck
  by_cases hx : x.ofLp (frame 2) ≤ d
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hxAbs
    rw [isClosed_separatedLowerSuperellipsoidTruncation.frontier_eq]
    refine ⟨?_, ?_⟩
    · change x ∈ closedSuperellipsoidBody frame c R ∧
        x.ofLp (frame 2) ≤ d - ε
      exact ⟨hxClosed, by linarith⟩
    exact fun hxLowerInterior ↦
      hxNotInterior (interior_mono inter_subset_left hxLowerInterior)
  · right
    rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hx))] at hxAbs
    rw [isClosed_separatedUpperSuperellipsoidTruncation.frontier_eq]
    refine ⟨?_, ?_⟩
    · change x ∈ closedSuperellipsoidBody frame c R ∧
        d + ε ≤ x.ofLp (frame 2)
      exact ⟨hxClosed, by linarith⟩
    exact fun hxUpperInterior ↦
      hxNotInterior (interior_mono inter_subset_left hxUpperInterior)

/-- Away from the neck strip, the post-boundary and old outer boundary agree exactly. -/
theorem separatedTruncationSphereFamily_boundary_off_neck
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    (separatedTruncationSphereFamily hR hlower hupper hε).carrier \
        separatedTruncationNeckSupport frame d ε =
      (outerSuperellipsoidSphereFamily frame c hR).carrier \
        separatedTruncationNeckSupport frame d ε := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨separatedTruncationSphereFamily_off_neck_subset_outer
      hR hlower hupper hε hx, hx.2⟩
  · intro x hx
    exact ⟨outerSphere_off_neck_subset_separatedTruncationSphereFamily
      hR hlower hupper hε hx, hx.2⟩

private theorem mem_separatedLowerInside_of_mem_outerInterior_of_lt
    {x : R3}
    (hxOuter : x ∈ interior (closedSuperellipsoidBody frame c R))
    (hxCut : x.ofLp (frame 2) < d - ε) :
    x ∈ separatedLowerSuperellipsoidInside frame c R d ε := by
  unfold separatedLowerSuperellipsoidInside separatedLowerSuperellipsoidTruncation
  have hsubset :
      interior (closedSuperellipsoidBody frame c R) ∩
          {y : R3 | y.ofLp (frame 2) < d - ε} ⊆
        closedSuperellipsoidBody frame c R ∩
          {y : R3 | y.ofLp (frame 2) ≤ d - ε} := by
    rintro y ⟨hyOuter, hyCut⟩
    exact ⟨interior_subset hyOuter,
      show y.ofLp (frame 2) ≤ d - ε from hyCut.le⟩
  exact interior_maximal
    hsubset
    (isOpen_interior.inter <|
      isOpen_Iio.preimage (coordinateCLM (frame 2)).continuous)
    ⟨hxOuter, hxCut⟩

private theorem mem_separatedUpperInside_of_mem_outerInterior_of_gt
    {x : R3}
    (hxOuter : x ∈ interior (closedSuperellipsoidBody frame c R))
    (hxCut : d + ε < x.ofLp (frame 2)) :
    x ∈ separatedUpperSuperellipsoidInside frame c R d ε := by
  unfold separatedUpperSuperellipsoidInside separatedUpperSuperellipsoidTruncation
  have hsubset :
      interior (closedSuperellipsoidBody frame c R) ∩
          {y : R3 | d + ε < y.ofLp (frame 2)} ⊆
        closedSuperellipsoidBody frame c R ∩
          {y : R3 | d + ε ≤ y.ofLp (frame 2)} := by
    rintro y ⟨hyOuter, hyCut⟩
    exact ⟨interior_subset hyOuter,
      show d + ε ≤ y.ofLp (frame 2) from hyCut.le⟩
  exact interior_maximal
    hsubset
    (isOpen_interior.inter <|
      isOpen_Ioi.preimage (coordinateCLM (frame 2)).continuous)
    ⟨hxOuter, hxCut⟩

/-- Outside the double-width neck, the union of the two child interiors has exactly the old
outer-body parity label. -/
theorem separatedInsides_agree_with_outerInterior_off_neck
    (hε : 0 < ε) (x : R3)
    (hxNeck : x ∉ separatedTruncationNeckSupport frame d ε) :
    (x ∈ interior (closedSuperellipsoidBody frame c R) ↔
      x ∈ separatedLowerSuperellipsoidInside frame c R d ε ∪
        separatedUpperSuperellipsoidInside frame c R d ε) := by
  constructor
  · intro hxOuter
    have hxAbs : 2 * ε ≤ |x.ofLp (frame 2) - d| := le_of_not_gt hxNeck
    by_cases hx : x.ofLp (frame 2) ≤ d
    · left
      rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hxAbs
      apply mem_separatedLowerInside_of_mem_outerInterior_of_lt hxOuter
      linarith
    · right
      rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hx))] at hxAbs
      apply mem_separatedUpperInside_of_mem_outerInterior_of_gt hxOuter
      linarith
  · intro hx
    rcases hx with hxLower | hxUpper
    · exact interior_mono inter_subset_left hxLower
    · exact interior_mono inter_subset_left hxUpper

/-- Separated convex truncations give the explicit honest global neck-pinch rounding datum. -/
def separatedTruncationGlobalNeckPinchRoundingData
    (hR : 0 < R) (hε : 0 < ε)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) :
    SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR where
  lowerInside := separatedLowerSuperellipsoidInside frame c R d ε
  upperInside := separatedUpperSuperellipsoidInside frame c R d ε
  isOpen_lowerInside := isOpen_interior
  isOpen_upperInside := isOpen_interior
  lower_disjoint_upper := separatedInsides_disjoint hε
  childFamily := separatedTruncationSphereFamily hR hlower hupper hε
  child_count := rfl
  childFamily_is_boundary :=
    separatedTruncationSphereFamily_is_boundary hR hlower hupper hε
  lowerInside_subset_halfBody := separatedLowerInside_subset_halfBody hR hε
  upperInside_subset_halfBody := separatedUpperInside_subset_halfBody hR hε
  neckSupport := separatedTruncationNeckSupport frame d ε
  isOpen_neckSupport := isOpen_separatedTruncationNeckSupport
  postBoundary_off_neck_subset_outer :=
    separatedTruncationSphereFamily_off_neck_subset_outer hR hlower hupper hε
  inside_agree_off_neck := separatedInsides_agree_with_outerInterior_off_neck hε

end Submission.Topology
