import Submission.Topology.ThreeBoundaryOuterDisk

/-!
# Canonical sides of projected zero-winding Jordan disks

The lifted Schoenflies inside is open, its closure is the lifted closed Jordan disk, and the
torus covering projection is an open local homeomorphism which is injective on that closed disk.
Consequently the projected closed disk is the disjoint union of an open disk and its original
embedded boundary circle.  This is the Jordan-side API needed by a connected three-boundary
carrier.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

namespace EmbeddedTorusIntersectionCircle

/-- The open side of the canonical projected zero-winding Jordan disk. -/
def zeroWindingProjectedOpenJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Set (transportedTorus Phi) :=
  torusCoveringProjectionToTorus Phi '' (C.zeroWindingJordanCircle hzero).inside

theorem isOpen_zeroWindingProjectedOpenJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    IsOpen (C.zeroWindingProjectedOpenJordanDisk hzero) :=
  (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).isOpenMap _
    (C.zeroWindingJordanCircle hzero).inside_isOpen

theorem zeroWindingProjectedOpenJordanDisk_subset_closed
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedOpenJordanDisk hzero ⊆
      C.zeroWindingProjectedClosedJordanDisk hzero :=
  image_mono subset_closure

/-- The lifted Jordan carrier projects exactly to the original embedded torus circle. -/
theorem image_zeroWindingJordanCarrier
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    torusCoveringProjectionToTorus Phi ''
        (C.zeroWindingJordanCircle hzero).carrier =
      Set.range C.torusCircle := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, hxy⟩
    obtain ⟨q, hq⟩ := hx
    let z := JordanCurve.Arcs.spherePlaneHomeoCircle q
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rw [← hxy, ← hq]
    simpa [z, zeroWindingJordanCircle] using
      (C.torusCoveringProjection_zeroWindingPlaneCircle hzero z).symm
  · rintro _ ⟨z, rfl⟩
    let q := JordanCurve.Arcs.spherePlaneHomeoCircle.symm z
    refine ⟨(C.zeroWindingJordanCircle hzero).parametrization q, ⟨q, rfl⟩, ?_⟩
    apply Subtype.ext
    change EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        (C.zeroWindingPlaneCircle hzero
          (JordanCurve.Arcs.spherePlaneHomeoCircle q)) = C.circle z
    rw [show JordanCurve.Arcs.spherePlaneHomeoCircle q = z by
      exact JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply z]
    exact C.torusCoveringProjection_zeroWindingPlaneCircle hzero z

/-- The projected closed disk is the closure of its projected open side. -/
theorem closure_zeroWindingProjectedOpenJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    closure (C.zeroWindingProjectedOpenJordanDisk hzero) =
      C.zeroWindingProjectedClosedJordanDisk hzero := by
  apply Set.Subset.antisymm
  · exact closure_minimal
      (C.zeroWindingProjectedOpenJordanDisk_subset_closed hzero)
      (C.isClosed_zeroWindingProjectedClosedJordanDisk hzero)
  · change torusCoveringProjectionToTorus Phi ''
        closure (C.zeroWindingJordanCircle hzero).inside ⊆
      closure (torusCoveringProjectionToTorus Phi ''
        (C.zeroWindingJordanCircle hzero).inside)
    exact image_closure_subset_closure_image
      (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous

/-- The projected open disk and its boundary circle are disjoint. -/
theorem disjoint_zeroWindingProjectedOpenJordanDisk_circle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Disjoint (C.zeroWindingProjectedOpenJordanDisk hzero) (Set.range C.torusCircle) := by
  rw [← C.image_zeroWindingJordanCarrier hzero, Set.disjoint_left]
  rintro y ⟨x, hxInside, rfl⟩ ⟨z, hzCarrier, hzx⟩
  have hxClosed : x ∈ closure (C.zeroWindingJordanCircle hzero).inside :=
    subset_closure hxInside
  have hzClosed : z ∈ closure (C.zeroWindingJordanCircle hzero).inside := by
    rw [(C.zeroWindingJordanCircle hzero).closure_inside]
    exact Or.inr hzCarrier
  have hzxPlane : z = x := by
    apply C.torusCoveringProjection_injOn_zeroWindingJordanDisk hzero hzClosed hxClosed
    exact congrArg Subtype.val hzx
  exact (C.zeroWindingJordanCircle hzero).inside_subset_compl hxInside (hzxPlane ▸ hzCarrier)

/-- Exact open-disk/boundary decomposition of the projected closed disk. -/
theorem zeroWindingProjectedClosedJordanDisk_eq_open_union_circle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hzero =
      C.zeroWindingProjectedOpenJordanDisk hzero ∪ Set.range C.torusCircle := by
  rw [zeroWindingProjectedClosedJordanDisk, zeroWindingClosedJordanDisk,
    (C.zeroWindingJordanCircle hzero).closure_inside, image_union,
    C.image_zeroWindingJordanCarrier hzero]
  rfl

/-- Removing the boundary circle from the canonical closed disk leaves exactly its open side. -/
theorem zeroWindingProjectedClosedJordanDisk_diff_circle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hzero \ Set.range C.torusCircle =
      C.zeroWindingProjectedOpenJordanDisk hzero := by
  rw [C.zeroWindingProjectedClosedJordanDisk_eq_open_union_circle hzero]
  ext x
  constructor
  · rintro ⟨hxOpen | hxBoundary, hxNotBoundary⟩
    · exact hxOpen
    · exact (hxNotBoundary hxBoundary).elim
  · intro hxOpen
    exact ⟨Or.inl hxOpen, fun hxBoundary ↦
      Set.disjoint_left.mp (C.disjoint_zeroWindingProjectedOpenJordanDisk_circle hzero)
        hxOpen hxBoundary⟩

/-- The topological frontier of the projected open disk is exactly the original circle. -/
theorem frontier_zeroWindingProjectedOpenJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    frontier (C.zeroWindingProjectedOpenJordanDisk hzero) = Set.range C.torusCircle := by
  rw [(C.isOpen_zeroWindingProjectedOpenJordanDisk hzero).frontier_eq,
    C.closure_zeroWindingProjectedOpenJordanDisk hzero,
    C.zeroWindingProjectedClosedJordanDisk_eq_open_union_circle hzero]
  ext x
  constructor
  · rintro ⟨hxOpen | hxBoundary, hxNotOpen⟩
    · exact (hxNotOpen hxOpen).elim
    · exact hxBoundary
  · intro hxBoundary
    exact ⟨Or.inr hxBoundary, fun hxOpen ↦
      Set.disjoint_left.mp (C.disjoint_zeroWindingProjectedOpenJordanDisk_circle hzero)
        hxOpen hxBoundary⟩

/-- The complement of the boundary circle is partitioned by the open disk and the exterior of
the closed disk. -/
theorem compl_circle_eq_open_union_compl_closed
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    (Set.range C.torusCircle)ᶜ =
      C.zeroWindingProjectedOpenJordanDisk hzero ∪
        (C.zeroWindingProjectedClosedJordanDisk hzero)ᶜ := by
  ext x
  constructor
  · intro hxNotBoundary
    by_cases hxDisk : x ∈ C.zeroWindingProjectedClosedJordanDisk hzero
    · left
      rw [← C.zeroWindingProjectedClosedJordanDisk_diff_circle hzero]
      exact ⟨hxDisk, hxNotBoundary⟩
    · exact Or.inr hxDisk
  · rintro (hxOpen | hxExterior) hxBoundary
    · exact Set.disjoint_left.mp
        (C.disjoint_zeroWindingProjectedOpenJordanDisk_circle hzero) hxOpen hxBoundary
    · exact hxExterior
        (by
          rw [C.zeroWindingProjectedClosedJordanDisk_eq_open_union_circle hzero]
          exact Or.inr hxBoundary)

end EmbeddedTorusIntersectionCircle

namespace ThreeBoundaryPairOfPantsCarrier

variable (Q : ThreeBoundaryPairOfPantsCarrier Phi)

/-- Each boundary circle separates the connected carrier interior onto one canonical side. -/
theorem hasCanonicalInteriorDiskSides : Q.HasCanonicalInteriorDiskSides := by
  intro i
  let O := (Q.circle i).zeroWindingProjectedOpenJordanDisk (Q.zeroWinding i)
  have hInteriorAvoidsBoundary : Q.interior ⊆ (Q.boundary i)ᶜ := by
    intro x hxInterior hxBoundary
    have hxCarrierBoundary : x ∈ Q.carrier \ Q.interior := by
      rw [Q.boundary_exact]
      exact Set.mem_iUnion.mpr ⟨i, hxBoundary⟩
    exact hxCarrierBoundary.2 hxInterior
  have hcover : Q.interior ⊆ O ∪ (Q.disk i)ᶜ := by
    change Q.interior ⊆
      (Q.circle i).zeroWindingProjectedOpenJordanDisk (Q.zeroWinding i) ∪
        ((Q.circle i).zeroWindingProjectedClosedJordanDisk (Q.zeroWinding i))ᶜ
    rw [← (Q.circle i).compl_circle_eq_open_union_compl_closed (Q.zeroWinding i)]
    exact hInteriorAvoidsBoundary
  have hOpenO : IsOpen O :=
    (Q.circle i).isOpen_zeroWindingProjectedOpenJordanDisk (Q.zeroWinding i)
  have hOpenExterior : IsOpen (Q.disk i)ᶜ := (Q.isClosed_disk i).isOpen_compl
  have hDisjoint : Disjoint O (Q.disk i)ᶜ :=
    disjoint_compl_right.mono_left
      ((Q.circle i).zeroWindingProjectedOpenJordanDisk_subset_closed (Q.zeroWinding i))
  obtain ⟨x, hxInterior⟩ := Q.interior_nonempty
  rcases hcover hxInterior with hxOpen | hxExterior
  · left
    exact (Q.interior_isConnected.isPreconnected.subset_left_of_subset_union
      hOpenO hOpenExterior hDisjoint hcover ⟨x, hxInterior, hxOpen⟩).trans
        ((Q.circle i).zeroWindingProjectedOpenJordanDisk_subset_closed (Q.zeroWinding i))
  · right
    have hInteriorExterior : Q.interior ⊆ (Q.disk i)ᶜ :=
      Q.interior_isConnected.isPreconnected.subset_right_of_subset_union
        hOpenO hOpenExterior hDisjoint hcover ⟨x, hxInterior, hxExterior⟩
    have hOpenDisjointInterior : Disjoint O Q.interior :=
      hDisjoint.mono_right hInteriorExterior
    have hOpenDisjointClosure : Disjoint O (closure Q.interior) :=
      hOpenDisjointInterior.closure_right hOpenO
    change Disjoint Q.carrier
      ((Q.circle i).zeroWindingProjectedClosedJordanDisk (Q.zeroWinding i) \
        Set.range (Q.circle i).torusCircle)
    rw [(Q.circle i).zeroWindingProjectedClosedJordanDisk_diff_circle]
    exact hOpenDisjointClosure.symm.mono_left Q.carrier_subset_closure_interior

end ThreeBoundaryPairOfPantsCarrier

end Submission.Topology
