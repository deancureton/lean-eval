import Submission.PlaneSchoenflies.Schoenflies.JordanThetaRegions
import Submission.Topology.DiskLocalizedParityTransition
import Submission.Topology.FourPortEndpointCollarPush
import Submission.Topology.ThreeBoundaryCanonicalDiskSides

/-!
# Raw four-port theta faces give disk-sided transitions

The three raw affected circles of a split or merge are the three cycles of a theta graph.  A
coherent plane lift has two bounded faces and one unbounded face.  Its outer cycle is not
determined by the local split/merge label: any of the three raw circles can be the outer cycle.
Accordingly, the data below records an explicit ordering of the three cycles, with index
`outerIndex` designating the outer cycle.

Jordan separation then says that the two bounded child faces fill the closed disk bounded by
the outer cycle.  If the lifted label-change lens lies in those faces, all three raw boundary
circles and the lens lie in the outer canonical torus disk.  Attaching that raw outer disk to a
maximal disk at either endpoint gives the corresponding forward or reverse elementary
disk-side cover.

This bypasses tangential collar pushes and the global pair-of-pants trace.  It does not hide the
two genuinely geometric inputs: selection of the outer planar theta cycle and identification of
the local label-change lens with the two bounded faces.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

/-- A coherent planar theta presentation with an explicitly selected outer cycle.

The index exhaustion is the finite bookkeeping that the selected outer and child cycles are
exactly the three raw cycles.  The two containment fields orient the Jordan theta: they say
which of the three complementary regions is unbounded.  This orientation cannot be recovered
from the local split/merge direction alone.
-/
structure RawFourPortOuterPlaneThetaData (R : FourPortRawCircleData raw) where
  outerIndex : Fin 3
  childOneIndex : Fin 3
  childTwoIndex : Fin 3
  indices_exhaust : ∀ i,
    i = outerIndex ∨ i = childOneIndex ∨ i = childTwoIndex
  commonArc : Set TorusCoveringPlane
  outerArcOne : Set TorusCoveringPlane
  outerArcTwo : Set TorusCoveringPlane
  exceptional : Set TorusCoveringPlane
  outer_carrier :
    ((R.circle outerIndex).zeroWindingJordanCircle (R.zeroWinding outerIndex)).carrier =
      outerArcOne ∪ outerArcTwo
  childOne_carrier :
    ((R.circle childOneIndex).zeroWindingJordanCircle
      (R.zeroWinding childOneIndex)).carrier =
      commonArc ∪ outerArcOne
  childTwo_carrier :
    ((R.circle childTwoIndex).zeroWindingJordanCircle
      (R.zeroWinding childTwoIndex)).carrier =
      commonArc ∪ outerArcTwo
  childOne_subset_outerClosed :
    ((R.circle childOneIndex).zeroWindingJordanCircle
      (R.zeroWinding childOneIndex)).carrier ⊆
      ((R.circle outerIndex).zeroWindingJordanCircle
          (R.zeroWinding outerIndex)).inside ∪
        ((R.circle outerIndex).zeroWindingJordanCircle
          (R.zeroWinding outerIndex)).carrier
  childTwo_subset_outerClosed :
    ((R.circle childTwoIndex).zeroWindingJordanCircle
      (R.zeroWinding childTwoIndex)).carrier ⊆
      ((R.circle outerIndex).zeroWindingJordanCircle
          (R.zeroWinding outerIndex)).inside ∪
        ((R.circle outerIndex).zeroWindingJordanCircle
          (R.zeroWinding outerIndex)).carrier
  outerArcOne_has_private_point :
    (outerArcOne \
      ((R.circle childTwoIndex).zeroWindingJordanCircle
        (R.zeroWinding childTwoIndex)).carrier).Nonempty
  outerArcTwo_has_private_point :
    (outerArcTwo \
      ((R.circle childOneIndex).zeroWindingJordanCircle
        (R.zeroWinding childOneIndex)).carrier).Nonempty
  exceptional_finite : exceptional.Finite
  common_local_line : ∀ p ∈ commonArc \ exceptional,
    ∃ d : TorusCoveringPlane, ∃ r : ℝ, 0 < r ∧
      Metric.ball p r ∩
          ((R.circle childOneIndex).zeroWindingJordanCircle
            (R.zeroWinding childOneIndex)).carrier =
        Metric.ball p r ∩ Schoenflies.determinantLine p d ∧
      Metric.ball p r ∩
          ((R.circle childTwoIndex).zeroWindingJordanCircle
            (R.zeroWinding childTwoIndex)).carrier =
        Metric.ball p r ∩ Schoenflies.determinantLine p d

namespace RawFourPortOuterPlaneThetaData

/-- The two bounded child faces exactly fill the closed disk of the selected outer cycle. -/
theorem outerClosed_eq_childFaces (T : RawFourPortOuterPlaneThetaData R) :
    closure
        ((R.circle T.outerIndex).zeroWindingJordanCircle
          (R.zeroWinding T.outerIndex)).inside =
      closure
          ((R.circle T.childOneIndex).zeroWindingJordanCircle
            (R.zeroWinding T.childOneIndex)).inside ∪
        closure
          ((R.circle T.childTwoIndex).zeroWindingJordanCircle
            (R.zeroWinding T.childTwoIndex)).inside := by
  exact Schoenflies.JordanThetaRegions.closure_inside_eq_union
    T.childOne_subset_outerClosed T.childTwo_subset_outerClosed
    T.outer_carrier T.childOne_carrier T.childTwo_carrier
    T.outerArcOne_has_private_point T.outerArcTwo_has_private_point
    T.exceptional_finite T.common_local_line

/-- The selected outer boundary itself lies in its projected canonical closed disk. -/
theorem outerCircle_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    torusCircleCarrier (R.circle T.outerIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  change Set.range (R.circle T.outerIndex).torusCircle ⊆ _
  rw [← (R.circle T.outerIndex).image_zeroWindingJordanCarrier
    (R.zeroWinding T.outerIndex)]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    ((R.circle T.outerIndex).zeroWindingJordanCircle
      (R.zeroWinding T.outerIndex)).closure_inside]
  exact Or.inr hx

/-- The first bounded child boundary lies in the selected outer canonical disk. -/
theorem childOneCircle_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    torusCircleCarrier (R.circle T.childOneIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  change Set.range (R.circle T.childOneIndex).torusCircle ⊆ _
  rw [← (R.circle T.childOneIndex).image_zeroWindingJordanCarrier
    (R.zeroWinding T.childOneIndex)]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    ((R.circle T.outerIndex).zeroWindingJordanCircle
      (R.zeroWinding T.outerIndex)).closure_inside]
  exact T.childOne_subset_outerClosed hx

/-- The second bounded child boundary lies in the selected outer canonical disk. -/
theorem childTwoCircle_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    torusCircleCarrier (R.circle T.childTwoIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  change Set.range (R.circle T.childTwoIndex).torusCircle ⊆ _
  rw [← (R.circle T.childTwoIndex).image_zeroWindingJordanCarrier
    (R.zeroWinding T.childTwoIndex)]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    ((R.circle T.outerIndex).zeroWindingJordanCircle
      (R.zeroWinding T.outerIndex)).closure_inside]
  exact T.childTwo_subset_outerClosed hx

/-- Every raw theta cycle lies in the selected outer canonical disk. -/
theorem rawCircle_subset_outerDisk
    (T : RawFourPortOuterPlaneThetaData R) (i : Fin 3) :
    torusCircleCarrier (R.circle i) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rcases T.indices_exhaust i with hi | hi | hi
  · simpa [hi] using T.outerCircle_subset_outerDisk
  · simpa [hi] using T.childOneCircle_subset_outerDisk
  · simpa [hi] using T.childTwoCircle_subset_outerDisk

/-- The complete raw affected boundary lies in the selected outer canonical disk. -/
theorem affectedBoundary_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    threeCircleBoundaryUnion R.circle ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact T.rawCircle_subset_outerDisk i hi

theorem preAffectedBoundary_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    fourPortPreAffectedBoundary R.direction R.circle ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inl hx

theorem postAffectedBoundary_subset_outerDisk (T : RawFourPortOuterPlaneThetaData R) :
    fourPortPostAffectedBoundary R.direction R.circle ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inr hx

end RawFourPortOuterPlaneThetaData

/-- The local face premise for the parity-change lens.  Each change point has a chosen plane
lift in one of the two bounded theta faces.  Containment in the outer disk is then a theorem,
not a field. -/
structure RawFourPortLensFaceLiftData (T : RawFourPortOuterPlaneThetaData R) where
  lift : regularStageLabelChangeLocus pre post → TorusCoveringPlane
  projects : ∀ x,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (lift x) = x
  mem_childFaces : ∀ x,
    lift x ∈
      closure
          ((R.circle T.childOneIndex).zeroWindingJordanCircle
            (R.zeroWinding T.childOneIndex)).inside ∪
        closure
          ((R.circle T.childTwoIndex).zeroWindingJordanCircle
            (R.zeroWinding T.childTwoIndex)).inside

namespace RawFourPortLensFaceLiftData

/-- The lifted local face premise places the parity-change locus in the selected outer disk. -/
theorem labelChange_subset_outerDisk
    {T : RawFourPortOuterPlaneThetaData R}
    (L : RawFourPortLensFaceLiftData T) :
    regularStageLabelChangeLocus pre post ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  intro x hx
  let xChange : regularStageLabelChangeLocus pre post := ⟨x, hx⟩
  refine ⟨L.lift xChange, ?_, L.projects xChange⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    T.outerClosed_eq_childFaces]
  exact L.mem_childFaces xChange

end RawFourPortLensFaceLiftData

/-! ## Attachment to an endpoint stage -/

/-- Identification of the selected raw outer cycle with a maximal disk of one audited endpoint
system.  The system can be the pre endpoint or the post endpoint; that choice determines the
direction of the resulting disk-side cover. -/
structure RawFourPortOuterStageDiskAttachment
    {circleCount : ℕ}
    (T : RawFourPortOuterPlaneThetaData R)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount))
    (hzero : S.AllInessential) where
  diskIndex : Fin circleCount
  diskIndex_mem : diskIndex ∈
    (S.canonicalMaximalInessentialTorusDiskFamily hzero).maximal
  outerDisk_eq : Set.range (S.torusDiskMap hzero diskIndex) =
    (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
      (R.zeroWinding T.outerIndex)

namespace RawFourPortOuterStageDiskAttachment

variable {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}
  {T : RawFourPortOuterPlaneThetaData R}

/-- If the selected outer cycle belongs to the pre endpoint, it gives a forward disk-side
cover. -/
def toForwardFiniteElementaryDiskSideCover
    (I : RawFourPortOuterStageDiskAttachment T S hzero)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover S hzero pre post where
  moveCount := 1
  newBoundaryPatch := fun _ ↦ raw.postAffectedBoundary
  changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
  diskIndex := fun _ ↦ I.diskIndex
  diskIndex_mem := fun _ ↦ I.diskIndex_mem
  newBoundaryPatch_subset_disk := by
    intro _
    rw [I.outerDisk_eq, ← R.post_range]
    exact T.postAffectedBoundary_subset_outerDisk
  changedLens_subset_disk := by
    intro _
    rw [I.outerDisk_eq]
    exact L.labelChange_subset_outerDisk
  postBoundary_subset := by
    intro x hx
    change x ∈ regularStageTorusBoundary post at hx
    rw [raw.postBoundary_exact] at hx
    rcases hx with hxUnaffected | hxAffected
    · apply Or.inl
      change x ∈ regularStageTorusBoundary pre
      rw [raw.preBoundary_exact]
      exact Or.inl hxUnaffected
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxAffected⟩)
  labelChange_subset := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- If the selected outer cycle belongs to the post endpoint, it gives the reverse disk-side
cover. -/
def toReverseFiniteElementaryDiskSideCover
    (I : RawFourPortOuterStageDiskAttachment T S hzero)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover S hzero post pre where
  moveCount := 1
  newBoundaryPatch := fun _ ↦ raw.preAffectedBoundary
  changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
  diskIndex := fun _ ↦ I.diskIndex
  diskIndex_mem := fun _ ↦ I.diskIndex_mem
  newBoundaryPatch_subset_disk := by
    intro _
    rw [I.outerDisk_eq, ← R.pre_range]
    exact T.preAffectedBoundary_subset_outerDisk
  changedLens_subset_disk := by
    intro _
    rw [I.outerDisk_eq]
    exact L.labelChange_subset_outerDisk
  postBoundary_subset := by
    intro x hx
    change x ∈ regularStageTorusBoundary pre at hx
    rw [raw.preBoundary_exact] at hx
    rcases hx with hxUnaffected | hxAffected
    · apply Or.inl
      change x ∈ regularStageTorusBoundary post
      rw [raw.postBoundary_exact]
      exact Or.inl hxUnaffected
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxAffected⟩)
  labelChange_subset := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, fun h ↦ hx h.symm⟩

end RawFourPortOuterStageDiskAttachment

/-- Identification of the selected raw outer cycle with an ordinary circle of one audited
endpoint system.  Maximality is not part of this interface: the canonical finite laminar-disk
construction enlarges this circle's disk to a selected maximal disk. -/
structure RawFourPortOuterStageCircleAttachment
    {circleCount : ℕ}
    (T : RawFourPortOuterPlaneThetaData R)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)) where
  circleIndex : Fin circleCount
  outerCircle_eq : S.circle circleIndex = R.circle T.outerIndex

namespace RawFourPortOuterStageCircleAttachment

variable {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}
  {T : RawFourPortOuterPlaneThetaData R}

private theorem projectedClosedJordanDisk_congr
    {C D : EmbeddedTorusIntersectionCircle Phi}
    (hCD : C = D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      D.zeroWindingProjectedClosedJordanDisk hD := by
  subst D
  rfl

/-- The ordinary endpoint-circle identification canonically supplies a maximal stage disk
containing the selected raw outer disk. -/
theorem exists_maximalDisk_superset
    (I : RawFourPortOuterStageCircleAttachment T S) :
    ∃ j ∈ (S.canonicalMaximalInessentialTorusDiskFamily hzero).maximal,
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
          (R.zeroWinding T.outerIndex) ⊆
        Set.range (S.torusDiskMap hzero j) := by
  obtain ⟨j, hj, hsubset⟩ :=
    (S.canonicalMaximalInessentialTorusDiskFamily hzero).every_disk_nested I.circleIndex
  refine ⟨j, hj, ?_⟩
  intro x hx
  apply hsubset
  rw [S.range_torusDiskMap_eq_projectedClosedJordanDisk]
  rw [projectedClosedJordanDisk_congr I.outerCircle_eq
    (hzero I.circleIndex) (R.zeroWinding T.outerIndex)]
  exact hx

/-- If the selected raw outer cycle is a pre-endpoint circle, canonical maximality gives a
forward disk-side cover. -/
noncomputable def toForwardFiniteElementaryDiskSideCover
    (I : RawFourPortOuterStageCircleAttachment T S)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover S hzero pre post := by
  let hexists := I.exists_maximalDisk_superset (hzero := hzero)
  let j := Classical.choose hexists
  have hj := (Classical.choose_spec hexists).1
  have hsubset := (Classical.choose_spec hexists).2
  exact {
    moveCount := 1
    newBoundaryPatch := fun _ ↦ raw.postAffectedBoundary
    changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
    diskIndex := fun _ ↦ j
    diskIndex_mem := fun _ ↦ hj
    newBoundaryPatch_subset_disk := by
      intro _
      change raw.postAffectedBoundary ⊆
        Set.range (S.torusDiskMap hzero (Classical.choose hexists))
      rw [← R.post_range]
      exact T.postAffectedBoundary_subset_outerDisk.trans hsubset
    changedLens_subset_disk := by
      intro _
      change regularStageLabelChangeLocus pre post ⊆
        Set.range (S.torusDiskMap hzero (Classical.choose hexists))
      exact L.labelChange_subset_outerDisk.trans hsubset
    postBoundary_subset := by
      intro x hx
      change x ∈ regularStageTorusBoundary post at hx
      rw [raw.postBoundary_exact] at hx
      rcases hx with hxUnaffected | hxAffected
      · apply Or.inl
        change x ∈ regularStageTorusBoundary pre
        rw [raw.preBoundary_exact]
        exact Or.inl hxUnaffected
      · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxAffected⟩)
    labelChange_subset := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩ }

/-- If the selected raw outer cycle is a post-endpoint circle, canonical maximality gives a
reverse disk-side cover. -/
noncomputable def toReverseFiniteElementaryDiskSideCover
    (I : RawFourPortOuterStageCircleAttachment T S)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover S hzero post pre := by
  let hexists := I.exists_maximalDisk_superset (hzero := hzero)
  let j := Classical.choose hexists
  have hj := (Classical.choose_spec hexists).1
  have hsubset := (Classical.choose_spec hexists).2
  exact {
    moveCount := 1
    newBoundaryPatch := fun _ ↦ raw.preAffectedBoundary
    changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
    diskIndex := fun _ ↦ j
    diskIndex_mem := fun _ ↦ hj
    newBoundaryPatch_subset_disk := by
      intro _
      change raw.preAffectedBoundary ⊆
        Set.range (S.torusDiskMap hzero (Classical.choose hexists))
      rw [← R.pre_range]
      exact T.preAffectedBoundary_subset_outerDisk.trans hsubset
    changedLens_subset_disk := by
      intro _
      change regularStageLabelChangeLocus pre post ⊆
        Set.range (S.torusDiskMap hzero (Classical.choose hexists))
      exact L.labelChange_subset_outerDisk.trans hsubset
    postBoundary_subset := by
      intro x hx
      change x ∈ regularStageTorusBoundary pre at hx
      rw [raw.preBoundary_exact] at hx
      rcases hx with hxUnaffected | hxAffected
      · apply Or.inl
        change x ∈ regularStageTorusBoundary post
        rw [raw.postBoundary_exact]
        exact Or.inl hxUnaffected
      · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxAffected⟩)
    labelChange_subset := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, fun h ↦ hx h.symm⟩ }

end RawFourPortOuterStageCircleAttachment

/-- Endpoint attachment data records on which side the selected outer raw disk occurs. -/
def RawFourPortEndpointDiskSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (T : RawFourPortOuterPlaneThetaData R)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (preZero : preSystem.AllInessential)
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount))
    (postZero : postSystem.AllInessential) :=
  RawFourPortOuterStageDiskAttachment T preSystem preZero ⊕
    RawFourPortOuterStageDiskAttachment T postSystem postZero

/-- It suffices to identify the raw outer cycle with an ordinary circle on either endpoint;
the canonical maximal-disk construction supplies the required enclosing selected disk. -/
def RawFourPortEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (T : RawFourPortOuterPlaneThetaData R)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  RawFourPortOuterStageCircleAttachment T preSystem ⊕
    RawFourPortOuterStageCircleAttachment T postSystem

/-- An endpoint-circle identification, rather than a maximal-disk equality, produces the exact
forward-or-reverse alternative required by a finite stage-side sequence. -/
noncomputable def rawFourPortEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {T : RawFourPortOuterPlaneThetaData R}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : RawFourPortEndpointCircleSideAttachment T preSystem postSystem)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  rcases I with I | I
  · exact Sum.inl (I.toForwardFiniteElementaryDiskSideCover (hzero := preZero) L)
  · exact Sum.inr (I.toReverseFiniteElementaryDiskSideCover (hzero := postZero) L)

/-- The raw theta argument produces the exact forward-or-reverse alternative required by a
finite stage-side sequence. -/
def rawFourPortEndpointDiskSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {T : RawFourPortOuterPlaneThetaData R}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : RawFourPortEndpointDiskSideAttachment T preSystem preZero postSystem postZero)
    (L : RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  rcases I with I | I
  · exact Sum.inl (I.toForwardFiniteElementaryDiskSideCover L)
  · exact Sum.inr (I.toReverseFiniteElementaryDiskSideCover L)

end Submission.Topology
