import Submission.PlaneSchoenflies.Schoenflies.JordanCarrierInvariance
import Submission.Topology.RawFourPortTopologicalDiskSide

/-!
# Projection-invariant raw four-port theta faces

Coherent plane lifts are aligned by deck translations.  Their Jordan disks therefore need not
equal the canonical zero-winding plane disks literally, but their projections to the transported
torus are the same.  This module formulates the raw theta disk-side argument at that invariant
level.
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

/-- A carrier identified with a translated Jordan circle has the same projected closed disk when
the projection is invariant under that translation. -/
theorem projected_closure_inside_eq_of_carrier_eq_translate
    (K J : Schoenflies.JordanCircle) (v : TorusCoveringPlane)
    (hcarrier : K.carrier = (J.translate v).carrier)
    (hprojection : ∀ x,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (x + v) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure K.inside =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure J.inside := by
  rw [K.inside_eq_of_carrier_eq (J.translate v) hcarrier,
    J.closure_inside_translate, Set.image_image]
  apply Set.image_congr
  intro x hx
  exact hprojection x

/-- A selected outer plane face whose three closed disks project to the three raw canonical
torus disks.  No literal equality between differently based plane lifts is required. -/
structure RawFourPortProjectedOuterFaceData (R : FourPortRawCircleData raw) where
  outerIndex : Fin 3
  childOneIndex : Fin 3
  childTwoIndex : Fin 3
  indices_exhaust : ∀ i,
    i = outerIndex ∨ i = childOneIndex ∨ i = childTwoIndex
  outerCircle : Schoenflies.JordanCircle
  childOneCircle : Schoenflies.JordanCircle
  childTwoCircle : Schoenflies.JordanCircle
  outerClosed_eq_childFaces :
    closure outerCircle.inside =
      closure childOneCircle.inside ∪ closure childTwoCircle.inside
  outer_projection :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure outerCircle.inside =
      (R.circle outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding outerIndex)
  childOne_projection :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure childOneCircle.inside =
      (R.circle childOneIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding childOneIndex)
  childTwo_projection :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure childTwoCircle.inside =
      (R.circle childTwoIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding childTwoIndex)

namespace RawFourPortProjectedOuterFaceData

private theorem torusCircleCarrier_subset_projectedClosedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    torusCircleCarrier C ⊆ C.zeroWindingProjectedClosedJordanDisk hzero := by
  change Set.range C.torusCircle ⊆ _
  rw [← C.image_zeroWindingJordanCarrier hzero]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    (C.zeroWindingJordanCircle hzero).closure_inside]
  exact Or.inr hx

/-- The first child canonical torus disk lies in the selected outer canonical torus disk. -/
theorem childOneDisk_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) :
    (R.circle T.childOneIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.childOneIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← T.childOne_projection, ← T.outer_projection]
  apply Set.image_mono
  rw [T.outerClosed_eq_childFaces]
  exact Set.subset_union_left

/-- The second child canonical torus disk lies in the selected outer canonical torus disk. -/
theorem childTwoDisk_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) :
    (R.circle T.childTwoIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.childTwoIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← T.childTwo_projection, ← T.outer_projection]
  apply Set.image_mono
  rw [T.outerClosed_eq_childFaces]
  exact Set.subset_union_right

/-- Every raw affected circle lies in the selected outer canonical torus disk. -/
theorem rawCircle_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) (i : Fin 3) :
    torusCircleCarrier (R.circle i) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rcases T.indices_exhaust i with hi | hi | hi
  · subst i
    exact torusCircleCarrier_subset_projectedClosedJordanDisk (R.circle T.outerIndex)
      (R.zeroWinding T.outerIndex)
  · subst i
    exact (torusCircleCarrier_subset_projectedClosedJordanDisk
      (R.circle T.childOneIndex)
      (R.zeroWinding T.childOneIndex)).trans T.childOneDisk_subset_outerDisk
  · subst i
    exact (torusCircleCarrier_subset_projectedClosedJordanDisk
      (R.circle T.childTwoIndex)
      (R.zeroWinding T.childTwoIndex)).trans T.childTwoDisk_subset_outerDisk

/-- The full affected boundary lies in the selected outer canonical torus disk. -/
theorem affectedBoundary_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) :
    threeCircleBoundaryUnion R.circle ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion]
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact T.rawCircle_subset_outerDisk i hi

theorem preAffectedBoundary_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) :
    raw.preAffectedBoundary ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← R.pre_range]
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inl hx

theorem postAffectedBoundary_subset_outerDisk
    (T : RawFourPortProjectedOuterFaceData R) :
    raw.postAffectedBoundary ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← R.post_range]
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inr hx

end RawFourPortProjectedOuterFaceData

/-- A lift of the parity-change locus into the two selected bounded plane faces. -/
structure RawFourPortProjectedFaceLensLiftData
    (T : RawFourPortProjectedOuterFaceData R) where
  lift : regularStageLabelChangeLocus pre post → TorusCoveringPlane
  projects : ∀ x,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (lift x) = x
  mem_childFaces : ∀ x,
    lift x ∈ closure T.childOneCircle.inside ∪ closure T.childTwoCircle.inside

namespace RawFourPortProjectedFaceLensLiftData

theorem labelChange_subset_outerDisk
    {T : RawFourPortProjectedOuterFaceData R}
    (L : RawFourPortProjectedFaceLensLiftData T) :
    regularStageLabelChangeLocus pre post ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  intro x hx
  let xChange : regularStageLabelChangeLocus pre post := ⟨x, hx⟩
  rw [← T.outer_projection, T.outerClosed_eq_childFaces]
  exact ⟨L.lift xChange, L.mem_childFaces xChange, L.projects xChange⟩

end RawFourPortProjectedFaceLensLiftData

/-- Identification of the selected outer raw circle with a circle of one endpoint system. -/
structure RawFourPortProjectedFaceStageCircleAttachment
    {circleCount : ℕ}
    (T : RawFourPortProjectedOuterFaceData R)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)) where
  circleIndex : Fin circleCount
  outerCircle_eq : S.circle circleIndex = R.circle T.outerIndex

namespace RawFourPortProjectedFaceStageCircleAttachment

variable {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}
  {T : RawFourPortProjectedOuterFaceData R}

private theorem projectedClosedJordanDisk_congr
    {C D : EmbeddedTorusIntersectionCircle Phi}
    (hCD : C = D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      D.zeroWindingProjectedClosedJordanDisk hD := by
  subst D
  rfl

theorem exists_maximalDisk_superset
    (I : RawFourPortProjectedFaceStageCircleAttachment T S) :
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

noncomputable def toForwardFiniteElementaryDiskSideCover
    (I : RawFourPortProjectedFaceStageCircleAttachment T S)
    (L : RawFourPortProjectedFaceLensLiftData T) :
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
      exact T.postAffectedBoundary_subset_outerDisk.trans hsubset
    changedLens_subset_disk := by
      intro _
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

noncomputable def toReverseFiniteElementaryDiskSideCover
    (I : RawFourPortProjectedFaceStageCircleAttachment T S)
    (L : RawFourPortProjectedFaceLensLiftData T) :
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
      exact T.preAffectedBoundary_subset_outerDisk.trans hsubset
    changedLens_subset_disk := by
      intro _
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
      exact Set.mem_iUnion.mpr ⟨0, fun heq ↦ hx heq.symm⟩ }

end RawFourPortProjectedFaceStageCircleAttachment

/-- A topological theta whose three plane disks project to the three raw canonical disks. -/
structure RawFourPortProjectedTopologicalThetaPresentation
    (R : FourPortRawCircleData raw) where
  theta : TopologicalPlanarJordanThetaData
  index01 : Fin 3
  index02 : Fin 3
  index12 : Fin 3
  indices_exhaust : ∀ i, i = index01 ∨ i = index02 ∨ i = index12
  projection01 :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure theta.circle01.inside =
      (R.circle index01).zeroWindingProjectedClosedJordanDisk (R.zeroWinding index01)
  projection02 :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure theta.circle02.inside =
      (R.circle index02).zeroWindingProjectedClosedJordanDisk (R.zeroWinding index02)
  projection12 :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure theta.circle12.inside =
      (R.circle index12).zeroWindingProjectedClosedJordanDisk (R.zeroWinding index12)

namespace RawFourPortProjectedTopologicalThetaPresentation

/-- The invariant topological theta theorem selects a projection-invariant outer face. -/
theorem nonempty_projectedOuterFaceData
    (P : RawFourPortProjectedTopologicalThetaPresentation R) :
    Nonempty (RawFourPortProjectedOuterFaceData R) := by
  rcases P.theta.exists_outer_cycle_decomposition with h01 | h02 | h12
  · exact ⟨{
      outerIndex := P.index01
      childOneIndex := P.index02
      childTwoIndex := P.index12
      indices_exhaust := P.indices_exhaust
      outerCircle := P.theta.circle01
      childOneCircle := P.theta.circle02
      childTwoCircle := P.theta.circle12
      outerClosed_eq_childFaces := h01
      outer_projection := P.projection01
      childOne_projection := P.projection02
      childTwo_projection := P.projection12 }⟩
  · exact ⟨{
      outerIndex := P.index02
      childOneIndex := P.index01
      childTwoIndex := P.index12
      indices_exhaust := fun i ↦ by
        rcases P.indices_exhaust i with hi | hi | hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inl hi
        · exact Or.inr (Or.inr hi)
      outerCircle := P.theta.circle02
      childOneCircle := P.theta.circle01
      childTwoCircle := P.theta.circle12
      outerClosed_eq_childFaces := h02
      outer_projection := P.projection02
      childOne_projection := P.projection01
      childTwo_projection := P.projection12 }⟩
  · exact ⟨{
      outerIndex := P.index12
      childOneIndex := P.index01
      childTwoIndex := P.index02
      indices_exhaust := fun i ↦ by
        rcases P.indices_exhaust i with hi | hi | hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
        · exact Or.inl hi
      outerCircle := P.theta.circle12
      childOneCircle := P.theta.circle01
      childTwoCircle := P.theta.circle02
      outerClosed_eq_childFaces := h12
      outer_projection := P.projection12
      childOne_projection := P.projection01
      childTwo_projection := P.projection02 }⟩

end RawFourPortProjectedTopologicalThetaPresentation

/-- Endpoint attachment may select either the pre or post system. -/
def RawFourPortProjectedFaceEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (T : RawFourPortProjectedOuterFaceData R)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  RawFourPortProjectedFaceStageCircleAttachment T preSystem ⊕
    RawFourPortProjectedFaceStageCircleAttachment T postSystem

/-- Projection-invariant theta faces give the exact forward-or-reverse disk-side alternative. -/
noncomputable def rawFourPortProjectedFaceEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {T : RawFourPortProjectedOuterFaceData R}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : RawFourPortProjectedFaceEndpointCircleSideAttachment T preSystem postSystem)
    (L : RawFourPortProjectedFaceLensLiftData T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  rcases I with I | I
  · exact Sum.inl (I.toForwardFiniteElementaryDiskSideCover (hzero := preZero) L)
  · exact Sum.inr (I.toReverseFiniteElementaryDiskSideCover (hzero := postZero) L)

end Submission.Topology
