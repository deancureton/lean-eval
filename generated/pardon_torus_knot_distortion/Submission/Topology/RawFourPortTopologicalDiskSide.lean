import Submission.Topology.RawFourPortThetaDiskSide
import Submission.Topology.TopologicalThetaOuterCycle

/-!
# Topological raw four-port disk-side transitions

The disk-side argument only consumes an ordering of the three raw circles and the exact equality
between the selected outer closed disk and the two child closed faces.  This module exposes that
minimal invariant interface.  Local straightening belongs solely in the upstream proof of the
face equality and is not retained downstream.
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

/-- The minimal output of selecting the outer cycle of the raw theta graph. -/
structure RawFourPortOuterFaceData (R : FourPortRawCircleData raw) where
  outerIndex : Fin 3
  childOneIndex : Fin 3
  childTwoIndex : Fin 3
  indices_exhaust : ∀ i,
    i = outerIndex ∨ i = childOneIndex ∨ i = childTwoIndex
  outerClosed_eq_childFaces :
    closure
        ((R.circle outerIndex).zeroWindingJordanCircle
          (R.zeroWinding outerIndex)).inside =
      closure
          ((R.circle childOneIndex).zeroWindingJordanCircle
            (R.zeroWinding childOneIndex)).inside ∪
        closure
          ((R.circle childTwoIndex).zeroWindingJordanCircle
            (R.zeroWinding childTwoIndex)).inside

namespace RawFourPortOuterFaceData

/-- The older locally polygonal theta package forgets to the invariant face package. -/
def ofOuterPlaneThetaData (T : RawFourPortOuterPlaneThetaData R) :
    RawFourPortOuterFaceData R where
  outerIndex := T.outerIndex
  childOneIndex := T.childOneIndex
  childTwoIndex := T.childTwoIndex
  indices_exhaust := T.indices_exhaust
  outerClosed_eq_childFaces := T.outerClosed_eq_childFaces

/-- The selected outer boundary lies in its projected canonical disk. -/
theorem outerCircle_subset_outerDisk (T : RawFourPortOuterFaceData R) :
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

/-- The first child boundary lies in the selected outer canonical disk. -/
theorem childOneCircle_subset_outerDisk (T : RawFourPortOuterFaceData R) :
    torusCircleCarrier (R.circle T.childOneIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  change Set.range (R.circle T.childOneIndex).torusCircle ⊆ _
  rw [← (R.circle T.childOneIndex).image_zeroWindingJordanCarrier
    (R.zeroWinding T.childOneIndex)]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    T.outerClosed_eq_childFaces]
  exact Or.inl (by
    rw [((R.circle T.childOneIndex).zeroWindingJordanCircle
      (R.zeroWinding T.childOneIndex)).closure_inside]
    exact Or.inr hx)

/-- The second child boundary lies in the selected outer canonical disk. -/
theorem childTwoCircle_subset_outerDisk (T : RawFourPortOuterFaceData R) :
    torusCircleCarrier (R.circle T.childTwoIndex) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  change Set.range (R.circle T.childTwoIndex).torusCircle ⊆ _
  rw [← (R.circle T.childTwoIndex).image_zeroWindingJordanCarrier
    (R.zeroWinding T.childTwoIndex)]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    T.outerClosed_eq_childFaces]
  exact Or.inr (by
    rw [((R.circle T.childTwoIndex).zeroWindingJordanCircle
      (R.zeroWinding T.childTwoIndex)).closure_inside]
    exact Or.inr hx)

/-- Every raw theta cycle lies in the selected outer canonical disk. -/
theorem rawCircle_subset_outerDisk
    (T : RawFourPortOuterFaceData R) (i : Fin 3) :
    torusCircleCarrier (R.circle i) ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rcases T.indices_exhaust i with hi | hi | hi
  · simpa [hi] using T.outerCircle_subset_outerDisk
  · simpa [hi] using T.childOneCircle_subset_outerDisk
  · simpa [hi] using T.childTwoCircle_subset_outerDisk

/-- The complete affected boundary lies in the selected outer canonical disk. -/
theorem affectedBoundary_subset_outerDisk (T : RawFourPortOuterFaceData R) :
    threeCircleBoundaryUnion R.circle ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact T.rawCircle_subset_outerDisk i hi

theorem preAffectedBoundary_subset_outerDisk (T : RawFourPortOuterFaceData R) :
    raw.preAffectedBoundary ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← R.pre_range]
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inl hx

theorem postAffectedBoundary_subset_outerDisk (T : RawFourPortOuterFaceData R) :
    raw.postAffectedBoundary ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  rw [← R.post_range]
  intro x hx
  apply T.affectedBoundary_subset_outerDisk
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inr hx

end RawFourPortOuterFaceData

/-- A plane lift of the parity-change locus into the two bounded theta faces. -/
structure RawFourPortFaceLensLiftData (T : RawFourPortOuterFaceData R) where
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

namespace RawFourPortFaceLensLiftData

/-- The lifted lens lies in the selected outer canonical disk. -/
theorem labelChange_subset_outerDisk
    {T : RawFourPortOuterFaceData R}
    (L : RawFourPortFaceLensLiftData T) :
    regularStageLabelChangeLocus pre post ⊆
      (R.circle T.outerIndex).zeroWindingProjectedClosedJordanDisk
        (R.zeroWinding T.outerIndex) := by
  intro x hx
  let xChange : regularStageLabelChangeLocus pre post := ⟨x, hx⟩
  refine ⟨L.lift xChange, ?_, L.projects xChange⟩
  rw [EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    T.outerClosed_eq_childFaces]
  exact L.mem_childFaces xChange

end RawFourPortFaceLensLiftData

/-- Identification of the selected raw outer circle with an ordinary endpoint-system circle. -/
structure RawFourPortOuterFaceStageCircleAttachment
    {circleCount : ℕ}
    (T : RawFourPortOuterFaceData R)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)) where
  circleIndex : Fin circleCount
  outerCircle_eq : S.circle circleIndex = R.circle T.outerIndex

namespace RawFourPortOuterFaceStageCircleAttachment

variable {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}
  {T : RawFourPortOuterFaceData R}

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
    (I : RawFourPortOuterFaceStageCircleAttachment T S) :
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
    (I : RawFourPortOuterFaceStageCircleAttachment T S)
    (L : RawFourPortFaceLensLiftData T) :
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

noncomputable def toReverseFiniteElementaryDiskSideCover
    (I : RawFourPortOuterFaceStageCircleAttachment T S)
    (L : RawFourPortFaceLensLiftData T) :
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
      exact Set.mem_iUnion.mpr ⟨0, fun heq ↦ hx heq.symm⟩ }

end RawFourPortOuterFaceStageCircleAttachment

/-- The topological theta presentation identifies the raw circles but chooses no outer cycle. -/
structure RawFourPortTopologicalThetaPresentation (R : FourPortRawCircleData raw) where
  theta : TopologicalPlanarJordanThetaData
  index01 : Fin 3
  index02 : Fin 3
  index12 : Fin 3
  indices_exhaust : ∀ i, i = index01 ∨ i = index02 ∨ i = index12
  circle01_eq :
    (R.circle index01).zeroWindingJordanCircle (R.zeroWinding index01) = theta.circle01
  circle02_eq :
    (R.circle index02).zeroWindingJordanCircle (R.zeroWinding index02) = theta.circle02
  circle12_eq :
    (R.circle index12).zeroWindingJordanCircle (R.zeroWinding index12) = theta.circle12

namespace RawFourPortTopologicalThetaPresentation

/-- The invariant topological theta theorem selects the minimal raw outer-face package. -/
theorem nonempty_outerFaceData
    (P : RawFourPortTopologicalThetaPresentation R) :
    Nonempty (RawFourPortOuterFaceData R) := by
  rcases TopologicalPlanarJordanThetaData.exists_outer_cycle_decomposition P.theta with
    h01 | h02 | h12
  · refine ⟨{
      outerIndex := P.index01
      childOneIndex := P.index02
      childTwoIndex := P.index12
      indices_exhaust := P.indices_exhaust
      outerClosed_eq_childFaces := ?_ }⟩
    simpa only [P.circle01_eq, P.circle02_eq, P.circle12_eq] using h01
  · refine ⟨{
      outerIndex := P.index02
      childOneIndex := P.index01
      childTwoIndex := P.index12
      indices_exhaust := fun i ↦ by
        rcases P.indices_exhaust i with hi | hi | hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inl hi
        · exact Or.inr (Or.inr hi)
      outerClosed_eq_childFaces := ?_ }⟩
    simpa only [P.circle01_eq, P.circle02_eq, P.circle12_eq] using h02
  · refine ⟨{
      outerIndex := P.index12
      childOneIndex := P.index01
      childTwoIndex := P.index02
      indices_exhaust := fun i ↦ by
        rcases P.indices_exhaust i with hi | hi | hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
        · exact Or.inl hi
      outerClosed_eq_childFaces := ?_ }⟩
    simpa only [P.circle01_eq, P.circle02_eq, P.circle12_eq] using h12

end RawFourPortTopologicalThetaPresentation

/-- Endpoint attachment may select either the pre or post system. -/
def RawFourPortFaceEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (T : RawFourPortOuterFaceData R)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  RawFourPortOuterFaceStageCircleAttachment T preSystem ⊕
    RawFourPortOuterFaceStageCircleAttachment T postSystem

/-- The minimal outer-face package and an ordinary endpoint-circle equality produce the exact
forward-or-reverse disk-side alternative. -/
noncomputable def rawFourPortFaceEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {T : RawFourPortOuterFaceData R}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : RawFourPortFaceEndpointCircleSideAttachment T preSystem postSystem)
    (L : RawFourPortFaceLensLiftData T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  rcases I with I | I
  · exact Sum.inl (I.toForwardFiniteElementaryDiskSideCover (hzero := preZero) L)
  · exact Sum.inr (I.toReverseFiniteElementaryDiskSideCover (hzero := postZero) L)

end Submission.Topology
