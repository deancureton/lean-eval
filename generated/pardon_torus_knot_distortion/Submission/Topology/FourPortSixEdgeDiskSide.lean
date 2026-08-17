import Submission.Topology.FourPortSixEdgeOuterFaceSelection

/-!
# Disk-sided four-port transitions from the honest six-edge graph

The planar six-edge theorem selects the raw cycle surrounding the rectangle and the other two
raw disks.  Deck translation does not change projection to the torus, so all three affected
raw circles lie in the projected canonical disk of that selected cycle.  A lift of the actual
parity-change lens into those bounded planar faces then places the entire move on one disk side.

The selected raw cycle may occur at either endpoint of the move.  Identifying it with an
ordinary circle of that endpoint system lets canonical maximality enlarge its disk and produces
the required forward-or-reverse elementary disk-side cover.
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

namespace FourPortRawSixEdgePresentation

variable (P : FourPortRawSixEdgePresentation R)

/-- The graph-circle indexing in `P` agrees with the indexing in its coherent lift data. -/
theorem rawEmbeddedCircle_eq_zeroWindingData (i : Fin 3) :
    P.rawEmbeddedCircle i = P.zeroWindingData.rawEmbeddedCircle i := by
  fin_cases i <;> rfl

namespace OuterRawFaceData

variable {D : P.planePathSystem.RectangleRotationData}

/-- Every raw endpoint-circle carrier lies in the disk selected by the planar face theorem. -/
theorem rawCircleCarrier_subset_selectedDisk
    (F : P.planePathSystem.OuterRawFaceData D) (i : Fin 3) :
    torusCircleCarrier (R.circle i) ⊆
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
          (P.zeroWindingData.rawZeroWinding F.outerIndex) := by
  rw [← P.rawEmbeddedCircle_carrier_eq i,
    P.rawEmbeddedCircle_eq_zeroWindingData i]
  exact
    FourPortSixEdgeZeroWindingData.OuterRawFaceData.rawCircleCarrier_subset_selectedDisk
      P.zeroWindingData F i

/-- The complete affected boundary lies in the selected canonical projected disk. -/
theorem affectedBoundary_subset_selectedDisk
    (F : P.planePathSystem.OuterRawFaceData D) :
    threeCircleBoundaryUnion R.circle ⊆
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
          (P.zeroWindingData.rawZeroWinding F.outerIndex) := by
  rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact rawCircleCarrier_subset_selectedDisk P F i hi

theorem preAffectedBoundary_subset_selectedDisk
    (F : P.planePathSystem.OuterRawFaceData D) :
    raw.preAffectedBoundary ⊆
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
          (P.zeroWindingData.rawZeroWinding F.outerIndex) := by
  rw [← R.pre_range]
  intro x hx
  apply affectedBoundary_subset_selectedDisk P F
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inl hx

theorem postAffectedBoundary_subset_selectedDisk
    (F : P.planePathSystem.OuterRawFaceData D) :
    raw.postAffectedBoundary ⊆
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
          (P.zeroWindingData.rawZeroWinding F.outerIndex) := by
  rw [← R.post_range]
  intro x hx
  apply affectedBoundary_subset_selectedDisk P F
  rw [← preAffected_union_postAffected R.direction R.circle]
  exact Or.inr hx

end OuterRawFaceData
end FourPortRawSixEdgePresentation

/-- A lift of the parity-change locus into the three bounded faces selected in the plane.

For the analytic four-port model the change lens is expected to lie in the rectangular face.
The more symmetric union below also permits either adjacent raw disk, and is exactly the right
side of the proved outer-face decomposition.
-/
structure FourPortSixEdgeFaceLensLiftData
    (P : FourPortRawSixEdgePresentation R)
    {D : P.planePathSystem.RectangleRotationData}
    (F : P.planePathSystem.OuterRawFaceData D) where
  lift : regularStageLabelChangeLocus pre post → TorusCoveringPlane
  projects : ∀ x,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (lift x) = x
  mem_boundedFaces : ∀ x,
    lift x ∈
      closure (P.planePathSystem.localRectangleJordanCircle D.rectangle).inside ∪
        closure
            (P.planePathSystem.rawPlaneJordanCircle F.childOneIndex).inside ∪
          closure
            (P.planePathSystem.rawPlaneJordanCircle F.childTwoIndex).inside

namespace FourPortSixEdgeFaceLensLiftData

variable {P : FourPortRawSixEdgePresentation R}
  {D : P.planePathSystem.RectangleRotationData}
  {F : P.planePathSystem.OuterRawFaceData D}

/-- The lifted bounded-face premise places every label-change point in the selected disk. -/
theorem labelChange_subset_selectedDisk (L : FourPortSixEdgeFaceLensLiftData P F) :
    regularStageLabelChangeLocus pre post ⊆
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
          (P.zeroWindingData.rawZeroWinding F.outerIndex) := by
  intro x hx
  let xChange : regularStageLabelChangeLocus pre post := ⟨x, hx⟩
  rw [← P.zeroWindingData.image_rawPlaneJordanClosedDisk F.outerIndex]
  refine ⟨L.lift xChange, ?_, L.projects xChange⟩
  change L.lift xChange ∈
    closure (P.planePathSystem.rawPlaneJordanCircle F.outerIndex).inside
  rw [F.outerClosed_eq]
  exact L.mem_boundedFaces xChange

end FourPortSixEdgeFaceLensLiftData

/-- Identification of the selected graph circle with an ordinary circle of one endpoint
intersection system. -/
structure FourPortSixEdgeOuterStageCircleAttachment
    {circleCount : ℕ}
    (P : FourPortRawSixEdgePresentation R)
    {D : P.planePathSystem.RectangleRotationData}
    (F : P.planePathSystem.OuterRawFaceData D)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)) where
  circleIndex : Fin circleCount
  outerCircle_eq : S.circle circleIndex =
    P.zeroWindingData.rawEmbeddedCircle F.outerIndex

namespace FourPortSixEdgeOuterStageCircleAttachment

variable {P : FourPortRawSixEdgePresentation R}
  {D : P.planePathSystem.RectangleRotationData}
  {F : P.planePathSystem.OuterRawFaceData D}
  {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}

private theorem projectedClosedJordanDisk_congr
    {C E : EmbeddedTorusIntersectionCircle Phi}
    (hCE : C = E)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hE : E.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      E.zeroWindingProjectedClosedJordanDisk hE := by
  subst E
  rfl

/-- Canonical laminar maximality enlarges the selected graph disk to a maximal stage disk. -/
theorem exists_maximalDisk_superset
    (I : FourPortSixEdgeOuterStageCircleAttachment P F S) :
    ∃ j ∈ (S.canonicalMaximalInessentialTorusDiskFamily hzero).maximal,
      (P.zeroWindingData.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
            (P.zeroWindingData.rawZeroWinding F.outerIndex) ⊆
        Set.range (S.torusDiskMap hzero j) := by
  obtain ⟨j, hj, hsubset⟩ :=
    (S.canonicalMaximalInessentialTorusDiskFamily hzero).every_disk_nested I.circleIndex
  refine ⟨j, hj, ?_⟩
  intro x hx
  apply hsubset
  rw [S.range_torusDiskMap_eq_projectedClosedJordanDisk]
  rw [projectedClosedJordanDisk_congr I.outerCircle_eq
    (hzero I.circleIndex) (P.zeroWindingData.rawZeroWinding F.outerIndex)]
  exact hx

/-- A pre-endpoint attachment produces a forward disk-side cover. -/
noncomputable def toForwardFiniteElementaryDiskSideCover
    (I : FourPortSixEdgeOuterStageCircleAttachment P F S)
    (L : FourPortSixEdgeFaceLensLiftData P F) :
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
      exact
        (FourPortRawSixEdgePresentation.OuterRawFaceData.postAffectedBoundary_subset_selectedDisk
          P F).trans hsubset
    changedLens_subset_disk := by
      intro _
      exact L.labelChange_subset_selectedDisk.trans hsubset
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

/-- A post-endpoint attachment produces the reversed disk-side cover. -/
noncomputable def toReverseFiniteElementaryDiskSideCover
    (I : FourPortSixEdgeOuterStageCircleAttachment P F S)
    (L : FourPortSixEdgeFaceLensLiftData P F) :
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
      exact
        (FourPortRawSixEdgePresentation.OuterRawFaceData.preAffectedBoundary_subset_selectedDisk
          P F).trans hsubset
    changedLens_subset_disk := by
      intro _
      exact L.labelChange_subset_selectedDisk.trans hsubset
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

end FourPortSixEdgeOuterStageCircleAttachment

/-- The selected outer graph circle may occur on either endpoint of the move. -/
def FourPortSixEdgeEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (P : FourPortRawSixEdgePresentation R)
    {D : P.planePathSystem.RectangleRotationData}
    (F : P.planePathSystem.OuterRawFaceData D)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  FourPortSixEdgeOuterStageCircleAttachment P F preSystem ⊕
    FourPortSixEdgeOuterStageCircleAttachment P F postSystem

/-- The honest six-edge outer face and an endpoint-circle attachment give the exact local
alternative consumed by a finite stage-side sequence. -/
noncomputable def fourPortSixEdgeEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {P : FourPortRawSixEdgePresentation R}
    {D : P.planePathSystem.RectangleRotationData}
    {F : P.planePathSystem.OuterRawFaceData D}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : FourPortSixEdgeEndpointCircleSideAttachment P F preSystem postSystem)
    (L : FourPortSixEdgeFaceLensLiftData P F) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  rcases I with I | I
  · exact Sum.inl (I.toForwardFiniteElementaryDiskSideCover (hzero := preZero) L)
  · exact Sum.inr (I.toReverseFiniteElementaryDiskSideCover (hzero := postZero) L)

/-! ## Canonically selected outer face -/

/-- Lens-lift data for the canonically selected outer face. -/
abbrev FourPortSixEdgeSelectedFaceLensLiftData
    (P : FourPortRawSixEdgePresentation R)
    (D : P.planePathSystem.RectangleRotationData) :=
  FourPortSixEdgeFaceLensLiftData P
    (P.planePathSystem.selectedOuterRawFaceData D)

/-- Endpoint attachment data for the canonically selected outer face. -/
abbrev FourPortSixEdgeSelectedEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (P : FourPortRawSixEdgePresentation R)
    (D : P.planePathSystem.RectangleRotationData)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  FourPortSixEdgeEndpointCircleSideAttachment P
    (P.planePathSystem.selectedOuterRawFaceData D) preSystem postSystem

/-- After canonical outer-face selection, the lift and endpoint attachment are the only inputs
to the local forward-or-reverse disk-side alternative. -/
noncomputable def selectedFourPortSixEdgeEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {P : FourPortRawSixEdgePresentation R}
    {D : P.planePathSystem.RectangleRotationData}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : FourPortSixEdgeSelectedEndpointCircleSideAttachment P D preSystem postSystem)
    (L : FourPortSixEdgeSelectedFaceLensLiftData P D) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre :=
  fourPortSixEdgeEndpointCircleSideAlternative I L

end Submission.Topology
