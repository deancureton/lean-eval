import Submission.Topology.FourPortSixEdgeOuterFaceSelection
import Submission.Topology.ReducedTorusCircleTransitions

/-!
# Reduced disk-sided transitions from a six-edge four-port graph

The planar outer-face argument depends only on the three zero-winding torus circles of the
six-edge graph.  This module attaches its selected disk directly to a reduced torus-circle
stage, without introducing an ambient sphere family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open FourPortSixEdgeZeroWindingData.OuterRawFaceData

variable {Phi : AmbientIsotopy}

/-- Exact reduced endpoint bookkeeping for one six-edge four-port move. -/
structure ReducedFourPortEndpointData
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    (Z : FourPortSixEdgeZeroWindingData G)
    (direction : FourPortBoundaryDirection)
    (pre post : ReducedTorusParityStage Phi) where
  unaffectedBoundary : Set (transportedTorus Phi)
  preBoundary_exact : pre.boundary = unaffectedBoundary ∪
    fourPortPreAffectedBoundary direction Z.rawEmbeddedCircle
  postBoundary_exact : post.boundary = unaffectedBoundary ∪
    fourPortPostAffectedBoundary direction Z.rawEmbeddedCircle

/-- A lift of the reduced label-change locus into the bounded faces selected in the plane. -/
structure ReducedFourPortFaceLensLiftData
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    (Z : FourPortSixEdgeZeroWindingData G)
    {D : Z.planePathSystem.RectangleRotationData}
    (O : Z.planePathSystem.OuterRawFaceData D)
    (pre post : ReducedTorusParityStage Phi) where
  lift : {x // (x ∈ pre.inside) ≠ (x ∈ post.inside)} → TorusCoveringPlane
  projects : ∀ x,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (lift x) = x
  mem_boundedFaces : ∀ x,
    lift x ∈
      closure (Z.planePathSystem.localRectangleJordanCircle D.rectangle).inside ∪
        closure (Z.planePathSystem.rawPlaneJordanCircle O.childOneIndex).inside ∪
          closure (Z.planePathSystem.rawPlaneJordanCircle O.childTwoIndex).inside

namespace ReducedFourPortFaceLensLiftData

variable {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
  {Z : FourPortSixEdgeZeroWindingData G}
  {D : Z.planePathSystem.RectangleRotationData}
  {O : Z.planePathSystem.OuterRawFaceData D}
  {pre post : ReducedTorusParityStage Phi}

/-- Every reduced label-change point lies in the selected projected graph disk. -/
theorem labelChange_subset_selectedDisk
    (L : ReducedFourPortFaceLensLiftData Z O pre post) :
    {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
      (Z.rawEmbeddedCircle O.outerIndex).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding O.outerIndex) := by
  intro x hx
  let xChange : {x // (x ∈ pre.inside) ≠ (x ∈ post.inside)} := ⟨x, hx⟩
  rw [← Z.image_rawPlaneJordanClosedDisk O.outerIndex]
  refine ⟨L.lift xChange, ?_, L.projects xChange⟩
  change L.lift xChange ∈
    closure (Z.planePathSystem.rawPlaneJordanCircle O.outerIndex).inside
  rw [O.outerClosed_eq]
  exact L.mem_boundedFaces xChange

end ReducedFourPortFaceLensLiftData

/-- Identification of the selected graph circle with one circle of a reduced endpoint family. -/
structure ReducedFourPortOuterCircleAttachment
    {ι : Type*} [Fintype ι]
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    (Z : FourPortSixEdgeZeroWindingData G)
    {D : Z.planePathSystem.RectangleRotationData}
    (O : Z.planePathSystem.OuterRawFaceData D)
    (F : FiniteDisjointTorusCircleFamily Phi ι) where
  circleIndex : ι
  outerCircle_eq : F.circle circleIndex = Z.rawEmbeddedCircle O.outerIndex

namespace ReducedFourPortOuterCircleAttachment

variable {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
  {Z : FourPortSixEdgeZeroWindingData G}
  {D : Z.planePathSystem.RectangleRotationData}
  {O : Z.planePathSystem.OuterRawFaceData D}
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : FiniteDisjointTorusCircleFamily Phi ι}
  {hzero : F.AllInessential}

private theorem projectedClosedJordanDisk_congr
    {C E : EmbeddedTorusIntersectionCircle Phi}
    (hCE : C = E)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hE : E.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      E.zeroWindingProjectedClosedJordanDisk hE := by
  subst E
  rfl

omit [DecidableEq ι] in
/-- The selected planar graph disk is exactly the chosen reduced-family torus disk. -/
theorem selectedDisk_eq_torusDiskRange
    (I : ReducedFourPortOuterCircleAttachment Z O F) :
    (Z.rawEmbeddedCircle O.outerIndex).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding O.outerIndex) =
      F.torusDiskRange hzero I.circleIndex := by
  rw [FiniteDisjointTorusCircleFamily.torusDiskRange,
    F.range_torusDiskMap_eq_projectedClosedJordanDisk]
  exact (projectedClosedJordanDisk_congr I.outerCircle_eq
    (hzero I.circleIndex) (Z.rawZeroWinding O.outerIndex)).symm

end ReducedFourPortOuterCircleAttachment

/-- The selected outer graph circle may belong to either reduced endpoint family. -/
def ReducedFourPortEndpointCircleSideAttachment
    {preIndex postIndex : Type*}
    [Fintype preIndex] [Fintype postIndex]
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    (Z : FourPortSixEdgeZeroWindingData G)
    {D : Z.planePathSystem.RectangleRotationData}
    (O : Z.planePathSystem.OuterRawFaceData D)
    (preFamily : FiniteDisjointTorusCircleFamily Phi preIndex)
    (postFamily : FiniteDisjointTorusCircleFamily Phi postIndex) :=
  ReducedFourPortOuterCircleAttachment Z O preFamily ⊕
    ReducedFourPortOuterCircleAttachment Z O postFamily

/-- The two vertical graph edges, as a transported-torus carrier. -/
def reducedFourPortParallelCarrier
    (G : FourPortSixEdgePathSystem (transportedTorus Phi)) :
    Set (transportedTorus Phi) :=
  Set.range G.left ∪ Set.range G.right

/-- The two horizontal graph edges, as a transported-torus carrier. -/
def reducedFourPortSurgeryCarrier
    (G : FourPortSixEdgePathSystem (transportedTorus Phi)) :
    Set (transportedTorus Phi) :=
  Set.range G.bottom ∪ Set.range G.top

namespace FourPortSixEdgeZeroWindingData.OuterRawFaceData

variable {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
  (Z : FourPortSixEdgeZeroWindingData G)
  {D : Z.planePathSystem.RectangleRotationData}
  (O : Z.planePathSystem.OuterRawFaceData D)

theorem parallelCarrier_subset_selectedDisk :
    reducedFourPortParallelCarrier G ⊆
      (Z.rawEmbeddedCircle O.outerIndex).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding O.outerIndex) := by
  intro x hx
  apply rawCircleCarrier_subset_selectedDisk Z O 0
  change x ∈ Set.range G.centralCircle
  rw [G.range_centralCircle, fourPortCentralUpperPath, Path.trans_range,
    Path.trans_range, Path.symm_range]
  rcases hx with hx | hx
  · exact Or.inl (Or.inl (Or.inl hx))
  · apply Or.inl
    apply Or.inr
    rwa [Path.symm_range]

theorem surgeryCarrier_subset_selectedDisk :
    reducedFourPortSurgeryCarrier G ⊆
      (Z.rawEmbeddedCircle O.outerIndex).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding O.outerIndex) := by
  intro x hx
  rcases hx with hx | hx
  · apply rawCircleCarrier_subset_selectedDisk Z O 1
    change x ∈ Set.range G.bottomCircle
    rw [G.range_bottomCircle]
    exact Or.inl hx
  · apply rawCircleCarrier_subset_selectedDisk Z O 2
    change x ∈ Set.range G.topCircle
    rw [G.range_topCircle]
    exact Or.inl hx

end FourPortSixEdgeZeroWindingData.OuterRawFaceData

/-- Local boundary-patch inclusions and the selected graph disk give the reduced cover. -/
noncomputable def reducedFourPortLocalPatchSideAlternative
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    {Z : FourPortSixEdgeZeroWindingData G}
    {D : Z.planePathSystem.RectangleRotationData}
    {O : Z.planePathSystem.OuterRawFaceData D}
    {pre post : ReducedTorusParityStage Phi}
    {preIndex postIndex : Type*}
    [Fintype preIndex] [DecidableEq preIndex]
    [Fintype postIndex] [DecidableEq postIndex]
    {preFamily : FiniteDisjointTorusCircleFamily Phi preIndex}
    {preZero : preFamily.AllInessential}
    {postFamily : FiniteDisjointTorusCircleFamily Phi postIndex}
    {postZero : postFamily.AllInessential}
    (preBoundary_eq : pre.boundary = preFamily.carrier)
    (postBoundary_eq : post.boundary = postFamily.carrier)
    (postBoundary_subset :
      post.boundary ⊆ pre.boundary ∪ reducedFourPortSurgeryCarrier G)
    (preBoundary_subset :
      pre.boundary ⊆ post.boundary ∪ reducedFourPortParallelCarrier G)
    (I : ReducedFourPortEndpointCircleSideAttachment Z O preFamily postFamily)
    (L : ReducedFourPortFaceLensLiftData Z O pre post) :
    ReducedCircleStageSideCover preFamily preZero postFamily postZero pre post := by
  rcases I with I | I
  · apply Sum.inl
    refine {
      diskIndex := I.circleIndex
      preBoundary_eq_carrier := preBoundary_eq
      postBoundary_subset := ?_
      labelChange_subset := ?_ }
    · apply postBoundary_subset.trans
      apply Set.union_subset_union Set.Subset.rfl
      have hpatch := surgeryCarrier_subset_selectedDisk Z O
      rw [I.selectedDisk_eq_torusDiskRange (hzero := preZero)] at hpatch
      exact hpatch
    · have hlens := L.labelChange_subset_selectedDisk
      rw [I.selectedDisk_eq_torusDiskRange (hzero := preZero)] at hlens
      exact hlens
  · apply Sum.inr
    refine {
      diskIndex := I.circleIndex
      preBoundary_eq_carrier := postBoundary_eq
      postBoundary_subset := ?_
      labelChange_subset := ?_ }
    · apply preBoundary_subset.trans
      apply Set.union_subset_union Set.Subset.rfl
      have hpatch := parallelCarrier_subset_selectedDisk Z O
      rw [I.selectedDisk_eq_torusDiskRange (hzero := postZero)] at hpatch
      exact hpatch
    · intro x hx
      have hlens := L.labelChange_subset_selectedDisk
      rw [I.selectedDisk_eq_torusDiskRange (hzero := postZero)] at hlens
      apply hlens
      exact fun h ↦ hx h.symm

/-- The six-edge outer disk gives the forward or reverse reduced stage-side cover. -/
noncomputable def reducedFourPortEndpointCircleSideAlternative
    {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
    {Z : FourPortSixEdgeZeroWindingData G}
    {D : Z.planePathSystem.RectangleRotationData}
    {O : Z.planePathSystem.OuterRawFaceData D}
    {direction : FourPortBoundaryDirection}
    {pre post : ReducedTorusParityStage Phi}
    (E : ReducedFourPortEndpointData Z direction pre post)
    {preIndex postIndex : Type*}
    [Fintype preIndex] [DecidableEq preIndex]
    [Fintype postIndex] [DecidableEq postIndex]
    {preFamily : FiniteDisjointTorusCircleFamily Phi preIndex}
    {preZero : preFamily.AllInessential}
    {postFamily : FiniteDisjointTorusCircleFamily Phi postIndex}
    {postZero : postFamily.AllInessential}
    (preBoundary_eq : pre.boundary = preFamily.carrier)
    (postBoundary_eq : post.boundary = postFamily.carrier)
    (I : ReducedFourPortEndpointCircleSideAttachment Z O preFamily postFamily)
    (L : ReducedFourPortFaceLensLiftData Z O pre post) :
    ReducedCircleStageSideCover preFamily preZero postFamily postZero pre post := by
  rcases I with I | I
  · apply Sum.inl
    refine {
      diskIndex := I.circleIndex
      preBoundary_eq_carrier := preBoundary_eq
      postBoundary_subset := ?_
      labelChange_subset := ?_ }
    · intro x hx
      rw [E.postBoundary_exact] at hx
      rcases hx with hxUnaffected | hxAffected
      · apply Or.inl
        rw [E.preBoundary_exact]
        exact Or.inl hxUnaffected
      · apply Or.inr
        rw [← I.selectedDisk_eq_torusDiskRange]
        have hxThree : x ∈ threeCircleBoundaryUnion Z.rawEmbeddedCircle := by
          rw [← preAffected_union_postAffected direction Z.rawEmbeddedCircle]
          exact Or.inr hxAffected
        rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion] at hxThree
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxThree
        exact rawCircleCarrier_subset_selectedDisk Z O i hi
    · intro x hx
      rw [← I.selectedDisk_eq_torusDiskRange]
      exact L.labelChange_subset_selectedDisk hx
  · apply Sum.inr
    refine {
      diskIndex := I.circleIndex
      preBoundary_eq_carrier := postBoundary_eq
      postBoundary_subset := ?_
      labelChange_subset := ?_ }
    · intro x hx
      rw [E.preBoundary_exact] at hx
      rcases hx with hxUnaffected | hxAffected
      · apply Or.inl
        rw [E.postBoundary_exact]
        exact Or.inl hxUnaffected
      · apply Or.inr
        rw [← I.selectedDisk_eq_torusDiskRange]
        have hxThree : x ∈ threeCircleBoundaryUnion Z.rawEmbeddedCircle := by
          rw [← preAffected_union_postAffected direction Z.rawEmbeddedCircle]
          exact Or.inl hxAffected
        rw [← iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion] at hxThree
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxThree
        exact rawCircleCarrier_subset_selectedDisk Z O i hi
    · intro x hx
      rw [← I.selectedDisk_eq_torusDiskRange]
      exact L.labelChange_subset_selectedDisk (by
        change (x ∈ post.inside) ≠ (x ∈ pre.inside) at hx
        exact fun h ↦ hx h.symm)

end Submission.Topology
