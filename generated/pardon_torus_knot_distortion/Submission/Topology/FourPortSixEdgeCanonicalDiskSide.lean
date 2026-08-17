import Submission.Topology.FourPortSixEdgeDiskSide
import Submission.Topology.FourPortSixEdgeLiftedBandContainment

/-!
# Canonical disk side of a chart-aligned six-edge move

The retained covering sheet determines the bounded side of the local four-port rectangle.  The
six-edge face theorem then chooses the outer raw circle without an orientation premise.  This
module packages that chain and isolates the remaining local geometry as one exact statement:
the parity-change locus lifts into the closed rectangular face.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData EmbeddedTorusIntersectionCircle

namespace FourPortRawSixEdgeBandPresentation

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : G.CutCircleTransverseCyclicOrderFamily}
  {b : Fin F.toPairedSeamEnumeration.bandCount}
  (T : F.LiftedGlobalBandTubularChartData b)
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {C : FourPortRawCircleData raw}
  (P : FourPortRawSixEdgeBandPresentation C)

/-- The retained covering sheet canonically orients the lifted local rectangle. -/
theorem canonicalRectangleRotationData :
    P.planePathSystem.RectangleRotationData :=
  (P.rectangleBandContainmentData T).rectangleRotationData

/-- The resulting outer face is selected by the planar six-edge theorem. -/
noncomputable def canonicalOuterRawFaceData :
    P.planePathSystem.OuterRawFaceData (P.canonicalRectangleRotationData T) :=
  P.planePathSystem.selectedOuterRawFaceData (P.canonicalRectangleRotationData T)

/-- Exact local geometry still needed after the chart and six-edge topology are constructed.

Every point where the endpoint inside labels differ has a covering-plane lift in the closed
bounded face of the local rectangle.  Unlike a conclusion about a canonical disk, this is a
pointwise statement about the explicit quadratic move. -/
structure RectangleLabelChangeContainmentData where
  labelChange_subset_projection_rectangleClosed :
    regularStageLabelChangeLocus pre post ⊆
      torusCoveringProjectionToTorus Phi ''
        closure
          (P.planePathSystem.localRectangleJordanCircle
            (P.canonicalRectangleRotationData T).rectangle).inside

namespace RectangleLabelChangeContainmentData

variable {T : F.LiftedGlobalBandTubularChartData b}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {C : FourPortRawCircleData raw}
  {P : FourPortRawSixEdgeBandPresentation C}

/-- Rectangle containment supplies the bounded-face lift used by the disk-side theorem. -/
noncomputable def toSelectedFaceLensLiftData
    (L : RectangleLabelChangeContainmentData T P) :
    FourPortSixEdgeFaceLensLiftData P.toFourPortRawSixEdgePresentation
      (P.canonicalOuterRawFaceData T) where
  lift x := Classical.choose
    (L.labelChange_subset_projection_rectangleClosed x.property)
  projects x := (Classical.choose_spec
    (L.labelChange_subset_projection_rectangleClosed x.property)).2
  mem_boundedFaces x := Or.inl <| Or.inl <|
    (Classical.choose_spec
      (L.labelChange_subset_projection_rectangleClosed x.property)).1

end RectangleLabelChangeContainmentData

/-- Endpoint attachment for the outer face canonically selected by the retained band chart. -/
abbrev CanonicalEndpointCircleSideAttachment
    {preCircleCount postCircleCount : ℕ}
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) :=
  FourPortSixEdgeEndpointCircleSideAttachment
    P.toFourPortRawSixEdgePresentation (P.canonicalOuterRawFaceData T)
      preSystem postSystem

/-- The chart-aligned six-edge move has a forward or reverse disk-side cover once its explicit
label-change lens and selected endpoint circle are attached. -/
noncomputable def canonicalEndpointCircleSideAlternative
    {preCircleCount postCircleCount : ℕ}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : CanonicalEndpointCircleSideAttachment T P preSystem postSystem)
    (L : RectangleLabelChangeContainmentData T P) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre :=
  fourPortSixEdgeEndpointCircleSideAlternative I L.toSelectedFaceLensLiftData

end FourPortRawSixEdgeBandPresentation
end Submission.Topology
