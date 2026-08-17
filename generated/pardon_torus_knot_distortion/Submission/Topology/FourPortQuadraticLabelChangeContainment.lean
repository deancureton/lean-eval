import Submission.Topology.FourPortSixEdgeCanonicalDiskSide
import Submission.Topology.FourPortSixEdgeQuadraticDisk

/-!
# Constructing the four-port rectangle label-change containment

For an actual quadratic endpoint move, each changed-label point has a coordinate in the
quadratic support disk.  If the two endpoint insides consistently select either the negative
graph side or the positive graph side, the elementary polynomial inequality puts that coordinate
in the central closed rectangle.  The lifted-chart disk theorem then supplies the exact bounded
face required by the canonical disk-side adapter.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData EmbeddedTorusIntersectionCircle

/-- The two consistent choices of side for the endpoint graph equations. -/
inductive FourPortInsideOrientation where
  | negative
  | positive
  deriving DecidableEq

/-- The strict graph-side predicate selected by an orientation. -/
def fourPortInsideLabel : FourPortInsideOrientation → ℝ → Prop
  | .negative, value => value < 0
  | .positive, value => 0 < value

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

/-- Exact chart-level data for the endpoint labels of the quadratic move.

This asks for coordinates only at points where the labels actually differ.  It does not assume
that the whole ambient band is a chart image, nor does it assume the desired rectangular or
canonical-disk containment. -/
structure QuadraticEndpointLabelData where
  orientation : FourPortInsideOrientation
  coordinate : regularStageLabelChangeLocus pre post → FourPortQuadraticDisk
  strip_coordinate : ∀ x,
    (T.strip (coordinate x) : transportedTorus Phi) = x.1
  pre_inside_iff : ∀ x, x.1 ∈ pre.inside ↔
    fourPortInsideLabel orientation (fourPortVerticalHeight (coordinate x))
  post_inside_iff : ∀ x, x.1 ∈ post.inside ↔
    fourPortInsideLabel orientation (fourPortHorizontalHeight (coordinate x))

namespace QuadraticEndpointLabelData

variable {T : F.LiftedGlobalBandTubularChartData b}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {C : FourPortRawCircleData raw}
  {P : FourPortRawSixEdgeBandPresentation C}

private theorem coordinate_mem_closedRectangle
    (D : QuadraticEndpointLabelData (pre := pre) (post := post) T)
    (x : regularStageLabelChangeLocus pre post) :
    (D.coordinate x : FourPortPlane) ∈ fourPortClosedRectangle := by
  have hlabel :
      fourPortInsideLabel D.orientation
          (fourPortVerticalHeight (D.coordinate x)) ≠
        fourPortInsideLabel D.orientation
          (fourPortHorizontalHeight (D.coordinate x)) := by
    intro heq
    apply x.property
    apply propext
    rw [D.pre_inside_iff, D.post_inside_iff, heq]
  cases hO : D.orientation with
  | negative =>
      exact mem_fourPortClosedRectangle_of_negative_labels_ne
        (D.coordinate x).property <| by
          simpa only [fourPortInsideLabel, hO] using hlabel
  | positive =>
      exact mem_fourPortClosedRectangle_of_positive_labels_ne
        (D.coordinate x).property <| by
          simpa only [fourPortInsideLabel, hO] using hlabel

/-- Consistent quadratic endpoint labels construct the exact bounded-face containment consumed
by the canonical disk-side theorem. -/
theorem toRectangleLabelChangeContainmentData
    (D : QuadraticEndpointLabelData (pre := pre) (post := post) T) :
    RectangleLabelChangeContainmentData T P where
  labelChange_subset_projection_rectangleClosed := by
    intro x hx
    let xChange : regularStageLabelChangeLocus pre post := ⟨x, hx⟩
    let u : FourPortPlane := D.coordinate xChange
    let y : TorusCoveringPlane := T.liftedStrip u
    have huRectangle : u ∈ fourPortClosedRectangle := by
      exact D.coordinate_mem_closedRectangle xChange
    have hyRectangle : y ∈ chartClosedRectangle T := by
      exact ⟨u, huRectangle, rfl⟩
    have hface := P.projection_chartClosedRectangle_subset_planeRectangleClosedFace T
      ⟨y, hyRectangle, rfl⟩
    have hprojection : torusCoveringProjectionToTorus Phi y = x := by
      rw [show y = T.liftedStrip u from rfl, T.projection_liftedStrip]
      exact D.strip_coordinate xChange
    rw [hprojection] at hface
    have hrectangle :
        P.planePathSystem.localRectangleData =
          (P.canonicalRectangleRotationData T).rectangle :=
      Subsingleton.elim _ _
    rwa [hrectangle] at hface

end QuadraticEndpointLabelData

/-- The former rectangle-containment premise of the canonical endpoint alternative is discharged
by the explicit quadratic endpoint-label data. -/
noncomputable def canonicalEndpointCircleSideAlternative_of_quadraticLabels
    {preCircleCount postCircleCount : ℕ}
    {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
    {preZero : preSystem.AllInessential}
    {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}
    {postZero : postSystem.AllInessential}
    (I : CanonicalEndpointCircleSideAttachment T P preSystem postSystem)
    (D : QuadraticEndpointLabelData (pre := pre) (post := post) T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre :=
  P.canonicalEndpointCircleSideAlternative T I
    D.toRectangleLabelChangeContainmentData

end FourPortRawSixEdgeBandPresentation
end Submission.Topology
