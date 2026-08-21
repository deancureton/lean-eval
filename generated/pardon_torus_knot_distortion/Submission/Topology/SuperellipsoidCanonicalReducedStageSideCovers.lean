import Submission.Topology.FourPortSixEdgeReducedDiskSide
import Submission.Topology.SuperellipsoidCanonicalReducedRegions

/-!
# Six-edge disk-side covers for the canonical reduced Boolean stages

The Boolean-region construction already proves the exact boundary and label-change inclusions
for one bit flip.  This module attaches the selected planar six-edge disk to the corresponding
finite reduced endpoint family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  (D : CanonicalEndpointRegularityData S)

/-- The public band-index type of the canonical reduced family. -/
abbrev CanonicalReducedBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

/-- The finite torus-circle family of one canonical Boolean reduced stage. -/
abbrev canonicalBooleanReducedCircleFamily
    (choice : D.CanonicalReducedBandIndex → Bool) :=
  FiniteDisjointTorusCircleFamily.ofSection
    (D.canonicalBooleanReducedStageEntry choice).circleSection

/-- The initial canonical Boolean stage is exactly the strict outer body on the torus. -/
theorem canonicalBooleanReducedStageData_initialInside_eq :
    (D.canonicalBooleanReducedStageData.toReducedTorusCircleStageGeometry
      |>.parityStage 0).inside =
      transportedTorusPart Phi (superellipsoidBody frame c S.outer.scale) := by
  rw [BooleanChoiceReducedTorusCircleStageData.toReducedTorusCircleStageGeometry_initialParityStage]
  change D.canonicalBooleanReducedRegion (fun _ ↦ false) = _
  rw [D.canonicalBooleanReducedRegion_false,
    superellipsoidReducedInside_eq_transportedTorusPart Phi frame c D.scale_pos]

namespace CanonicalReducedFlipSixEdge

variable {D : CanonicalEndpointRegularityData S}
  {choice : D.CanonicalReducedBandIndex → Bool} {b : D.CanonicalReducedBandIndex}
  {hb : choice b = false}
  {preZero : (D.canonicalBooleanReducedCircleFamily choice).AllInessential}
  {postZero : (D.canonicalBooleanReducedCircleFamily
    (Function.update choice b true)).AllInessential}
  {graph : FourPortSixEdgePathSystem (transportedTorus Phi)}
  {zeroWinding : FourPortSixEdgeZeroWindingData graph}
  {rotation : zeroWinding.planePathSystem.RectangleRotationData}
  {outer : zeroWinding.planePathSystem.OuterRawFaceData rotation}

/-- One six-edge attachment gives the exact reduced forward-or-reverse disk-side cover. -/
noncomputable def reducedCircleStageSideCover
    (parallelCarrier_eq : reducedFourPortParallelCarrier graph =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).parallelPatch)
    (surgeryCarrier_eq : reducedFourPortSurgeryCarrier graph =
      transportedTorusPart Phi
        (D.centralHeightFlowStraightenedChartFamily.chart b).surgeryPatch)
    (endpointAttachment : ReducedFourPortEndpointCircleSideAttachment zeroWinding outer
      (D.canonicalBooleanReducedCircleFamily choice)
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)))
    (lensLift : ReducedFourPortFaceLensLiftData zeroWinding outer
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry (Function.update choice b true)).parityStage) :
    ReducedCircleStageSideCover
      (D.canonicalBooleanReducedCircleFamily choice) preZero
      (D.canonicalBooleanReducedCircleFamily (Function.update choice b true)) postZero
      (D.canonicalBooleanReducedStageEntry choice).parityStage
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).parityStage := by
  apply reducedFourPortLocalPatchSideAlternative
    (preBoundary_eq := (FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
      (D.canonicalBooleanReducedStageEntry choice).circleSection).symm)
    (postBoundary_eq := (FiniteDisjointTorusCircleFamily.carrier_eq_transportedTorusPart
      (D.canonicalBooleanReducedStageEntry
        (Function.update choice b true)).circleSection).symm)
    (I := endpointAttachment) (L := lensLift)
  · intro x hx
    rcases D.canonicalBooleanReducedStageEntry_update_true_boundary_subset
        choice b hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      rwa [surgeryCarrier_eq]
  · intro x hx
    rcases D.canonicalBooleanReducedStageEntry_boundary_subset_update_true
        choice b hb hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      rwa [parallelCarrier_eq]

end CanonicalReducedFlipSixEdge
end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
