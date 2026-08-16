import Submission.Topology.OrientedCoordinateRegularBand

/-!
# The central circle of a regular transported-torus band

The center height of `OrientedCoordinateRegularBandData` is already a regular value.  The
complete regular-level classification therefore supplies a circle parametrization for every
connected component of that central descended level.  This file transports each classified
circle to the embedded torus and records its exact ambient range.

No circle-classification premise is added to the regular-band data.  The small auxiliary
`RegularCoordinateTorusLevel` below exists only to reuse the canonical
`FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent` constructor.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

namespace OrientedCoordinateRegularBandData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- The center of a regular band is itself a regular value. -/
theorem central_isRegularValue
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    IsRegularValue (orientedCoordinateLift Phi frame 2) d := by
  apply B.isRegularValue_of_mem_closedBand
  rw [sub_self, abs_zero]
  linarith [B.ε_pos]

/-- A quotient-level package at the central height.  Its interval is bookkeeping only; all
regularity comes directly from the band data. -/
def centralRegularCoordinateTorusLevel
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    RegularCoordinateTorusLevel Phi frame (d - 1) (d + 1) := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    orientedCoordinateLift_contDiff Phi frame 2
  let selection : CompactRegularLevelSelection f (d - 1) (d + 1) := {
    level := d
    level_mem := by constructor <;> linarith
    isCompact := isCompact_fundamentalLevelSet hf.continuous d
    localCharts := regularValue_has_local_charts hf B.central_isRegularValue
  }
  exact {
    selection := selection
    quotientLocallyLineModeled :=
      isLocallyLineModeled_coordinateTorusLevel_of_regularValue
        Phi frame B.central_isRegularValue
  }

/-- The complete ODE classification of the center level, derived without any extra premise. -/
def centralComponentCircleClassification
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    ComponentCircleClassification (coordinateTorusLevelSet Phi frame d) :=
  componentCircleClassification_regularCoordinateLevel
    Phi frame B.central_isRegularValue

/-- Transport one classified central-level component to an embedded ambient torus circle. -/
def embeddedCentralCircleOfClassification
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame d))
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) :
    EmbeddedTorusIntersectionCircle Phi :=
  FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
    B.centralRegularCoordinateTorusLevel C c

/-- The transported circle has exactly the ambient image of the selected descended component. -/
theorem range_embeddedCentralCircleOfClassification
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame d))
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) :
    Set.range (B.embeddedCentralCircleOfClassification C c).circle =
      (fun z : coordinateTorusLevelSet Phi frame d ↦
        transportedTorusMap Phi z) '' componentPiece c := by
  exact FiniteCoordinatePlaneTorusCircleFamily.component_circle_range
    B.centralRegularCoordinateTorusLevel C c

/-- The canonical embedded circle assigned to a central-level component. -/
def embeddedCentralCircle
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) :
    EmbeddedTorusIntersectionCircle Phi :=
  B.embeddedCentralCircleOfClassification
    B.centralComponentCircleClassification c

/-- Exact range of the canonical central component circle. -/
theorem range_embeddedCentralCircle
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) :
    Set.range (B.embeddedCentralCircle c).circle =
      (fun z : coordinateTorusLevelSet Phi frame d ↦
        transportedTorusMap Phi z) '' componentPiece c :=
  B.range_embeddedCentralCircleOfClassification
    B.centralComponentCircleClassification c

/-- Descended central-level point corresponding to a point of the transported torus. -/
def centralLevelPoint
    (_B : OrientedCoordinateRegularBandData Phi frame d)
    (x : transportedTorus Phi)
    (hx : torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm x) = d) :
    coordinateTorusLevelSet Phi frame d := by
  refine ⟨(transportedTorusHomeomorph Phi).symm x, ?_⟩
  exact hx

/-- Canonical central component circle passing through a specified central-level point. -/
def embeddedCentralCircleThrough
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (x : transportedTorus Phi)
    (hx : torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm x) = d) :
    EmbeddedTorusIntersectionCircle Phi :=
  B.embeddedCentralCircle (ConnectedComponents.mk (B.centralLevelPoint x hx))

/-- The specified central-level point lies in its canonical component circle. -/
theorem mem_range_embeddedCentralCircleThrough
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (x : transportedTorus Phi)
    (hx : torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm x) = d) :
    (x : R3) ∈ Set.range (B.embeddedCentralCircleThrough x hx).circle := by
  rw [embeddedCentralCircleThrough, B.range_embeddedCentralCircle]
  refine ⟨B.centralLevelPoint x hx, ?_, ?_⟩
  · change ConnectedComponents.mk (B.centralLevelPoint x hx) =
      ConnectedComponents.mk (B.centralLevelPoint x hx)
    rfl
  · change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm x) = x
    exact congrArg Subtype.val
      ((transportedTorusHomeomorph Phi).apply_symm_apply x)

end OrientedCoordinateRegularBandData

end Submission.Topology
