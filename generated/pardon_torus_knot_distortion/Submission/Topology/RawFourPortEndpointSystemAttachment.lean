import Submission.Topology.RawFourPortOuterThetaSelection

/-!
# Attaching raw four-port circles to audited endpoint systems

The planar theta theorem selects the outer cycle without knowing whether that cycle belongs to
the pre or post endpoint.  This file performs the remaining finite bookkeeping.  It records the
ordinary audited-system index of each raw circle on its actual endpoint, then constructs the
forward-or-reverse outer-circle attachment selected by the planar theorem.

No maximal disk is chosen here.  Canonical laminar maximality in `RawFourPortThetaDiskSide`
enlarges the selected ordinary circle disk automatically.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

/-- Whether the raw circle occurs at the pre endpoint of the split or merge. -/
def fourPortCircleBelongsToPre
    (direction : FourPortBoundaryDirection) (i : Fin 3) : Prop :=
  match direction with
  | .split => i = 0
  | .merge => i = 1 ∨ i = 2

/-- Whether the raw circle occurs at the post endpoint of the split or merge. -/
def fourPortCircleBelongsToPost
    (direction : FourPortBoundaryDirection) (i : Fin 3) : Prop :=
  match direction with
  | .split => i = 1 ∨ i = 2
  | .merge => i = 0

/-- Every raw four-port circle occurs at one of the two endpoints. -/
theorem fourPortCircleBelongsToPre_or_post
    (direction : FourPortBoundaryDirection) (i : Fin 3) :
    fourPortCircleBelongsToPre direction i ∨
      fourPortCircleBelongsToPost direction i := by
  cases direction <;> fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)

/-- Ordinary circle indices identifying every raw circle with the endpoint system on which it
occurs.  The split/merge direction decides which of the two systems owns each index. -/
structure RawFourPortEndpointSystemCircleData
    {preCircleCount postCircleCount : ℕ}
    (R : FourPortRawCircleData raw)
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) where
  preIndex : ∀ i, fourPortCircleBelongsToPre R.direction i → Fin preCircleCount
  preCircle_eq : ∀ i h,
    preSystem.circle (preIndex i h) = R.circle i
  postIndex : ∀ i, fourPortCircleBelongsToPost R.direction i → Fin postCircleCount
  postCircle_eq : ∀ i h,
    postSystem.circle (postIndex i h) = R.circle i

namespace RawFourPortEndpointSystemCircleData

variable {preCircleCount postCircleCount : ℕ}
  {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
  {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}

/-- Whichever raw cycle the planar theorem selects, its ordinary endpoint-system circle gives
the required endpoint attachment. -/
def endpointCircleSideAttachment
    (D : RawFourPortEndpointSystemCircleData R preSystem postSystem)
    (T : RawFourPortOuterPlaneThetaData R) :
    RawFourPortEndpointCircleSideAttachment T preSystem postSystem := by
  classical
  by_cases hpre : fourPortCircleBelongsToPre R.direction T.outerIndex
  · exact Sum.inl {
      circleIndex := D.preIndex T.outerIndex hpre
      outerCircle_eq := D.preCircle_eq T.outerIndex hpre }
  · have hpost : fourPortCircleBelongsToPost R.direction T.outerIndex := by
      rcases fourPortCircleBelongsToPre_or_post R.direction T.outerIndex with h | h
      · exact False.elim (hpre h)
      · exact h
    exact Sum.inr {
      circleIndex := D.postIndex T.outerIndex hpost
      outerCircle_eq := D.postCircle_eq T.outerIndex hpost }

/-- If the bounded-face lift is available for every legitimately selected outer presentation,
the generic planar selection and endpoint ownership produce the exact local sided alternative.

The universal quantifier is only over inhabitants of `RawFourPortOuterPlaneThetaData R`, hence
over presentations already certified to be the unbounded theta face. -/
noncomputable def planarThetaStageSideAlternative
    {preZero : preSystem.AllInessential}
    {postZero : postSystem.AllInessential}
    (D : RawFourPortEndpointSystemCircleData R preSystem postSystem)
    (P : RawFourPortPlanarThetaPresentation R)
    (lens : ∀ T : RawFourPortOuterPlaneThetaData R, RawFourPortLensFaceLiftData T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre := by
  let T := Classical.choice P.nonempty_outerPlaneThetaData
  exact rawFourPortEndpointCircleSideAlternative
    (D.endpointCircleSideAttachment T) (lens T)

end RawFourPortEndpointSystemCircleData
end Submission.Topology
