import Submission.Topology.SuperellipsoidCanonicalFiniteStageIntegration
import Submission.Topology.SuperellipsoidSeparatedTerminalSection

/-!
# Honest separated terminal regular stage

The separated neck-pinch rounding already supplies the two embedded spheres, their open parity
cells, and the exact frontier.  The canonical sections at the two shifted cut heights supply the
complete circle family.  Only sphere-side filling disks and the stage-local event container remain
as geometric decoration before this becomes a finite sphere-surgery intersection system.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε : ℝ}
  {lowerOuterIndex lowerCutIndex upperOuterIndex upperCutIndex : Type u}
  [Fintype lowerOuterIndex] [Fintype lowerCutIndex]
  [Fintype upperOuterIndex] [Fintype upperCutIndex]
  {lowerGraph : FiniteSuperellipsoidBarrierGraph Phi frame c R (d - ε)
    lowerOuterIndex lowerCutIndex}
  {upperGraph : FiniteSuperellipsoidBarrierGraph Phi frame c R (d + ε)
    upperOuterIndex upperCutIndex}
  (lowerOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily lowerGraph)
  (lowerCutOrder : CutCircleTransverseCyclicOrderFamily lowerGraph)
  (upperOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily upperGraph)
  (upperCutOrder : CutCircleTransverseCyclicOrderFamily upperGraph)
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d - ε))]
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d + ε))]

variable (hR : 0 < R) (hε : 0 < ε)
  (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
    x.ofLp (frame 2) < d - ε)
  (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
    d + ε < x.ofLp (frame 2))

/-- The canonical separated rounding datum used by the terminal stage. -/
noncomputable def canonicalSeparatedTerminalRoundingData :
    SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR :=
  separatedTruncationGlobalNeckPinchRoundingData hR hε hlower hupper

/-- The honest parity stage bounded by the two separated convex truncations. -/
noncomputable def canonicalSeparatedTerminalParityStage :
    RegularSphereFamilyParityStage Phi :=
  (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).postStage

/-- The two transported-torus terminal cells of the separated parity stage. -/
noncomputable def canonicalSeparatedTerminalTwoComponentStage :
    TerminalTwoComponentSphereStage
      (canonicalSeparatedTerminalParityStage (Phi := Phi) hR hε hlower hupper) :=
  (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).terminalStage

/-- The remaining disk and event decoration of the canonical separated terminal section. -/
structure CanonicalSeparatedTerminalDiskDecoration where
  sphereDisk :
    SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder → BoundaryParametrizedEmbeddedDiskInR3
  sphereDisk_mem : ∀ i, Set.range (sphereDisk i).disk ⊆
    (separatedTruncationSphereFamily hR hlower hupper hε).carrier
  sphereDisk_boundary : ∀ i t,
    (sphereDisk i).disk (unitDiskBoundary t) =
      ((canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder hR hε).circle i).windingLoop.curve t
  eventRegion : Set R3
  circle_mem_event : ∀ i t,
    (((canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε).circle i).windingLoop.curve t : R3) ∈
      eventRegion

namespace CanonicalSeparatedTerminalDiskDecoration

/-- The separated spheres and canonical circles give the exact regular-stage geometry. -/
noncomputable def toFiniteCircleSectionRegularStageGeometry
    (D : CanonicalSeparatedTerminalDiskDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    FiniteCircleSectionRegularStageGeometry
      (canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder hR hε) where
  sphereFamily := separatedTruncationSphereFamily hR hlower hupper hε
  insideCell := separatedLowerSuperellipsoidInside frame c R d ε ∪
    separatedUpperSuperellipsoidInside frame c R d ε
  sphereFamily_is_boundary :=
    separatedTruncationSphereFamily_is_boundary hR hlower hupper hε
  intersection_eq :=
    (separatedTerminalTorusSection_eq_sphereCarrier_inter
      (Phi := Phi) (frame := frame) (c := c) (R := R) (d := d) (ε := ε)
      hR hlower hupper hε).symm
  sphereDisk := D.sphereDisk
  sphereDisk_mem := D.sphereDisk_mem
  sphereDisk_boundary := D.sphereDisk_boundary
  eventRegion := D.eventRegion
  circle_mem_event := D.circle_mem_event

/-- The final decorated separated stage is an honest finite sphere-surgery system. -/
noncomputable def toFiniteSphereSurgeryIntersectionSystem
    (D : CanonicalSeparatedTerminalDiskDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    FiniteSphereSurgeryIntersectionSystem Phi
      (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder) :=
  D.toFiniteCircleSectionRegularStageGeometry
    |>.toFiniteSphereSurgeryIntersectionSystem

end CanonicalSeparatedTerminalDiskDecoration
end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
