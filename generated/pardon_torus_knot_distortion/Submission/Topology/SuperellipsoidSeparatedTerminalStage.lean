import Submission.Topology.SuperellipsoidCanonicalFiniteStageIntegration
import Submission.Topology.FiniteSphereCircleSystem
import Submission.Topology.SuperellipsoidSeparatedTerminalSection
import Submission.Topology.SphereCircleProper

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

/-- Every lower terminal circle belongs to the lower child sphere, and every upper circle belongs
to the upper child sphere. -/
noncomputable def canonicalSeparatedTerminalComponentData :
    FiniteEmbeddedSphereCircleComponentData
      (separatedTruncationSphereFamily hR hlower hupper hε)
      (canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder hR hε).circle where
  component
    | Sum.inl _ => ⟨0, by simp [separatedTruncationSphereFamily]⟩
    | Sum.inr _ => ⟨1, by simp [separatedTruncationSphereFamily]⟩
  circle_mem := by
    rintro (i | j) x hx
    · change x ∈ Set.range
        ((canonicalLowerFiniteSection lowerOuterOrder lowerCutOrder hR).circle i).circle at hx
      have hsection := (canonicalLowerFiniteSection lowerOuterOrder lowerCutOrder hR)
        |>.circle_mem_section i hx
      change x ∈ ((separatedTruncationSphereFamily hR hlower hupper hε).sphere
        ⟨0, by simp [separatedTruncationSphereFamily]⟩).carrier
      simpa [lowerTruncatedSuperellipsoidTorusSection,
        separatedTruncationSphereFamily, separatedLowerSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hsection.2
    · change x ∈ Set.range
        ((canonicalUpperFiniteSection upperOuterOrder upperCutOrder hR).circle j).circle at hx
      have hsection := (canonicalUpperFiniteSection upperOuterOrder upperCutOrder hR)
        |>.circle_mem_section j hx
      change x ∈ ((separatedTruncationSphereFamily hR hlower hupper hε).sphere
        ⟨1, by simp [separatedTruncationSphereFamily]⟩).carrier
      simpa [upperTruncatedSuperellipsoidTorusSection,
        separatedTruncationSphereFamily, separatedUpperSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hsection.2

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

/-- Minimal sphere-chart data for the terminal circle family.  The full embedded filling disks are
derived by stereographic projection and planar Schoenflies. -/
structure CanonicalSeparatedTerminalPoleDecoration where
  poles : FiniteEmbeddedSphereCirclePoleData
    (separatedTruncationSphereFamily hR hlower hupper hε)
    (canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε).circle
  eventRegion : Set R3
  circle_mem_event : ∀ i t,
    (((canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε).circle i).windingLoop.curve t : R3) ∈
      eventRegion

namespace CanonicalSeparatedTerminalPoleDecoration

/-- Off-circle poles construct all terminal sphere-side disks automatically. -/
noncomputable def toDiskDecoration
    (D : CanonicalSeparatedTerminalPoleDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    CanonicalSeparatedTerminalDiskDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper where
  sphereDisk := D.poles.embeddedDisk
  sphereDisk_mem := D.poles.embeddedDisk_range_subset_family
  sphereDisk_boundary := D.poles.embeddedDisk_boundary
  eventRegion := D.eventRegion
  circle_mem_event := D.circle_mem_event

/-- The canonical separated terminal system derived from off-circle poles. -/
noncomputable def toFiniteSphereSurgeryIntersectionSystem
    (D : CanonicalSeparatedTerminalPoleDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    FiniteSphereSurgeryIntersectionSystem Phi
      (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder) :=
  D.toDiskDecoration.toFiniteSphereSurgeryIntersectionSystem

end CanonicalSeparatedTerminalPoleDecoration

/-- Honest terminal decoration reduced to the sphere component containing each circle.  Off-circle
poles and all Schoenflies filling disks are derived. -/
structure CanonicalSeparatedTerminalComponentDecoration where
  components : FiniteEmbeddedSphereCircleComponentData
    (separatedTruncationSphereFamily hR hlower hupper hε)
    (canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε).circle
  eventRegion : Set R3
  circle_mem_event : ∀ i t,
    (((canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε).circle i).windingLoop.curve t : R3) ∈
      eventRegion

namespace CanonicalSeparatedTerminalComponentDecoration

/-- Component assignments choose poles and hence construct the terminal pole decoration. -/
noncomputable def toPoleDecoration
    (D : CanonicalSeparatedTerminalComponentDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    CanonicalSeparatedTerminalPoleDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper where
  poles := D.components.toPoleData
  eventRegion := D.eventRegion
  circle_mem_event := D.circle_mem_event

/-- The separated terminal surgery system follows from component assignments alone. -/
noncomputable def toFiniteSphereSurgeryIntersectionSystem
    (D : CanonicalSeparatedTerminalComponentDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper) :
    FiniteSphereSurgeryIntersectionSystem Phi
      (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder) :=
  D.toPoleDecoration.toFiniteSphereSurgeryIntersectionSystem

end CanonicalSeparatedTerminalComponentDecoration

/-- Fully canonical terminal decoration.  Its event container is the exact terminal torus
section; quantitative charging can later transport these circles to the counted barriers. -/
noncomputable def canonicalSeparatedTerminalComponentDecoration :
    CanonicalSeparatedTerminalComponentDecoration lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper where
  components := canonicalSeparatedTerminalComponentData lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder hR hε hlower hupper
  eventRegion := separatedTerminalTorusSection
  circle_mem_event i t := by
    let terminalSection := canonicalSeparatedTerminalFiniteSection lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε
    apply terminalSection.circle_mem_section i
    refine ⟨Circle.exp t, ?_⟩
    exact (terminalSection.circle i).parametrization t

/-- The separated terminal sphere-surgery system needs no sphere-side disk assumptions. -/
noncomputable def canonicalSeparatedTerminalSphereSurgerySystem :
    FiniteSphereSurgeryIntersectionSystem Phi
      (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder) :=
  (canonicalSeparatedTerminalComponentDecoration lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder hR hε hlower hupper)
    |>.toFiniteSphereSurgeryIntersectionSystem

/-- Number of circles in the canonical separated terminal stage. -/
abbrev canonicalSeparatedTerminalCircleCount :=
  Fintype.card (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder)

/-- The canonical terminal system reindexed by `Fin` for finite stage sequences. -/
noncomputable def canonicalSeparatedTerminalFinSphereSurgerySystem :
    FiniteSphereSurgeryIntersectionSystem Phi
      (Fin (canonicalSeparatedTerminalCircleCount lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder)) :=
  (canonicalSeparatedTerminalSphereSurgerySystem lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder hR hε hlower hupper).reindex
      (Fintype.equivFin (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder)).symm

@[simp] theorem canonicalSeparatedTerminalFinSphereSurgerySystem_sphereFamily :
    (canonicalSeparatedTerminalFinSphereSurgerySystem lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper).sphereFamily =
      (canonicalSeparatedTerminalParityStage (Phi := Phi) hR hε hlower hupper).sphereFamily :=
  rfl

@[simp] theorem canonicalSeparatedTerminalFinSphereSurgerySystem_insideCell :
    (canonicalSeparatedTerminalFinSphereSurgerySystem lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper).insideCell =
      (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).lowerInside ∪
        (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).upperInside :=
  rfl

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
