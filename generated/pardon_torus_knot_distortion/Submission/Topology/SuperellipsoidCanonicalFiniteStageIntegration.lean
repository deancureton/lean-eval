import Submission.Topology.DiskLocalizedParityTransition
import Submission.Topology.SuperellipsoidCanonicalTruncatedSphereSection
import Submission.Topology.SuperellipsoidFiniteStageTransportCharging

/-!
# Canonical endpoint sections and finite-stage transport integration

This module records the purely logical assembly which remains after the geometric moving-sphere
construction has produced its honest regular stages.  In the all-inessential branch, a
`FiniteStageSideDiskCoverData` at every transition is exactly enough to build the heterogeneous
parity sequence.  Thus the final transport-resolution record need not assume an unstructured
`inessentialResolution` field.

The canonical truncated-sphere circle sections are retained separately.  At the literal common
cut height the two truncated spheres share their cutting disk, so they cannot themselves be the
terminal regular two-sphere family.  A geometric integration must use separated or rounded
terminal spheres and identify their circle systems with canonical sections at the corresponding
two regular heights.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- The remaining geometric decoration needed to turn an already classified finite circle
section into one honest regular sphere-surgery stage.  Circle decomposition and intersection
exactness come from the section; only the ambient sphere, its parity side, sphere-side filling
disks, and a stage-local event container remain fields.

The event container here is deliberately not asserted to lie in the selected quantitative
outer/cut event region.  In particular, the cutting faces of separated terminal spheres occur
at two shifted heights and are not events at the original selected cut height.  Quantitative
charging in the transport route below therefore comes from `SmoothedLoopChargingTransport`,
not from `eventRegion`. -/
structure FiniteCircleSectionRegularStageGeometry
    {ambientSection : Set R3} {ι : Type*} [Fintype ι]
    (circleSection : FiniteEmbeddedTorusCircleSection Phi ambientSection ι) where
  sphereFamily : FiniteEmbeddedTopologicalSphereFamilyInR3
  insideCell : Set R3
  sphereFamily_is_boundary : sphereFamily.carrier = frontier insideCell
  intersection_eq : sphereFamily.carrier ∩ transportedTorus Phi = ambientSection
  sphereDisk : ι → BoundaryParametrizedEmbeddedDiskInR3
  sphereDisk_mem : ∀ i, Set.range (sphereDisk i).disk ⊆ sphereFamily.carrier
  sphereDisk_boundary : ∀ i t,
    (sphereDisk i).disk (unitDiskBoundary t) =
      (circleSection.circle i).windingLoop.curve t
  eventRegion : Set R3
  circle_mem_event : ∀ i t,
    ((circleSection.circle i).windingLoop.curve t : R3) ∈ eventRegion

namespace FiniteCircleSectionRegularStageGeometry

variable {ambientSection : Set R3} {ι : Type*} [Fintype ι]
  {circleSection : FiniteEmbeddedTorusCircleSection Phi ambientSection ι}

/-- A finite classified section with its honest sphere-side decoration is exactly a regular
sphere-surgery intersection system. -/
def toFiniteSphereSurgeryIntersectionSystem
    (D : FiniteCircleSectionRegularStageGeometry circleSection) :
    FiniteSphereSurgeryIntersectionSystem Phi ι where
  sphereFamily := D.sphereFamily
  insideCell := D.insideCell
  sphereFamily_is_boundary := D.sphereFamily_is_boundary
  circle := circleSection.circle
  pairwise_disjoint := circleSection.pairwise_disjoint
  intersection_exact := D.intersection_eq.trans circleSection.section_exact
  sphereDisk := D.sphereDisk
  sphereDisk_mem := D.sphereDisk_mem
  sphereDisk_boundary := D.sphereDisk_boundary
  eventRegion := D.eventRegion
  circle_mem_event := D.circle_mem_event

end FiniteCircleSectionRegularStageGeometry

namespace PairedBandMovingSphereCollarData.FiniteRegularSphereSurgeryStageSequence

/-- Stage-sided disk covers and an honest terminal two-sphere stage give the complete
all-inessential finite-band resolution. -/
def allInessentialResolutionOfStageSideDiskCovers
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : F.AllInessential)
    (D : FiniteStageSideDiskCoverData F hzero)
    (terminal : TerminalTwoComponentSphereStage (F.parityStage F.length))
    (lower upper : Set (transportedTorus Phi))
    (hlower : terminal.lower = lower)
    (hupper : terminal.upper = upper) :
    AllInessentialFiniteBandResolution F lower upper := by
  let paritySequence := D.toFiniteInessentialParityTransitionSequence
  exact {
    paritySequence := paritySequence
    length_eq := rfl
    stage_eq := fun _ _ ↦ rfl
    terminal := terminal
    terminal_lower_eq := hlower
    terminal_upper_eq := hupper
  }

end PairedBandMovingSphereCollarData.FiniteRegularSphereSurgeryStageSequence

namespace FiniteSuperellipsoidBarrierGraph.TruncatedSphereAlternatingCycles

universe u

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
  (cutOrder : CutCircleTransverseCyclicOrderFamily G)
  [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

/-- The precise remaining regular-stage decoration of the unconditional canonical lower
truncated-sphere section. -/
abbrev CanonicalLowerRegularStageGeometry (hR : 0 < R) :=
  FiniteCircleSectionRegularStageGeometry
    (canonicalLowerFiniteSection outerOrder cutOrder hR)

/-- The precise remaining regular-stage decoration of the unconditional canonical upper
truncated-sphere section. -/
abbrev CanonicalUpperRegularStageGeometry (hR : 0 < R) :=
  FiniteCircleSectionRegularStageGeometry
    (canonicalUpperFiniteSection outerOrder cutOrder hR)

end FiniteSuperellipsoidBarrierGraph.TruncatedSphereAlternatingCycles

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Torus

/-- The finite-stage transport inputs after the geometric construction has supplied honest
regular stages.  Compared with `SuperellipsoidFiniteStageTransportResolutionData`, the
all-inessential branch is reduced to a sided disk cover for each successive four-port move and
an explicitly supplied terminal two-component cell decomposition.

The `stageSequence` itself is intentionally not synthesized here.  It must come from the
coherent-theta decomposition, paired-band collars, `RegularStageDecoration`s, and sphere-side
disk fillings; those are geometric constructions, not logical consequences of the endpoint
circle sections.  Likewise, this record does not identify the terminal stage with the separated
two-sphere family: that identification must be supplied by the global neck-pinch rounding
construction.  The canonical lower and upper sections above live at one literal cut level and
cannot by themselves furnish a pairwise-disjoint terminal sphere family. -/
structure SuperellipsoidFiniteStageSideCoverTransportData
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness) where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialInside_eq :
    (stageSequence.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale)
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  essentialSurgery : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData (stageSequence.system k) i)
  chargingTransport : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi
          ((stageSequence.system k).circle i).windingLoop.curve)
        ((stageSequence.system k).circle i).windingLoop.lift.first.winding
        ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  terminal : TerminalTwoComponentSphereStage
    (stageSequence.parityStage stageSequence.length)
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper
  stageSideCovers : ∀ hzero : stageSequence.AllInessential,
    Nonempty (FiniteStageSideDiskCoverData stageSequence hzero)

namespace SuperellipsoidFiniteStageSideCoverTransportData

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Stage-sided four-port disk covers construct the exact transport-resolution record consumed
by the resolved-double-bubble theorem. -/
def toFiniteStageTransportResolutionData
    (D : SuperellipsoidFiniteStageSideCoverTransportData
      p q K Phi frame c r WB selection) :
    SuperellipsoidFiniteStageTransportResolutionData
      p q K Phi frame c r WB selection where
  stageSequence := D.stageSequence
  lower := D.lower
  upper := D.upper
  initialInside_eq := D.initialInside_eq
  lower_subset := D.lower_subset
  upper_subset := D.upper_subset
  essentialSurgery := D.essentialSurgery
  chargingTransport := D.chargingTransport
  inessentialResolution := by
    intro hzero
    obtain ⟨covers⟩ := D.stageSideCovers hzero
    exact ⟨D.stageSequence.allInessentialResolutionOfStageSideDiskCovers hzero covers
      D.terminal D.lower D.upper D.terminal_lower_eq D.terminal_upper_eq⟩

end SuperellipsoidFiniteStageSideCoverTransportData

end Submission.PardonDistortion
