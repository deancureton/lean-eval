import Submission.Topology.FiniteRegularSphereSurgeryStageEntry
import Submission.Topology.RegularStageSphereDisk
import Submission.Topology.SuperellipsoidInitialSphereStage
import Submission.Topology.SuperellipsoidSeparatedTerminalStage

/-!
# Canonical entries for the superellipsoid finite-stage family

This module places the three kinds of honest regular systems used by the construction into the
uniform finite-entry interface: the initial outer sphere, each relative moving-sphere stage, and
the final pair of separated truncated spheres.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

namespace FiniteSuperellipsoidOuterTorusSmoothCircleFamily

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  (F : FiniteSuperellipsoidOuterTorusSmoothCircleFamily Phi frame c R d)
  [Fintype F.index]

/-- The canonical initial outer sphere is a finite regular-stage entry. -/
def initialOuterFiniteStageEntry (hR : 0 < R) :
    FiniteRegularSphereSurgeryStageEntry Phi where
  circleCount := Fintype.card F.index
  system := F.initialOuterFinSphereSurgerySystem hR
  isOpen_insideCell := by
    change IsOpen (interior (closedSuperellipsoidBody frame c R))
    exact isOpen_interior

@[simp] theorem initialOuterFiniteStageEntry_parityStage (hR : 0 < R) :
    (F.initialOuterFiniteStageEntry hR).parityStage =
      initialOuterSuperellipsoidParityStage Phi frame c hR :=
  rfl

end FiniteSuperellipsoidOuterTorusSmoothCircleFamily

namespace PairedBandMovingSphereCollarData.RegularStageBasicDecoration

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge ι : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge] [Fintype ι]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}
  {choice : Fin P.bandCount → Bool}
  {D : PairedBandMovingSphereCollarData C choice}

/-- An honest moving-sphere stage with an open inside cell is a finite regular-stage entry. -/
def toFiniteStageEntry (E : RegularStageBasicDecoration D ι)
    (isOpen_insideCell : IsOpen E.insideCell) :
    FiniteRegularSphereSurgeryStageEntry Phi where
  circleCount := Fintype.card ι
  system := E.toFiniteSphereSurgeryIntersectionSystem.reindex (Fintype.equivFin ι).symm
  isOpen_insideCell := isOpen_insideCell

end PairedBandMovingSphereCollarData.RegularStageBasicDecoration

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe u

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε : ℝ}
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
  (hR : 0 < R) (hε : 0 < ε)
  (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
    x.ofLp (frame 2) < d - ε)
  (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
    d + ε < x.ofLp (frame 2))

/-- The canonical pair of separated terminal spheres is a finite regular-stage entry. -/
def canonicalSeparatedTerminalFiniteStageEntry :
    FiniteRegularSphereSurgeryStageEntry Phi where
  circleCount := canonicalSeparatedTerminalCircleCount lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder
  system := canonicalSeparatedTerminalFinSphereSurgerySystem lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder hR hε hlower hupper
  isOpen_insideCell := by
    change IsOpen
      ((canonicalSeparatedTerminalRoundingData hR hε hlower hupper).lowerInside ∪
        (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).upperInside)
    exact (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).isOpen_lowerInside.union
      (canonicalSeparatedTerminalRoundingData hR hε hlower hupper).isOpen_upperInside

@[simp] theorem canonicalSeparatedTerminalFiniteStageEntry_parityStage :
    (canonicalSeparatedTerminalFiniteStageEntry lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper).parityStage =
      canonicalSeparatedTerminalParityStage (Phi := Phi) hR hε hlower hupper :=
  rfl

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
