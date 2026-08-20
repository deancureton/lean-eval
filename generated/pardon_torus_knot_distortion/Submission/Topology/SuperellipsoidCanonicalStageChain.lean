import Submission.Topology.FiniteRegularSphereSurgeryStageChain
import Submission.Topology.SuperellipsoidCanonicalStageEntries

/-!
# Canonical superellipsoid finite-stage chain

The outer superellipsoid and the separated truncations provide fixed endpoint entries.  Inserting
any finite family of honest moving-sphere entries between them gives the exact finite chain used by
the surgery alternative, with endpoint parity stages identified definitionally.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε : ℝ}
  (initialFamily : FiniteSuperellipsoidOuterTorusSmoothCircleFamily
    Phi frame c R d)
  [Fintype initialFamily.index]
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

/-- Insert the honest moving stages between the canonical initial and terminal entries. -/
def canonicalSuperellipsoidStageChain
    (middleCount : ℕ)
    (middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi) :
    FiniteRegularSphereSurgeryStageChain Phi where
  middleCount := middleCount
  initial := initialFamily.initialOuterFiniteStageEntry hR
  middle := middle
  terminal := canonicalSeparatedTerminalFiniteStageEntry lowerOuterOrder lowerCutOrder
    upperOuterOrder upperCutOrder hR hε hlower hupper

@[simp] theorem canonicalSuperellipsoidStageChain_length
    (middleCount : ℕ)
    (middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi) :
    ((canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper middleCount middle)
        |>.toFiniteRegularSphereSurgeryStageSequence).length = middleCount + 1 :=
  rfl

@[simp] theorem canonicalSuperellipsoidStageChain_initialParityStage
    (middleCount : ℕ)
    (middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi) :
    ((canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper middleCount middle)
        |>.toFiniteRegularSphereSurgeryStageSequence).parityStage 0 =
      initialOuterSuperellipsoidParityStage Phi frame c hR := by
  simp [canonicalSuperellipsoidStageChain]

@[simp] theorem canonicalSuperellipsoidStageChain_terminalParityStage
    (middleCount : ℕ)
    (middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi) :
    ((canonicalSuperellipsoidStageChain initialFamily lowerOuterOrder lowerCutOrder
      upperOuterOrder upperCutOrder hR hε hlower hupper middleCount middle)
        |>.toFiniteRegularSphereSurgeryStageSequence).parityStage (middleCount + 1) =
      canonicalSeparatedTerminalParityStage (Phi := Phi) hR hε hlower hupper := by
  simp [canonicalSuperellipsoidStageChain]

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
