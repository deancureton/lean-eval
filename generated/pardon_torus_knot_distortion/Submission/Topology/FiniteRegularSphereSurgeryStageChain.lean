import Submission.Topology.FiniteRegularSphereSurgeryStageEntry

/-!
# Finite regular-stage chains with fixed endpoints

The geometric construction has a distinguished initial outer sphere and a distinguished terminal
pair of separated spheres.  This module inserts an arbitrary finite family of intermediate moving
stages between those endpoints and exposes exact formulas for all three index classes.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology
namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- A fixed initial and terminal stage with finitely many intermediate moving stages. -/
structure FiniteRegularSphereSurgeryStageChain (Phi : AmbientIsotopy) where
  middleCount : ℕ
  initial : FiniteRegularSphereSurgeryStageEntry Phi
  middle : Fin middleCount → FiniteRegularSphereSurgeryStageEntry Phi
  terminal : FiniteRegularSphereSurgeryStageEntry Phi

namespace FiniteRegularSphereSurgeryStageChain

/-- The entry at `0` is initial, entries `1, …, middleCount` are the moving stages, and the last
entry is terminal. -/
def entry (C : FiniteRegularSphereSurgeryStageChain Phi) :
    Fin (C.middleCount + 2) → FiniteRegularSphereSurgeryStageEntry Phi :=
  Fin.cases C.initial fun k ↦ Fin.lastCases C.terminal C.middle k

@[simp] theorem entry_zero (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.entry 0 = C.initial :=
  rfl

@[simp] theorem entry_middle (C : FiniteRegularSphereSurgeryStageChain Phi)
    (k : Fin C.middleCount) :
    C.entry k.castSucc.succ = C.middle k := by
  simp [entry]

@[simp] theorem entry_last (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.entry (Fin.last (C.middleCount + 1)) = C.terminal := by
  have hlast : Fin.last (C.middleCount + 1) = (Fin.last C.middleCount).succ := by
    apply Fin.ext
    simp
  unfold entry
  calc
    Fin.cases C.initial (fun k ↦ Fin.lastCases C.terminal C.middle k)
        (Fin.last (C.middleCount + 1)) =
      Fin.cases C.initial (fun k ↦ Fin.lastCases C.terminal C.middle k)
        (Fin.last C.middleCount).succ := congrArg _ hlast
    _ = C.terminal := by
      rw [Fin.cases_succ, Fin.lastCases_last]

/-- A chain with `middleCount` intermediate stages has `middleCount + 1` transitions. -/
def toFiniteRegularSphereSurgeryStageFamily
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    FiniteRegularSphereSurgeryStageFamily Phi :=
  FiniteRegularSphereSurgeryStageFamily.ofEntries C.entry

@[simp] theorem toFiniteRegularSphereSurgeryStageFamily_length
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageFamily.length = C.middleCount + 1 :=
  rfl

@[simp] theorem toFiniteRegularSphereSurgeryStageFamily_initialParityStage
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageFamily.parityStage 0 = C.initial.parityStage := by
  change (C.entry 0).parityStage = C.initial.parityStage
  rw [C.entry_zero]

@[simp] theorem toFiniteRegularSphereSurgeryStageFamily_terminalParityStage
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageFamily.parityStage
        (Fin.last (C.middleCount + 1)) =
      C.terminal.parityStage := by
  change (C.entry (Fin.last (C.middleCount + 1))).parityStage = C.terminal.parityStage
  rw [C.entry_last]

/-- The legacy natural-indexed stage sequence canonically associated to the finite chain. -/
def toFiniteRegularSphereSurgeryStageSequence
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    FiniteRegularSphereSurgeryStageSequence Phi :=
  C.toFiniteRegularSphereSurgeryStageFamily.toFiniteRegularSphereSurgeryStageSequence

@[simp] theorem toFiniteRegularSphereSurgeryStageSequence_length
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageSequence.length = C.middleCount + 1 :=
  rfl

@[simp] theorem toFiniteRegularSphereSurgeryStageSequence_initialParityStage
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageSequence.parityStage 0 = C.initial.parityStage := by
  rw [toFiniteRegularSphereSurgeryStageSequence,
    FiniteRegularSphereSurgeryStageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage
      C.toFiniteRegularSphereSurgeryStageFamily (Nat.zero_le _)]
  exact C.toFiniteRegularSphereSurgeryStageFamily_initialParityStage

@[simp] theorem toFiniteRegularSphereSurgeryStageSequence_terminalParityStage
    (C : FiniteRegularSphereSurgeryStageChain Phi) :
    C.toFiniteRegularSphereSurgeryStageSequence.parityStage (C.middleCount + 1) =
      C.terminal.parityStage := by
  change (C.toFiniteRegularSphereSurgeryStageFamily
      |>.toFiniteRegularSphereSurgeryStageSequence
      |>.parityStage C.toFiniteRegularSphereSurgeryStageFamily.length) =
    C.terminal.parityStage
  rw [FiniteRegularSphereSurgeryStageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage
      C.toFiniteRegularSphereSurgeryStageFamily (le_refl _)]
  change C.toFiniteRegularSphereSurgeryStageFamily.parityStage
      (Fin.last (C.middleCount + 1)) = C.terminal.parityStage
  exact C.toFiniteRegularSphereSurgeryStageFamily_terminalParityStage

end FiniteRegularSphereSurgeryStageChain
end PairedBandMovingSphereCollarData
end Submission.Topology
