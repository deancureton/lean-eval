import Submission.Topology.ReducedTorusCircleTransitions

/-!
# Reduced torus-circle stages along the Boolean prefix path

The canonical Boolean path flips one four-port band at a time.  This file evaluates exact
torus-circle sections and open parity regions along that path and packages the stage-sided disk
covers needed by the reduced all-inessential argument.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open PairedBandMovingSphereCollarData
open Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ}

/-- At reduced stage `k`, exactly the bands with index below `k` have been flipped. -/
def reducedPrefixBandChoice {n : ℕ} (k : Fin (n + 1)) (i : Fin n) : Bool :=
  decide (i.1 < k.1)

@[simp] theorem reducedPrefixBandChoice_zero {n : ℕ} :
    reducedPrefixBandChoice (0 : Fin (n + 1)) = fun _ ↦ false := by
  funext i
  simp [reducedPrefixBandChoice]

@[simp] theorem reducedPrefixBandChoice_last {n : ℕ} :
    reducedPrefixBandChoice (Fin.last n) = fun _ ↦ true := by
  funext i
  simp [reducedPrefixBandChoice, i.isLt]

@[simp] theorem reducedPrefixBandChoice_castSucc_self {n : ℕ} (k : Fin n) :
    reducedPrefixBandChoice k.castSucc k = false := by
  simp [reducedPrefixBandChoice]

@[simp] theorem reducedPrefixBandChoice_succ_self {n : ℕ} (k : Fin n) :
    reducedPrefixBandChoice k.succ k = true := by
  simp [reducedPrefixBandChoice]

/-- Consecutive prefix states differ only at the current band. -/
theorem reducedPrefixBandChoice_succ_eq_castSucc_of_ne
    {n : ℕ} (k i : Fin n) (hik : i ≠ k) :
    reducedPrefixBandChoice k.succ i = reducedPrefixBandChoice k.castSucc i := by
  by_cases hil : i.1 < k.1
  · have his : i.1 < k.1 + 1 := by omega
    simp [reducedPrefixBandChoice, Fin.val_succ, Fin.val_castSucc, hil, his]
  · have hne : i.1 ≠ k.1 := by
      intro h
      exact hik (Fin.ext h)
    have his : ¬ i.1 < k.1 + 1 := by omega
    simp [reducedPrefixBandChoice, Fin.val_succ, Fin.val_castSucc, hil, his]

/-- The successor prefix is the current prefix updated at its unique changed band. -/
theorem reducedPrefixBandChoice_succ_eq_update {n : ℕ} (k : Fin n) :
    reducedPrefixBandChoice k.succ =
      Function.update (reducedPrefixBandChoice k.castSucc) k true := by
  funext i
  by_cases hik : i = k
  · subst i
    simp
  · rw [Function.update_of_ne hik]
    exact reducedPrefixBandChoice_succ_eq_castSucc_of_ne k i hik

/-- An exact reduced torus-circle stage for every Boolean resolution choice. -/
structure BooleanChoiceReducedTorusCircleStageData (Phi : AmbientIsotopy) (n : ℕ) where
  stage : (Fin n → Bool) → ReducedTorusCircleStageEntry Phi

namespace BooleanChoiceReducedTorusCircleStageData

/-- Evaluate the reduced stage construction along the one-band-at-a-time prefix path. -/
def entry (D : BooleanChoiceReducedTorusCircleStageData Phi n) (k : Fin (n + 1)) :
    ReducedTorusCircleStageEntry Phi :=
  D.stage (reducedPrefixBandChoice k)

/-- The canonical Boolean prefix is an exact reduced torus-circle stage geometry. -/
def toReducedTorusCircleStageGeometry
    (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    ReducedTorusCircleStageGeometry Phi :=
  ReducedTorusCircleStageGeometry.ofEntries D.entry

@[simp] theorem toReducedTorusCircleStageGeometry_length
    (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    D.toReducedTorusCircleStageGeometry.length = n :=
  rfl

@[simp] theorem entry_zero (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    D.entry 0 = D.stage (fun _ ↦ false) := by
  rw [entry, reducedPrefixBandChoice_zero]

@[simp] theorem entry_last (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    D.entry (Fin.last n) = D.stage (fun _ ↦ true) := by
  rw [entry, reducedPrefixBandChoice_last]

@[simp] theorem toReducedTorusCircleStageGeometry_initialParityStage
    (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    D.toReducedTorusCircleStageGeometry.parityStage 0 =
      (D.stage (fun _ ↦ false)).parityStage := by
  change (D.entry 0).parityStage = _
  rw [D.entry_zero]

@[simp] theorem toReducedTorusCircleStageGeometry_terminalParityStage
    (D : BooleanChoiceReducedTorusCircleStageData Phi n) :
    D.toReducedTorusCircleStageGeometry.parityStage n =
      (D.stage (fun _ ↦ true)).parityStage := by
  rw [show D.toReducedTorusCircleStageGeometry.parityStage n =
      (D.entry (Fin.last n)).parityStage by
    exact ReducedTorusCircleStageGeometry.ofEntries_parityStage D.entry (Fin.last n)]
  rw [D.entry_last]

/-- Stage-sided disk covers indexed directly by the Boolean flip which they audit. -/
structure IndexedStageSideCoverData
    (D : BooleanChoiceReducedTorusCircleStageData Phi n) where
  cover : ∀
    (hzero : D.toReducedTorusCircleStageGeometry
      |>.toReducedTorusCircleStageSequence.AllInessential)
    (k : Fin n),
    ReducedCircleStageSideCover
      (D.toReducedTorusCircleStageGeometry.circleFamily k.1)
      (D.toReducedTorusCircleStageGeometry.circleFamily_allInessential
        hzero k.1 (Nat.le_of_lt k.isLt))
      (D.toReducedTorusCircleStageGeometry.circleFamily (k.1 + 1))
      (D.toReducedTorusCircleStageGeometry.circleFamily_allInessential
        hzero (k.1 + 1) k.isLt)
      (D.toReducedTorusCircleStageGeometry.parityStage k.1)
      (D.toReducedTorusCircleStageGeometry.parityStage (k.1 + 1))

namespace IndexedStageSideCoverData

/-- Boolean-indexed covers supply the natural-indexed reduced transition interface. -/
def toStageSideCoverData
    {D : BooleanChoiceReducedTorusCircleStageData Phi n}
    (C : D.IndexedStageSideCoverData) :
    D.toReducedTorusCircleStageGeometry.StageSideCoverData where
  cover hzero k hk := C.cover hzero ⟨k, hk⟩

end IndexedStageSideCoverData

/-- Boolean stages, local sided covers, and terminal cells form the complete reduced resolution. -/
structure ResolutionData
    (D : BooleanChoiceReducedTorusCircleStageData Phi n)
    (lower upper : Set (transportedTorus Phi)) where
  covers : D.IndexedStageSideCoverData
  terminal : TerminalTwoSphereCoreCells
    (D.toReducedTorusCircleStageGeometry.parityStage n).inside
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper

namespace ResolutionData

/-- Forget the Boolean indexing and retain the reduced stage-side resolution. -/
def toStageSideCoverResolutionData
    {D : BooleanChoiceReducedTorusCircleStageData Phi n}
    {lower upper : Set (transportedTorus Phi)}
    (R : D.ResolutionData lower upper) :
    D.toReducedTorusCircleStageGeometry.StageSideCoverResolutionData lower upper where
  covers := R.covers.toStageSideCoverData
  terminal := R.terminal
  terminal_lower_eq := R.terminal_lower_eq
  terminal_upper_eq := R.terminal_upper_eq

/-- The Boolean reduced geometry supplies the all-inessential resolution consumed by the axis. -/
def toReducedAllInessentialResolution
    {D : BooleanChoiceReducedTorusCircleStageData Phi n}
    {lower upper : Set (transportedTorus Phi)}
    (R : D.ResolutionData lower upper)
    (hzero : D.toReducedTorusCircleStageGeometry
      |>.toReducedTorusCircleStageSequence.AllInessential) :
    ReducedAllInessentialResolution
      D.toReducedTorusCircleStageGeometry.toReducedTorusCircleStageSequence lower upper :=
  R.toStageSideCoverResolutionData.toReducedAllInessentialResolution hzero

end ResolutionData
end BooleanChoiceReducedTorusCircleStageData
end Submission.Topology
