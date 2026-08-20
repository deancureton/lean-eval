import Submission.Topology.FiniteRegularSphereSurgeryStageEntry

/-!
# Canonical finite families obtained by flipping Boolean bands one at a time

For `n` independent local surgery bands, the canonical path from the all-false resolution to the
all-true resolution has `n + 1` states.  State `k` resolves precisely the bands with index below
`k`.  Consecutive states differ at exactly one band.  This file packages that combinatorics and
turns any choice-indexed regular-stage construction into the finite family used by surgery.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology
namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- At state `k`, exactly the bands with index strictly below `k` have been flipped. -/
def prefixBandChoice {n : ℕ} (k : Fin (n + 1)) (i : Fin n) : Bool :=
  decide (i.1 < k.1)

@[simp]
theorem prefixBandChoice_zero {n : ℕ} :
    prefixBandChoice (0 : Fin (n + 1)) = fun _ ↦ false := by
  funext i
  simp [prefixBandChoice]

@[simp]
theorem prefixBandChoice_last {n : ℕ} :
    prefixBandChoice (Fin.last n) = fun _ ↦ true := by
  funext i
  simp [prefixBandChoice, i.isLt]

@[simp]
theorem prefixBandChoice_castSucc_self {n : ℕ} (k : Fin n) :
    prefixBandChoice k.castSucc k = false := by
  simp [prefixBandChoice]

@[simp]
theorem prefixBandChoice_succ_self {n : ℕ} (k : Fin n) :
    prefixBandChoice k.succ k = true := by
  simp [prefixBandChoice]

/-- Away from the current band, consecutive states have the same resolution choice. -/
theorem prefixBandChoice_succ_eq_castSucc_of_ne
    {n : ℕ} (k i : Fin n) (hik : i ≠ k) :
    prefixBandChoice k.succ i = prefixBandChoice k.castSucc i := by
  by_cases hil : i.1 < k.1
  · have his : i.1 < k.1 + 1 := by omega
    simp [prefixBandChoice, Fin.val_succ, Fin.val_castSucc, hil, his]
  · have hne : i.1 ≠ k.1 := by
      intro h
      exact hik (Fin.ext h)
    have his : ¬ i.1 < k.1 + 1 := by omega
    simp [prefixBandChoice, Fin.val_succ, Fin.val_castSucc, hil, his]

/-- Consecutive states are related by setting exactly the current band to true. -/
theorem prefixBandChoice_succ_eq_update
    {n : ℕ} (k : Fin n) :
    prefixBandChoice k.succ = Function.update (prefixBandChoice k.castSucc) k true := by
  funext i
  by_cases hik : i = k
  · subst i
    simp
  · rw [Function.update_of_ne hik]
    exact prefixBandChoice_succ_eq_castSucc_of_ne k i hik

/-- A complete regular stage for every Boolean resolution choice. -/
structure BooleanChoiceRegularStageData (Phi : AmbientIsotopy) (n : ℕ) where
  stage : (Fin n → Bool) → FiniteRegularSphereSurgeryStageEntry Phi

namespace BooleanChoiceRegularStageData

/-- Evaluate the stage construction along the canonical one-band-at-a-time path. -/
def entry (D : BooleanChoiceRegularStageData Phi n) (k : Fin (n + 1)) :
    FiniteRegularSphereSurgeryStageEntry Phi :=
  D.stage (prefixBandChoice k)

/-- The canonical Boolean path is an honest finite regular-stage family with `n` transitions. -/
def toFiniteRegularSphereSurgeryStageFamily
    (D : BooleanChoiceRegularStageData Phi n) :
    FiniteRegularSphereSurgeryStageFamily Phi :=
  FiniteRegularSphereSurgeryStageFamily.ofEntries D.entry

@[simp]
theorem toFiniteRegularSphereSurgeryStageFamily_length
    (D : BooleanChoiceRegularStageData Phi n) :
    D.toFiniteRegularSphereSurgeryStageFamily.length = n :=
  rfl

@[simp]
theorem entry_zero (D : BooleanChoiceRegularStageData Phi n) :
    D.entry 0 = D.stage (fun _ ↦ false) := by
  rw [entry, prefixBandChoice_zero]

@[simp]
theorem entry_last (D : BooleanChoiceRegularStageData Phi n) :
    D.entry (Fin.last n) = D.stage (fun _ ↦ true) := by
  rw [entry, prefixBandChoice_last]

@[simp]
theorem toFiniteRegularSphereSurgeryStageFamily_initialParityStage
    (D : BooleanChoiceRegularStageData Phi n) :
    D.toFiniteRegularSphereSurgeryStageFamily.parityStage 0 =
      (D.stage (fun _ ↦ false)).parityStage := by
  change (D.entry 0).parityStage = _
  rw [D.entry_zero]

@[simp]
theorem toFiniteRegularSphereSurgeryStageFamily_terminalParityStage
    (D : BooleanChoiceRegularStageData Phi n) :
    D.toFiniteRegularSphereSurgeryStageFamily.parityStage (Fin.last n) =
      (D.stage (fun _ ↦ true)).parityStage := by
  change (D.entry (Fin.last n)).parityStage = _
  rw [D.entry_last]

end BooleanChoiceRegularStageData
end PairedBandMovingSphereCollarData
end Submission.Topology
