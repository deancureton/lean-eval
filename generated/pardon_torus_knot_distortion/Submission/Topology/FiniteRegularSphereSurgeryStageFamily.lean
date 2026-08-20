import Submission.Topology.PairedBandMovingSphere

/-!
# Finite families of regular sphere-surgery stages

The surgery alternative audits only the stages numbered from `0` through `length`, but its
historical sequence structure stores systems at every natural number.  This module gives the
geometric construction a genuinely finite interface and automatically chooses the common event
region as the union of the finitely many stage event regions.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology
namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- Exactly the finitely many regular stages inspected by the surgery alternative. -/
structure FiniteRegularSphereSurgeryStageFamily (Phi : AmbientIsotopy) where
  length : ℕ
  circleCount : Fin (length + 1) → ℕ
  system : ∀ k, FiniteSphereSurgeryIntersectionSystem Phi (Fin (circleCount k))
  parityStage : Fin (length + 1) → RegularSphereFamilyParityStage Phi
  sphereFamily_eq : ∀ k, (system k).sphereFamily = (parityStage k).sphereFamily

namespace FiniteRegularSphereSurgeryStageFamily

/-- Clamp an arbitrary natural index to the finite audited interval. -/
def boundedIndex (F : FiniteRegularSphereSurgeryStageFamily Phi) (k : ℕ) :
    Fin (F.length + 1) :=
  ⟨min k F.length, Nat.lt_succ_of_le (Nat.min_le_right k F.length)⟩

@[simp] theorem boundedIndex_eq_of_le
    (F : FiniteRegularSphereSurgeryStageFamily Phi) {k : ℕ} (hk : k ≤ F.length) :
    F.boundedIndex k = ⟨k, Nat.lt_succ_of_le hk⟩ := by
  apply Fin.ext
  simp [boundedIndex, Nat.min_eq_left hk]

/-- Extend the finite circle counts by constantly reusing the last stage past `length`. -/
def extendedCircleCount (F : FiniteRegularSphereSurgeryStageFamily Phi) (k : ℕ) : ℕ :=
  F.circleCount (F.boundedIndex k)

/-- Extend the finite systems by constantly reusing the last stage past `length`. -/
def extendedSystem (F : FiniteRegularSphereSurgeryStageFamily Phi) (k : ℕ) :
    FiniteSphereSurgeryIntersectionSystem Phi (Fin (F.extendedCircleCount k)) :=
  F.system (F.boundedIndex k)

/-- Transporting a finite-stage circle index transports the corresponding circle pointwise. -/
theorem system_circle_cast (F : FiniteRegularSphereSurgeryStageFamily Phi)
    {j j' : Fin (F.length + 1)} (h : j = j') (i : Fin (F.circleCount j')) :
    (F.system j).circle (Fin.cast (congrArg F.circleCount h).symm i) =
      (F.system j').circle i := by
  subst j'
  rfl

/-- Transport a circle index from an audited finite stage into its natural-indexed extension. -/
def extendedIndexOfLE (F : FiniteRegularSphereSurgeryStageFamily Phi)
    {k : ℕ} (hk : k ≤ F.length) :
    Fin (F.circleCount ⟨k, Nat.lt_succ_of_le hk⟩) → Fin (F.extendedCircleCount k) :=
  Fin.cast (congrArg F.circleCount (F.boundedIndex_eq_of_le hk)).symm

@[simp] theorem extendedIndexOfLE_val
    (F : FiniteRegularSphereSurgeryStageFamily Phi) {k : ℕ} (hk : k ≤ F.length)
    (i : Fin (F.circleCount ⟨k, Nat.lt_succ_of_le hk⟩)) :
    (F.extendedIndexOfLE hk i).1 = i.1 :=
  rfl

/-- Pointwise circle transport from an audited finite stage to its natural-indexed extension. -/
theorem extendedSystem_circle_of_le
    (F : FiniteRegularSphereSurgeryStageFamily Phi) {k : ℕ} (hk : k ≤ F.length)
    (i : Fin (F.circleCount ⟨k, Nat.lt_succ_of_le hk⟩)) :
    (F.extendedSystem k).circle (F.extendedIndexOfLE hk i) =
      (F.system ⟨k, Nat.lt_succ_of_le hk⟩).circle i := by
  exact F.system_circle_cast (F.boundedIndex_eq_of_le hk) i

/-- Extend the finite parity stages by constantly reusing the last stage past `length`. -/
def extendedParityStage (F : FiniteRegularSphereSurgeryStageFamily Phi) (k : ℕ) :
    RegularSphereFamilyParityStage Phi :=
  F.parityStage (F.boundedIndex k)

/-- The finite union of all audited stage event regions. -/
def commonEventRegion (F : FiniteRegularSphereSurgeryStageFamily Phi) : Set R3 :=
  ⋃ k, (F.system k).eventRegion

/-- A finite stage family supplies the legacy natural-indexed surgery sequence without any
additional event-containment input. -/
def toFiniteRegularSphereSurgeryStageSequence
    (F : FiniteRegularSphereSurgeryStageFamily Phi) :
    FiniteRegularSphereSurgeryStageSequence Phi where
  length := F.length
  circleCount := F.extendedCircleCount
  system := F.extendedSystem
  parityStage := F.extendedParityStage
  sphereFamily_eq k := F.sphereFamily_eq (F.boundedIndex k)
  commonEventRegion := F.commonEventRegion
  stage_event_subset k _ := Set.subset_iUnion (fun j ↦ (F.system j).eventRegion)
    (F.boundedIndex k)

@[simp] theorem toFiniteRegularSphereSurgeryStageSequence_length
    (F : FiniteRegularSphereSurgeryStageFamily Phi) :
    F.toFiniteRegularSphereSurgeryStageSequence.length = F.length :=
  rfl

@[simp] theorem toFiniteRegularSphereSurgeryStageSequence_parityStage
    (F : FiniteRegularSphereSurgeryStageFamily Phi) {k : ℕ} (hk : k ≤ F.length) :
    F.toFiniteRegularSphereSurgeryStageSequence.parityStage k =
      F.parityStage ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [toFiniteRegularSphereSurgeryStageSequence, extendedParityStage,
    F.boundedIndex_eq_of_le hk]

end FiniteRegularSphereSurgeryStageFamily
end PairedBandMovingSphereCollarData
end Submission.Topology
