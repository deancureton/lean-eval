import Submission.Topology.FiniteRegularSphereSurgeryStageFamily
import Submission.Topology.SuperellipsoidThreePageAttachment

/-!
# Uniform entries for finite regular sphere-surgery families

An honest sphere-surgery system already contains its sphere family, ambient inside cell, and exact
frontier theorem.  If that inside cell is open, the parity stage is canonical.  This module uses
that observation to reduce finite-family assembly to a finite collection of complete systems with
open inside cells.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology
namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- One complete regular stage together with the openness needed for its canonical parity side. -/
structure FiniteRegularSphereSurgeryStageEntry (Phi : AmbientIsotopy) where
  circleCount : ℕ
  system : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)
  isOpen_insideCell : IsOpen system.insideCell

namespace FiniteRegularSphereSurgeryStageEntry

/-- The parity stage canonically determined by a regular sphere-surgery entry. -/
def parityStage (E : FiniteRegularSphereSurgeryStageEntry Phi) :
    RegularSphereFamilyParityStage Phi :=
  RegularSphereFamilyParityStage.ofOpenRegion Phi E.system.sphereFamily E.system.insideCell
    E.isOpen_insideCell E.system.sphereFamily_is_boundary

@[simp] theorem parityStage_sphereFamily
    (E : FiniteRegularSphereSurgeryStageEntry Phi) :
    E.parityStage.sphereFamily = E.system.sphereFamily :=
  rfl

@[simp] theorem parityStage_inside
    (E : FiniteRegularSphereSurgeryStageEntry Phi) :
    E.parityStage.inside = transportedTorusPart Phi E.system.insideCell :=
  rfl

end FiniteRegularSphereSurgeryStageEntry

namespace FiniteRegularSphereSurgeryStageFamily

/-- A finite collection of complete open-inside systems assembles into the exact finite family
consumed by the natural-indexed surgery-sequence adapter. -/
def ofEntries {length : ℕ}
    (entry : Fin (length + 1) → FiniteRegularSphereSurgeryStageEntry Phi) :
    FiniteRegularSphereSurgeryStageFamily Phi where
  length := length
  circleCount k := (entry k).circleCount
  system k := (entry k).system
  parityStage k := (entry k).parityStage
  sphereFamily_eq _ := rfl

@[simp] theorem ofEntries_system {length : ℕ}
    (entry : Fin (length + 1) → FiniteRegularSphereSurgeryStageEntry Phi)
    (k : Fin (length + 1)) :
    (ofEntries entry).system k = (entry k).system :=
  rfl

@[simp] theorem ofEntries_parityStage {length : ℕ}
    (entry : Fin (length + 1) → FiniteRegularSphereSurgeryStageEntry Phi)
    (k : Fin (length + 1)) :
    (ofEntries entry).parityStage k = (entry k).parityStage :=
  rfl

end FiniteRegularSphereSurgeryStageFamily
end PairedBandMovingSphereCollarData
end Submission.Topology
