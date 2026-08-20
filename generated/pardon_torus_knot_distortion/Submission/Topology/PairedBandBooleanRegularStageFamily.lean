import Submission.Topology.FiniteBooleanFlipStageFamily
import Submission.Topology.SuperellipsoidCanonicalStageEntries

/-!
# Boolean regular-stage families from paired-band collars

The paired-band construction naturally produces one collar and one finite circle decomposition for
every Boolean smoothing choice.  This module packages those varying finite index types and turns
the resulting decorations into the uniform `Fin`-indexed stage entries used by the finite surgery
sequence.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology
namespace PairedBandMovingSphereCollarData

universe u

variable {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}

/-- A complete honest regular moving-sphere stage for every Boolean smoothing choice.  The circle
index type may vary with the choice; conversion to a stage entry canonically reindexes it by a
finite ordinal. -/
structure BooleanChoicePairedBandRegularStageData where
  circleIndex : (Fin P.bandCount → Bool) → Type u
  circleIndex_fintype : ∀ choice, Fintype (circleIndex choice)
  collar : ∀ choice, PairedBandMovingSphereCollarData C choice
  decoration : ∀ choice,
    letI := circleIndex_fintype choice
    RegularStageBasicDecoration (collar choice) (circleIndex choice)
  isOpen_insideCell : ∀ choice,
    letI := circleIndex_fintype choice
    IsOpen (decoration choice).insideCell

namespace BooleanChoicePairedBandRegularStageData

/-- Convert one choice-indexed paired-band stage to the uniform finite-entry interface. -/
def stageEntry (D : BooleanChoicePairedBandRegularStageData (C := C))
    (choice : Fin P.bandCount → Bool) :
    FiniteRegularSphereSurgeryStageEntry Phi := by
  letI := D.circleIndex_fintype choice
  exact (D.decoration choice).toFiniteStageEntry (D.isOpen_insideCell choice)

/-- All Boolean paired-band stages form the choice-indexed input for the canonical flip path. -/
def toBooleanChoiceRegularStageData
    (D : BooleanChoicePairedBandRegularStageData (C := C)) :
    BooleanChoiceRegularStageData Phi P.bandCount where
  stage := D.stageEntry

@[simp] theorem toBooleanChoiceRegularStageData_stage
    (D : BooleanChoicePairedBandRegularStageData (C := C))
    (choice : Fin P.bandCount → Bool) :
    D.toBooleanChoiceRegularStageData.stage choice = D.stageEntry choice :=
  rfl

end BooleanChoicePairedBandRegularStageData
end PairedBandMovingSphereCollarData
end Submission.Topology
