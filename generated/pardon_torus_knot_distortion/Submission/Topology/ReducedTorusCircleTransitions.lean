import Submission.Topology.ReducedTorusCircleCore

/-!
# Stage-sided reduced transitions from torus circles

For one elementary four-port move, the canonical disk core may come from either endpoint.  The
boundary inherited from that endpoint is covered automatically.  It is enough to put the new
boundary patch and the label-change lens in one canonical endpoint disk.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace FiniteDisjointTorusCircleFamily

/-- The whole circle carrier is contained in the canonical maximal-disk union. -/
theorem carrier_subset_canonicalDiskUnion
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) :
    F.carrier ⊆ F.canonicalDiskUnion hzero := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact F.circle_range_subset_canonicalDiskUnion hzero i hxi

end FiniteDisjointTorusCircleFamily

/-- A forward reduced transition localized in one disk of the pre-stage circle family. -/
structure ReducedForwardCircleDiskSideCover
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (pre post : ReducedTorusParityStage Phi) where
  diskIndex : ι
  preBoundary_eq_carrier : pre.boundary = F.carrier
  postBoundary_subset :
    post.boundary ⊆ pre.boundary ∪ F.torusDiskRange hzero diskIndex
  labelChange_subset :
    {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
      F.torusDiskRange hzero diskIndex

namespace ReducedForwardCircleDiskSideCover

variable {F : FiniteDisjointTorusCircleFamily Phi ι}
  {hzero : F.AllInessential} {pre post : ReducedTorusParityStage Phi}

/-- A stage-sided disk cover supplies the exact reduced inessential transition. -/
def toReducedInessentialParityTransition
    (D : ReducedForwardCircleDiskSideCover F hzero pre post) :
    ReducedInessentialParityTransition pre post where
  core := F.toReducedInessentialTorusCoreData hzero
  support := F.canonicalDiskUnion hzero
  support_subset_diskUnion := Subset.rfl
  boundaries_subset_support := by
    intro x hx
    rcases hx with hxPre | hxPost
    · apply F.carrier_subset_canonicalDiskUnion hzero
      rwa [← D.preBoundary_eq_carrier]
    · rcases D.postBoundary_subset hxPost with hxOld | hxDisk
      · apply F.carrier_subset_canonicalDiskUnion hzero
        rwa [← D.preBoundary_eq_carrier]
      · exact F.torusDiskRange_subset_canonicalDiskUnion hzero D.diskIndex hxDisk
  labelChange_subset_support :=
    D.labelChange_subset.trans
      (F.torusDiskRange_subset_canonicalDiskUnion hzero D.diskIndex)

end ReducedForwardCircleDiskSideCover

/-- A reverse cover is a forward cover whose canonical core comes from the post stage. -/
abbrev ReducedReverseCircleDiskSideCover
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (pre post : ReducedTorusParityStage Phi) :=
  ReducedForwardCircleDiskSideCover F hzero post pre

namespace ReducedForwardCircleDiskSideCover

variable {F : FiniteDisjointTorusCircleFamily Phi ι}
  {hzero : F.AllInessential} {pre post : ReducedTorusParityStage Phi}

/-- Reversing a stage-sided cover gives the transition in the required forward direction. -/
def toReducedInessentialParityTransitionOfReverse
    (D : ReducedReverseCircleDiskSideCover F hzero pre post) :
    ReducedInessentialParityTransition pre post := by
  let T := D.toReducedInessentialParityTransition
  exact {
    core := T.core
    support := T.support
    support_subset_diskUnion := T.support_subset_diskUnion
    boundaries_subset_support := by
      simpa only [Set.union_comm] using T.boundaries_subset_support
    labelChange_subset_support := by
      intro x hx
      apply T.labelChange_subset_support
      exact ne_comm.mp hx
  }

end ReducedForwardCircleDiskSideCover

/-- Every step may choose the canonical disk side from either endpoint. -/
def ReducedCircleStageSideCover
    {preIndex postIndex : Type*}
    [Fintype preIndex] [DecidableEq preIndex]
    [Fintype postIndex] [DecidableEq postIndex]
    (preFamily : FiniteDisjointTorusCircleFamily Phi preIndex)
    (preZero : preFamily.AllInessential)
    (postFamily : FiniteDisjointTorusCircleFamily Phi postIndex)
    (postZero : postFamily.AllInessential)
    (pre post : ReducedTorusParityStage Phi) :=
  ReducedForwardCircleDiskSideCover preFamily preZero pre post ⊕
    ReducedReverseCircleDiskSideCover postFamily postZero pre post

namespace ReducedCircleStageSideCover

variable {preIndex postIndex : Type*}
  [Fintype preIndex] [DecidableEq preIndex]
  [Fintype postIndex] [DecidableEq postIndex]
  {preFamily : FiniteDisjointTorusCircleFamily Phi preIndex}
  {preZero : preFamily.AllInessential}
  {postFamily : FiniteDisjointTorusCircleFamily Phi postIndex}
  {postZero : postFamily.AllInessential}
  {pre post : ReducedTorusParityStage Phi}

/-- Either endpoint choice constructs the same forward reduced transition. -/
def toReducedInessentialParityTransition
    (D : ReducedCircleStageSideCover preFamily preZero postFamily postZero pre post) :
    ReducedInessentialParityTransition pre post :=
  match D with
  | .inl forward => forward.toReducedInessentialParityTransition
  | .inr reverse => reverse.toReducedInessentialParityTransitionOfReverse

end ReducedCircleStageSideCover

namespace ReducedTorusCircleStageGeometry

/-- The circle family underlying one exact reduced stage. -/
def circleFamily (D : ReducedTorusCircleStageGeometry Phi) (k : ℕ) :
    FiniteDisjointTorusCircleFamily Phi (Fin (D.circleCount k)) :=
  FiniteDisjointTorusCircleFamily.ofSection (D.circleSection k)

theorem circleFamily_allInessential
    (D : ReducedTorusCircleStageGeometry Phi)
    (hzero : D.toReducedTorusCircleStageSequence.AllInessential)
    (k : ℕ) (hk : k ≤ D.length) :
    (D.circleFamily k).AllInessential := by
  intro i
  exact hzero k hk i

/-- Stage-sided disk covers for every all-inessential canonical prefix step. -/
structure StageSideCoverData (D : ReducedTorusCircleStageGeometry Phi) where
  cover : ∀ (hzero : D.toReducedTorusCircleStageSequence.AllInessential)
    (k : ℕ) (hk : k < D.length),
    ReducedCircleStageSideCover
      (D.circleFamily k)
      (D.circleFamily_allInessential hzero k (Nat.le_of_lt hk))
      (D.circleFamily (k + 1))
      (D.circleFamily_allInessential hzero (k + 1) hk)
      (D.parityStage k) (D.parityStage (k + 1))

namespace StageSideCoverData

variable {D : ReducedTorusCircleStageGeometry Phi}

/-- The stage-sided covers form the reduced inessential transition sequence. -/
def toReducedInessentialParityTransitionSequence
    (C : D.StageSideCoverData)
    (hzero : D.toReducedTorusCircleStageSequence.AllInessential) :
    ReducedInessentialParityTransitionSequence Phi where
  length := D.length
  stage := D.parityStage
  transition k hk := (C.cover hzero k hk).toReducedInessentialParityTransition

@[simp] theorem toReducedInessentialParityTransitionSequence_stage
    (C : D.StageSideCoverData)
    (hzero : D.toReducedTorusCircleStageSequence.AllInessential) (k : ℕ) :
    (C.toReducedInessentialParityTransitionSequence hzero).stage k = D.parityStage k :=
  rfl

@[simp] theorem toReducedInessentialParityTransitionSequence_length
    (C : D.StageSideCoverData)
    (hzero : D.toReducedTorusCircleStageSequence.AllInessential) :
    (C.toReducedInessentialParityTransitionSequence hzero).length = D.length :=
  rfl

end StageSideCoverData

/-- Terminal child cells complete the all-inessential reduced resolution. -/
structure StageSideCoverResolutionData
    (D : ReducedTorusCircleStageGeometry Phi)
    (lower upper : Set (transportedTorus Phi)) where
  covers : D.StageSideCoverData
  terminal : TerminalTwoSphereCoreCells (D.parityStage D.length).inside
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper

namespace StageSideCoverResolutionData

variable {D : ReducedTorusCircleStageGeometry Phi}
  {lower upper : Set (transportedTorus Phi)}

/-- Stage-sided covers and the terminal partition give the exact reduced resolution. -/
def toReducedAllInessentialResolution
    (C : D.StageSideCoverResolutionData lower upper)
    (hzero : D.toReducedTorusCircleStageSequence.AllInessential) :
    ReducedAllInessentialResolution
      D.toReducedTorusCircleStageSequence lower upper where
  paritySequence := C.covers.toReducedInessentialParityTransitionSequence hzero
  length_eq := rfl
  stage_eq := by
    intro k _hk
    rfl
  terminal := C.terminal
  terminal_lower_eq := C.terminal_lower_eq
  terminal_upper_eq := C.terminal_upper_eq

end StageSideCoverResolutionData
end ReducedTorusCircleStageGeometry
end Submission.Topology
