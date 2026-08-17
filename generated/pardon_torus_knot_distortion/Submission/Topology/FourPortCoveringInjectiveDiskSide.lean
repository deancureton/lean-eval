import Submission.Topology.CoveringInjectiveCarrier
import Submission.Topology.DiskLocalizedParityTransition
import Submission.Topology.FourPortEndpointCollarPush

/-!
# Covering-injective four-port traces give disk-sided transitions

The collar-pushed four-port trace is a regular closed three-boundary carrier.  If it lies in the
projection of one covering-injective open plane set, the covering lift forces every trace loop to
have zero winding.  The canonical outer-disk theorem therefore places the entire trace, and in
particular the parity-change locus, in one of its three canonical disks.

The final conversion to `FiniteElementaryDiskSideCover` needs only explicit index attachment:
the chosen trace circle must name a maximal circle of the relevant endpoint system, its canonical
disk must be that system disk, and the new endpoint boundary must be inherited away from the
trace.  These are kept as geometric fields rather than hidden in a homology premise.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}

namespace FourPortEndpointCollarPushData

/-- The collar-augmented trace is regular closed: its carrier is literally the closure of its
open interior. -/
theorem traceRegularClosedCarrierData
    (D : FourPortEndpointCollarPushData raw)
    (A : D.GlobalTraceAttachment) :
    ThreeBoundaryRegularClosedCarrierData
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier where
  interior_isOpen := A.isOpen
  carrier_isClosed := isClosed_closure

/-- A covering-injective neighborhood of the whole collar trace gives one canonical disk
containing that trace, with no pair-of-pants homology premise. -/
theorem exists_canonicalDisk_contains_trace_of_coveringInjective
    (D : FourPortEndpointCollarPushData raw)
    (A : D.GlobalTraceAttachment)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (htrace : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ∃ i, (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier.disk i := by
  let P := D.toEmbeddedPairOfPantsTrace A
  exact (D.traceRegularClosedCarrierData A)
    |>.exists_canonicalDisk_contains_carrier_of_subset_coveringProjection_image
      U hU hinj htrace

/-- Consequently one canonical trace disk contains the exact parity-label change locus. -/
theorem exists_canonicalDisk_covers_labelChange_of_coveringInjective
    (D : FourPortEndpointCollarPushData raw)
    (A : D.GlobalTraceAttachment)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (htrace : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ∃ i, regularStageLabelChangeLocus pre post ⊆
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier.disk i := by
  obtain ⟨i, hi⟩ :=
    D.exists_canonicalDisk_contains_trace_of_coveringInjective A U hU hinj htrace
  exact ⟨i, (D.toEmbeddedPairOfPantsTrace A).labelChangeLocus_subset_carrier.trans hi⟩

end FourPortEndpointCollarPushData

/-! ## Exact attachment to one endpoint system -/

/-- Index and outside-attachment data identifying the three trace disks with disks of one
endpoint intersection system.

For a pre-sided cover use `postBoundary_subset_pre_union_trace`; for a post-sided cover use its
reverse analogue.  In a concrete four-port stage these follow from outside agreement together
with inclusion of the raw collar endpoints in the closed collar trace. -/
structure FourPortTraceSystemDiskIndexAttachment
    {circleCount : ℕ}
    (D : FourPortEndpointCollarPushData raw)
    (A : D.GlobalTraceAttachment)
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount))
    (hzero : S.AllInessential) where
  traceToSystemIndex : Fin 3 → Fin circleCount
  traceToSystemIndex_mem : ∀ i,
    traceToSystemIndex i ∈
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).maximal
  systemDisk_eq_traceDisk : ∀ i,
    Set.range (S.torusDiskMap hzero (traceToSystemIndex i)) =
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier.disk i
  rawPreAffectedBoundary_subset_trace : raw.preAffectedBoundary ⊆
    (D.toEmbeddedPairOfPantsTrace A).carrier
  rawPostAffectedBoundary_subset_trace : raw.postAffectedBoundary ⊆
    (D.toEmbeddedPairOfPantsTrace A).carrier

namespace FourPortTraceSystemDiskIndexAttachment

variable {circleCount : ℕ}
  {D : FourPortEndpointCollarPushData raw}
  {A : D.GlobalTraceAttachment}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}

/-- Outside agreement plus inclusion of the raw post endpoint in the closed trace gives the
forward boundary-attachment statement used by the disk-side cover. -/
theorem postBoundary_subset_pre_union_trace
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero) :
    regularStageTorusBoundary post ⊆
      regularStageTorusBoundary pre ∪ (D.toEmbeddedPairOfPantsTrace A).carrier := by
  intro x hx
  rw [raw.postBoundary_exact] at hx
  rcases hx with hxUnaffected | hxAffected
  · exact Or.inl (by rw [raw.preBoundary_exact]; exact Or.inl hxUnaffected)
  · exact Or.inr (I.rawPostAffectedBoundary_subset_trace hxAffected)

/-- The analogous reverse boundary-attachment statement. -/
theorem preBoundary_subset_post_union_trace
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero) :
    regularStageTorusBoundary pre ⊆
      regularStageTorusBoundary post ∪ (D.toEmbeddedPairOfPantsTrace A).carrier := by
  intro x hx
  rw [raw.preBoundary_exact] at hx
  rcases hx with hxUnaffected | hxAffected
  · exact Or.inl (by rw [raw.postBoundary_exact]; exact Or.inl hxUnaffected)
  · exact Or.inr (I.rawPreAffectedBoundary_subset_trace hxAffected)

/-- A chosen trace disk containing the trace produces the forward, pre-system-sided elementary
disk cover. -/
def toForwardFiniteElementaryDiskSideCover
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero)
    (i : Fin 3)
    (hi : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier.disk i) :
    FiniteElementaryDiskSideCover S hzero pre post where
  moveCount := 1
  newBoundaryPatch := fun _ ↦ (D.toEmbeddedPairOfPantsTrace A).carrier
  changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
  diskIndex := fun _ ↦ I.traceToSystemIndex i
  diskIndex_mem := fun _ ↦ I.traceToSystemIndex_mem i
  newBoundaryPatch_subset_disk := by
    intro _ x hx
    rw [I.systemDisk_eq_traceDisk i]
    exact hi hx
  changedLens_subset_disk := by
    intro _ x hx
    rw [I.systemDisk_eq_traceDisk i]
    exact hi ((D.toEmbeddedPairOfPantsTrace A).labelChangeLocus_subset_carrier hx)
  postBoundary_subset := by
    intro x hx
    rcases I.postBoundary_subset_pre_union_trace hx with hxPre | hxTrace
    · exact Or.inl hxPre
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxTrace⟩)
  labelChange_subset := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- The same chosen disk produces the reverse, post-system-sided elementary disk cover. -/
def toReverseFiniteElementaryDiskSideCover
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero)
    (i : Fin 3)
    (hi : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      (D.toEmbeddedPairOfPantsTrace A).toThreeBoundaryPairOfPantsCarrier.disk i) :
    FiniteElementaryDiskSideCover S hzero post pre where
  moveCount := 1
  newBoundaryPatch := fun _ ↦ (D.toEmbeddedPairOfPantsTrace A).carrier
  changedLens := fun _ ↦ regularStageLabelChangeLocus pre post
  diskIndex := fun _ ↦ I.traceToSystemIndex i
  diskIndex_mem := fun _ ↦ I.traceToSystemIndex_mem i
  newBoundaryPatch_subset_disk := by
    intro _ x hx
    rw [I.systemDisk_eq_traceDisk i]
    exact hi hx
  changedLens_subset_disk := by
    intro _ x hx
    rw [I.systemDisk_eq_traceDisk i]
    exact hi ((D.toEmbeddedPairOfPantsTrace A).labelChangeLocus_subset_carrier hx)
  postBoundary_subset := by
    intro x hx
    rcases I.preBoundary_subset_post_union_trace hx with hxPost | hxTrace
    · exact Or.inl hxPost
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, hxTrace⟩)
  labelChange_subset := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, fun h ↦ hx h.symm⟩

/-- Covering-injectivity chooses the forward disk-sided move once the trace circles are indexed
in the pre-stage system. -/
theorem exists_forwardFiniteElementaryDiskSideCover_of_coveringInjective
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (htrace : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    Nonempty (FiniteElementaryDiskSideCover S hzero pre post) := by
  obtain ⟨i, hi⟩ :=
    D.exists_canonicalDisk_contains_trace_of_coveringInjective A U hU hinj htrace
  exact ⟨I.toForwardFiniteElementaryDiskSideCover i hi⟩

/-- Covering-injectivity chooses the reverse disk-sided move when the trace circles are indexed
in the post-stage system. -/
theorem exists_reverseFiniteElementaryDiskSideCover_of_coveringInjective
    (I : FourPortTraceSystemDiskIndexAttachment D A S hzero)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (htrace : (D.toEmbeddedPairOfPantsTrace A).carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    Nonempty (FiniteElementaryDiskSideCover S hzero post pre) := by
  obtain ⟨i, hi⟩ :=
    D.exists_canonicalDisk_contains_trace_of_coveringInjective A U hU hinj htrace
  exact ⟨I.toReverseFiniteElementaryDiskSideCover i hi⟩

end FourPortTraceSystemDiskIndexAttachment

end Submission.Topology
