import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.SuperellipsoidThreePageAttachment

/-!
# Parity transitions localized directly in inessential torus disks

The open ambient neighborhood used to construct a local four-port smoothing is usually larger
than the part of the transported torus whose parity label actually changes.  Requiring the whole
open band to lie in a maximal inessential torus disk is generally too strong: near a boundary arc
the open band meets both local sides of that disk.

The parity argument only needs the connected rank-two core to miss three subsets: the two endpoint
boundaries and the locus on which the inside labels differ.  This file packages the smallest
direct constructor of `InessentialParityTransition` from those three disk-union containments.  Its
ambient support is simply the ambient image of their union; no openness is needed by the abstract
transition.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- Regard a transported-torus subset as an ambient subset of `R3`. -/
def transportedTorusAmbientImage
    (s : Set (transportedTorus Phi)) : Set R3 :=
  ((fun x : transportedTorus Phi ↦ (x : R3)) '' s)

@[simp] theorem mem_transportedTorusPart_ambientImage_iff
    {s : Set (transportedTorus Phi)} {x : transportedTorus Phi} :
    x ∈ transportedTorusPart Phi (transportedTorusAmbientImage s) ↔ x ∈ s := by
  constructor
  · rintro ⟨y, hy, hval⟩
    have hxy : x = y := Subtype.ext hval.symm
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The exact transported-torus locus which a parity transition must remove from its core. -/
def diskLocalizedParityLocus
    (pre post : RegularSphereFamilyParityStage Phi) :
    Set (transportedTorus Phi) :=
  transportedTorusPart Phi pre.sphereFamily.carrier ∪
    transportedTorusPart Phi post.sphereFamily.carrier ∪
      {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)}

/-- Use the ambient image of the exact parity locus as the abstract transition support. -/
def diskLocalizedParitySupport
    (pre post : RegularSphereFamilyParityStage Phi) : Set R3 :=
  transportedTorusAmbientImage (diskLocalizedParityLocus pre post)

namespace InessentialParityTransition

variable {pre post : RegularSphereFamilyParityStage Phi}
  {circleCount : ℕ}
  (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount))
  (hzero : S.AllInessential)

/-- Construct the parity transition from containment of exactly the endpoint boundaries and
label-change locus in the canonical maximal disk union. -/
def ofDiskLocalizedChange
    (hpre : transportedTorusPart Phi pre.sphereFamily.carrier ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion)
    (hpost : transportedTorusPart Phi post.sphereFamily.carrier ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion)
    (hchange : {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion) :
    InessentialParityTransition pre post where
  coreCircleCount := circleCount
  coreSystem := S
  coreAllInessential := hzero
  maximal := S.canonicalMaximalInessentialTorusDiskFamily hzero
  pushout := MaximalInessentialTorusDiskFamily.canonicalConnectedPushoutData S hzero
  support := diskLocalizedParitySupport pre post
  diskCover := InessentialBandDiskCover.ofSubsetDiskUnion <| by
    intro x hx
    rw [diskLocalizedParitySupport,
      mem_transportedTorusPart_ambientImage_iff] at hx
    rcases hx with hxBoundary | hxChange
    · rcases hxBoundary with hxPre | hxPost
      · exact hpre hxPre
      · exact hpost hxPost
    · exact hchange hxChange
  boundaries_subset_support := by
    intro x hx
    rw [diskLocalizedParitySupport,
      mem_transportedTorusPart_ambientImage_iff]
    rcases hx with hxPre | hxPost
    · exact Or.inl (Or.inl hxPre)
    · exact Or.inl (Or.inr hxPost)
  labelChange_subset_support := by
    intro x hx
    rw [diskLocalizedParitySupport,
      mem_transportedTorusPart_ambientImage_iff]
    exact Or.inr hx

end InessentialParityTransition

/-! ## Finite elementary disk-side covers -/

/-- The exact nesting data for finitely many elementary four-port moves.  For each move, the
new boundary patch and the parity-changing lens lie in one selected maximal pre-stage disk.
Everything else on the post boundary is inherited from the pre boundary.

This is strictly weaker than putting an ambient-open four-port support in that disk. -/
structure FiniteElementaryDiskSideCover
    {circleCount : ℕ}
    (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount))
    (hzero : S.AllInessential)
    (pre post : RegularSphereFamilyParityStage Phi) where
  moveCount : ℕ
  newBoundaryPatch : Fin moveCount → Set (transportedTorus Phi)
  changedLens : Fin moveCount → Set (transportedTorus Phi)
  diskIndex : Fin moveCount → Fin circleCount
  diskIndex_mem : ∀ b,
    diskIndex b ∈ (S.canonicalMaximalInessentialTorusDiskFamily hzero).maximal
  newBoundaryPatch_subset_disk : ∀ b, newBoundaryPatch b ⊆
    Set.range (S.torusDiskMap hzero (diskIndex b))
  changedLens_subset_disk : ∀ b, changedLens b ⊆
    Set.range (S.torusDiskMap hzero (diskIndex b))
  postBoundary_subset : transportedTorusPart Phi post.sphereFamily.carrier ⊆
    transportedTorusPart Phi pre.sphereFamily.carrier ∪
      ⋃ b, newBoundaryPatch b
  labelChange_subset : {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
    ⋃ b, changedLens b

namespace FiniteElementaryDiskSideCover

variable {pre post : RegularSphereFamilyParityStage Phi}
  {circleCount : ℕ}
  {S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount)}
  {hzero : S.AllInessential}

theorem newBoundaryPatch_subset_diskUnion
    (C : FiniteElementaryDiskSideCover S hzero pre post) (b : Fin C.moveCount) :
    C.newBoundaryPatch b ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨C.diskIndex b,
    Set.mem_iUnion.mpr ⟨C.diskIndex_mem b, C.newBoundaryPatch_subset_disk b hx⟩⟩

theorem changedLens_subset_diskUnion
    (C : FiniteElementaryDiskSideCover S hzero pre post) (b : Fin C.moveCount) :
    C.changedLens b ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨C.diskIndex b,
    Set.mem_iUnion.mpr ⟨C.diskIndex_mem b, C.changedLens_subset_disk b hx⟩⟩

theorem preBoundary_subset_diskUnion
    (_C : FiniteElementaryDiskSideCover S hzero pre post)
    (hsphere : S.sphereFamily = pre.sphereFamily) :
    transportedTorusPart Phi pre.sphereFamily.carrier ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion := by
  intro x hx
  apply MaximalInessentialTorusDiskFamily.sphereFamilyPart_subset_diskUnion
  rw [hsphere]
  exact hx

theorem postBoundary_subset_diskUnion
    (C : FiniteElementaryDiskSideCover S hzero pre post)
    (hsphere : S.sphereFamily = pre.sphereFamily) :
    transportedTorusPart Phi post.sphereFamily.carrier ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion := by
  intro x hx
  rcases C.postBoundary_subset hx with hxPre | hxPatch
  · exact C.preBoundary_subset_diskUnion hsphere hxPre
  · simp only [Set.mem_iUnion] at hxPatch
    obtain ⟨b, hb⟩ := hxPatch
    exact C.newBoundaryPatch_subset_diskUnion b hb

theorem labelChange_subset_diskUnion
    (C : FiniteElementaryDiskSideCover S hzero pre post) :
    {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion := by
  intro x hx
  have hxLens := C.labelChange_subset hx
  simp only [Set.mem_iUnion] at hxLens
  obtain ⟨b, hb⟩ := hxLens
  exact C.changedLens_subset_diskUnion b hb

/-- A finite family of one-sided disk-contained four-port moves gives the parity transition. -/
def toInessentialParityTransition
    (C : FiniteElementaryDiskSideCover S hzero pre post)
    (hsphere : S.sphereFamily = pre.sphereFamily) :
    InessentialParityTransition pre post :=
  InessentialParityTransition.ofDiskLocalizedChange S hzero
    (C.preBoundary_subset_diskUnion hsphere)
    (C.postBoundary_subset_diskUnion hsphere)
    C.labelChange_subset_diskUnion

/-- The same disk-side cover can be used in the opposite stage direction.  This is needed when
the outermost disk containing a pair-of-pants trace belongs to the post stage. -/
def toReverseInessentialParityTransition
    (C : FiniteElementaryDiskSideCover S hzero post pre)
    (hsphere : S.sphereFamily = post.sphereFamily) :
    InessentialParityTransition pre post :=
  InessentialParityTransition.ofDiskLocalizedChange S hzero
    (C.postBoundary_subset_diskUnion hsphere)
    (C.preBoundary_subset_diskUnion hsphere) (by
      intro x hx
      apply C.labelChange_subset_diskUnion
      exact fun h ↦ hx h.symm)

end FiniteElementaryDiskSideCover

/-! ## Stage-sided finite ordering -/

/-- At each elementary move, the disk containing the local pair-of-pants trace may belong to
either endpoint stage.  A sequential ordering records that choice after all intermediate stages
have been included in the essential-circle audit. -/
structure FiniteStageSideDiskCoverData
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : F.AllInessential) where
  cover : ∀ k (hk : k < F.length),
    (FiniteElementaryDiskSideCover (F.system k) (hzero k (Nat.le_of_lt hk))
      (F.parityStage k) (F.parityStage (k + 1))) ⊕
    (FiniteElementaryDiskSideCover (F.system (k + 1))
      (hzero (k + 1) hk)
      (F.parityStage (k + 1)) (F.parityStage k))

namespace FiniteStageSideDiskCoverData

variable {F : FiniteRegularSphereSurgeryStageSequence Phi}
  {hzero : F.AllInessential}

/-- Heterogeneous pre- or post-sided disk covers construct the parity sequence used by finite
induction. -/
def toFiniteInessentialParityTransitionSequence
    (D : FiniteStageSideDiskCoverData F hzero) :
    FiniteInessentialParityTransitionSequence Phi where
  length := F.length
  stage := F.parityStage
  transition := by
    intro k hk
    rcases D.cover k hk with C | C
    · exact C.toInessentialParityTransition (F.sphereFamily_eq k)
    · exact C.toReverseInessentialParityTransition
        (F.sphereFamily_eq (k + 1))

end FiniteStageSideDiskCoverData

/-! ## Direct use for the explicit global neck pinch -/

namespace SuperellipsoidGlobalNeckPinchRoundingData

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ} {hR : 0 < R}
  (rounding : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR)
  {circleCount : ℕ}
  (S : FiniteSphereSurgeryIntersectionSystem Phi (Fin circleCount))
  (hzero : S.AllInessential)

/-- Construct the global parity transition without covering the entire declared ambient neck.
The remaining geometric statements concern only the new boundary and the actual label-change
locus.  The old outer boundary is covered automatically by exact intersection and all-
inessentiality. -/
def toInessentialParityTransitionOfDiskLocalizedChange
    (hsphere : S.sphereFamily =
      (initialOuterSuperellipsoidParityStage Phi frame c hR).sphereFamily)
    (hpost : transportedTorusPart Phi
        (rounding.postStage (Phi := Phi)).sphereFamily.carrier ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion)
    (hchange : {x |
        (x ∈ (initialOuterSuperellipsoidParityStage Phi frame c hR).inside) ≠
          (x ∈ (rounding.postStage (Phi := Phi)).inside)} ⊆
      (S.canonicalMaximalInessentialTorusDiskFamily hzero).diskUnion) :
    InessentialParityTransition
      (initialOuterSuperellipsoidParityStage Phi frame c hR)
      (rounding.postStage (Phi := Phi)) :=
  InessentialParityTransition.ofDiskLocalizedChange S hzero (by
    intro x hx
    apply MaximalInessentialTorusDiskFamily.sphereFamilyPart_subset_diskUnion
    rw [hsphere]
    exact hx) hpost hchange

end SuperellipsoidGlobalNeckPinchRoundingData

end Submission.Topology
