import Submission.Topology.SuperellipsoidFiniteStageAxisCharging
import Submission.Topology.ResolvedStageLogicalAdapters

/-!
# The axis alternative from torus parity stages

The charged-axis branch uses only the finite winding circles at each stage.  The all-inessential
branch uses only the torus boundary, its two open parity cells, and the canonical disk-pushout
core.  This module removes the unused ambient sphere family from that logical alternative.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- A regular parity partition recorded entirely on the transported torus. -/
structure ReducedTorusParityStage (Phi : AmbientIsotopy) where
  boundary : Set (transportedTorus Phi)
  inside : Set (transportedTorus Phi)
  outside : Set (transportedTorus Phi)
  isOpen_inside : IsOpen inside
  isOpen_outside : IsOpen outside
  inside_disjoint_outside : Disjoint inside outside
  surface_partition : Set.univ = inside ∪ outside ∪ boundary

namespace ReducedTorusParityStage

/-- An open torus region with its exact frontier gives a reduced parity stage. -/
def ofOpenRegion
    (Phi : AmbientIsotopy) (region boundary : Set (transportedTorus Phi))
    (isOpen_region : IsOpen region) (boundary_eq : boundary = frontier region) :
    ReducedTorusParityStage Phi where
  boundary := boundary
  inside := region
  outside := (closure region)ᶜ
  isOpen_inside := isOpen_region
  isOpen_outside := isClosed_closure.isOpen_compl
  inside_disjoint_outside := by
    rw [Set.disjoint_left]
    intro x hxInside hxOutside
    exact hxOutside (subset_closure hxInside)
  surface_partition := by
    rw [boundary_eq]
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_compl_iff]
    by_cases hxRegion : x ∈ region
    · exact Or.inl (Or.inl hxRegion)
    · by_cases hxClosure : x ∈ closure region
      · right
        rw [isOpen_region.frontier_eq]
        exact ⟨hxClosure, hxRegion⟩
      · exact Or.inl (Or.inr hxClosure)

end ReducedTorusParityStage

namespace PairedBandMovingSphereCollarData.RegularSphereFamilyParityStage

/-- Forget the unused ambient realization of an existing sphere-family parity stage. -/
def toReducedTorusParityStage
    (S : RegularSphereFamilyParityStage Phi) : ReducedTorusParityStage Phi where
  boundary := transportedTorusPart Phi S.sphereFamily.carrier
  inside := S.inside
  outside := S.outside
  isOpen_inside := S.isOpen_inside
  isOpen_outside := S.isOpen_outside
  inside_disjoint_outside := S.inside_disjoint_outside
  surface_partition := S.surface_partition

end PairedBandMovingSphereCollarData.RegularSphereFamilyParityStage

namespace FiniteEmbeddedTorusCircleSection

/-- An exact finite section and a torus region with that frontier form a reduced stage. -/
def toReducedTorusParityStage
    {ambientSection : Set R3} {ι : Type*} [Fintype ι]
    (_S : FiniteEmbeddedTorusCircleSection Phi ambientSection ι)
    (region : Set (transportedTorus Phi)) (isOpen_region : IsOpen region)
    (frontier_eq : frontier region = transportedTorusPart Phi ambientSection) :
    ReducedTorusParityStage Phi :=
  ReducedTorusParityStage.ofOpenRegion Phi region
    (transportedTorusPart Phi ambientSection) isOpen_region frontier_eq.symm

end FiniteEmbeddedTorusCircleSection

/-- The exact canonical-disk consequences used by one all-inessential transition. -/
structure ReducedInessentialTorusCoreData (Phi : AmbientIsotopy) where
  diskUnion : Set (transportedTorus Phi)
  diskComplement : Set (transportedTorus Phi)
  diskComplement_eq : diskComplement = diskUnionᶜ
  complement_isConnected : IsConnected diskComplement
  complement_carries : CarriesBasedLoopTorusGenus Phi diskComplement
  loop_zero_of_range_subset_diskUnion :
    ∀ {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s),
      Set.range L.curve ⊆ diskUnion → L.windingPair = (0, 0)

namespace ReducedInessentialTorusCoreData

/-- Any existing maximal-disk pushout realizes the reduced core interface. -/
def ofMaximalSystem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData) : ReducedInessentialTorusCoreData Phi where
  diskUnion := M.diskUnion
  diskComplement := M.diskComplement
  diskComplement_eq := rfl
  complement_isConnected :=
    MaximalInessentialTorusDiskFamily.ConnectedPushoutData.complement_isConnected M P
  complement_carries := carriesBasedLoopTorusGenus_of_finitePuncturePushout P.pushout
  loop_zero_of_range_subset_diskUnion := by
    intro s L hsub
    obtain ⟨i, _hi, hdisk⟩ := M.connected_range_subset_one_maximalDisk L hsub
    exact S.windingPair_eq_zero_of_range_subset_torusDisk i L hdisk

/-- The canonical maximal-disk construction realizes the reduced core interface. -/
def ofFiniteSphereSystem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) : ReducedInessentialTorusCoreData Phi :=
  ofMaximalSystem S hzero (S.canonicalMaximalInessentialTorusDiskFamily hzero)
    (MaximalInessentialTorusDiskFamily.canonicalConnectedPushoutData S hzero)

end ReducedInessentialTorusCoreData

/-- One disk-localized transition between reduced torus parity stages. -/
structure ReducedInessentialParityTransition
    (pre post : ReducedTorusParityStage Phi) where
  core : ReducedInessentialTorusCoreData Phi
  support : Set (transportedTorus Phi)
  support_subset_diskUnion : support ⊆ core.diskUnion
  boundaries_subset_support : pre.boundary ∪ post.boundary ⊆ support
  labelChange_subset_support :
    {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆ support

namespace ReducedInessentialParityTransition

variable {pre post : ReducedTorusParityStage Phi}

theorem core_disjoint_support (T : ReducedInessentialParityTransition pre post) :
    Disjoint T.core.diskComplement T.support := by
  rw [Set.disjoint_left]
  intro x hxCore hxSupport
  rw [T.core.diskComplement_eq] at hxCore
  exact hxCore (T.support_subset_diskUnion hxSupport)

theorem preBoundary_subset_diskUnion
    (T : ReducedInessentialParityTransition pre post) :
    pre.boundary ⊆ T.core.diskUnion := by
  intro x hx
  exact T.support_subset_diskUnion (T.boundaries_subset_support (Or.inl hx))

theorem core_subset_preInside_or_outside
    (T : ReducedInessentialParityTransition pre post) :
    T.core.diskComplement ⊆ pre.inside ∨
      T.core.diskComplement ⊆ pre.outside := by
  have hsubset : T.core.diskComplement ⊆ pre.inside ∪ pre.outside := by
    intro x hxCore
    have hxUniv : x ∈ (Set.univ : Set (transportedTorus Phi)) := Set.mem_univ x
    rw [pre.surface_partition] at hxUniv
    rcases hxUniv with hxCell | hxBoundary
    · exact hxCell
    · rw [T.core.diskComplement_eq] at hxCore
      exact (hxCore (T.preBoundary_subset_diskUnion hxBoundary)).elim
  exact T.core.complement_isConnected.isPreconnected
    |>.subset_or_subset pre.isOpen_inside pre.isOpen_outside
      pre.inside_disjoint_outside hsubset

theorem not_core_subset_preOutside_of_carrier
    (T : ReducedInessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    ¬ T.core.diskComplement ⊆ pre.outside := by
  intro hOutside
  have hInsideDisk : pre.inside ⊆ T.core.diskUnion := by
    intro x hxInside
    by_contra hxDisk
    have hxCore : x ∈ T.core.diskComplement := by
      rw [T.core.diskComplement_eq]
      exact hxDisk
    exact Set.disjoint_left.mp pre.inside_disjoint_outside hxInside (hOutside hxCore)
  obtain ⟨W⟩ := hpre
  have hFirstRange : Set.range W.first.curve ⊆ T.core.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hInsideDisk (W.first.curve_mem t)
  have hSecondRange : Set.range W.second.curve ⊆ T.core.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hInsideDisk (W.second.curve_mem t)
  have hFirstZero := T.core.loop_zero_of_range_subset_diskUnion W.first hFirstRange
  have hSecondZero := T.core.loop_zero_of_range_subset_diskUnion W.second hSecondRange
  have hindependent := W.independent
  rw [hFirstZero, hSecondZero] at hindependent
  exact hindependent (by simp [windingDet])

theorem core_subset_preInside
    (T : ReducedInessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    T.core.diskComplement ⊆ pre.inside := by
  rcases T.core_subset_preInside_or_outside with hInside | hOutside
  · exact hInside
  · exact False.elim (T.not_core_subset_preOutside_of_carrier hpre hOutside)

theorem core_inside_agree
    (T : ReducedInessentialParityTransition pre post)
    (x : transportedTorus Phi) (hxCore : x ∈ T.core.diskComplement) :
    x ∈ pre.inside ↔ x ∈ post.inside := by
  by_cases hpre : x ∈ pre.inside <;> by_cases hpost : x ∈ post.inside
  · exact iff_of_true hpre hpost
  · exact False.elim <| Set.disjoint_left.mp T.core_disjoint_support hxCore
      (T.labelChange_subset_support (by simp [hpre, hpost]))
  · exact False.elim <| Set.disjoint_left.mp T.core_disjoint_support hxCore
      (T.labelChange_subset_support (by simp [hpre, hpost]))
  · exact iff_of_false hpre hpost

theorem carries_post
    (T : ReducedInessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    CarriesBasedLoopTorusGenus Phi post.inside := by
  apply T.core.complement_carries.mono
  intro x hxCore
  exact (T.core_inside_agree x hxCore).mp (T.core_subset_preInside hpre hxCore)

end ReducedInessentialParityTransition

namespace PairedBandMovingSphereCollarData.InessentialParityTransition

/-- Forgetting ambient sphere data sends the existing transition to the reduced interface. -/
def toReducedInessentialParityTransition
    {pre post : RegularSphereFamilyParityStage Phi}
    (T : InessentialParityTransition pre post) :
    ReducedInessentialParityTransition pre.toReducedTorusParityStage
      post.toReducedTorusParityStage where
  core := ReducedInessentialTorusCoreData.ofMaximalSystem
    T.coreSystem T.coreAllInessential T.maximal T.pushout
  support := transportedTorusPart Phi T.support
  support_subset_diskUnion := T.diskCover.supportPart_subset_diskUnion
  boundaries_subset_support := T.boundaries_subset_support
  labelChange_subset_support := T.labelChange_subset_support

end PairedBandMovingSphereCollarData.InessentialParityTransition

/-- A finite sequence of reduced all-inessential parity transitions. -/
structure ReducedInessentialParityTransitionSequence (Phi : AmbientIsotopy) where
  length : ℕ
  stage : ℕ → ReducedTorusParityStage Phi
  transition : ∀ k, k < length →
    ReducedInessentialParityTransition (stage k) (stage (k + 1))

namespace ReducedInessentialParityTransitionSequence

theorem carries_stage
    (F : ReducedInessentialParityTransitionSequence Phi)
    (hzero : CarriesBasedLoopTorusGenus Phi (F.stage 0).inside) :
    ∀ k, k ≤ F.length → CarriesBasedLoopTorusGenus Phi (F.stage k).inside := by
  intro k hk
  induction k with
  | zero => exact hzero
  | succ k ih =>
      exact (F.transition k (Nat.lt_of_succ_le hk)).carries_post
        (ih (Nat.le_of_lt (Nat.lt_of_succ_le hk)))

theorem carries_terminal
    (F : ReducedInessentialParityTransitionSequence Phi)
    (hzero : CarriesBasedLoopTorusGenus Phi (F.stage 0).inside) :
    CarriesBasedLoopTorusGenus Phi (F.stage F.length).inside :=
  F.carries_stage hzero F.length le_rfl

end ReducedInessentialParityTransitionSequence

/-- Finite winding-circle stages for the reduced charged-axis alternative. -/
structure ReducedTorusCircleStageSequence (Phi : AmbientIsotopy) where
  length : ℕ
  circleCount : ℕ → ℕ
  circle : ∀ k, Fin (circleCount k) → EmbeddedTorusIntersectionCircle Phi
  parityStage : ℕ → ReducedTorusParityStage Phi

namespace ReducedTorusCircleStageSequence

def AllInessential (F : ReducedTorusCircleStageSequence Phi) : Prop :=
  ∀ k, k ≤ F.length → ∀ i, (F.circle k i).windingLoop.windingPair = (0, 0)

def HasAxisCircleIfEssential (F : ReducedTorusCircleStageSequence Phi) : Prop :=
  ∀ k, k ≤ F.length →
    (∃ i, (F.circle k i).Essential) →
      ∃ i, IsNonzeroAxisSlope
        (F.circle k i).windingLoop.lift.first.winding
        (F.circle k i).windingLoop.lift.second.winding

end ReducedTorusCircleStageSequence

/-- The reduced all-inessential sequence ends in two disjoint open child cells. -/
structure ReducedAllInessentialResolution
    (F : ReducedTorusCircleStageSequence Phi)
    (lower upper : Set (transportedTorus Phi)) where
  paritySequence : ReducedInessentialParityTransitionSequence Phi
  length_eq : paritySequence.length = F.length
  stage_eq : ∀ k, k ≤ F.length → paritySequence.stage k = F.parityStage k
  terminal : TerminalTwoSphereCoreCells (paritySequence.stage paritySequence.length).inside
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper

namespace ReducedTorusCircleStageSequence

/-- Charged axis circles or an all-inessential reduced parity sequence reach a terminal child. -/
theorem carries_terminalChild_of_axisCharging
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (F : ReducedTorusCircleStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (axisCircle : F.HasAxisCircleIfEssential)
    (chargingTransport : ∀ k, k ≤ F.length → ∀ i,
      (F.circle k i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi (F.circle k i).windingLoop.curve)
          (F.circle k i).windingLoop.lift.first.winding
          (F.circle k i).windingLoop.lift.second.winding)
    (inessentialResolution : F.AllInessential →
      Nonempty (ReducedAllInessentialResolution F lower upper))
    (hparent : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside)
    (hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    CarriesBasedLoopTorusGenus Phi lower ∨
      CarriesBasedLoopTorusGenus Phi upper := by
  classical
  by_cases hessential : ∃ k, k ≤ F.length ∧ ∃ i, (F.circle k i).Essential
  · obtain ⟨k, hk, hstage⟩ := hessential
    obtain ⟨i, haxis⟩ := axisCircle k hk hstage
    have hi : (F.circle k i).Essential := haxis.2
    let T := chargingTransport k hk i hi
    let A : SuperellipsoidDoubleBubbleSelection.ChargedAxisLoop selection p q := {
      loop := transportedLoopCoordinates Phi (F.circle k i).windingLoop.curve
      firstWinding := (F.circle k i).windingLoop.lift.first.winding
      secondWinding := (F.circle k i).windingLoop.lift.second.winding
      axis := haxis
      certificate := T.targetCertificate
      charging := T.targetCharging
    }
    exact False.elim <|
      selection.no_chargedAxisLoop_of_distortion_lt p q hcontra ⟨A⟩
  · have hzero : F.AllInessential := by
      intro k hk i
      have hi : ¬ (F.circle k i).Essential := fun hi ↦
        hessential ⟨k, hk, i, hi⟩
      exact not_ne_iff.mp (show
        ¬ (F.circle k i).windingLoop.windingPair ≠ (0, 0) from hi)
    obtain ⟨D⟩ := inessentialResolution hzero
    have hInitial : CarriesBasedLoopTorusGenus Phi
        (D.paritySequence.stage 0).inside := by
      rw [D.stage_eq 0 (Nat.zero_le F.length)]
      exact hparent
    have hterminal := D.paritySequence.carries_terminal hInitial
    have hchildren := D.terminal.carries_lower_or_upper_of_carries_inside hterminal
    rwa [D.terminal_lower_eq, D.terminal_upper_eq] at hchildren

end ReducedTorusCircleStageSequence
end Submission.Topology
