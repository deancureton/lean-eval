import Submission.Topology.SuperellipsoidEventCharging
import Submission.Topology.SuperellipsoidFiniteStageAdapter

/-!
# Quantitative charging for finite regular superellipsoid stages

The older finite-stage adapter accepts an arbitrary function from an event-covered compression
to a charged compression.  That loses the stage index and hence the smooth parametrization which
produces the signed intersection certificate.  Here the essential-stage branch is resolved
before that provenance is erased: raw regular data for the selected stage circle is transported
through the surgery boundary equality and charged to the common outer/cut event region.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Torus

/-- The four raw analytic hypotheses needed by the canonical shifted intersection certificate
for an embedded transported-torus circle. -/
structure RawRegularTorusCircleData
    {Phi : AmbientIsotopy} (C : EmbeddedTorusIntersectionCircle Phi)
    (p q : ℕ) : Prop where
  contDiff_first : ContDiff ℝ 1 C.windingLoop.lift.first.angle
  contDiff_second : ContDiff ℝ 1 C.windingLoop.lift.second.angle
  regular_transformed_roots : ∀ t,
    Circle.exp (transformedSlopeAngle p q C.windingLoop.lift t) = 1 →
      deriv (transformedSlopeAngle p q C.windingLoop.lift) t ≠ 0
  coordinates_injOn : Set.InjOn
    (transportedLoopCoordinates Phi C.windingLoop.curve)
    (Ico (0 : ℝ) (2 * Real.pi))

/-- The finite-stage Pardon alternative with a quantitatively charged essential branch.  The
charged disk is constructed from the actual stage index and its raw regular data; no function
from arbitrary event-covered disks is assumed. -/
theorem finiteRegularSphereSurgery_chargedCompression_or_carries_terminalChild
    (p q : ℕ) (hc : p.Coprime q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (rawRegular : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        RawRegularTorusCircleData ((F.system k).circle i) p q)
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (hcommon : F.commonEventRegion ⊆
      superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk)
    (hparent : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside) :
    Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q selection) ∨
      CarriesBasedLoopTorusGenus Phi lower ∨
        CarriesBasedLoopTorusGenus Phi upper := by
  classical
  by_cases hessential : ∃ k, k ≤ F.length ∧
      ∃ i, ((F.system k).circle i).Essential
  · obtain ⟨k, hk, i, hi⟩ := hessential
    obtain ⟨D⟩ := essentialSurgery k hk i hi
    let R := rawRegular k hk i hi
    have hstageRegion : (F.system k).eventRegion ⊆
        superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk :=
      (F.stage_event_subset k hk).trans hcommon
    exact Or.inl <| chargedCompressionOfEssentialSphereCircleRawRegular
      selection D p q hc sigma hclass hstageRegion R.contDiff_first R.contDiff_second
        R.regular_transformed_roots R.coordinates_injOn
  · have hzero : F.AllInessential := by
      intro k hk i
      have hi : ¬ ((F.system k).circle i).Essential := fun hi ↦
        hessential ⟨k, hk, i, hi⟩
      exact not_ne_iff.mp (show
        ¬ ((F.system k).circle i).windingLoop.windingPair ≠ (0, 0) from hi)
    obtain ⟨D⟩ := inessentialResolution hzero
    have hInitial : CarriesBasedLoopTorusGenus Phi
        (D.paritySequence.stage 0).inside := by
      rw [D.stage_eq 0 (Nat.zero_le F.length)]
      exact hparent
    have hterminal := D.paritySequence.carries_terminal hInitial
    have hchildren := D.terminal.toTerminalTwoSphereCoreCells
      |>.carries_lower_or_upper_of_carries_inside hterminal
    rw [D.terminal_lower_eq, D.terminal_upper_eq] at hchildren
    exact Or.inr hchildren

/-- A finite regular sphere-surgery sequence gives the resolved superellipsoid step from raw
regular circle data and common event-region containment alone.  In particular, the quantitative
compression branch is constructed rather than supplied as a separate premise. -/
theorem SuperellipsoidResolvedDoubleBubbleStep.ofFiniteRegularSphereSurgeryRawRegular
    (p q : ℕ) (hc : p.Coprime q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (initialInside_eq : (F.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale))
    (lower_subset : lower ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upper_subset : upper ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (rawRegular : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        RawRegularTorusCircleData ((F.system k).circle i) p q)
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (hcommon : F.commonEventRegion ⊆
      superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection where
  cutAlternative := by
    have hInitial : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside := by
      rw [initialInside_eq]
      exact CarriesTransportedBasedLoopGenus.mono
        (selection.originalBox_subset_outerBody hr)
        (⟨WB.toBasedLoopCarrierWitness⟩ : CarriesTransportedBasedLoopGenus Phi
          (orientedBox frame c r))
    rcases finiteRegularSphereSurgery_chargedCompression_or_carries_terminalChild
        p q hc K Phi sigma hclass frame c selection F lower upper essentialSurgery
        rawRegular inessentialResolution hcommon hInitial with hcharged | hlower | hupper
    · exact Or.inr (Or.inr hcharged)
    · exact Or.inl (hlower.mono lower_subset)
    · exact Or.inr (Or.inl (hupper.mono upper_subset))

/-! ## Raw-regular finite-stage assembly -/

/-- The finite-stage resolution package with its analytic provenance retained.  This is the
charge-free replacement for `SuperellipsoidFiniteStageResolutionData`: only essential stage
circles need the raw regular certificate used to construct their quantitative compression. -/
structure SuperellipsoidFiniteStageRawResolutionData
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness) where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialInside_eq :
    (stageSequence.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale)
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  essentialSurgery : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData (stageSequence.system k) i)
  rawRegular : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      RawRegularTorusCircleData ((stageSequence.system k).circle i) p q
  inessentialResolution : stageSequence.AllInessential →
    Nonempty (AllInessentialFiniteBandResolution stageSequence lower upper)
  commonEvent_subset : stageSequence.commonEventRegion ⊆
    superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk

namespace SuperellipsoidFiniteStageRawResolutionData

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Raw-regular finite-stage data constructs a resolved double-bubble step without an abstract
event-covered-compression charging function. -/
theorem toResolvedDoubleBubbleStep
    (D : SuperellipsoidFiniteStageRawResolutionData
      p q K Phi frame c r WB selection)
    (hc : p.Coprime q) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hr : 0 < r) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection :=
  SuperellipsoidResolvedDoubleBubbleStep.ofFiniteRegularSphereSurgeryRawRegular
    p q hc K Phi sigma hclass frame c hr WB selection D.stageSequence D.lower D.upper
      D.initialInside_eq D.lower_subset D.upper_subset D.essentialSurgery D.rawRegular
      D.inessentialResolution D.commonEvent_subset

end SuperellipsoidFiniteStageRawResolutionData

/-- Pointwise charge-free raw-regular finite-stage geometry supplies the global resolved-step
hypothesis consumed by the quantitative shrinking argument. -/
theorem hasSuperellipsoidResolvedDoubleBubbleSteps_of_finiteStageRawResolution
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (resolution : ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
      ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
      ∀ selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
        WB.toSmoothLoopCarrierWitness,
        Nonempty (SuperellipsoidFiniteStageRawResolutionData
          p q K Phi frame c r WB selection)) :
    HasSuperellipsoidResolvedDoubleBubbleSteps p q hp hq hc K Phi sigma hclass := by
  intro frame c r hr hcarrier WB selection
  obtain ⟨D⟩ := resolution frame c r hr hcarrier WB selection
  exact ⟨D.toResolvedDoubleBubbleStep hc sigma hclass hr⟩

end Submission.PardonDistortion
