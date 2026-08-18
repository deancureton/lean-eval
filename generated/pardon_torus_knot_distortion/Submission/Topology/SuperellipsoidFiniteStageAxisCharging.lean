import Submission.SuperellipsoidPardonGeometricStep
import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.SuperellipsoidAxisLoopExclusion

/-!
# Finite-stage resolution using charged axis circles

An innermost-circle surgery is stronger than the quantitative argument needs.  If a regular
sphere stage has an essential intersection, its topological role is only to produce one
intersection circle whose winding lies on a nonzero coordinate axis.  Transverse charging of
that circle already contradicts the selected event-count bound.

This module proves the finite-stage and capstone adapters for that reduced interface.  The
remaining sphere topology is the honest assertion that a finite sphere intersection containing
an essential circle contains a nonzero axis circle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- Every stage with an essential circle contains a circle of nonzero coordinate-axis slope. -/
def FiniteRegularSphereSurgeryStageSequence.HasAxisCircleIfEssential
    (F : FiniteRegularSphereSurgeryStageSequence Phi) : Prop :=
  ∀ k, k ≤ F.length →
    (∃ i, ((F.system k).circle i).Essential) →
      ∃ i, IsNonzeroAxisSlope
        ((F.system k).circle i).windingLoop.lift.first.winding
        ((F.system k).circle i).windingLoop.lift.second.winding

namespace FiniteRegularSphereSurgeryStageSequence

variable {F : FiniteRegularSphereSurgeryStageSequence Phi}

/-- Under the contrary distortion inequality, the finite regular-stage alternative needs no
embedded innermost surgery: an axis circle is quantitatively impossible, while the
all-inessential branch propagates to a terminal child as before. -/
theorem carries_terminalChild_of_axisCharging
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (axisCircle : F.HasAxisCircleIfEssential)
    (chargingTransport : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
          (transportedLoopCoordinates Phi ((F.system k).circle i).windingLoop.curve)
          ((F.system k).circle i).windingLoop.lift.first.winding
          ((F.system k).circle i).windingLoop.lift.second.winding)
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (hparent : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside)
    (hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    CarriesBasedLoopTorusGenus Phi lower ∨
      CarriesBasedLoopTorusGenus Phi upper := by
  classical
  by_cases hessential : ∃ k, k ≤ F.length ∧
      ∃ i, ((F.system k).circle i).Essential
  · obtain ⟨k, hk, hstage⟩ := hessential
    obtain ⟨i, haxis⟩ := axisCircle k hk hstage
    have hi : ((F.system k).circle i).Essential := haxis.2
    let T := chargingTransport k hk i hi
    let A : SuperellipsoidDoubleBubbleSelection.ChargedAxisLoop selection p q := {
      loop := transportedLoopCoordinates Phi ((F.system k).circle i).windingLoop.curve
      firstWinding := ((F.system k).circle i).windingLoop.lift.first.winding
      secondWinding := ((F.system k).circle i).windingLoop.lift.second.winding
      axis := haxis
      certificate := T.targetCertificate
      charging := T.targetCharging
    }
    exact False.elim <|
      selection.no_chargedAxisLoop_of_distortion_lt p q hcontra ⟨A⟩
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
    rwa [D.terminal_lower_eq, D.terminal_upper_eq] at hchildren

end FiniteRegularSphereSurgeryStageSequence
end PairedBandMovingSphereCollarData
end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {p q : ℕ} {K : Knot}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- Geometric resolution data for the reduced axis-circle route. -/
structure SuperellipsoidFiniteStageAxisResolutionData where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialInside_eq : (stageSequence.parityStage 0).inside = transportedTorusPart Phi
    (orientedBox frame c r)
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  axisCircle : stageSequence.HasAxisCircleIfEssential
  chargingTransport : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      SuperellipsoidDoubleBubbleSelection.SmoothedLoopChargingTransport selection p q
        (transportedLoopCoordinates Phi
          ((stageSequence.system k).circle i).windingLoop.curve)
        ((stageSequence.system k).circle i).windingLoop.lift.first.winding
        ((stageSequence.system k).circle i).windingLoop.lift.second.winding
  inessentialResolution : stageSequence.AllInessential →
    Nonempty (AllInessentialFiniteBandResolution stageSequence lower upper)

namespace SuperellipsoidFiniteStageAxisResolutionData

/-- Under the benchmark's contrary inequality, an axis-stage resolution produces a shrinking
lower or upper child carrier. -/
theorem carries_lower_or_upper
    (D : SuperellipsoidFiniteStageAxisResolutionData
      (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
      (WB := WB) (selection := selection))
    (hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c selection.outer.scale ∩
          {x | x.ofLp (frame 2) ≤ selection.cut.height}) ∨
      CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c selection.outer.scale ∩
          {x | selection.cut.height ≤ x.ofLp (frame 2)}) := by
  have hparent : CarriesBasedLoopTorusGenus Phi
      (D.stageSequence.parityStage 0).inside := by
    rw [D.initialInside_eq]
    exact ⟨WB.toBasedLoopCarrierWitness⟩
  rcases D.stageSequence.carries_terminalChild_of_axisCharging
      p q K Phi frame c selection D.lower D.upper
      D.axisCircle D.chargingTransport D.inessentialResolution hparent hcontra with
    hlower | hupper
  · exact Or.inl (hlower.mono D.lower_subset)
  · exact Or.inr (hupper.mono D.upper_subset)

end SuperellipsoidFiniteStageAxisResolutionData

/-- Uniform existence of the reduced finite-stage axis resolution. -/
def HasSuperellipsoidFiniteStageAxisResolutions
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) : Prop :=
  ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
    ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
    ∀ S : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness,
      Nonempty (SuperellipsoidFiniteStageAxisResolutionData
        (p := p) (q := q) (K := K) (Phi := Phi) (frame := frame) (c := c) (r := r)
        (WB := WB) (selection := S))

/-- The reduced axis-stage topology theorem implies Pardon's benchmark bound. -/
theorem pardonTarget_of_superellipsoidFiniteStageAxisResolutions
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hresolved : HasSuperellipsoidFiniteStageAxisResolutions
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_le_of_real_bound p q K
  intro hfinite
  by_contra hnot
  have hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ) :=
    lt_of_not_ge hnot
  apply not_exists_shrinking_orientedBasedLoopCarrier Phi
  intro frame c r hr hcarrier
  obtain ⟨WB⟩ :=
    exists_smoothBasedLoopCarrierWitness_of_orientedBasedLoopCarrier
      Phi frame c hr hcarrier
  obtain ⟨S⟩ := exists_superellipsoidDoubleBubbleSelection_unconditional
    K Phi frame c hr hfinite WB.toSmoothLoopCarrierWitness
  obtain ⟨D⟩ := hresolved frame c r hr hcarrier WB S
  have hsides := D.carries_lower_or_upper hcontra
  have hRle : S.outer.scale ≤ (1 + shellEpsilon) * r := by
    have hfactor : (superellipsoidOuterFactor : ℝ) = 1 + shellEpsilon := by
      norm_num [superellipsoidOuterFactor, shellEpsilon]
    rw [← hfactor]
    exact S.outer.scale_mem.2
  have hscale : successorScale S.outer.scale r ≤ shrinkFactor * r :=
    successorScale_le_shrinkFactor_mul hr.le hRle
  have hscalePos : 0 < successorScale S.outer.scale r :=
    successorScale_pos (S.outer.scale_pos hr) hr
  rcases hsides with hlower | hupper
  · refine ⟨axisCycle.trans frame,
      lowerHalfCenter frame c S.outer.scale S.cut.height,
      successorScale S.outer.scale r, hscalePos, ?_, hscale⟩
    exact hlower.mono (S.lowerHalf_subset_successor hr)
  · refine ⟨axisCycle.trans frame,
      upperHalfCenter frame c S.outer.scale S.cut.height,
      successorScale S.outer.scale r, hscalePos, ?_, hscale⟩
    exact hupper.mono (S.upperHalf_subset_successor hr)

end Submission.PardonDistortion
