import Submission.CapstoneReduction
import Submission.SuperellipsoidCompressionExclusion
import Submission.Topology.BasedSmoothLoopCarrier

/-!
# Smooth-superellipsoid handoff to Pardon's shrinking contradiction

This module leaves only the two genuinely topological constructions visible: finite complete
orbits of each regular outer seam, and the resolved sphere-surgery alternative.  All coarea,
event-count, successor-box, extended-real, and infinite-iteration work is discharged here.
-/

open Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology
open Submission.SurfaceRegularValue

noncomputable section

/-- Every regular smooth outer level has a finite family of complete rotated-gradient orbits
covering its lift modulo deck translations. -/
def HasFiniteRegularSuperellipsoidSeamOrbitCovers (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c R,
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256) →
      Nonempty (FiniteSuperellipsoidSeamOrbitCover Phi frame c R)

/-- Resolution of one selected smooth double bubble. -/
structure SuperellipsoidResolvedDoubleBubbleStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness) where
  cutAlternative : CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c S.outer.scale ∩
          {x | x.ofLp (frame 2) ≤ S.cut.height}) ∨
      CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c S.outer.scale ∩
          {x | S.cut.height ≤ x.ofLp (frame 2)}) ∨
      Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q S)

/-- Exact topology theorem required after all smooth genericity and counting choices are made. -/
def HasSuperellipsoidResolvedDoubleBubbleSteps
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (_hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) : Prop :=
  ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
    ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
    ∀ S : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness,
      Nonempty (SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB S)

/-- The two topology inputs imply the exact one-step uniformly shrinking based carrier. -/
theorem real_bound_of_superellipsoidResolvedDoubleBubbleSteps
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (horbits : HasFiniteRegularSuperellipsoidSeamOrbitCovers Phi)
    (hresolved : HasSuperellipsoidResolvedDoubleBubbleSteps
      p q hp hq hc K Phi sigma hclass)
    (hfinite : distortion K ≠ ⊤) :
    ((Nat.min p q : ℕ) : ℝ) ≤ 160 * (distortion K).toReal := by
  by_contra hnot
  have hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ) :=
    lt_of_not_ge hnot
  apply not_exists_shrinking_orientedBasedLoopCarrier Phi
  intro frame c r hr hcarrier
  obtain ⟨WB⟩ :=
    exists_smoothBasedLoopCarrierWitness_of_orientedBasedLoopCarrier
      Phi frame c hr hcarrier
  obtain ⟨S⟩ := exists_superellipsoidDoubleBubbleSelection_of_orbitCover
    K Phi frame c hr hfinite WB.toSmoothLoopCarrierWitness (by
      intro outer
      exact horbits frame c outer.scale outer.surfaceRegular)
  obtain ⟨G⟩ := hresolved frame c r hr hcarrier WB S
  have hsides : CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c S.outer.scale ∩
          {x | x.ofLp (frame 2) ≤ S.cut.height}) ∨
      CarriesTransportedBasedLoopGenus Phi
        (superellipsoidBody frame c S.outer.scale ∩
          {x | S.cut.height ≤ x.ofLp (frame 2)}) := by
    rcases G.cutAlternative with hleft | hright | hcharged
    · exact Or.inl hleft
    · exact Or.inr hright
    · obtain ⟨charged⟩ := hcharged
      exact False.elim <|
        (S.no_compressionCharging_of_distortion_lt charged.disk p q
          charged.certificate hcontra) charged.charging
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

/-- Final benchmark target from the two explicit smooth-topology inputs. -/
theorem pardonTarget_of_superellipsoidResolvedDoubleBubbleSteps
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (horbits : HasFiniteRegularSuperellipsoidSeamOrbitCovers Phi)
    (hresolved : HasSuperellipsoidResolvedDoubleBubbleSteps
      p q hp hq hc K Phi sigma hclass) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K := by
  apply pardonTarget_le_of_real_bound p q K
  intro hfinite
  exact real_bound_of_superellipsoidResolvedDoubleBubbleSteps
    p q hp hq hc K Phi sigma hclass horbits hresolved hfinite

end

end Submission.PardonDistortion
