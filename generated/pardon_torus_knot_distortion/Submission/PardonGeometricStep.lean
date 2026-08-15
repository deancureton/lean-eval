import Submission.CapstoneReduction
import Submission.CompressionExclusion
import Submission.DoubleBubbleSelection
import Submission.Topology.LoopHalfspaceCut

/-!
# Exact geometric interface for Pardon's one-step argument

This file connects the verified coarea selection, loop rerouting alternative,
compression intersection lower bound, and rational successor-box geometry.
It leaves no numerical or iteration work implicit: the sole remaining input
is the geometric construction that reroutes the two carrier loops and turns
each resulting double bubble into a charged compressing disk.
-/

open Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

noncomputable section

/-- A compressing disk together with both the transverse lower-bound
certificate and its injective charging into the selected events. -/
structure ChargedCompression
    (p q : ℕ) {K : Knot} {Phi : AmbientIsotopy}
    {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : DoubleBubbleSelection K frame c r) where
  disk : GeneralCompressingDiskWitness Phi
  certificate : TransverseIntersectionCertificate p q
    (transportedLoopCoordinates Phi disk.boundaryLoop.curve)
    disk.boundaryLoop.lift.first.winding
    disk.boundaryLoop.lift.second.winding
  charging : Nonempty (S.CompressionCharging disk p q)

/-- Complete geometric resolution of one already-selected double bubble.
The third branch is deliberately the *specific charged compression produced
by the cut construction*, rather than every abstract connectivity witness. -/
structure ResolvedDoubleBubbleStep
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (S : DoubleBubbleSelection K frame c r) where
  cutAlternative : CarriesTransportedLoopGenus Phi
      (orientedBox frame c S.outerScale) →
    CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outerScale ∩
          lowerClosedHalfspace frame S.cutHeight) ∨
      CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outerScale ∩
          upperClosedHalfspace frame S.cutHeight) ∨
      Nonempty (ChargedCompression (Phi := Phi) p q S)

/-- The remaining geometric theorem, stated uniformly over every selected
box and regular cut produced by coarea. -/
def HasResolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c r, 0 < r → OrientedLoopCarrier Phi frame c r →
    ∀ S : DoubleBubbleSelection K frame c r,
      Nonempty (ResolvedDoubleBubbleStep p q K Phi frame c r S)

private theorem abs_cutHeight_sub_center_le
    {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : DoubleBubbleSelection K frame c r) :
    |S.cutHeight - c.ofLp (frame 2)| ≤ shellEpsilon * r := by
  rw [abs_le]
  constructor <;> linarith [S.cutHeight_mem.1, S.cutHeight_mem.2]

/-- A resolved selected step produces the exact shrinking successor required
by the nested-box engine. -/
theorem hasPardonShrinkingStep_of_resolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hresolved : HasResolvedDoubleBubbleSteps p q K Phi) :
    HasPardonShrinkingStep p q K Phi := by
  intro hfinite hcontra frame c r hr hcarrier
  obtain ⟨S⟩ := exists_doubleBubbleSelection K frame c hr hfinite
  obtain ⟨G⟩ := hresolved frame c r hr hcarrier S
  have hRpos : 0 < S.outerScale := hr.trans S.outerScale_mem.1
  have hRle : S.outerScale ≤ (1 + shellEpsilon) * r := by
    have heps : (1 + shellEpsilon : ℝ) = 8 / 7 := by
      norm_num [shellEpsilon]
    rw [heps]
    exact S.outerScale_mem.2
  have hparent : CarriesTransportedLoopGenus Phi
      (orientedBox frame c S.outerScale) := by
    apply hcarrier.mono
    intro x hx
    rw [mem_orientedBox_iff] at hx ⊢
    intro i
    exact (hx i).trans
      (mul_lt_mul_of_pos_left S.outerScale_mem.1 (axisWeight_pos i))
  have hsides : CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outerScale ∩
          lowerClosedHalfspace frame S.cutHeight) ∨
      CarriesTransportedLoopGenus Phi
        (orientedBox frame c S.outerScale ∩
          upperClosedHalfspace frame S.cutHeight) := by
    rcases G.cutAlternative hparent with hleft | hright | hcharged
    · exact Or.inl hleft
    · exact Or.inr hright
    · obtain ⟨charged⟩ := hcharged
      exact False.elim <|
        (S.no_compressionCharging_of_distortion_lt charged.disk p q
          charged.certificate hcontra) charged.charging
  have hscale : successorScale S.outerScale r ≤ shrinkFactor * r :=
    successorScale_le_shrinkFactor_mul hr.le hRle
  rcases hsides with hlower | hupper
  · refine ⟨axisCycle.trans frame,
      lowerHalfCenter frame c S.outerScale S.cutHeight,
      successorScale S.outerScale r, successorScale_pos hRpos hr, ?_, hscale⟩
    apply CarriesTransportedLoopGenus.mono ?_ hlower
    simpa only [lowerClosedHalfspace] using
      lowerHalf_subset_successor frame c hRpos hr
        (abs_cutHeight_sub_center_le S)
  · refine ⟨axisCycle.trans frame,
      upperHalfCenter frame c S.outerScale S.cutHeight,
      successorScale S.outerScale r, successorScale_pos hRpos hr, ?_, hscale⟩
    apply CarriesTransportedLoopGenus.mono ?_ hupper
    simpa only [upperClosedHalfspace] using
      upperHalf_subset_successor frame c hRpos hr
        (abs_cutHeight_sub_center_le S)

/-- Consequently, resolving the geometric double-bubble construction closes
the benchmark's extended-real target. -/
theorem pardonTarget_of_resolvedDoubleBubbleSteps
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (hresolved : HasResolvedDoubleBubbleSteps p q K Phi) :
    (1 / 160 : ℝ≥0∞) * ((Nat.min p q : ℕ) : ℝ≥0∞) ≤ distortion K :=
  pardonTarget_of_hasPardonShrinkingStep p q K Phi
    (hasPardonShrinkingStep_of_resolvedDoubleBubbleSteps p q K Phi hresolved)

end

end Submission.PardonDistortion
