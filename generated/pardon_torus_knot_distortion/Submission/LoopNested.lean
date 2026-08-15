import Submission.Coarea.OrientedBoundarySelection
import Submission.NestedCarrier
import Submission.Topology.LoopCarrier

/-!
# The nested oriented-box contradiction for arbitrary-loop carriers

This module connects the concrete transported torus and the uniform local
chart radius to the abstract shrinking engine.  The only input left to the
topological cutting argument is a one-step successor theorem.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-- An oriented box carries genus when its intersection with the transported
torus contains two loops with independent winding pairs. -/
def OrientedLoopCarrier (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Prop :=
  CarriesTransportedLoopGenus Phi (orientedBox frame c r)

private theorem transportedTorus_isCompact (Phi : AmbientIsotopy) :
    IsCompact (transportedTorus Phi) := by
  exact isCompact_range (transportedTorusMap_isEmbedding Phi).continuous

private theorem ball_zero_subset_orientedBox
    (frame : Equiv.Perm (Fin 3)) {r : ℝ} (hr : 0 < r) :
    Metric.ball (0 : R3) r ⊆ orientedBox frame 0 r := by
  intro x hx
  rw [mem_orientedBox_iff]
  intro i
  have hcoord : |x.ofLp (frame i)| ≤ ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x (frame i)
  have hnorm : ‖x‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  have hweight : r ≤ axisWeight i * r := by
    nlinarith [one_le_axisWeight i]
  simpa using hcoord.trans_lt (hnorm.trans_le hweight)

/-- A sufficiently large oriented box contains the entire compact
transported torus and therefore starts the nested-carrier argument. -/
theorem exists_positive_orientedLoopCarrier (Phi : AmbientIsotopy) :
    ∃ (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ),
      0 < r ∧ OrientedLoopCarrier Phi frame c r := by
  obtain ⟨r, hr, htorus⟩ :=
    (transportedTorus_isCompact Phi).isBounded.subset_ball_lt 0 (0 : R3)
  let frame : Equiv.Perm (Fin 3) := Equiv.refl _
  have hbox : transportedTorus Phi ⊆ orientedBox frame 0 r :=
    htorus.trans (ball_zero_subset_orientedBox frame hr)
  refine ⟨frame, 0, r, hr, ?_⟩
  exact (transportedTorus_carriesTransportedLoopGenus Phi).mono hbox

private theorem mem_closedOrientedBox_of_mem_orientedBox
    {frame : Equiv.Perm (Fin 3)} {c x : R3} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ orientedBox frame c r) :
    x ∈ closedOrientedBox frame c r := by
  rw [closedOrientedBox, mem_ofPred_eq]
  exact (mem_orientedBox_iff_gauge_lt hr).mp hx |>.le

/-- Uniform local flatness gives a positive lower bound on the scale of every
loop-carrying oriented box. -/
theorem exists_uniform_scale_lower_bound (Phi : AmbientIsotopy) :
    ∃ rho > 0, ∀ frame c r, 0 < r →
      OrientedLoopCarrier Phi frame c r → rho ≤ r := by
  obtain ⟨delta, hdelta, hsmall⟩ :=
    exists_uniform_pos_ambient_ball_loop_noncarrier Phi
  refine ⟨delta / 5, div_pos hdelta (by norm_num), ?_⟩
  intro frame c r hr hcarrier
  by_contra hnot
  have hrho : r < delta / 5 := lt_of_not_ge hnot
  obtain ⟨W⟩ := hcarrier
  let y : transportedTorus Phi := W.first.curve 0
  have hybox : (y : R3) ∈ orientedBox frame c r :=
    W.first.curve_mem 0
  have hsubset : orientedBox frame c r ⊆
      Metric.ball (y : R3) delta := by
    intro x hx
    have hdist := dist_lt_five_mul_scale_of_mem_closedOrientedBox hr
      (mem_closedOrientedBox_of_mem_orientedBox hr hx)
      (mem_closedOrientedBox_of_mem_orientedBox hr hybox)
    rw [Metric.mem_ball]
    calc
      dist x (y : R3) < 5 * r := hdist
      _ < delta := by nlinarith
  apply hsmall y
  exact ⟨W.mono (preimage_mono hsubset)⟩

/-- The fully concrete nested-box engine.  A uniformly shrinking successor
for every carrying oriented box is impossible. -/
theorem not_exists_shrinking_orientedLoopCarrier
    (Phi : AmbientIsotopy)
    (hshrink : ∀ frame c r, 0 < r → OrientedLoopCarrier Phi frame c r →
      ∃ frame' c' r', 0 < r' ∧ OrientedLoopCarrier Phi frame' c' r' ∧
        r' ≤ shrinkFactor * r) : False := by
  obtain ⟨rho, hrho, hlower⟩ := exists_uniform_scale_lower_bound Phi
  apply not_exists_uniformly_positive_shrinkable
    (fun r ↦ ∃ frame c, OrientedLoopCarrier Phi frame c r)
    shrinkFactor rho shrinkFactor_pos.le shrinkFactor_lt_one hrho
  · obtain ⟨frame, c, r, hr, hcarrier⟩ :=
      exists_positive_orientedLoopCarrier Phi
    exact ⟨r, hr, frame, c, hcarrier⟩
  · rintro r hr ⟨frame, c, hcarrier⟩
    exact hlower frame c r hr hcarrier
  · rintro r hr ⟨frame, c, hcarrier⟩
    obtain ⟨frame', c', r', hr', hcarrier', hscale⟩ :=
      hshrink frame c r hr hcarrier
    exact ⟨r', hr', ⟨frame', c', hcarrier'⟩, hscale⟩

/-- Contrapositive form used by the capstone: if the strict inequality
`160D < I` supplies a shrinking successor, then `I ≤ 160D`. -/
theorem invariant_le_one_sixty_of_orientedLoopCarrier
    (Phi : AmbientIsotopy) (I D : ℝ)
    (hshrink : 160 * D < I → ∀ frame c r, 0 < r →
      OrientedLoopCarrier Phi frame c r →
      ∃ frame' c' r', 0 < r' ∧ OrientedLoopCarrier Phi frame' c' r' ∧
        r' ≤ shrinkFactor * r) :
    I ≤ 160 * D := by
  by_contra hnot
  exact not_exists_shrinking_orientedLoopCarrier Phi
    (hshrink (lt_of_not_ge hnot))

end Submission.PardonDistortion
