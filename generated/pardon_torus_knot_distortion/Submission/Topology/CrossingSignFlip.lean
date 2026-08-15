import Submission.Topology.SortedCrossingConstruction

/-!
# Sign reversal at a regular one-dimensional crossing

A nonzero derivative at a zero forces opposite signs on the two sides.  The proof uses the
one-sided limits of the secant slope.  This closes the sole analytic hypothesis left by the
sorted cyclic crossing construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology Filter

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-- A differentiable real function with a simple zero has a uniform sign flip across that zero. -/
theorem hasLocalSignFlip_of_hasDerivAt {f : ℝ → ℝ} {c f' : ℝ}
    (hd : HasDerivAt f f' c) (hc : f c = 0) (hf' : f' ≠ 0) :
    ∃ ε > 0, ∀ x ∈ Ioo (c - ε) c, ∀ y ∈ Ioo c (c + ε), f x * f y < 0 := by
  let g : ℝ → ℝ := fun t ↦ t⁻¹ * (f (c + t) - f c)
  have hlimRight : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 f') := by
    simpa only [g, smul_eq_mul] using hd.tendsto_slope_zero_right
  have hlimLeft : Tendsto g (𝓝[<] (0 : ℝ)) (𝓝 f') := by
    simpa only [g, smul_eq_mul] using hd.tendsto_slope_zero_left
  have hsq : 0 < f' * f' := mul_self_pos.mpr hf'
  have hrightEvent : {t | 0 < g t * f'} ∈ 𝓝[>] (0 : ℝ) := by
    have htend : Tendsto (fun t ↦ g t * f') (𝓝[>] (0 : ℝ)) (𝓝 (f' * f')) :=
      hlimRight.mul_const f'
    exact htend.eventually (Ioi_mem_nhds hsq)
  have hleftEvent : {t | 0 < g t * f'} ∈ 𝓝[<] (0 : ℝ) := by
    have htend : Tendsto (fun t ↦ g t * f') (𝓝[<] (0 : ℝ)) (𝓝 (f' * f')) :=
      hlimLeft.mul_const f'
    exact htend.eventually (Ioi_mem_nhds hsq)
  obtain ⟨b, hb, hbsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset.mp hrightEvent)
  obtain ⟨a, ha, hasub⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset.mp hleftEvent)
  let ε := min b (-a)
  have hε : 0 < ε := lt_min hb (neg_pos.mpr ha)
  refine ⟨ε, hε, ?_⟩
  intro x hx y hy
  let tx := x - c
  let ty := y - c
  have htx : tx ∈ Ioo a 0 := by
    constructor
    · have hεa : ε ≤ -a := min_le_right b (-a)
      dsimp [tx]
      linarith [hx.1]
    · dsimp [tx]
      linarith [hx.2]
  have hty : ty ∈ Ioo 0 b := by
    constructor
    · dsimp [ty]
      linarith [hy.1]
    · have hεb : ε ≤ b := min_le_left b (-a)
      dsimp [ty]
      linarith [hy.2]
  have hgx : 0 < g tx * f' := hasub htx
  have hgy : 0 < g ty * f' := hbsub hty
  have hgg : 0 < g tx * g ty := by
    rcases mul_pos_iff.mp hgx with hpos | hneg
    · rcases mul_pos_iff.mp hgy with hpos' | hneg'
      · exact mul_pos hpos.1 hpos'.1
      · exact False.elim (not_lt_of_ge hpos.2.le hneg'.2)
    · rcases mul_pos_iff.mp hgy with hpos' | hneg'
      · exact False.elim (not_lt_of_ge hpos'.2.le hneg.2)
      · exact mul_pos_of_neg_of_neg hneg.1 hneg'.1
  have htxneg : tx < 0 := htx.2
  have htypos : 0 < ty := hty.1
  have hxEq : f x = tx * g tx := by
    have htxne : tx ≠ 0 := ne_of_lt htxneg
    rw [show x = c + tx by dsimp [tx]; ring]
    dsimp only [g]
    rw [hc]
    field_simp [htxne]
    ring
  have hyEq : f y = ty * g ty := by
    have htyne : ty ≠ 0 := ne_of_gt htypos
    rw [show y = c + ty by dsimp [ty]; ring]
    dsimp only [g]
    rw [hc]
    field_simp [htyne]
    ring
  rw [hxEq, hyEq]
  have htprod : tx * ty < 0 := mul_neg_of_neg_of_pos htxneg htypos
  nlinarith

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-- `SmoothRegularLoopCutData` automatically supplies the local sign-flip input used by sorted
crossing construction. -/
theorem SmoothRegularLoopCutData.hasLocalSignFlipAtCrossings
    (H : SmoothRegularLoopCutData frame d L) :
    HasLocalSignFlipAtCrossings H := by
  intro c hc
  apply hasLocalSignFlip_of_hasDerivAt
  · exact H.hasDerivAt_height c
  · exact (H.mem_crossings_iff c).mp hc |>.2
  · exact H.deriv_height_ne_zero_of_mem_crossings hc

/-- Nonempty regular crossing sets therefore have unconditional finite cyclic excursion
bookkeeping. -/
def SmoothRegularLoopCutData.finiteCyclicExcursionBookkeeping
    (H : SmoothRegularLoopCutData frame d L) (hcross : H.crossings.Nonempty) :
    FiniteCyclicExcursionBookkeeping H :=
  finiteCyclicExcursionBookkeeping_of_sortedCrossings H hcross
    H.hasLocalSignFlipAtCrossings

/-! ## The crossing-free case -/

/-- If the canonical-period crossing finset is empty, periodicity rules out a zero at every real
parameter, including parameters across the chosen seam. -/
theorem SmoothRegularLoopCutData.height_ne_zero_of_crossings_eq_empty
    (H : SmoothRegularLoopCutData frame d L) (hempty : H.crossings = ∅) (t : ℝ) :
    windingLoopCutHeight frame d L t ≠ 0 := by
  intro htzero
  let u : ℝ := toIcoMod Real.two_pi_pos 0 t
  let k : ℤ := toIcoDiv Real.two_pi_pos 0 t
  have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 t
  have hukt : u + (k : ℝ) * (2 * Real.pi) = t :=
    toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 t
  have huzero : windingLoopCutHeight frame d L u = 0 := by
    calc
      windingLoopCutHeight frame d L u =
          windingLoopCutHeight frame d L (u + (k : ℝ) * (2 * Real.pi)) :=
        ((H.periodic_height.int_mul k) u).symm
      _ = windingLoopCutHeight frame d L t := by rw [hukt]
      _ = 0 := htzero
  have hucross : u ∈ H.crossings :=
    (H.mem_crossings_iff u).mpr ⟨hu, huzero⟩
  rw [hempty] at hucross
  simp at hucross

/-- A regular periodic loop with no crossings lies strictly on one side of the cutting plane. -/
theorem SmoothRegularLoopCutData.all_height_neg_or_all_height_pos_of_crossings_eq_empty
    (H : SmoothRegularLoopCutData frame d L) (hempty : H.crossings = ∅) :
    (∀ t, windingLoopCutHeight frame d L t < 0) ∨
      (∀ t, 0 < windingLoopCutHeight frame d L t) := by
  simpa only [mem_univ, forall_const] using
    H.crossingFreeArc_all_neg_or_all_pos isPreconnected_univ univ_nonempty
      (fun t _ ↦ H.height_ne_zero_of_crossings_eq_empty hempty t)

/-- In geometric language, an empty crossing set puts the original loop in one closed
halfspace piece. -/
theorem SmoothRegularLoopCutData.all_curve_mem_lower_or_all_curve_mem_upper_of_crossings_eq_empty
    (H : SmoothRegularLoopCutData frame d L) (hempty : H.crossings = ∅) :
    (∀ t, L.curve t ∈ lowerSurfaceRegion Phi parent frame d) ∨
      (∀ t, L.curve t ∈ upperSurfaceRegion Phi parent frame d) := by
  simpa only [mem_univ, forall_const] using
    H.crossingFreeArc_mem_lower_or_upper isPreconnected_univ univ_nonempty
      (fun t _ ↦ H.height_ne_zero_of_crossings_eq_empty hempty t)

/-- A loop already contained in the target set is its own periodic arc replacement. -/
def periodicArcReplacementSelf {target : Set (transportedTorus Phi)}
    (hmem : ∀ t, L.curve t ∈ target) :
    PeriodicArcReplacement (target := target) L where
  rerouted := L.curve
  continuous_rerouted := L.continuous_curve
  periodic_rerouted := L.periodic_curve
  rerouted_mem := hmem
  reroutedLift := L.lift
  homotopy := fun _ t ↦ L.curve t
  continuous_homotopy := L.continuous_curve.comp continuous_snd
  periodic_homotopy := fun _ ↦ L.periodic_curve
  homotopy_zero := rfl
  homotopy_one := rfl

/-- The empty-crossing case has a genuine trivial rerouting outcome: no plane-slice replacement
paths are needed. -/
def SmoothRegularLoopCutData.reroutingOutcomeOfCrossingsEqEmpty
    (H : SmoothRegularLoopCutData frame d L) (hempty : H.crossings = ∅) :
    LoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L := by
  by_cases hlower : ∀ t, L.curve t ∈ lowerSurfaceRegion Phi parent frame d
  · exact .inLeft (periodicArcReplacementSelf hlower)
  · have hupper : ∀ t, L.curve t ∈ upperSurfaceRegion Phi parent frame d :=
      (H.all_curve_mem_lower_or_all_curve_mem_upper_of_crossings_eq_empty hempty).resolve_left
        hlower
    exact .inRight (periodicArcReplacementSelf hupper)

/-- Complete analytic case split: either sorted cyclic excursion bookkeeping is available, or
the finite crossing set is empty. -/
theorem SmoothRegularLoopCutData.bookkeeping_or_crossings_eq_empty
    (H : SmoothRegularLoopCutData frame d L) :
    Nonempty (FiniteCyclicExcursionBookkeeping H) ∨ H.crossings = ∅ := by
  classical
  by_cases hcross : H.crossings.Nonempty
  · exact Or.inl ⟨H.finiteCyclicExcursionBookkeeping hcross⟩
  · exact Or.inr (Finset.not_nonempty_iff_eq_empty.mp hcross)

end Submission.Topology
