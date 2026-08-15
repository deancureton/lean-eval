import Submission.Topology.SmoothWindingApproximation
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Smooth periodic approximation by finite Fourier sums

This file discharges `HasPeriodicSmoothApproximation`.  A continuous periodic real function
descends to the additive circle.  The density of the finite complex span of the Fourier
monomials gives a uniformly close finite Fourier sum.  Its real part, pulled back to the real
line, is smooth, exactly periodic, and uniformly close to the original function.
-/

open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

/-! ## Descending periodic functions -/

lemma continuous_periodicLift {f : ℝ → ℝ} {T : ℝ}
    (hf : Continuous f) (hperiodic : Function.Periodic f T) :
    Continuous hperiodic.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples T)).continuous_iff.mpr
  rw [show hperiodic.lift ∘
      (QuotientAddGroup.mk : ℝ → AddCircle T) = f by
    funext t
    exact Function.Periodic.lift_coe hperiodic t]
  exact hf

/-! ## Smoothness of finite Fourier sums on the real cover -/

lemma contDiff_fourier_pullback {T : ℝ} [Fact (0 < T)] (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ fourier (T := T) n (t : AddCircle T)) := by
  rw [show (fun t : ℝ ↦ fourier (T := T) n (t : AddCircle T)) =
      fun t : ℝ ↦ Complex.exp (2 * Real.pi * Complex.I * n * t / T) by
    funext t
    exact fourier_coe_apply]
  rw [show (fun t : ℝ ↦ Complex.exp (2 * Real.pi * Complex.I * n * t / T)) =
      fun t : ℝ ↦ Complex.exp
        ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (T : ℂ)) * (t : ℂ)) by
    funext t
    congr 1
    ring]
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

lemma contDiff_span_fourier_pullback {T : ℝ} [Fact (0 < T)]
    (g : C(AddCircle T, ℂ))
    (hg : g ∈ Submodule.span ℂ (range (@fourier T))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ g (t : AddCircle T)) := by
  refine Submodule.span_induction (p := fun g _ ↦
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ g (t : AddCircle T))) ?_ ?_ ?_ ?_ hg
  · intro g hg
    obtain ⟨n, rfl⟩ := hg
    exact contDiff_fourier_pullback n
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (0 : ℂ)))
  · intro g h _ _ hg hh
    simpa only [ContinuousMap.add_apply] using hg.add hh
  · intro c g _ hg
    simpa only [ContinuousMap.smul_apply, smul_eq_mul] using contDiff_const.mul hg

/-! ## Fourier approximation -/

theorem hasPeriodicSmoothApproximation_fourier : HasPeriodicSmoothApproximation := by
  intro f hf hperiodic tolerance htolerance
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := Real.two_pi_pos
  let _ : Fact (0 < T) := ⟨hT⟩
  let descended : C(AddCircle T, ℝ) :=
    ⟨hperiodic.lift, continuous_periodicLift hf hperiodic⟩
  let target : C(AddCircle T, ℂ) := {
    toFun := fun x ↦ (descended x : ℂ)
    continuous_toFun := Complex.continuous_ofReal.comp descended.continuous
  }
  have hclosure : target ∈
      (Submodule.span ℂ (range (@fourier T))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hclosure
  obtain ⟨g, hgspan, hgtarget⟩ := hclosure tolerance htolerance
  have hnorm : ‖g - target‖ < tolerance := by
    simpa only [dist_eq_norm, norm_sub_rev] using hgtarget
  let approx : ℝ → ℝ := fun t ↦ (g (t : AddCircle T)).re
  refine ⟨{
    toFun := approx
    contDiff_toFun := ?_
    periodic_toFun := ?_
    dist_lt := ?_
  }⟩
  · exact Complex.reCLM.contDiff.comp
      (contDiff_span_fourier_pullback g hgspan)
  · intro t
    change (g ((t + T : ℝ) : AddCircle T)).re = (g (t : AddCircle T)).re
    rw [AddCircle.coe_add_period]
  · intro t
    rw [Real.dist_eq]
    calc
      |(g (t : AddCircle T)).re - f t| =
          |(g (t : AddCircle T) - (f t : ℂ)).re| := by simp
      _ ≤ ‖g (t : AddCircle T) - (f t : ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖(g - target) (t : AddCircle T)‖ := by
        simp [target, descended, Function.Periodic.lift_coe]
      _ ≤ ‖g - target‖ := ContinuousMap.norm_coe_le_norm _ _
      _ < tolerance := hnorm

/-! ## Unconditional geometric wrapper -/

/-- Every winding loop in an open transported-torus subset has an arbitrarily close smooth-angle
representative in the same subset, with a smooth ambient curve and exactly the same winding pair. -/
theorem exists_smoothWindingApproximation_unconditional
    {Phi : LeanEval.KnotTheory.PardonDistortion.AmbientIsotopy}
    {U : Set (Submission.Torus.transportedTorus Phi)}
    (hU : IsOpen U) (L : TransportedWindingLoop Phi U)
    {ambientTolerance : ℝ} (hambientTolerance : 0 < ambientTolerance) :
    Nonempty (SmoothWindingApproximation L U ambientTolerance) :=
  exists_smoothWindingApproximation hasPeriodicSmoothApproximation_fourier
    hU L hambientTolerance

end Submission.Topology
