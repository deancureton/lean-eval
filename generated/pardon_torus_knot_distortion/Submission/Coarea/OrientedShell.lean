import Submission.Coarea.Lipschitz
import Submission.OrientedBox

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- Weighted coordinates in an arbitrary permuted box frame. -/
def normalizedOrientedBoxCoordinates
    (frame : Equiv.Perm (Fin 3)) (c x : R3) : Fin 3 → ℝ :=
  fun i ↦ (x - c).ofLp (frame i) / axisWeight i

/-- Weighted sup gauge for an oriented rational box. -/
def orientedBoxGauge (frame : Equiv.Perm (Fin 3)) (c x : R3) : ℝ :=
  ‖normalizedOrientedBoxCoordinates frame c x‖

lemma mem_orientedBox_iff_gauge_lt
    {frame : Equiv.Perm (Fin 3)} {c x : R3} {r : ℝ} (hr : 0 < r) :
    x ∈ orientedBox frame c r ↔ orientedBoxGauge frame c x < r := by
  rw [orientedBox, orientedBoxGauge, pi_norm_lt_iff hr]
  constructor
  · intro hx i
    rw [normalizedOrientedBoxCoordinates, Real.norm_eq_abs, abs_div,
      abs_of_pos (axisWeight_pos i), div_lt_iff₀ (axisWeight_pos i)]
    simpa [mul_comm] using hx i
  · intro hx i
    have hi := hx i
    rw [normalizedOrientedBoxCoordinates, Real.norm_eq_abs, abs_div,
      abs_of_pos (axisWeight_pos i), div_lt_iff₀ (axisWeight_pos i)] at hi
    simpa [mul_comm] using hi

lemma normalizedOrientedBoxCoordinates_sub
    (frame : Equiv.Perm (Fin 3)) (c x y : R3) (i : Fin 3) :
    (normalizedOrientedBoxCoordinates frame c x -
      normalizedOrientedBoxCoordinates frame c y) i =
        (x - y).ofLp (frame i) / axisWeight i := by
  simp only [normalizedOrientedBoxCoordinates, Pi.sub_apply]
  field_simp [ne_of_gt (axisWeight_pos i)]
  change (x - c).ofLp (frame i) - (y - c).ofLp (frame i) =
    (x - y).ofLp (frame i)
  simp

lemma norm_normalizedOrientedBoxCoordinates_sub_le
    (frame : Equiv.Perm (Fin 3)) (c x y : R3) :
    ‖normalizedOrientedBoxCoordinates frame c x -
      normalizedOrientedBoxCoordinates frame c y‖ ≤ dist x y := by
  rw [pi_norm_le_iff_of_nonneg dist_nonneg]
  intro i
  rw [normalizedOrientedBoxCoordinates_sub, Real.norm_eq_abs, abs_div,
    abs_of_pos (axisWeight_pos i)]
  calc
    |(x - y).ofLp (frame i)| / axisWeight i ≤ |(x - y).ofLp (frame i)| :=
      div_le_self (abs_nonneg _) (one_le_axisWeight i)
    _ = ‖(x - y).ofLp (frame i)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) (frame i)
    _ = dist x y := by rw [dist_eq_norm]

lemma lipschitzWith_orientedBoxGauge
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    LipschitzWith 1 (orientedBoxGauge frame c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, orientedBoxGauge] using
    (dist_norm_norm_le (normalizedOrientedBoxCoordinates frame c x)
      (normalizedOrientedBoxCoordinates frame c y)).trans
        (norm_normalizedOrientedBoxCoordinates_sub_le frame c x y)

lemma continuous_orientedBoxGauge
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    Continuous (orientedBoxGauge frame c) :=
  (lipschitzWith_orientedBoxGauge frame c).continuous

/-- Oriented shell gauge restricted to the knot. -/
def orientedShellParameter
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (t : ℝ) : ℝ :=
  orientedBoxGauge frame c (K.curve t)

lemma exists_lipschitzWith_orientedShellParameter
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) :
    ∃ C : ℝ≥0, LipschitzWith C (orientedShellParameter K frame c) := by
  obtain ⟨C, hcurve⟩ :=
    Submission.Coarea.PardonApplication.exists_lipschitzWith_knotCurve K
  refine ⟨C, ?_⟩
  have hcomp := (lipschitzWith_orientedBoxGauge frame c).comp hcurve
  change LipschitzWith C (orientedBoxGauge frame c ∘ K.curve)
  simpa only [one_mul] using hcomp

/-- A one-Lipschitz outer function cannot increase the metric derivative of a
differentiable inner curve, even when the outer gauge itself is nonsmooth. -/
lemma abs_deriv_comp_le_norm_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (f : ℝ → E) (t : ℝ)
    (hg : LipschitzWith 1 g) (hf : DifferentiableAt ℝ f t)
    (hcomp : DifferentiableAt ℝ (g ∘ f) t) :
    |deriv (g ∘ f) t| ≤ ‖deriv f t‖ := by
  have hgderiv := hcomp.hasDerivAt
  have hfderiv := hf.hasDerivAt
  rw [← Real.norm_eq_abs]
  refine le_of_tendsto_of_tendsto hgderiv.tendsto_slope.norm
    hfderiv.tendsto_slope.norm ?_
  filter_upwards with u
  rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (by simpa [dist_eq_norm] using hg.dist_le_mul (f u) (f t)) (norm_nonneg _)

lemma abs_deriv_orientedShellParameter_le_speed_of_differentiableAt
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3) (t : ℝ)
    (h : DifferentiableAt ℝ (orientedShellParameter K frame c) t) :
    |deriv (orientedShellParameter K frame c) t| ≤ speed K t := by
  exact abs_deriv_comp_le_norm_deriv (orientedBoxGauge frame c) K.curve t
    (lipschitzWith_orientedBoxGauge frame c)
    (K.smooth.differentiable (by simp) t) h

/-- Branch-free coarea selector for an oriented box shell. -/
theorem exists_orientedShellRegularValue_fiberCount_le_integral_of_isCompact
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b,
      y ∉ (orientedShellParameter K frame c) ''
        Submission.Coarea.lipschitzExceptionalSet
          (orientedShellParameter K frame c) ∧
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c) s y).Finite ∧
      (Submission.Coarea.fiberCount (orientedShellParameter K frame c) s y : ℝ≥0∞) ≤
        (∫⁻ t in s, ENNReal.ofReal
          |deriv (orientedShellParameter K frame c) t|) /
            ENNReal.ofReal (b - a) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_orientedShellParameter K frame c
  exact Submission.Coarea.exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact
    hC hs hab

end

end PardonDistortion
end Submission
