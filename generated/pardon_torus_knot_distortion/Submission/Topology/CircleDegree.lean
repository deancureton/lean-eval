import ChallengeDeps

namespace Submission
namespace PardonDistortion

open Set

/-- The standard angular parametrization of the unit circle in `ℂ`. -/
noncomputable def unitCircleParam (t : ℝ) : ℂ :=
  (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I

lemma continuous_unitCircleParam : Continuous unitCircleParam := by
  unfold unitCircleParam
  fun_prop

@[simp] lemma unitCircleParam_add_two_pi (t : ℝ) :
    unitCircleParam (t + 2 * Real.pi) = unitCircleParam t := by
  simp [unitCircleParam, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- A nonzero-degree map from the boundary circle to `Circle` cannot extend
continuously across the plane (and hence cannot extend across a disk after
precomposing with a radial retraction). -/
theorem no_circle_filling_of_nonzero_degree
    (n : ℤ) (hn : n ≠ 0) (phase : ℝ) :
    ¬ ∃ g : ℂ → Circle, Continuous g ∧
      ∀ t : ℝ, g (unitCircleParam t) = Circle.exp ((n : ℝ) * t + phase) := by
  rintro ⟨g, hg, hboundary⟩
  let gc : C(ℂ, Circle) := ⟨g, hg⟩
  have hbase : Circle.exp ((g 0 : ℂ).arg) = gc (0 : ℂ) := by
    simp [gc, Circle.exp_arg]
  obtain ⟨G, _hG0, hGlift⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℂ) ((g 0 : ℂ).arg) hbase |>.exists
  let discrepancy : ℝ → ℝ := fun t ↦
    (G (unitCircleParam t) - ((n : ℝ) * t + phase)) / (2 * Real.pi)
  have hcontinuous : Continuous discrepancy := by
    dsimp [discrepancy]
    have h₁ : Continuous (fun t : ℝ ↦ G (unitCircleParam t)) :=
      G.continuous.comp continuous_unitCircleParam
    have h₂ : Continuous (fun t : ℝ ↦ (n : ℝ) * t + phase) := by fun_prop
    exact h₁.sub h₂ |>.div_const _
  have hinteger (t : ℝ) : ∃ m : ℤ, discrepancy t = (m : ℝ) := by
    have hexp : Circle.exp (G (unitCircleParam t)) =
        Circle.exp ((n : ℝ) * t + phase) := by
      have h₁ : Circle.exp (G (unitCircleParam t)) = gc (unitCircleParam t) :=
        congrFun hGlift (unitCircleParam t)
      exact h₁.trans (hboundary t)
    obtain ⟨m, hm⟩ := (Circle.exp_eq_exp).1 hexp
    refine ⟨m, ?_⟩
    dsimp [discrepancy]
    apply (div_eq_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).2
    linarith
  have hperiod : discrepancy (2 * Real.pi) = discrepancy 0 - (n : ℝ) := by
    dsimp [discrepancy]
    have hu : unitCircleParam (2 * Real.pi) = unitCircleParam 0 := by
      simpa using unitCircleParam_add_two_pi 0
    rw [hu]
    field_simp
    ring
  obtain ⟨m₀, hm₀⟩ := hinteger 0
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · have hn_le : n ≤ -1 := by omega
    let middle : ℝ := (m₀ : ℝ) + 1 / 2
    have hmiddle : middle ∈ Set.uIcc (discrepancy 0) (discrepancy (2 * Real.pi)) := by
      rw [Set.mem_uIcc, hperiod, hm₀]
      left
      dsimp [middle]
      constructor
      · norm_num
      · have hn_le_real : (n : ℝ) ≤ -1 := by exact_mod_cast hn_le
        linarith
    obtain ⟨t, _ht, htvalue⟩ :=
      (intermediate_value_uIcc hcontinuous.continuousOn) hmiddle
    obtain ⟨m, hm⟩ := hinteger t
    have hreal : (m : ℝ) = (m₀ : ℝ) + 1 / 2 := by
      rw [hm] at htvalue
      exact htvalue
    have htwice : (2 : ℝ) * (m : ℝ) = 2 * (m₀ : ℝ) + 1 := by linarith
    have hint : (2 : ℤ) * m = 2 * m₀ + 1 := by exact_mod_cast htwice
    omega
  · have hone_le : (1 : ℤ) ≤ n := by omega
    let middle : ℝ := (m₀ : ℝ) - 1 / 2
    have hmiddle : middle ∈ Set.uIcc (discrepancy 0) (discrepancy (2 * Real.pi)) := by
      rw [Set.mem_uIcc, hperiod, hm₀]
      right
      dsimp [middle]
      constructor
      · have hone_le_real : (1 : ℝ) ≤ n := by exact_mod_cast hone_le
        linarith
      · norm_num
    obtain ⟨t, _ht, htvalue⟩ :=
      (intermediate_value_uIcc hcontinuous.continuousOn) hmiddle
    obtain ⟨m, hm⟩ := hinteger t
    have hreal : (m : ℝ) = (m₀ : ℝ) - 1 / 2 := by
      rw [hm] at htvalue
      exact htvalue
    have htwice : (2 : ℝ) * (m : ℝ) = 2 * (m₀ : ℝ) - 1 := by linarith
    have hint : (2 : ℤ) * m = 2 * m₀ - 1 := by exact_mod_cast htwice
    omega

end PardonDistortion
end Submission
