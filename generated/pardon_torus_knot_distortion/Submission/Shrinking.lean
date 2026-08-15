import Mathlib.Analysis.SpecificLimits.Basic

namespace Submission
namespace PardonDistortion

/-- A positive scale predicate with a uniform positive lower bound cannot be
closed under shrinking by a fixed factor strictly between zero and one. -/
theorem not_exists_uniformly_positive_shrinkable
    (P : ℝ → Prop) (c ρ : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) (hρ : 0 < ρ)
    (hstart : ∃ r, 0 < r ∧ P r)
    (hlower : ∀ r, 0 < r → P r → ρ ≤ r)
    (hshrink : ∀ r, 0 < r → P r →
      ∃ r', 0 < r' ∧ P r' ∧ r' ≤ c * r) : False := by
  let S := {r : ℝ // 0 < r ∧ P r}
  let start : S := ⟨hstart.choose, hstart.choose_spec⟩
  let next : S → S := fun r ↦
    ⟨(hshrink r r.property.1 r.property.2).choose,
      (hshrink r r.property.1 r.property.2).choose_spec.1,
      (hshrink r r.property.1 r.property.2).choose_spec.2.1⟩
  let u : ℕ → S := fun n ↦ (next^[n]) start
  have hstep (n : ℕ) : (u (n + 1) : ℝ) ≤ c * (u n : ℝ) := by
    change ((next^[n + 1]) start : ℝ) ≤ c * ((next^[n]) start : ℝ)
    rw [Function.iterate_succ_apply']
    exact (hshrink _ ((next^[n]) start).property.1
      ((next^[n]) start).property.2).choose_spec.2.2
  have hgeom (n : ℕ) : (u n : ℝ) ≤ c ^ n * (start : ℝ) := by
    exact le_geom (u := fun k ↦ (u k : ℝ)) hc₀ n fun k _ ↦ hstep k
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hρ start.property.1) hc₁
  have hsmall : c ^ n * (start : ℝ) < ρ := by
    exact (lt_div_iff₀ start.property.1).mp hn
  have hlarge : ρ ≤ (u n : ℝ) :=
    hlower (u n) (u n).property.1 (u n).property.2
  exact (not_lt_of_ge (hlarge.trans (hgeom n))) hsmall

end PardonDistortion
end Submission
