import Submission.PardonReduction
import Submission.Shrinking

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

/-- The weighted intersection count for a double bubble: intersections with
the outer sphere count once and intersections with the shared cutting disk
count twice, once for each of the two resulting spheres. -/
noncomputable def doubleBubbleCount (outer cut : Set ℝ) : ℕ :=
  outer.ncard + 2 * cut.ncard

lemma doubleBubbleCount_cast
    (outer cut : Set ℝ) :
    (doubleBubbleCount outer cut : ℝ) =
      (outer.ncard : ℝ) + 2 * (cut.ncard : ℝ) := by
  simp [doubleBubbleCount]

/-- Pardon's two coarea estimates, `80D` on the outer sphere and `40D` on the
cutting disk, give the final `160D` weighted count. -/
lemma doubleBubbleCount_lt_one_sixty
    (outer cut : Set ℝ) (D : ℝ)
    (houter : (outer.ncard : ℝ) < 80 * D)
    (hcut : (cut.ncard : ℝ) < 40 * D) :
    (doubleBubbleCount outer cut : ℝ) < 160 * D := by
  rw [doubleBubbleCount_cast]
  linarith

/-- Abstract nested-box engine.  Once the geometric/topological argument says
that every genus-carrying box has a genus-carrying successor at scale at most
`69/70` of the old scale, local flatness (a uniform positive lower scale)
contradicts indefinite iteration. -/
theorem not_exists_nested_carrier
    (Carrier : R3 → ℝ → Prop) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hstart : ∃ c r, 0 < r ∧ Carrier c r)
    (hlower : ∀ c r, 0 < r → Carrier c r → ρ ≤ r)
    (hshrink : ∀ c r, 0 < r → Carrier c r →
      ∃ c' r', 0 < r' ∧ Carrier c' r' ∧ r' ≤ shrinkFactor * r) : False := by
  apply not_exists_uniformly_positive_shrinkable
    (fun r ↦ ∃ c, Carrier c r) shrinkFactor ρ
    shrinkFactor_pos.le shrinkFactor_lt_one hρ
  · obtain ⟨c, r, hr, hc⟩ := hstart
    exact ⟨r, hr, c, hc⟩
  · rintro r hr ⟨c, hc⟩
    exact hlower c r hr hc
  · rintro r hr ⟨c, hc⟩
    obtain ⟨c', r', hr', hc', hscale⟩ := hshrink c r hr hc
    exact ⟨r', hr', ⟨c', hc'⟩, hscale⟩

/-- Contrapositive packaging of the nested-box engine.  If a shrinking
successor exists whenever `160D < I`, then the invariant is at most `160D`. -/
lemma invariant_le_one_sixty_of_carrier
    (Carrier : R3 → ℝ → Prop) (I D ρ : ℝ)
    (hρ : 0 < ρ)
    (hstart : ∃ c r, 0 < r ∧ Carrier c r)
    (hlower : ∀ c r, 0 < r → Carrier c r → ρ ≤ r)
    (hshrink : 160 * D < I → ∀ c r, 0 < r → Carrier c r →
      ∃ c' r', 0 < r' ∧ Carrier c' r' ∧ r' ≤ shrinkFactor * r) :
    I ≤ 160 * D := by
  by_contra hnot
  have hlarge : 160 * D < I := lt_of_not_ge hnot
  exact not_exists_nested_carrier Carrier ρ hρ hstart hlower (hshrink hlarge)

end PardonDistortion
end Submission
