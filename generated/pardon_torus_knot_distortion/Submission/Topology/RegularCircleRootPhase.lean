import Submission.Topology.RegularCircleRootGlobalDegree
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Order.Interval.Set.Infinite

/-!
# Moving the seam away from regular circle roots

Regular roots in a compact period are finite, so an interior non-root phase always exists.  A
translation by that phase preserves `C¹` regularity and winding and puts the translated lift in
the seam-free situation of `RegularCircleRootGlobalDegree`.
-/

open Set

noncomputable section

namespace Submission.Topology

namespace RegularPeriodicCircleLift

variable {theta : ℝ → ℝ} {winding : ℤ}

theorem exists_nonroot_phase (H : RegularPeriodicCircleLift theta winding) :
    ∃ s ∈ Ioo (0 : ℝ) (2 * Real.pi), Circle.exp (theta s) ≠ 1 := by
  obtain ⟨s, hs, hsroot⟩ :=
    (Set.Ioo_infinite Real.two_pi_pos).exists_notMem_finite
      H.rootFinset.finite_toSet
  refine ⟨s, hs, ?_⟩
  intro hroot
  exact hsroot ((H.mem_rootFinset_iff s).mpr ⟨⟨hs.1.le, hs.2⟩, hroot⟩)

/-- A canonical phase in the open period which is not a root. -/
def nonrootPhase (H : RegularPeriodicCircleLift theta winding) : ℝ :=
  Classical.choose H.exists_nonroot_phase

theorem nonrootPhase_mem_period (H : RegularPeriodicCircleLift theta winding) :
    H.nonrootPhase ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
  (Classical.choose_spec H.exists_nonroot_phase).1

theorem exp_nonrootPhase_ne_one (H : RegularPeriodicCircleLift theta winding) :
    Circle.exp (theta H.nonrootPhase) ≠ 1 :=
  (Classical.choose_spec H.exists_nonroot_phase).2

/-- Translation of the real lift by a parameter phase. -/
def shiftedLift (_H : RegularPeriodicCircleLift theta winding) (s t : ℝ) : ℝ :=
  theta (t + s)

/-- Translation preserves all raw regular-periodic-lift hypotheses. -/
theorem shiftedRegularPeriodicCircleLift
    (H : RegularPeriodicCircleLift theta winding) (s : ℝ) :
    RegularPeriodicCircleLift (H.shiftedLift s) winding where
  contDiff_theta := H.contDiff_theta.comp (contDiff_id.add contDiff_const)
  angle_add_period t := by
    change theta (t + 2 * Real.pi + s) =
      theta (t + s) + (winding : ℝ) * (2 * Real.pi)
    rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring,
      H.angle_add_period]
  regular_root t hroot := by
    change deriv (fun x ↦ theta (x + s)) t ≠ 0
    rw [deriv_comp_add_const]
    exact H.regular_root (t + s) hroot

theorem shiftedLift_nonroot_seam
    (H : RegularPeriodicCircleLift theta winding) :
    Circle.exp (H.shiftedLift H.nonrootPhase 0) ≠ 1 := by
  simpa only [shiftedLift, zero_add] using H.exp_nonrootPhase_ne_one

/-- Every regular periodic lift has the signed-root theorem after a canonical phase translation,
with no seam hypothesis in the input. -/
theorem shifted_sum_crossingSign_eq_winding
    (H : RegularPeriodicCircleLift theta winding) :
    let S := H.shiftedRegularPeriodicCircleLift H.nonrootPhase
    ∑ i : Fin S.rootFinset.card,
      realRootCrossingSign (H.shiftedLift H.nonrootPhase) (S.orderedRoot i) = winding := by
  let S := H.shiftedRegularPeriodicCircleLift H.nonrootPhase
  exact S.sum_crossingSign_orderedRoot_eq_winding (by
    simpa only [S, shiftedLift, zero_add] using H.exp_nonrootPhase_ne_one)

end RegularPeriodicCircleLift

end Submission.Topology
