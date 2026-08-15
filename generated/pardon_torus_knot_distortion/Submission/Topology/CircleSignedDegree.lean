import Submission.Topology.IntersectionCertificate
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# One-dimensional signed degree on the circle

This module isolates the ordered one-dimensional argument behind transverse intersection counts.
A smooth real lift `theta` has roots where `Circle.exp (theta t) = 1`.  An ordered regular-root
datum records those roots exactly, the sign of the nonzero derivative, and the integer sheet on
each successive complementary interval.  The sheet changes by the local crossing sign and gains
the winding integer over one complete period.

The signed-root theorem is then a genuine telescoping proof: it does not assume the signed sum.
Constructing the sheet data from local inverse-function/sign-change estimates is intentionally a
separate geometric bridge, so callers can state precisely which regularity input they possess.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Submission.Topology

/-- The orientation of a regular scalar root. -/
def realRootCrossingSign (theta : ℝ → ℝ) (t : ℝ) : ℤ :=
  if 0 < deriv theta t then 1 else -1

@[simp] theorem realRootCrossingSign_natAbs (theta : ℝ → ℝ) (t : ℝ) :
    (realRootCrossingSign theta t).natAbs = 1 := by
  simp only [realRootCrossingSign]
  split <;> norm_num

/-- Ordered regular roots of `exp(theta) = 1` in the canonical half-open period, together with
the integer sheet on successive complementary intervals.  `sheet_jump` is the local crossing
conclusion supplied by the sign of the derivative; `sheet_end` is the seam conclusion supplied by
the lift's exact winding.  Neither field states a global signed sum. -/
structure OrderedRegularCircleRootData (theta : ℝ → ℝ) (winding : ℤ) where
  contDiff_theta : ContDiff ℝ 1 theta
  angle_add_period : ∀ t,
    theta (t + 2 * Real.pi) = theta t + (winding : ℝ) * (2 * Real.pi)
  count : ℕ
  root : Fin count → ℝ
  strictMono_root : StrictMono root
  root_mem_period : ∀ i, root i ∈ Ico (0 : ℝ) (2 * Real.pi)
  root_exp_eq_one : ∀ i, Circle.exp (theta (root i)) = 1
  root_complete : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
    Circle.exp (theta t) = 1 → ∃ i, root i = t
  regular_root : ∀ i, deriv theta (root i) ≠ 0
  sheet : ℕ → ℤ
  sheet_jump : ∀ i : Fin count,
    sheet (i.1 + 1) - sheet i.1 = realRootCrossingSign theta (root i)
  sheet_end : sheet count - sheet 0 = winding

namespace OrderedRegularCircleRootData

variable {theta : ℝ → ℝ} {winding : ℤ}

/-- The finite root set in the canonical half-open period. -/
def rootFinset (D : OrderedRegularCircleRootData theta winding) : Finset ℝ :=
  Finset.univ.image D.root

theorem root_injective (D : OrderedRegularCircleRootData theta winding) :
    Function.Injective D.root :=
  D.strictMono_root.injective

theorem mem_rootFinset_iff (D : OrderedRegularCircleRootData theta winding) (t : ℝ) :
    t ∈ D.rootFinset ↔
      t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧ Circle.exp (theta t) = 1 := by
  constructor
  · intro ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    subst t
    exact ⟨D.root_mem_period i, D.root_exp_eq_one i⟩
  · rintro ⟨ht, hroot⟩
    obtain ⟨i, hi⟩ := D.root_complete t ht hroot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

theorem rootFinset_card (D : OrderedRegularCircleRootData theta winding) :
    D.rootFinset.card = D.count := by
  rw [rootFinset, Finset.card_image_iff.mpr D.root_injective.injOn]
  simp

/-- The signed sum over the ordered root indices is the winding.  This is the core one-dimensional
crossing theorem and is just the telescoping sum of successive sheet changes. -/
theorem sum_crossingSign_indices (D : OrderedRegularCircleRootData theta winding) :
    ∑ i : Fin D.count, realRootCrossingSign theta (D.root i) = winding := by
  calc
    (∑ i : Fin D.count, realRootCrossingSign theta (D.root i)) =
        ∑ i : Fin D.count, (D.sheet (i.1 + 1) - D.sheet i.1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (D.sheet_jump i).symm
    _ = ∑ i ∈ Finset.range D.count, (D.sheet (i + 1) - D.sheet i) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i ↦ D.sheet (i + 1) - D.sheet i) D.count
    _ = D.sheet D.count - D.sheet 0 := Finset.sum_range_sub D.sheet D.count
    _ = winding := D.sheet_end

/-- Finset form of the one-dimensional signed crossing theorem. -/
theorem sum_crossingSign_rootFinset (D : OrderedRegularCircleRootData theta winding) :
    ∑ t ∈ D.rootFinset, realRootCrossingSign theta t = winding := by
  rw [rootFinset, Finset.sum_image D.root_injective.injOn]
  exact D.sum_crossingSign_indices

end OrderedRegularCircleRootData

end Submission.Topology
