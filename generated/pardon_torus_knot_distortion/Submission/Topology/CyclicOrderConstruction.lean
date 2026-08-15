import Submission.Topology.PlaneSliceComponents

/-!
# Constructing cyclic excursion bookkeeping from ordered crossings

The analytic input in `SmoothRegularLoopCutData` constructs the finite crossing finset.  Sorting
that finset on a circle produces finitely many lifted intervals, with the seam interval ending in
the next period.  This module packages precisely that pure order-theoretic output as
`OrderedCyclicIntervalSkeleton` and constructs `FiniteCyclicExcursionBookkeeping` from it.

No side labels are assumed.  Every interval's label is chosen from the sign of its midpoint, and
regularity plus absence of interior crossings proves that the whole interval has that sign.  The
only strengthened transverse input is `opposite_signs_at_common_endpoint`; it is the elementary
local sign-change fact supplied by a nonzero derivative when two representatives share an
endpoint.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}
  {H : SmoothRegularLoopCutData frame d L}

/-- The sorted cyclic interval skeleton obtained from a nonempty finite crossing set.

The representatives start in `[0,2π)`.  Their right endpoints may be in the following period,
which is exactly how the seam interval is represented.  Coverage and pairwise disjointness are
stated for all integer translates, making the result independent of a chosen fundamental
period. -/
structure OrderedCyclicIntervalSkeleton
    (H : SmoothRegularLoopCutData frame d L) where
  count : ℕ
  count_pos : 0 < count
  left : Fin count → ℝ
  right : Fin count → ℝ
  left_mem_period : ∀ i, left i ∈ Ico (0 : ℝ) (2 * Real.pi)
  left_lt_right : ∀ i, left i < right i
  right_le_next_period : ∀ i, right i ≤ left i + 2 * Real.pi
  left_crossing : ∀ i, windingLoopCutHeight frame d L (left i) = 0
  right_crossing : ∀ i, windingLoopCutHeight frame d L (right i) = 0
  translated_pairwise_disjoint : Pairwise fun p q : Fin count × ℤ ↦
    Disjoint
      (Ioo (left p.1 + (p.2 : ℝ) * (2 * Real.pi))
        (right p.1 + (p.2 : ℝ) * (2 * Real.pi)))
      (Ioo (left q.1 + (q.2 : ℝ) * (2 * Real.pi))
        (right q.1 + (q.2 : ℝ) * (2 * Real.pi)))
  cover_noncrossings : ∀ t,
    windingLoopCutHeight frame d L t ≠ 0 →
      ∃ (i : Fin count) (n : ℤ),
        t ∈ Ioo (left i + (n : ℝ) * (2 * Real.pi))
          (right i + (n : ℝ) * (2 * Real.pi))
  no_crossing_in_interval : ∀ (i : Fin count) (n : ℤ) t,
    t ∈ Ioo (left i + (n : ℝ) * (2 * Real.pi))
      (right i + (n : ℝ) * (2 * Real.pi)) →
        windingLoopCutHeight frame d L t ≠ 0
  opposite_signs_at_common_endpoint : ∀ i j,
    i ≠ j → right i = left j →
      ∃ x ∈ Ioo (left i) (right i), ∃ y ∈ Ioo (left j) (right j),
        windingLoopCutHeight frame d L x *
          windingLoopCutHeight frame d L y < 0

namespace OrderedCyclicIntervalSkeleton

variable (S : OrderedCyclicIntervalSkeleton H)

/-- Midpoint of a representative lifted interval. -/
def midpoint (i : Fin S.count) : ℝ := (S.left i + S.right i) / 2

theorem midpoint_mem (i : Fin S.count) :
    S.midpoint i ∈ Ioo (S.left i) (S.right i) := by
  constructor <;> dsimp [midpoint] <;> linarith [S.left_lt_right i]

/-- Side chosen from the midpoint: `true` means upper. -/
def intervalUpper (i : Fin S.count) : Bool :=
  if 0 < windingLoopCutHeight frame d L (S.midpoint i) then true else false

theorem midpoint_ne_zero (i : Fin S.count) :
    windingLoopCutHeight frame d L (S.midpoint i) ≠ 0 := by
  have hm := S.midpoint_mem i
  have hm0 : S.midpoint i ∈ Ioo
      (S.left i + (0 : ℤ) * (2 * Real.pi))
      (S.right i + (0 : ℤ) * (2 * Real.pi)) := by
    simpa using hm
  exact S.no_crossing_in_interval i 0 (S.midpoint i) hm0

/-- The chosen midpoint label is valid on the entire open interval. -/
theorem strict_side (i : Fin S.count) (t : ℝ)
    (ht : t ∈ Ioo (S.left i) (S.right i)) :
    if S.intervalUpper i then 0 < windingLoopCutHeight frame d L t
      else windingLoopCutHeight frame d L t < 0 := by
  have hzero : ∀ u ∈ Ioo (S.left i) (S.right i),
      windingLoopCutHeight frame d L u ≠ 0 := by
    intro u hu
    apply S.no_crossing_in_interval i 0 u
    simpa using hu
  have hsign := H.crossingFreeArc_all_neg_or_all_pos
    isPreconnected_Ioo (nonempty_Ioo.mpr (S.left_lt_right i)) hzero
  by_cases hmid : 0 < windingLoopCutHeight frame d L (S.midpoint i)
  · have hu : S.intervalUpper i = true := by simp [intervalUpper, hmid]
    rw [hu]
    simp only [if_true]
    rcases hsign with hneg | hpos
    · exact False.elim ((not_lt_of_ge (hmid.le)) (hneg _ (S.midpoint_mem i)))
    · exact hpos t ht
  · have hu : S.intervalUpper i = false := by simp [intervalUpper, hmid]
    rw [hu]
    simp only [Bool.false_eq_true, if_false]
    rcases hsign with hneg | hpos
    · exact hneg t ht
    · exact False.elim (hmid (hpos _ (S.midpoint_mem i)))

/-- Construct the fully signed excursion representative. -/
def excursion (i : Fin S.count) : CyclicExcursionInterval H where
  left := S.left i
  right := S.right i
  left_mem_period := S.left_mem_period i
  left_lt_right := S.left_lt_right i
  right_le_next_period := S.right_le_next_period i
  left_crossing := S.left_crossing i
  right_crossing := S.right_crossing i
  upper := S.intervalUpper i
  strict_side := S.strict_side i

theorem excursion_translatedParams (i : Fin S.count) (n : ℤ) :
    (S.excursion i).translatedParams n =
      Ioo (S.left i + (n : ℝ) * (2 * Real.pi))
        (S.right i + (n : ℝ) * (2 * Real.pi)) := rfl

/-- Adjacent representatives receive opposite side labels. -/
theorem intervalUpper_ne_of_common_endpoint {i j : Fin S.count}
    (hij : i ≠ j) (hcommon : S.right i = S.left j) :
    S.intervalUpper i ≠ S.intervalUpper j := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    S.opposite_signs_at_common_endpoint i j hij hcommon
  intro heq
  have hxi := S.strict_side i x hx
  have hyj := S.strict_side j y hy
  rw [heq] at hxi
  cases hside : S.intervalUpper j with
  | false =>
      simp [hside] at hxi hyj
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hxi.le hyj.le)) hxy
  | true =>
      simp [hside] at hxi hyj
      exact (not_lt_of_ge (mul_nonneg hxi.le hyj.le)) hxy

/-- The complete finite cyclic excursion bookkeeping constructed from the ordered skeleton. -/
def toFiniteCyclicExcursionBookkeeping :
    FiniteCyclicExcursionBookkeeping H where
  count := S.count
  excursion := S.excursion
  translated_pairwise_disjoint := by
    intro p q hpq
    simpa only [excursion_translatedParams] using
      S.translated_pairwise_disjoint hpq
  cover_noncrossings := by
    intro t ht
    obtain ⟨i, n, hin⟩ := S.cover_noncrossings t ht
    exact ⟨i, n, by simpa only [excursion_translatedParams] using hin⟩
  no_crossing_in_excursion := by
    intro i n t ht
    apply S.no_crossing_in_interval i n t
    simpa only [excursion_translatedParams] using ht
  alternating_at_common_endpoint := by
    intro i j hij hcommon
    exact S.intervalUpper_ne_of_common_endpoint hij hcommon

end OrderedCyclicIntervalSkeleton

end Submission.Topology
