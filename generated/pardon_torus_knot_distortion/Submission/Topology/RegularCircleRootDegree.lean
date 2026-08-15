import Submission.Topology.RegularCircleRootConstruction
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Local degree of a regular real crossing

The lemmas here prove the local floor change at an isolated regular integer crossing.  They are
the analytic input for telescoping the ordered roots constructed in
`RegularCircleRootConstruction`.
-/

open Filter Set

noncomputable section

namespace Submission.Topology

private theorem exists_floor_sides_of_deriv_pos {f : ℝ → ℝ} {r a b : ℝ} {k : ℤ}
    (hf : ContDiff ℝ 1 f) (hr : f r = k) (hd : 0 < deriv f r)
    (ha : a < r) (hb : r < b) :
    ∃ x ∈ Ioo a r, ∃ y ∈ Ioo r b, ⌊f x⌋ = k - 1 ∧ ⌊f y⌋ = k := by
  let g : ℝ → ℝ := fun t ↦ f t - (k : ℝ)
  have hgr : g r = 0 := by simp only [g, hr, sub_self]
  have hdg : 0 < deriv g r := by
    simpa only [g, deriv_sub_const] using hd
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hdg hgr
  have hgcont : ContinuousAt g r :=
    hf.continuous.continuousAt.sub continuousAt_const
  have hclose : ∀ᶠ t in nhds r, g t ∈ Ioo (-1 : ℝ) 1 :=
    hgcont.eventually (isOpen_Ioo.mem_nhds (by simp only [hgr]; norm_num))
  have hevent : ∀ᶠ t in nhds r,
      SignType.sign (g t) = SignType.sign (t - r) ∧ g t ∈ Ioo (-1 : ℝ) 1 :=
    hsign.and hclose
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ : ℝ := min (ε / 2) (min ((r - a) / 2) ((b - r) / 2))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  let x := r - δ
  let y := r + δ
  have hxdist : dist x r < ε := by
    rw [show dist x r = δ by
      rw [Real.dist_eq, show x - r = -δ by dsimp only [x]; ring, abs_neg, abs_of_pos hδ]]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hydist : dist y r < ε := by
    rw [show dist y r = δ by simp only [y, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos hδ]]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hxP := heps hxdist
  have hyP := heps hydist
  have hxa : a < x := by
    dsimp only [x, δ]
    have hle : min (ε / 2) (min ((r - a) / 2) ((b - r) / 2)) ≤ (r - a) / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hxr : x < r := by dsimp only [x]; linarith
  have hyr : r < y := by dsimp only [y]; linarith
  have hyb : y < b := by
    dsimp only [y, δ]
    have hle : min (ε / 2) (min ((r - a) / 2) ((b - r) / 2)) ≤ (b - r) / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨x, ⟨hxa, hxr⟩, y, ⟨hyr, hyb⟩, ?_, ?_⟩
  · rw [Int.floor_eq_iff]
    have hgneg : g x < 0 := by
      rw [← sign_eq_neg_one_iff, hxP.1]
      apply sign_neg
      dsimp only [x]
      linarith
    dsimp only [g] at hxP hgneg
    constructor <;> simp only [Int.cast_sub, Int.cast_one] <;> linarith [hxP.2.1]
  · rw [Int.floor_eq_iff]
    have hgpos : 0 < g y := by
      rw [← sign_eq_one_iff, hyP.1]
      apply sign_pos
      dsimp only [y]
      linarith
    dsimp only [g] at hyP hgpos
    constructor <;> linarith [hyP.2.2]

private theorem exists_floor_sides_of_deriv_neg {f : ℝ → ℝ} {r a b : ℝ} {k : ℤ}
    (hf : ContDiff ℝ 1 f) (hr : f r = k) (hd : deriv f r < 0)
    (ha : a < r) (hb : r < b) :
    ∃ x ∈ Ioo a r, ∃ y ∈ Ioo r b, ⌊f x⌋ = k ∧ ⌊f y⌋ = k - 1 := by
  let g : ℝ → ℝ := fun t ↦ f t - (k : ℝ)
  have hgr : g r = 0 := by simp only [g, hr, sub_self]
  have hdg : deriv g r < 0 := by
    simpa only [g, deriv_sub_const] using hd
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hdg hgr
  have hgcont : ContinuousAt g r :=
    hf.continuous.continuousAt.sub continuousAt_const
  have hclose : ∀ᶠ t in nhds r, g t ∈ Ioo (-1 : ℝ) 1 :=
    hgcont.eventually (isOpen_Ioo.mem_nhds (by simp only [hgr]; norm_num))
  have hevent : ∀ᶠ t in nhds r,
      SignType.sign (g t) = SignType.sign (r - t) ∧ g t ∈ Ioo (-1 : ℝ) 1 :=
    hsign.and hclose
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ : ℝ := min (ε / 2) (min ((r - a) / 2) ((b - r) / 2))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  let x := r - δ
  let y := r + δ
  have hxP : SignType.sign (g x) = SignType.sign (r - x) ∧
      g x ∈ Ioo (-1 : ℝ) 1 := by
    apply heps
    rw [show dist x r = δ by
      rw [Real.dist_eq, show x - r = -δ by dsimp only [x]; ring, abs_neg, abs_of_pos hδ]]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hyP : SignType.sign (g y) = SignType.sign (r - y) ∧
      g y ∈ Ioo (-1 : ℝ) 1 := by
    apply heps
    rw [show dist y r = δ by simp only [y, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos hδ]]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hxa : a < x := by
    dsimp only [x, δ]
    have hle : min (ε / 2) (min ((r - a) / 2) ((b - r) / 2)) ≤ (r - a) / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hxr : x < r := by dsimp only [x]; linarith
  have hyr : r < y := by dsimp only [y]; linarith
  have hyb : y < b := by
    dsimp only [y, δ]
    have hle : min (ε / 2) (min ((r - a) / 2) ((b - r) / 2)) ≤ (b - r) / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨x, ⟨hxa, hxr⟩, y, ⟨hyr, hyb⟩, ?_, ?_⟩
  · rw [Int.floor_eq_iff]
    have hgpos : 0 < g x := by
      rw [← sign_eq_one_iff, hxP.1]
      apply sign_pos
      dsimp only [x]
      linarith
    dsimp only [g] at hxP hgpos
    constructor <;> linarith [hxP.2.2]
  · rw [Int.floor_eq_iff]
    have hgneg : g y < 0 := by
      rw [← sign_eq_neg_one_iff, hyP.1]
      apply sign_neg
      dsimp only [y]
      linarith
    dsimp only [g] at hyP hgneg
    constructor <;> simp only [Int.cast_sub, Int.cast_one] <;> linarith [hyP.2.1]

/-- An interval containing exactly one integer root changes floor by the crossing sign. -/
theorem floor_sub_floor_eq_crossingSign_of_unique_root
    {f : ℝ → ℝ} {a r b : ℝ} {k : ℤ}
    (hf : ContDiff ℝ 1 f) (ha : a < r) (hb : r < b) (hr : f r = k)
    (hregular : deriv f r ≠ 0)
    (hunique : ∀ t ∈ Icc a b, (∃ z : ℤ, f t = z) → t = r) :
    ⌊f b⌋ - ⌊f a⌋ = realRootCrossingSign f r := by
  rcases lt_or_gt_of_ne hregular with hneg | hpos
  · obtain ⟨x, hx, y, hy, hfloorx, hfloory⟩ :=
      exists_floor_sides_of_deriv_neg hf hr hneg ha hb
    have hax : ⌊f a⌋ = ⌊f x⌋ := floor_eq_of_forall_ne_intCast hx.1.le
      hf.continuous.continuousOn fun t ht z htz ↦ by
        have htr := hunique t ⟨ht.1, ht.2.trans (hx.2.le.trans hb.le)⟩ ⟨z, htz⟩
        rw [htr] at ht
        exact (not_le_of_gt hx.2) ht.2
    have hyb : ⌊f y⌋ = ⌊f b⌋ := floor_eq_of_forall_ne_intCast hy.2.le
      hf.continuous.continuousOn fun t ht z htz ↦ by
        have htr := hunique t ⟨ha.le.trans (hy.1.le.trans ht.1), ht.2⟩ ⟨z, htz⟩
        rw [htr] at ht
        exact (not_le_of_gt hy.1) ht.1
    rw [← hyb, hax, hfloory, hfloorx, realRootCrossingSign, if_neg (not_lt.mpr hneg.le)]
    omega
  · obtain ⟨x, hx, y, hy, hfloorx, hfloory⟩ :=
      exists_floor_sides_of_deriv_pos hf hr hpos ha hb
    have hax : ⌊f a⌋ = ⌊f x⌋ := floor_eq_of_forall_ne_intCast hx.1.le
      hf.continuous.continuousOn fun t ht z htz ↦ by
        have htr := hunique t ⟨ht.1, ht.2.trans (hx.2.le.trans hb.le)⟩ ⟨z, htz⟩
        rw [htr] at ht
        exact (not_le_of_gt hx.2) ht.2
    have hyb : ⌊f y⌋ = ⌊f b⌋ := floor_eq_of_forall_ne_intCast hy.2.le
      hf.continuous.continuousOn fun t ht z htz ↦ by
        have htr := hunique t ⟨ha.le.trans (hy.1.le.trans ht.1), ht.2⟩ ⟨z, htz⟩
        rw [htr] at ht
        exact (not_le_of_gt hy.1) ht.1
    rw [← hyb, hax, hfloory, hfloorx, realRootCrossingSign, if_pos hpos]
    omega

/-- Ordered integer roots together with one non-root gap point before and after every root.  Unlike
`OrderedRegularCircleRootData`, this structure contains no jump or signed-sum conclusion. -/
structure OrderedRegularIntegerRootGaps (f : ℝ → ℝ) (a b : ℝ) where
  count : ℕ
  root : Fin count → ℝ
  gap : Fin (count + 1) → ℝ
  gap_zero : gap 0 = a
  gap_last : gap (Fin.last count) = b
  gap_lt_root : ∀ i, gap i.castSucc < root i
  root_lt_gap : ∀ i, root i < gap i.succ
  root_intCast : ∀ i, ∃ k : ℤ, f (root i) = k
  regular_root : ∀ i, deriv f (root i) ≠ 0
  unique_root_between : ∀ i t,
    t ∈ Icc (gap i.castSucc) (gap i.succ) →
      (∃ k : ℤ, f t = k) → t = root i

namespace OrderedRegularIntegerRootGaps

variable {f : ℝ → ℝ} {a b : ℝ}

/-- A finite ordered collection of all regular integer crossings has signed count equal to the
endpoint floor change.  The proof derives each jump from the derivative, then telescopes. -/
theorem sum_crossingSign_eq_floor_sub_floor
    (G : OrderedRegularIntegerRootGaps f a b) (hf : ContDiff ℝ 1 f) :
    ∑ i : Fin G.count, realRootCrossingSign f (G.root i) = ⌊f b⌋ - ⌊f a⌋ := by
  let sheet : ℕ → ℤ := fun i ↦
    if hi : i ≤ G.count then ⌊f (G.gap ⟨i, Nat.lt_succ_iff.mpr hi⟩)⌋ else 0
  have hjump (i : Fin G.count) :
      sheet (i.1 + 1) - sheet i.1 = realRootCrossingSign f (G.root i) := by
    obtain ⟨k, hk⟩ := G.root_intCast i
    have hlocal := floor_sub_floor_eq_crossingSign_of_unique_root hf
      (G.gap_lt_root i) (G.root_lt_gap i) hk (G.regular_root i)
      (G.unique_root_between i)
    have hsucc :
        (⟨i.1 + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_iff.mpr i.isLt)⟩ :
          Fin (G.count + 1)) = i.succ := by
      apply Fin.ext
      rfl
    have hcast :
        (⟨i.1, Nat.lt_succ_iff.mpr (Nat.le_of_lt i.isLt)⟩ :
          Fin (G.count + 1)) = i.castSucc := by
      apply Fin.ext
      rfl
    simp only [sheet, Nat.le_of_lt i.isLt, Nat.succ_le_iff.mpr i.isLt, dite_true,
      hsucc, hcast]
    exact hlocal
  calc
    (∑ i : Fin G.count, realRootCrossingSign f (G.root i)) =
        ∑ i : Fin G.count, (sheet (i.1 + 1) - sheet i.1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hjump i).symm
    _ = ∑ i ∈ Finset.range G.count, (sheet (i + 1) - sheet i) := by
      exact Fin.sum_univ_eq_sum_range (fun i ↦ sheet (i + 1) - sheet i) G.count
    _ = sheet G.count - sheet 0 := Finset.sum_range_sub sheet G.count
    _ = ⌊f b⌋ - ⌊f a⌋ := by
      simp only [sheet, le_rfl, Nat.zero_le, dite_true]
      rw [show (⟨G.count, Nat.lt_succ_self G.count⟩ : Fin (G.count + 1)) =
        Fin.last G.count by rfl, G.gap_last, show (⟨0, Nat.succ_pos G.count⟩ :
          Fin (G.count + 1)) = 0 by rfl, G.gap_zero]

end OrderedRegularIntegerRootGaps

end Submission.Topology
