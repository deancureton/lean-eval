import Submission.Coarea.General
import Submission.Coarea.BoxShell
import Mathlib.Analysis.Calculus.Rademacher

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Submission.Coarea

noncomputable section

/-!
# One-dimensional coarea for Lipschitz functions

The quantitative sets below turn pointwise differentiability with nonzero
derivative into a countable measurable partition by injective pieces.  This is
the one-dimensional decomposition underlying the Lipschitz area formula.
-/

/-- Points from which `f` expands all sufficiently nearby distances by at
least `c`. -/
def lowerLipSet (f : ℝ → ℝ) (c δ : ℝ) : Set ℝ :=
  {x | ∀ y, dist y x < δ → c * dist y x ≤ dist (f y) (f x)}

lemma isClosed_lowerLipSet {f : ℝ → ℝ} (hf : Continuous f) (c δ : ℝ) :
    IsClosed (lowerLipSet f c δ) := by
  have heq : lowerLipSet f c δ =
      ⋂ y : ℝ, {x | δ ≤ dist y x} ∪
        {x | c * dist y x ≤ dist (f y) (f x)} := by
    ext x
    simp only [lowerLipSet, mem_ofPred_eq, mem_iInter, mem_union]
    constructor
    · intro h y
      by_cases hy : dist y x < δ
      · exact Or.inr (h y hy)
      · exact Or.inl (le_of_not_gt hy)
    · intro h y hy
      rcases h y with hfar | hlower
      · exact False.elim ((not_lt_of_ge hfar) hy)
      · exact hlower
  rw [heq]
  apply isClosed_iInter
  intro y
  apply IsClosed.union
  · exact isClosed_le continuous_const (continuous_const.dist continuous_id)
  · exact isClosed_le
      (continuous_const.mul (continuous_const.dist continuous_id))
      ((hf.comp continuous_const).dist hf)

lemma injOn_lowerLipSet_inter_of_diam_lt {f : ℝ → ℝ} {c δ : ℝ}
    (hc : 0 < c) {u : Set ℝ}
    (hdiam : ∀ x ∈ u, ∀ y ∈ u, dist y x < δ) :
    InjOn f (lowerLipSet f c δ ∩ u) := by
  intro x hx y hy hxy
  by_contra hne
  have hdist : 0 < dist y x := dist_pos.mpr (Ne.symm hne)
  have hlower := hx.1 y (hdiam x hx.2 y hy.2)
  rw [hxy, dist_self] at hlower
  exact (not_le_of_gt (mul_pos hc hdist)) hlower

/-- A nonzero derivative supplies one of the quantitative lower-Lipschitz
neighborhoods. -/
lemma exists_mem_lowerLipSet_of_hasDerivAt {f : ℝ → ℝ} {x d : ℝ}
    (hderiv : HasDerivAt f d x) (hd : d ≠ 0) :
    ∃ n m : ℕ,
      x ∈ lowerLipSet f (1 / (n + 1 : ℝ)) (1 / (m + 1 : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  have hc : (1 / (n + 1 : ℝ)) < |d| := by simpa [Real.norm_eq_abs] using hn
  have hevent : ∀ᶠ y in 𝓝[≠] x,
      (1 / (n + 1 : ℝ)) < ‖slope f x y‖ :=
    ((hderiv.tendsto_slope.norm).eventually (Ioi_mem_nhds hc))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨n, m, ?_⟩
  intro y hy
  by_cases hyx : y = x
  · subst y
    simp
  have hslope : (1 / (n + 1 : ℝ)) < ‖slope f x y‖ :=
    hball ⟨show y ∈ Metric.ball x ε by simpa [Metric.mem_ball, dist_comm] using hy.trans hm,
      by simpa using hyx⟩
  have hdist : 0 < dist y x := dist_pos.mpr hyx
  rw [slope, norm_smul, Real.norm_eq_abs, abs_inv, abs_sub_comm,
    ← Real.dist_eq, vsub_eq_sub, ← dist_eq_norm] at hslope
  have hslope' : (1 / (n + 1 : ℝ)) < dist (f y) (f x) / dist y x := by
    simpa [div_eq_inv_mul, dist_comm] using hslope
  exact ((lt_div_iff₀ hdist).mp hslope').le

/-- A short interval cut out of a quantitative lower-Lipschitz set. -/
def lowerLipCell (f : ℝ → ℝ) (n m : ℕ) (k : ℤ) : Set ℝ :=
  lowerLipSet f (1 / (n + 1 : ℝ)) (1 / (m + 1 : ℝ)) ∩
    Ico ((k : ℝ) * (1 / (m + 1 : ℝ) / 2))
      ((k + 1 : ℤ) * (1 / (m + 1 : ℝ) / 2))

lemma measurableSet_lowerLipCell {f : ℝ → ℝ} (hf : Continuous f)
    (n m : ℕ) (k : ℤ) : MeasurableSet (lowerLipCell f n m k) :=
  (isClosed_lowerLipSet hf _ _).measurableSet.inter measurableSet_Ico

lemma injOn_lowerLipCell (f : ℝ → ℝ) (n m : ℕ) (k : ℤ) :
    InjOn f (lowerLipCell f n m k) := by
  have hc : 0 < (1 / (n + 1 : ℝ)) := by positivity
  apply injOn_lowerLipSet_inter_of_diam_lt hc
  intro x hx y hy
  have hδ : 0 < (1 / (m + 1 : ℝ)) := by positivity
  have hw : 0 < (1 / (m + 1 : ℝ) / 2) := by positivity
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  push_cast at hxhi hyhi
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

/-- A fixed coding of the three integer parameters of `lowerLipCell` by a
natural number. -/
def lowerLipIndexEquiv : ((ℕ × ℕ) × ℤ) ≃ ℕ :=
  (Equiv.prodCongr Nat.pairEquiv Equiv.intEquivNat).trans Nat.pairEquiv

/-- Enumeration of all quantitative lower-Lipschitz cells. -/
def lowerLipCandidate (f : ℝ → ℝ) (j : ℕ) : Set ℝ :=
  let z := lowerLipIndexEquiv.symm j
  lowerLipCell f z.1.1 z.1.2 z.2

lemma measurableSet_lowerLipCandidate {f : ℝ → ℝ} (hf : Continuous f) (j : ℕ) :
    MeasurableSet (lowerLipCandidate f j) := by
  exact measurableSet_lowerLipCell hf _ _ _

lemma injOn_lowerLipCandidate (f : ℝ → ℝ) (j : ℕ) :
    InjOn f (lowerLipCandidate f j) := by
  exact injOn_lowerLipCell f _ _ _

/-- Every point with a nonzero derivative lies in one enumerated injective
cell. -/
lemma mem_iUnion_lowerLipCandidate_of_hasDerivAt {f : ℝ → ℝ} {x d : ℝ}
    (hderiv : HasDerivAt f d x) (hd : d ≠ 0) :
    x ∈ ⋃ j, lowerLipCandidate f j := by
  obtain ⟨n, m, hmem⟩ := exists_mem_lowerLipSet_of_hasDerivAt hderiv hd
  let w : ℝ := 1 / (m + 1 : ℝ) / 2
  have hw : 0 < w := by dsimp [w]; positivity
  let k : ℤ := ⌊x / w⌋
  have hlo : (k : ℝ) ≤ x / w := Int.floor_le (x / w)
  have hhi : x / w < (k : ℝ) + 1 := Int.lt_floor_add_one (x / w)
  have hxcell : x ∈ lowerLipCell f n m k := by
    refine ⟨hmem, ?_⟩
    have hxw : x / w * w = x := div_mul_cancel₀ x hw.ne'
    constructor
    · change (k : ℝ) * w ≤ x
      exact (mul_le_mul_of_nonneg_right hlo hw.le).trans_eq hxw
    · rw [Int.cast_add, Int.cast_one]
      change x < ((k : ℝ) + 1) * w
      rw [← hxw]
      exact mul_lt_mul_of_pos_right hhi hw
  let z : (ℕ × ℕ) × ℤ := ((n, m), k)
  refine mem_iUnion.mpr ⟨lowerLipIndexEquiv z, ?_⟩
  simpa [lowerLipCandidate, z] using hxcell

/-- Points where the ordinary derivative exists and is nonzero. -/
def differentiableRegularSet (f : ℝ → ℝ) : Set ℝ :=
  {x | DifferentiableAt ℝ f x ∧ deriv f x ≠ 0}

lemma measurableSet_differentiableRegularSet (f : ℝ → ℝ) :
    MeasurableSet (differentiableRegularSet f) := by
  exact (measurableSet_of_differentiableAt ℝ f).inter
    ((measurableSet_singleton 0).preimage (measurable_deriv f)).compl

lemma differentiableRegularSet_subset_iUnion_lowerLipCandidate (f : ℝ → ℝ) :
    differentiableRegularSet f ⊆ ⋃ j, lowerLipCandidate f j := by
  intro x hx
  exact mem_iUnion_lowerLipCandidate_of_hasDerivAt hx.1.hasDerivAt hx.2

/-- A measurable disjoint injective partition of the regular differentiability
set of a continuous real function, restricted to `s`. -/
theorem exists_countable_injective_partition_differentiableRegular
    {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : MeasurableSet s) :
    ∃ pieces : ℕ → Set ℝ,
      (∀ n, MeasurableSet (pieces n)) ∧
      Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)) ∧
      (∀ n, InjOn f (pieces n)) ∧
      ⋃ n, pieces n = s ∩ differentiableRegularSet f := by
  let u : ℕ → Set ℝ := lowerLipCandidate f
  let pieces : ℕ → Set ℝ := fun n ↦
    (s ∩ differentiableRegularSet f) ∩ disjointSequence u n
  have humeas : ∀ n, MeasurableSet (u n) :=
    fun n ↦ measurableSet_lowerLipCandidate hf n
  refine ⟨pieces, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hs.inter (measurableSet_differentiableRegularSet f)).inter
      (measurableSet_disjointSequence u humeas n)
  · intro i j hij
    exact ((pairwise_disjoint_disjointSequence u) hij).mono
      inter_subset_right inter_subset_right
  · intro n
    exact (injOn_lowerLipCandidate f n).mono
      (inter_subset_right.trans (disjointSequence_subset u n))
  · rw [← inter_iUnion, iUnion_disjointSequence]
    apply inter_eq_left.mpr
    exact (inter_subset_right.trans
      (differentiableRegularSet_subset_iUnion_lowerLipCandidate f))

/-- The countable branch mass of the regular differentiability set has first
moment equal to the integral of the absolute derivative. -/
theorem exists_countableBranchFiberMass_lintegral_eq_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : MeasurableSet s) :
    ∃ pieces : ℕ → Set ℝ,
      (∀ n, MeasurableSet (pieces n)) ∧
      Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)) ∧
      (∀ n, InjOn f (pieces n)) ∧
      ⋃ n, pieces n = s ∩ differentiableRegularSet f ∧
      ∫⁻ y, countableBranchFiberMass f pieces y =
        ∫⁻ x in s, ENNReal.ofReal |deriv f x| := by
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover⟩ :=
    exists_countable_injective_partition_differentiableRegular hf hs
  have hpieceRegular (n : ℕ) {x : ℝ} (hx : x ∈ pieces n) :
      x ∈ differentiableRegularSet f := by
    have hxunion : x ∈ ⋃ n, pieces n := mem_iUnion.mpr ⟨n, hx⟩
    rw [hcover] at hxunion
    exact hxunion.2
  refine ⟨pieces, hmeas, hdisj, hinj, hcover, ?_⟩
  rw [lintegral_countableBranchFiberMass_eq f (deriv f) pieces hmeas
    (fun n x hx ↦ (hpieceRegular n hx).1.hasDerivAt.hasDerivWithinAt) hinj]
  rw [← lintegral_iUnion hmeas hdisj, hcover]
  rw [← lintegral_indicator hs,
    ← lintegral_indicator (hs.inter (measurableSet_differentiableRegularSet f))]
  apply lintegral_congr
  intro x
  by_cases hxreg : x ∈ differentiableRegularSet f
  · by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem (show x ∈ s ∩ differentiableRegularSet f from ⟨hxs, hxreg⟩),
        Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem (fun h ↦ hxs h.1), Set.indicator_of_notMem hxs]
  · have hxinter : x ∉ s ∩ differentiableRegularSet f := fun h ↦ hxreg h.2
    rw [Set.indicator_of_notMem hxinter]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      by_cases hxdiff : DifferentiableAt ℝ f x
      · have hzero : deriv f x = 0 := by
          by_contra hne
          exact hxreg ⟨hxdiff, hne⟩
        simp [hzero]
      · rw [deriv_zero_of_not_differentiableAt hxdiff]
        simp
    · rw [Set.indicator_of_notMem hxs]

/-- Domain points not represented by the injective regular partition. -/
def lipschitzExceptionalSet (f : ℝ → ℝ) : Set ℝ :=
  {x | ¬DifferentiableAt ℝ f x} ∪
    {x | DifferentiableAt ℝ f x ∧ deriv f x = 0}

lemma compl_differentiableRegularSet (f : ℝ → ℝ) :
    (differentiableRegularSet f)ᶜ = lipschitzExceptionalSet f := by
  ext x
  simp only [differentiableRegularSet, lipschitzExceptionalSet, mem_compl_iff,
    mem_ofPred_eq, mem_union]
  tauto

/-- Rademacher's theorem and the Lipschitz Hausdorff-image estimate show that
the image of the nondifferentiability set is null. -/
lemma volume_image_not_differentiableAt_eq_zero {f : ℝ → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    volume (f '' {x | ¬DifferentiableAt ℝ f x}) = 0 := by
  have hnull : volume {x | ¬DifferentiableAt ℝ f x} = 0 :=
    ae_iff.mp hf.ae_differentiableAt
  have himage := hf.hausdorffMeasure_image_le (d := (1 : ℝ)) zero_le_one
    {x | ¬DifferentiableAt ℝ f x}
  have himage' : volume (f '' {x | ¬DifferentiableAt ℝ f x}) ≤
      (C : ℝ≥0∞) ^ (1 : ℝ) * volume {x | ¬DifferentiableAt ℝ f x} := by
    simpa only [MeasureTheory.hausdorffMeasure_real] using himage
  rw [hnull, mul_zero] at himage'
  exact bot_unique himage'

/-- The image of differentiability points with zero derivative is null by
the zero-Jacobian image theorem. -/
lemma volume_image_differentiableAt_deriv_eq_zero {f : ℝ → ℝ} :
    volume (f '' {x | DifferentiableAt ℝ f x ∧ deriv f x = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun x ↦ fderiv ℝ f x)
  · intro x hx
    exact hx.1.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    rw [← toSpanSingleton_deriv, ContinuousLinearMap.det_toSpanSingleton]
    exact hx.2

/-- All exceptional values of a real Lipschitz function form a null set. -/
theorem volume_image_lipschitzExceptionalSet_eq_zero
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    volume (f '' lipschitzExceptionalSet f) = 0 := by
  rw [lipschitzExceptionalSet, image_union]
  exact MeasureTheory.measure_union_null
    (volume_image_not_differentiableAt_eq_zero hf)
    volume_image_differentiableAt_deriv_eq_zero

/-- The integral of the absolute derivative of a Lipschitz real function over
a compact set is finite. -/
lemma lintegral_abs_deriv_ne_top_of_lipschitz_of_isCompact
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s : Set ℝ} (hs : IsCompact s) :
    (∫⁻ x in s, ENNReal.ofReal |deriv f x|) ≠ ⊤ := by
  have hbound : (∫⁻ x in s, ENNReal.ofReal |deriv f x|) ≤
      (C : ℝ≥0∞) * volume s := by
    calc
      (∫⁻ x in s, ENNReal.ofReal |deriv f x|) ≤
          ∫⁻ _x in s, (C : ℝ≥0∞) := by
        apply MeasureTheory.setLIntegral_mono' hs.measurableSet
        intro x _
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hf (x₀ := x)
      _ = (C : ℝ≥0∞) * volume s := MeasureTheory.setLIntegral_const s C
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.measure_ne_top) hbound

lemma lintegral_abs_deriv_le_lipschitz_mul_volume
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫⁻ x in s, ENNReal.ofReal |deriv f x|) ≤ (C : ℝ≥0∞) * volume s := by
  calc
    (∫⁻ x in s, ENNReal.ofReal |deriv f x|) ≤
        ∫⁻ _x in s, (C : ℝ≥0∞) := by
      apply MeasureTheory.setLIntegral_mono' hs
      intro x _
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hf (x₀ := x)
    _ = (C : ℝ≥0∞) * volume s := MeasureTheory.setLIntegral_const s C

/-- A Lipschitz function on a compact parameter set admits a nonexceptional
level whose actual fiber cardinality obeys the one-dimensional coarea bound.
No monotonicity-branch hypothesis is required. -/
theorem exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b,
      y ∉ f '' lipschitzExceptionalSet f ∧
      (fiberSet f s y).Finite ∧
      (fiberCount f s y : ℝ≥0∞) ≤
        (∫⁻ x in s, ENNReal.ofReal |deriv f x|) /
          ENNReal.ofReal (b - a) := by
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover, hmoment⟩ :=
    exists_countableBranchFiberMass_lintegral_eq_of_continuous
      hf.continuous hs.measurableSet
  have hpieceRegular (n : ℕ) {x : ℝ} (hx : x ∈ pieces n) :
      x ∈ differentiableRegularSet f := by
    have hxunion : x ∈ ⋃ n, pieces n := mem_iUnion.mpr ⟨n, hx⟩
    rw [hcover] at hxunion
    exact hxunion.2
  obtain ⟨y, hyIoc, hyExceptional, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab
      (measurable_countableBranchFiberMass f (deriv f) pieces hmeas
        (fun n x hx ↦ (hpieceRegular n hx).1.hasDerivAt.hasDerivWithinAt)
        hinj).aemeasurable
      hmoment.le (volume_image_lipschitzExceptionalSet_eq_zero hf)
  have hyRegular (x : ℝ) (hxy : f x = y) : x ∈ differentiableRegularSet f := by
    by_contra hx
    have hxExceptional : x ∈ lipschitzExceptionalSet f := by
      rw [← compl_differentiableRegularSet]
      exact hx
    exact hyExceptional ⟨x, hxExceptional, hxy⟩
  have hfiber : fiberSet f (⋃ n, pieces n) y = fiberSet f s y := by
    ext x
    simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxpieces, hxy⟩
      have hxsr : x ∈ s ∩ differentiableRegularSet f := by
        rw [← hcover]
        exact hxpieces
      exact ⟨hxsr.1, hxy⟩
    · rintro ⟨hxs, hxy⟩
      refine ⟨?_, hxy⟩
      rw [hcover]
      exact ⟨hxs, hyRegular x hxy⟩
  have hmassEnc : countableBranchFiberMass f pieces y =
      ((fiberSet f s y).encard : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          ((fiberSet f (⋃ n, pieces n) y).encard : ℝ≥0∞) :=
        countableBranchFiberMass_eq_encard hf.continuous pieces hmeas hdisj hinj y
      _ = ((fiberSet f s y).encard : ℝ≥0∞) := by rw [hfiber]
  have hright_ne :
      (∫⁻ x in s, ENNReal.ofReal |deriv f x|) /
          ENNReal.ofReal (b - a) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact lintegral_abs_deriv_ne_top_of_lipschitz_of_isCompact hf hs
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hmass_ne : countableBranchFiberMass f pieces y ≠ ⊤ :=
    ne_top_of_le_ne_top hright_ne hybound
  have hencard_ne : (fiberSet f s y).encard ≠ ⊤ := by
    rw [← ENat.toENNReal_ne_top, ← hmassEnc]
    exact hmass_ne
  have hfinite : (fiberSet f s y).Finite := encard_ne_top_iff.mp hencard_ne
  have hfinitePieces : (fiberSet f (⋃ n, pieces n) y).Finite := by
    rw [hfiber]
    exact hfinite
  have hmassCount : countableBranchFiberMass f pieces y =
      (fiberCount f s y : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          (fiberCount f (⋃ n, pieces n) y : ℝ≥0∞) :=
        countableBranchFiberMass_eq_fiberCount hf.continuous pieces hmeas hdisj hinj y
          hfinitePieces
      _ = (fiberCount f s y : ℝ≥0∞) := by
        change ((fiberSet f (⋃ n, pieces n) y).ncard : ℝ≥0∞) =
          ((fiberSet f s y).ncard : ℝ≥0∞)
        rw [hfiber]
  rw [hmassCount] at hybound
  exact ⟨y, hyIoc, hyExceptional, hfinite, hybound⟩

/-- A simpler consequence bounding the first moment by the Lipschitz constant
times the measure of the parameter set. -/
theorem exists_lipschitzRegularValue_fiberCount_le_mul_volume_of_isCompact
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b,
      y ∉ f '' lipschitzExceptionalSet f ∧
      (fiberSet f s y).Finite ∧
      (fiberCount f s y : ℝ≥0∞) ≤
        ((C : ℝ≥0∞) * volume s) / ENNReal.ofReal (b - a) := by
  obtain ⟨y, hy, hyExceptional, hfinite, hybound⟩ :=
    exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact hf hs hab
  refine ⟨y, hy, hyExceptional, hfinite, hybound.trans ?_⟩
  exact ENNReal.div_le_div
    (lintegral_abs_deriv_le_lipschitz_mul_volume hf hs.measurableSet) le_rfl

namespace PardonApplication

open LeanEval.KnotTheory.PardonDistortion

/-- The smooth periodic parametrization of a knot has some global Lipschitz
constant. -/
lemma exists_lipschitzWith_knotCurve (K : Knot) :
    ∃ C : ℝ≥0, LipschitzWith C K.curve := by
  have hperiodic : Function.Periodic (deriv K.curve) (2 * Real.pi) :=
    Submission.PardonDistortion.deriv_periodic K
  have hcontinuous : Continuous (deriv K.curve) :=
    K.smooth.continuous_deriv (by simp)
  have hbounded : Bornology.IsBounded (range (deriv K.curve)) :=
    hperiodic.isBounded_of_continuous (by positivity) hcontinuous
  obtain ⟨r, hr⟩ := hbounded.subset_closedBall (0 : LeanEval.KnotTheory.PardonDistortion.R3)
  let C : ℝ≥0 := ⟨max r 0, le_max_right r 0⟩
  refine ⟨C, lipschitzWith_of_nnnorm_deriv_le
    (K.smooth.differentiable (by simp)) ?_⟩
  intro x
  have hx := hr (mem_range_self x)
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact_mod_cast hx.trans (le_max_left r 0)

/-- In particular, the weighted rational-box shell coordinate along a knot is
globally Lipschitz, so the selector above applies directly to it. -/
lemma exists_lipschitzWith_boxShellParameter (K : Knot)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) :
    ∃ C : ℝ≥0,
      LipschitzWith C (Submission.PardonDistortion.boxShellParameter K c) := by
  obtain ⟨C, hcurve⟩ := exists_lipschitzWith_knotCurve K
  refine ⟨C, ?_⟩
  have hcomp := (Submission.PardonDistortion.lipschitzWith_rationalBoxGauge c).comp hcurve
  change LipschitzWith C (fun x ↦
    Submission.PardonDistortion.rationalBoxGauge c (K.curve x))
  change LipschitzWith C
    (Submission.PardonDistortion.rationalBoxGauge c ∘ K.curve)
  simpa only [one_mul] using hcomp

/-- The branch-free Lipschitz coarea selector specialized to Pardon's box
shell coordinate. -/
theorem exists_boxShellRegularValue_fiberCount_le_integral_of_isCompact
    (K : Knot) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b,
      y ∉ (Submission.PardonDistortion.boxShellParameter K c) ''
        lipschitzExceptionalSet (Submission.PardonDistortion.boxShellParameter K c) ∧
      (fiberSet (Submission.PardonDistortion.boxShellParameter K c) s y).Finite ∧
      (fiberCount (Submission.PardonDistortion.boxShellParameter K c) s y : ℝ≥0∞) ≤
        (∫⁻ x in s, ENNReal.ofReal
          |deriv (Submission.PardonDistortion.boxShellParameter K c) x|) /
            ENNReal.ofReal (b - a) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_boxShellParameter K c
  exact exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact hC hs hab

end PardonApplication

end

end Submission.Coarea
