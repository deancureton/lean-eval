import ChallengeDeps

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Submission.Coarea

noncomputable section

/-!
# One-dimensional coarea for finitely many injective branches

This file supplies the one-dimensional analytic core used when choosing a generic level in
Pardon's argument.  A differentiable real function restricted to finitely many pairwise-disjoint
injective branches has finite fibers.  Its fiber-counting function is measurable, and its
Lebesgue integral is exactly the sum of the integrals of the absolute derivatives on the
branches.  A first-moment argument then finds a low-cardinality regular level while avoiding any
prescribed null set.
-/

/-- The points of `s` mapped to the level `y`. -/
def fiberSet (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) : Set ℝ :=
  s ∩ f ⁻¹' {y}

/-- The cardinality of a level fiber inside `s`. It is zero for an infinite fiber, following
the convention of `Set.ncard`; the finite-branch results below prove finiteness in their setting. -/
noncomputable def fiberCount (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) : ℕ :=
  (fiberSet f s y).ncard

/-- The number of injective branches whose image contains `y`. -/
noncomputable def branchFiberCount {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (pieces : ι → Set ℝ) (y : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ y ∈ f '' pieces i).card

theorem coe_branchFiberCount {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (pieces : ι → Set ℝ) (y : ℝ) :
    (branchFiberCount f pieces y : ℝ≥0∞) =
      ∑ i, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
  classical
  simp [branchFiberCount, Set.indicator]

theorem fiberCount_of_injOn {f : ℝ → ℝ} {s : Set ℝ} (hf : InjOn f s) (y : ℝ) :
    fiberCount f s y = (f '' s).indicator (fun _ ↦ 1) y := by
  classical
  by_cases hy : y ∈ f '' s
  · rcases hy with ⟨x, hx, hxy⟩
    have hset : fiberSet f s y = {x} := by
      ext z
      simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hz, hfz⟩
        exact hf hz hx (hfz.trans hxy.symm)
      · rintro rfl
        exact ⟨hx, hxy⟩
    rw [fiberCount, hset, ncard_singleton, Set.indicator_of_mem]
    exact ⟨x, hx, hxy⟩
  · have hset : fiberSet f s y = ∅ := by
      ext z
      simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      rintro ⟨hz, hfz⟩
      exact hy ⟨z, hz, hfz⟩
    rw [fiberCount, hset, ncard_empty, Set.indicator_of_notMem hy]

theorem fiberCount_iUnion_eq_branchFiberCount
    {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn f (pieces i)) (y : ℝ) :
    fiberCount f (⋃ i, pieces i) y = branchFiberCount f pieces y := by
  classical
  have hfinite (i : ι) : (fiberSet f (pieces i) y).Finite := by
    by_cases he : (fiberSet f (pieces i) y).Nonempty
    · obtain ⟨x, hx⟩ := he
      apply (finite_singleton x).subset
      intro z hz
      rw [mem_singleton_iff]
      exact hinj i hz.1 hx.1 (hz.2.trans hx.2.symm)
    · rw [not_nonempty_iff_eq_empty.mp he]
      exact finite_empty
  have hfiberDisj :
      Pairwise fun i j ↦ Disjoint (fiberSet f (pieces i) y) (fiberSet f (pieces j) y) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hfiber :
      fiberSet f (⋃ i, pieces i) y = ⋃ i, fiberSet f (pieces i) y := by
    ext x
    simp [fiberSet]
  rw [fiberCount, hfiber, Set.ncard_iUnion_of_finite hfinite hfiberDisj]
  change (∑ᶠ i : ι, fiberCount f (pieces i) y) = branchFiberCount f pieces y
  simp_rw [fiberCount_of_injOn (hinj _)]
  rw [finsum_eq_sum_of_fintype]
  simp [branchFiberCount, Set.indicator]

theorem measurable_coe_branchFiberCount {ι : Type*} [Fintype ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hinj : ∀ i, InjOn f (pieces i)) :
    Measurable fun y ↦ (branchFiberCount f pieces y : ℝ≥0∞) := by
  have hcont (i : ι) : ContinuousOn f (pieces i) :=
    fun x hx ↦ (hderiv i x hx).continuousWithinAt
  have himage (i : ι) : MeasurableSet (f '' pieces i) :=
    (hmeas i).image_of_continuousOn_injOn (hcont i) (hinj i)
  rw [show (fun y ↦ (branchFiberCount f pieces y : ℝ≥0∞)) =
      fun y ↦ ∑ i, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y by
    funext y
    exact coe_branchFiberCount f pieces y]
  exact Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator (himage i)

/-- The one-dimensional coarea formula for a finite family of injective differentiable branches. -/
theorem lintegral_branchFiberCount_eq {ι : Type*} [Fintype ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hinj : ∀ i, InjOn f (pieces i)) :
    ∫⁻ y, (branchFiberCount f pieces y : ℝ≥0∞) =
      ∑ i, ∫⁻ x in pieces i, ENNReal.ofReal |f' x| := by
  classical
  have hcont (i : ι) : ContinuousOn f (pieces i) :=
    fun x hx ↦ (hderiv i x hx).continuousWithinAt
  have himage (i : ι) : MeasurableSet (f '' pieces i) :=
    (hmeas i).image_of_continuousOn_injOn (hcont i) (hinj i)
  simp_rw [coe_branchFiberCount]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    calc
      ∫⁻ y, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y =
          ∫⁻ y in f '' pieces i, (1 : ℝ≥0∞) := by
            rw [lintegral_indicator (himage i)]
      _ = ∫⁻ x in pieces i, ENNReal.ofReal |f' x| := by
        simpa using
          (lintegral_image_eq_lintegral_abs_deriv_mul
            (hmeas i) (hderiv i) (hinj i) (fun _ ↦ (1 : ℝ≥0∞)))
  · intro i _
    exact measurable_const.indicator (himage i)

/-- Coarea stated for the actual fiber cardinality of a disjoint union of injective branches. -/
theorem lintegral_fiberCount_eq {ι : Type*} [Fintype ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn f (pieces i)) :
    ∫⁻ y, (fiberCount f (⋃ i, pieces i) y : ℝ≥0∞) =
      ∑ i, ∫⁻ x in pieces i, ENNReal.ofReal |f' x| := by
  simp_rw [fiberCount_iUnion_eq_branchFiberCount f pieces hdisj hinj]
  exact lintegral_branchFiberCount_eq f f' pieces hmeas hderiv hinj

/-- A first-moment bound on an interval that simultaneously avoids a prescribed null set. -/
theorem exists_Ioc_notMem_le_of_lintegral_le
    {F : ℝ → ℝ≥0∞} {a b : ℝ} {L : ℝ≥0∞} {N : Set ℝ}
    (hab : a < b) (hF : AEMeasurable F (volume.restrict (Ioc a b)))
    (hL : ∫⁻ y, F y ≤ L) (hN : volume N = 0) :
    ∃ y ∈ Ioc a b, y ∉ N ∧ F y ≤ L / ENNReal.ofReal (b - a) := by
  have hvol_ne : volume (Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvol_top : volume (Ioc a b) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hgood :
      0 < volume {y ∈ Ioc a b | F y ≤ ⨍⁻ z in Ioc a b, F z ∂volume} :=
    measure_le_setLAverage_pos hvol_ne hvol_top hF
  have hgood_sdiff :
      volume ({y ∈ Ioc a b | F y ≤ ⨍⁻ z in Ioc a b, F z ∂volume} \ N) ≠ 0 := by
    rw [measure_sdiff_null hN]
    exact hgood.ne'
  obtain ⟨y, hy, hyN⟩ := nonempty_of_measure_ne_zero hgood_sdiff
  refine ⟨y, hy.1, hyN, hy.2.trans ?_⟩
  rw [setLAverage_eq, Real.volume_Ioc]
  exact ENNReal.div_le_div
    ((setLIntegral_le_lintegral (Ioc a b) F).trans hL) le_rfl

/-- A regular value has no critical point in its fiber. -/
def IsRegularValue (f : ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ x, f x = y → deriv f x ≠ 0

def criticalSet (f : ℝ → ℝ) : Set ℝ :=
  {x | deriv f x = 0}

def criticalValues (f : ℝ → ℝ) : Set ℝ :=
  f '' criticalSet f

theorem not_mem_criticalValues_iff {f : ℝ → ℝ} {y : ℝ} :
    y ∉ criticalValues f ↔ IsRegularValue f y := by
  simp only [criticalValues, criticalSet, mem_image, mem_ofPred_eq, not_exists,
    IsRegularValue]
  constructor
  · intro h x hfx hdx
    exact h x ⟨hdx, hfx⟩
  · intro h x hx
    exact h x hx.2 hx.1

/-- The critical values of a `C¹` real function form a null set. -/
theorem volume_criticalValues_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    volume (criticalValues f) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun x ↦ fderiv ℝ f x)
  · intro x hx
    exact (hf.differentiable_one x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    rw [← toSpanSingleton_deriv, ContinuousLinearMap.det_toSpanSingleton]
    exact hx

/-- A finite-branch coarea estimate with a regular level in any nonempty interval. -/
theorem exists_regularValue_fiberCount_le {ι : Type*} [Fintype ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn f (pieces i)) (hsmooth : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b, IsRegularValue f y ∧
      (fiberCount f (⋃ i, pieces i) y : ℝ≥0∞) ≤
        (∑ i, ∫⁻ x in pieces i, ENNReal.ofReal |f' x|) / ENNReal.ofReal (b - a) := by
  have hmeasBranch :=
    measurable_coe_branchFiberCount f f' pieces hmeas hderiv hinj
  have hcountEq :
      (fun y ↦ (fiberCount f (⋃ i, pieces i) y : ℝ≥0∞)) =
        fun y ↦ (branchFiberCount f pieces y : ℝ≥0∞) := by
    funext y
    rw [fiberCount_iUnion_eq_branchFiberCount f pieces hdisj hinj]
  have hmeasCount :
      Measurable fun y ↦ (fiberCount f (⋃ i, pieces i) y : ℝ≥0∞) := by
    rw [hcountEq]
    exact hmeasBranch
  obtain ⟨y, hy, hycrit, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab hmeasCount.aemeasurable
      (lintegral_fiberCount_eq f f' pieces hmeas hderiv hdisj hinj).le
      (volume_criticalValues_eq_zero hsmooth)
  exact ⟨y, hy, not_mem_criticalValues_iff.mp hycrit, hybound⟩

end
end Submission.Coarea
