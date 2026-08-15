import Submission.Coarea.FiniteBranches

open Filter MeasureTheory Set
open scoped ENNReal Function NNReal Topology

namespace Submission.Coarea

noncomputable section

/-!
# Countable one-dimensional coarea

Mathlib's one-dimensional change-of-variables theorem is stated for a single injective
measurable piece.  This file packages its countable, pairwise-disjoint extension.  Unlike the
finite-branch result, this version permits infinitely many monotonicity intervals; Tonelli's
theorem accounts for their contributions.

We also prove that a regular fiber in a compact parameter set is finite.  This fact needs no
chosen branch decomposition: the inverse function theorem makes the fiber discrete, while
compactness makes a discrete closed fiber finite.
-/

/-- The extended number of injective branches whose images contain a level. -/
def countableBranchFiberMass {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (pieces : ι → Set ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑' i, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y

theorem measurable_countableBranchFiberMass {ι : Type*} [Countable ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hinj : ∀ i, InjOn f (pieces i)) :
    Measurable (countableBranchFiberMass f pieces) := by
  apply Measurable.tsum
  intro i
  have hcont : ContinuousOn f (pieces i) :=
    fun x hx ↦ (hderiv i x hx).continuousWithinAt
  exact measurable_const.indicator <|
    (hmeas i).image_of_continuousOn_injOn hcont (hinj i)

/-- Countable additivity upgrades the injective one-dimensional change-of-variables formula to
any countable family of measurable injective pieces. -/
theorem lintegral_countableBranchFiberMass_eq {ι : Type*} [Countable ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hinj : ∀ i, InjOn f (pieces i)) :
    ∫⁻ y, countableBranchFiberMass f pieces y =
      ∑' i, ∫⁻ x in pieces i, ENNReal.ofReal |f' x| := by
  classical
  change (∫⁻ y, ∑' i, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) = _
  rw [lintegral_tsum]
  · apply tsum_congr
    intro i
    have hcont : ContinuousOn f (pieces i) :=
      fun x hx ↦ (hderiv i x hx).continuousWithinAt
    have himage : MeasurableSet (f '' pieces i) :=
      (hmeas i).image_of_continuousOn_injOn hcont (hinj i)
    calc
      ∫⁻ y, (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y =
          ∫⁻ y in f '' pieces i, (1 : ℝ≥0∞) := by
            rw [lintegral_indicator himage]
      _ = ∫⁻ x in pieces i, ENNReal.ofReal |f' x| := by
        simpa using
          (lintegral_image_eq_lintegral_abs_deriv_mul
            (hmeas i) (hderiv i) (hinj i) (fun _ ↦ (1 : ℝ≥0∞)))
  · intro i
    have hcont : ContinuousOn f (pieces i) :=
      fun x hx ↦ (hderiv i x hx).continuousWithinAt
    exact (measurable_const.indicator <|
      (hmeas i).image_of_continuousOn_injOn hcont (hinj i)).aemeasurable

/-- The countable-branch first-moment estimate.  No finite bound on the number of branches is
required. -/
theorem exists_regularValue_countableBranchFiberMass_le
    {ι : Type*} [Countable ι]
    (f f' : ℝ → ℝ) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i x, x ∈ pieces i → HasDerivWithinAt f (f' x) (pieces i) x)
    (hinj : ∀ i, InjOn f (pieces i)) (hsmooth : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b, IsRegularValue f y ∧
      countableBranchFiberMass f pieces y ≤
        (∑' i, ∫⁻ x in pieces i, ENNReal.ofReal |f' x|) /
          ENNReal.ofReal (b - a) := by
  obtain ⟨y, hy, hycrit, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab
      (measurable_countableBranchFiberMass f f' pieces hmeas hderiv hinj).aemeasurable
      (lintegral_countableBranchFiberMass_eq f f' pieces hmeas hderiv hinj).le
      (volume_criticalValues_eq_zero hsmooth)
  exact ⟨y, hy, not_mem_criticalValues_iff.mp hycrit, hybound⟩

/-- The open set on which the derivative is nonzero. -/
def regularSet (f : ℝ → ℝ) : Set ℝ :=
  {x | deriv f x ≠ 0}

theorem isOpen_regularSet {f : ℝ → ℝ} (hsmooth : ContDiff ℝ 1 f) :
    IsOpen (regularSet f) := by
  exact (isClosed_singleton.preimage hsmooth.continuous_deriv_one).isOpen_compl

/-- A `C¹` real function is injective on each member of a countable open cover of its regular
set.  This is the local inverse theorem plus the Lindelöf property of the real line. -/
theorem exists_countable_open_injective_cover_regularSet
    {f : ℝ → ℝ} (hsmooth : ContDiff ℝ 1 f) :
    ∃ u : ℕ → Set ℝ, (∀ n, IsOpen (u n)) ∧ (∀ n, InjOn f (u n)) ∧
      regularSet f = ⋃ n, u n := by
  classical
  let V : regularSet f → Set ℝ := fun x ↦
    (((hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv x.property).toOpenPartialHomeomorph f).source ∩
      regularSet f
  have hopen (x : regularSet f) : IsOpen (V x) := by
    exact (((hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv x.property).toOpenPartialHomeomorph f).open_source.inter
      (isOpen_regularSet hsmooth)
  have hinj (x : regularSet f) : InjOn f (V x) := by
    exact (((hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv x.property).toOpenPartialHomeomorph f).injOn.mono
      inter_subset_left
  have hcover : regularSet f ⊆ ⋃ x : regularSet f, V x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact ⟨((hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv hx).mem_toOpenPartialHomeomorph_source, hx⟩
  by_cases hne : (regularSet f).Nonempty
  · have hnonempty : Nonempty (regularSet f) := Set.nonempty_coe_sort.mpr hne
    obtain ⟨e, he⟩ :=
      @IsLindelof.indexed_countable_subcover ℝ _ (regularSet f) (regularSet f) hnonempty
        (HereditarilyLindelofSpace.isLindelof (regularSet f)) V hopen hcover
    refine ⟨fun n ↦ V (e n), fun n ↦ hopen (e n), fun n ↦ hinj (e n), ?_⟩
    apply Subset.antisymm he
    exact iUnion_subset fun n ↦ inter_subset_right
  · have hempty : regularSet f = ∅ := not_nonempty_iff_eq_empty.mp hne
    exact ⟨fun _ ↦ ∅, fun _ ↦ isOpen_empty, fun _ ↦ injOn_empty f,
      by simp [hempty]⟩

/-- Remove all earlier members from a sequence of sets. -/
def disjointSequence {α : Type*} (u : ℕ → Set α) (n : ℕ) : Set α :=
  u n \ ⋃ k ∈ Finset.range n, u k

theorem disjointSequence_subset {α : Type*} (u : ℕ → Set α) (n : ℕ) :
    disjointSequence u n ⊆ u n :=
  sdiff_subset

theorem pairwise_disjoint_disjointSequence {α : Type*} (u : ℕ → Set α) :
    Pairwise (Disjoint on disjointSequence u) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hxj.2 <| mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by simpa, hxi.1⟩⟩
  · exact hxi.2 <| mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨by simpa, hxj.1⟩⟩

theorem iUnion_disjointSequence {α : Type*} (u : ℕ → Set α) :
    ⋃ n, disjointSequence u n = ⋃ n, u n := by
  classical
  apply Subset.antisymm
  · exact iUnion_mono fun n ↦ disjointSequence_subset u n
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hex : ∃ n, x ∈ u n := ⟨n, hn⟩
    let dec : DecidablePred (fun n ↦ x ∈ u n) := Classical.decPred _
    let first : ℕ := @Nat.find _ dec hex
    have hfirst : x ∈ u first := @Nat.find_spec _ dec hex
    refine mem_iUnion.mpr ⟨first, hfirst, ?_⟩
    intro hearlier
    obtain ⟨k, hk⟩ := mem_iUnion.mp hearlier
    obtain ⟨hklt, hku⟩ := mem_iUnion.mp hk
    have hle : first ≤ k := @Nat.find_min' _ dec hex k hku
    exact (not_lt_of_ge hle) (by simpa using hklt)

theorem measurableSet_disjointSequence {α : Type*} [MeasurableSpace α]
    (u : ℕ → Set α) (hu : ∀ n, MeasurableSet (u n)) (n : ℕ) :
    MeasurableSet (disjointSequence u n) := by
  apply (hu n).diff
  exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦ hu k

/-- Every measurable subset of the regular set of a `C¹` real function admits a countable,
pairwise-disjoint measurable partition on whose pieces the function is injective. -/
theorem exists_countable_injective_partition_regular
    {f : ℝ → ℝ} (hsmooth : ContDiff ℝ 1 f) {s : Set ℝ} (hs : MeasurableSet s) :
    ∃ pieces : ℕ → Set ℝ,
      (∀ n, MeasurableSet (pieces n)) ∧
      Pairwise (Disjoint on pieces) ∧
      (∀ n, InjOn f (pieces n)) ∧
      ⋃ n, pieces n = s ∩ regularSet f := by
  obtain ⟨u, huopen, huinj, hucover⟩ :=
    exists_countable_open_injective_cover_regularSet hsmooth
  let pieces : ℕ → Set ℝ := fun n ↦ s ∩ disjointSequence u n
  have humeas : ∀ n, MeasurableSet (u n) := fun n ↦ (huopen n).measurableSet
  refine ⟨pieces, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hs.inter (measurableSet_disjointSequence u humeas n)
  · intro i j hij
    exact ((pairwise_disjoint_disjointSequence u) hij).mono
      inter_subset_right inter_subset_right
  · intro n
    exact (huinj n).mono <| inter_subset_right.trans (disjointSequence_subset u n)
  · rw [← inter_iUnion, iUnion_disjointSequence, ← hucover]

/-- On the regular part of any measurable parameter set, the countable coarea mass has exactly
the integral of the absolute derivative as its first moment. -/
theorem exists_countableBranchFiberMass_lintegral_eq
    {f : ℝ → ℝ} (hsmooth : ContDiff ℝ 1 f) {s : Set ℝ} (hs : MeasurableSet s) :
    ∃ pieces : ℕ → Set ℝ,
      (∀ n, MeasurableSet (pieces n)) ∧
      Pairwise (Disjoint on pieces) ∧
      (∀ n, InjOn f (pieces n)) ∧
      ⋃ n, pieces n = s ∩ regularSet f ∧
      ∫⁻ y, countableBranchFiberMass f pieces y =
        ∫⁻ x in s, ENNReal.ofReal |deriv f x| := by
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover⟩ :=
    exists_countable_injective_partition_regular hsmooth hs
  refine ⟨pieces, hmeas, hdisj, hinj, hcover, ?_⟩
  rw [lintegral_countableBranchFiberMass_eq f (deriv f) pieces hmeas
    (fun n x hx ↦ (hsmooth.differentiable_one x).hasDerivAt.hasDerivWithinAt) hinj]
  rw [← lintegral_iUnion hmeas hdisj, hcover]
  have hzero : ∀ x ∉ regularSet f, ENNReal.ofReal |deriv f x| = 0 := by
    intro x hx
    simp only [regularSet, mem_ofPred_eq, not_not] at hx
    simp [hx]
  rw [← lintegral_indicator hs,
    ← lintegral_indicator (hs.inter (isOpen_regularSet hsmooth).measurableSet)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ regularSet f
  · by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem (show x ∈ s ∩ regularSet f from ⟨hxs, hx⟩),
        Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem (fun h ↦ hxs h.1), Set.indicator_of_notMem hxs]
  · have hxinter : x ∉ s ∩ regularSet f := fun h ↦ hx h.2
    rw [Set.indicator_of_notMem hxinter]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, hzero x hx]
    · rw [Set.indicator_of_notMem hxs]

theorem countableBranchFiberMass_eq_encard {ι : Type*} [Countable ι]
    {f : ℝ → ℝ} (hf : Continuous f) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hdisj : Pairwise (Disjoint on pieces)) (hinj : ∀ i, InjOn f (pieces i)) (y : ℝ) :
    countableBranchFiberMass f pieces y =
      ((fiberSet f (⋃ i, pieces i) y).encard : ℝ≥0∞) := by
  classical
  have hmeasFiber (i : ι) : MeasurableSet (fiberSet f (pieces i) y) := by
    exact (hmeas i).inter ((measurableSet_singleton y).preimage hf.measurable)
  have hdisjFiber : Pairwise (Disjoint on fun i ↦ fiberSet f (pieces i) y) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hone (i : ι) :
      (f '' pieces i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y =
        (Measure.count : Measure ℝ) (fiberSet f (pieces i) y) := by
    by_cases hy : y ∈ f '' pieces i
    · obtain ⟨x, hx, hxy⟩ := hy
      have hset : fiberSet f (pieces i) y = {x} := by
        ext z
        simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨hz, hfz⟩
          exact hinj i hz hx (hfz.trans hxy.symm)
        · rintro rfl
          exact ⟨hx, hxy⟩
      rw [Set.indicator_of_mem (show y ∈ f '' pieces i from ⟨x, hx, hxy⟩), hset,
        Measure.count_singleton]
    · have hset : fiberSet f (pieces i) y = ∅ := by
        ext z
        simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false]
        rintro ⟨hz, hfz⟩
        exact hy ⟨z, hz, hfz⟩
      rw [Set.indicator_of_notMem hy, hset, measure_empty]
  calc
    countableBranchFiberMass f pieces y =
        ∑' i, (Measure.count : Measure ℝ) (fiberSet f (pieces i) y) := by
          apply tsum_congr
          exact hone
    _ = (Measure.count : Measure ℝ) (⋃ i, fiberSet f (pieces i) y) :=
      (measure_iUnion hdisjFiber hmeasFiber).symm
    _ = (((⋃ i, fiberSet f (pieces i) y).encard : ℕ∞) : ℝ≥0∞) := by
      rw [Measure.count_apply (MeasurableSet.iUnion hmeasFiber)]
    _ = ((fiberSet f (⋃ i, pieces i) y).encard : ℝ≥0∞) := by
      congr 2
      ext x
      simp [fiberSet]

theorem countableBranchFiberMass_eq_fiberCount {ι : Type*} [Countable ι]
    {f : ℝ → ℝ} (hf : Continuous f) (pieces : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hdisj : Pairwise (Disjoint on pieces)) (hinj : ∀ i, InjOn f (pieces i)) (y : ℝ)
    (hfinite : (fiberSet f (⋃ i, pieces i) y).Finite) :
    countableBranchFiberMass f pieces y =
      (fiberCount f (⋃ i, pieces i) y : ℝ≥0∞) := by
  rw [countableBranchFiberMass_eq_encard hf pieces hmeas hdisj hinj y]
  rw [fiberCount, ← hfinite.cast_ncard_eq]
  exact ENat.toENNReal_coe _

/-- A regular level has only finitely many preimages in a compact parameter set.  This uses no
global monotonicity or finite-branch assumption. -/
theorem finite_fiberSet_of_isCompact_of_regularValue
    {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} (hs : IsCompact s)
    (hsmooth : ContDiff ℝ 1 f) (hy : IsRegularValue f y) :
    (fiberSet f s y).Finite := by
  have hcompact : IsCompact (fiberSet f s y) := by
    apply hs.inter_right
    exact isClosed_singleton.preimage hsmooth.continuous
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hfx : f x = y := by
    simpa [fiberSet] using hx.2
  have hderiv : deriv f x ≠ 0 := hy x hfx
  have hleft := (hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero).eventually_left_inverse hderiv
  obtain ⟨u, hu_sub, hu_open, hxu⟩ := mem_nhds_iff.mp hleft
  refine ⟨u, hu_open, ?_⟩
  ext z
  constructor
  · rintro ⟨hzu, hzs⟩
    have hzf : f z = y := by
      simpa [fiberSet] using hzs.2
    have hzleft := hu_sub hzu
    have hxleft := hu_sub hxu
    calc
      z = HasStrictDerivAt.localInverse f (deriv f x) x
          (hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero) hderiv (f z) := hzleft.symm
      _ = HasStrictDerivAt.localInverse f (deriv f x) x
          (hsmooth.contDiffAt.hasStrictDerivAt one_ne_zero) hderiv (f x) := by rw [hzf, hfx]
      _ = x := hxleft
  · rintro rfl
    exact ⟨hxu, hx⟩

/-- General one-dimensional coarea inequality for a `C¹` function on a compact parameter set.
There is no global assumption about monotonicity intervals or their number. -/
theorem exists_regularValue_fiberCount_le_integral_of_isCompact
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s) (hsmooth : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioc a b, IsRegularValue f y ∧
      (fiberCount f s y : ℝ≥0∞) ≤
        (∫⁻ x in s, ENNReal.ofReal |deriv f x|) / ENNReal.ofReal (b - a) := by
  have hsmeas : MeasurableSet s := hs.measurableSet
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover, hmoment⟩ :=
    exists_countableBranchFiberMass_lintegral_eq hsmooth hsmeas
  obtain ⟨y, hyIoc, hycrit, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab
      (measurable_countableBranchFiberMass f (deriv f) pieces hmeas
        (fun n x hx ↦ (hsmooth.differentiable_one x).hasDerivAt.hasDerivWithinAt)
        hinj).aemeasurable
      hmoment.le (volume_criticalValues_eq_zero hsmooth)
  have hyreg : IsRegularValue f y := not_mem_criticalValues_iff.mp hycrit
  have hfiber : fiberSet f (⋃ n, pieces n) y = fiberSet f s y := by
    ext x
    simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxpieces, hfx⟩
      have hxsr : x ∈ s ∩ regularSet f := by
        rw [← hcover]
        exact hxpieces
      exact ⟨hxsr.1, hfx⟩
    · rintro ⟨hxs, hfx⟩
      have hxreg : x ∈ regularSet f := hyreg x hfx
      refine ⟨?_, hfx⟩
      rw [hcover]
      exact ⟨hxs, hxreg⟩
  have hfiniteS : (fiberSet f s y).Finite :=
    finite_fiberSet_of_isCompact_of_regularValue hs hsmooth hyreg
  have hfinitePieces : (fiberSet f (⋃ n, pieces n) y).Finite := by
    rw [hfiber]
    exact hfiniteS
  have hmass : countableBranchFiberMass f pieces y = (fiberCount f s y : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          (fiberCount f (⋃ n, pieces n) y : ℝ≥0∞) :=
        countableBranchFiberMass_eq_fiberCount hsmooth.continuous pieces hmeas hdisj hinj y
          hfinitePieces
      _ = (fiberCount f s y : ℝ≥0∞) := by
        change ((fiberSet f (⋃ n, pieces n) y).ncard : ℝ≥0∞) =
          ((fiberSet f s y).ncard : ℝ≥0∞)
        rw [hfiber]
  rw [hmass] at hybound
  exact ⟨y, hyIoc, hyreg, hybound⟩

end
end Submission.Coarea
