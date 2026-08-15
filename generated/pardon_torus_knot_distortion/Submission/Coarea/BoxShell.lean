import Submission.Coarea.FiniteBranches
import Submission.LocalArc

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Coarea selection for rational-box shells

The weighted sup norm below has the rational boxes from `BoxGeometry` as its
sublevel sets.  Its Lipschitz constant is one because all three axis weights
are at least one.  Consequently a differentiable branch of its restriction to
a knot has derivative bounded by the speed of the knot.

The final theorem packages the finite-branch coarea argument.  Its hypotheses
record precisely the piecewise differentiability and the local arclength
estimate needed by the nonsmooth sup norm.  The conclusion retains Pardon's
exact constant `10 * (1 + 1 / ε) * D`.
-/

/-- Weighted coordinates whose sup norm cuts out the rational boxes. -/
noncomputable def normalizedBoxCoordinates (c x : R3) : Fin 3 → ℝ :=
  fun i ↦ (x - c).ofLp i / axisWeight i

/-- The weighted sup-norm distance from the center of a rational box. -/
noncomputable def rationalBoxGauge (c x : R3) : ℝ :=
  ‖normalizedBoxCoordinates c x‖

/-- The level set used as the boundary of the scale-`r` rational box. -/
def rationalBoxBoundary (c : R3) (r : ℝ) : Set R3 :=
  {x | rationalBoxGauge c x = r}

lemma rationalBoxGauge_nonneg (c x : R3) : 0 ≤ rationalBoxGauge c x :=
  norm_nonneg _

lemma mem_rationalBox_iff_gauge_lt {c x : R3} {r : ℝ} (hr : 0 < r) :
    x ∈ rationalBox c r ↔ rationalBoxGauge c x < r := by
  rw [rationalBox, rationalBoxGauge, pi_norm_lt_iff hr]
  constructor
  · intro hx i
    rw [normalizedBoxCoordinates, Real.norm_eq_abs, abs_div,
      abs_of_pos (axisWeight_pos i), div_lt_iff₀ (axisWeight_pos i)]
    simpa [mul_comm] using hx i
  · intro hx i
    have hi := hx i
    rw [normalizedBoxCoordinates, Real.norm_eq_abs, abs_div,
      abs_of_pos (axisWeight_pos i), div_lt_iff₀ (axisWeight_pos i)] at hi
    simpa [mul_comm] using hi

lemma normalizedBoxCoordinates_sub (c x y : R3) (i : Fin 3) :
    (normalizedBoxCoordinates c x - normalizedBoxCoordinates c y) i =
      (x - y).ofLp i / axisWeight i := by
  simp only [normalizedBoxCoordinates, Pi.sub_apply]
  field_simp [ne_of_gt (axisWeight_pos i)]
  change (x - c).ofLp i - (y - c).ofLp i = (x - y).ofLp i
  simp

lemma norm_normalizedBoxCoordinates_sub_le (c x y : R3) :
    ‖normalizedBoxCoordinates c x - normalizedBoxCoordinates c y‖ ≤ dist x y := by
  rw [pi_norm_le_iff_of_nonneg dist_nonneg]
  intro i
  rw [normalizedBoxCoordinates_sub, Real.norm_eq_abs, abs_div,
    abs_of_pos (axisWeight_pos i)]
  calc
    |(x - y).ofLp i| / axisWeight i ≤ |(x - y).ofLp i| := by
      exact div_le_self (abs_nonneg _) (one_le_axisWeight i)
    _ = ‖(x - y).ofLp i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) i
    _ = dist x y := by rw [dist_eq_norm]

/-- The rational-box gauge is one-Lipschitz in the ambient Euclidean metric. -/
lemma lipschitzWith_rationalBoxGauge (c : R3) :
    LipschitzWith 1 (rationalBoxGauge c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, rationalBoxGauge] using
    (dist_norm_norm_le (normalizedBoxCoordinates c x) (normalizedBoxCoordinates c y)).trans
      (norm_normalizedBoxCoordinates_sub_le c x y)

lemma continuous_rationalBoxGauge (c : R3) : Continuous (rationalBoxGauge c) :=
  (lipschitzWith_rationalBoxGauge c).continuous

/-- The topological boundary of a positive-scale rational box is contained in
the corresponding gauge level.  Thus counting gauge fibers safely bounds the
number of intersections with the actual box boundary. -/
lemma frontier_rationalBox_subset_boundary {c : R3} {r : ℝ} (hr : 0 < r) :
    frontier (rationalBox c r) ⊆ rationalBoxBoundary c r := by
  intro x hx
  have hleClosed : IsClosed ((rationalBoxGauge c) ⁻¹' Iic r) :=
    isClosed_Iic.preimage (continuous_rationalBoxGauge c)
  have hbox_le : rationalBox c r ⊆ (rationalBoxGauge c) ⁻¹' Iic r := by
    intro z hz
    exact (mem_rationalBox_iff_gauge_lt hr).mp hz |>.le
  have hxle : rationalBoxGauge c x ≤ r :=
    closure_minimal hbox_le hleClosed (frontier_subset_closure hx)
  have hgeClosed : IsClosed ((rationalBoxGauge c) ⁻¹' Ici r) :=
    isClosed_Ici.preimage (continuous_rationalBoxGauge c)
  have hcompl_ge : (rationalBox c r)ᶜ ⊆ (rationalBoxGauge c) ⁻¹' Ici r := by
    intro z hz
    exact le_of_not_gt fun hlt ↦ hz ((mem_rationalBox_iff_gauge_lt hr).mpr hlt)
  have hxcompl : x ∈ frontier (rationalBox c r)ᶜ := by
    rw [frontier_compl]
    exact hx
  have hxge : r ≤ rationalBoxGauge c x :=
    closure_minimal hcompl_ge hgeClosed (frontier_subset_closure hxcompl)
  exact le_antisymm hxle hxge

/-- The shell coordinate of a point on the knot. -/
noncomputable def boxShellParameter (K : Knot) (c : R3) (t : ℝ) : ℝ :=
  rationalBoxGauge c (K.curve t)

lemma boxShellParameter_eq_iff_mem_boundary (K : Knot) (c : R3) (t y : ℝ) :
    boxShellParameter K c t = y ↔ K.curve t ∈ rationalBoxBoundary c y :=
  Iff.rfl

lemma fiberSet_boxShellParameter (K : Knot) (c : R3) (s : Set ℝ) (y : ℝ) :
    Submission.Coarea.fiberSet (boxShellParameter K c) s y =
      s ∩ K.curve ⁻¹' rationalBoxBoundary c y := by
  rfl

/-- At a point where the box gauge is differentiable, composing it with the
knot cannot increase the norm of the derivative. -/
lemma norm_deriv_boxShellParameter_le_speed_of_differentiableAt
    (K : Knot) (c : R3) (t : ℝ)
    (hg : DifferentiableAt ℝ (rationalBoxGauge c) (K.curve t)) :
    |deriv (boxShellParameter K c) t| ≤ speed K t := by
  have hg_norm : ‖fderiv ℝ (rationalBoxGauge c) (K.curve t)‖ ≤ 1 :=
    hg.hasFDerivAt.le_of_lipschitz (lipschitzWith_rationalBoxGauge c)
  have hcurve : HasDerivAt K.curve (deriv K.curve t) t :=
    (K.smooth.differentiable (by simp) t).hasDerivAt
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt t hcurve
  have hderiv : deriv (boxShellParameter K c) t =
      fderiv ℝ (rationalBoxGauge c) (K.curve t) (deriv K.curve t) := by
    exact hcomp.deriv
  rw [hderiv, ← Real.norm_eq_abs, speed]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hg_norm)

/-- Cardinality of the intersection with a rational-box level, inside a
chosen parameter set. -/
noncomputable def boxBoundaryCount (K : Knot) (c : R3) (s : Set ℝ) (y : ℝ) : ℕ :=
  Submission.Coarea.fiberCount (boxShellParameter K c) s y

lemma boxBoundaryCount_eq_ncard (K : Knot) (c : R3) (s : Set ℝ) (y : ℝ) :
    boxBoundaryCount K c s y =
      (s ∩ K.curve ⁻¹' rationalBoxBoundary c y).ncard := by
  rw [boxBoundaryCount, Submission.Coarea.fiberCount,
    fiberSet_boxShellParameter]

/-- The direct box-shell averaging estimate: a branchwise variation bound
`L` yields a boundary with at most `L / (ε r)` intersections. -/
theorem exists_boxBoundaryCount_le_length_div_shellWidth
    {ι : Type*} [Fintype ι]
    (K : Knot) (c : R3) (pieces : ι → Set ℝ) (g' : ℝ → ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i t, t ∈ pieces i →
      HasDerivWithinAt (boxShellParameter K c) (g' t) (pieces i) t)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn (boxShellParameter K c) (pieces i))
    {s : Set ℝ} (hcover : ⋃ i, pieces i = s)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {L : ℝ≥0∞}
    (hlength : ∑ i, ∫⁻ t in pieces i, ENNReal.ofReal |g' t| ≤ L) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      (boxBoundaryCount K c s y : ℝ≥0∞) ≤
        L / ENNReal.ofReal (ε * r) := by
  have hab : r < (1 + ε) * r := by nlinarith
  have hmeasCount :
      Measurable fun y ↦
        (Submission.Coarea.fiberCount (boxShellParameter K c) (⋃ i, pieces i) y : ℝ≥0∞) := by
    have hbranch := Submission.Coarea.measurable_coe_branchFiberCount
      (boxShellParameter K c) g' pieces hmeas hderiv hinj
    simpa only [Submission.Coarea.fiberCount_iUnion_eq_branchFiberCount
      (boxShellParameter K c) pieces hdisj hinj] using hbranch
  have hmoment :
      ∫⁻ y, (Submission.Coarea.fiberCount
        (boxShellParameter K c) (⋃ i, pieces i) y : ℝ≥0∞) ≤ L := by
    rw [Submission.Coarea.lintegral_fiberCount_eq
      (boxShellParameter K c) g' pieces hmeas hderiv hdisj hinj]
    exact hlength
  obtain ⟨y, hy, -, hybound⟩ :=
    Submission.Coarea.exists_Ioc_notMem_le_of_lintegral_le hab
      hmeasCount.aemeasurable hmoment (N := ∅) (measure_empty)
  refine ⟨y, hy, ?_⟩
  rw [boxBoundaryCount, ← hcover]
  have hwidth : (1 + ε) * r - r = ε * r := by ring
  simpa only [hwidth] using hybound

/-- Finite-branch coarea selects an enlarged rational-box boundary with the
exact constant used in Pardon's proof.

The `hlength` hypothesis is the local arclength estimate after restricting to
the shell branches.  `LocalArc.arcContent_preimage_rationalBox_le`, together
with the standard arclength change of variables, supplies this estimate with
`D = (distortion K).toReal`. -/
theorem exists_boxBoundaryCount_le
    {ι : Type*} [Fintype ι]
    (K : Knot) (c : R3) (pieces : ι → Set ℝ) (g' : ℝ → ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i t, t ∈ pieces i →
      HasDerivWithinAt (boxShellParameter K c) (g' t) (pieces i) t)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn (boxShellParameter K c) (pieces i))
    {s : Set ℝ} (hcover : ⋃ i, pieces i = s)
    {r ε D : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hlength :
      ∑ i, ∫⁻ t in pieces i, ENNReal.ofReal |g' t| ≤
        ENNReal.ofReal (10 * ((1 + ε) * r) * D)) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      (boxBoundaryCount K c s y : ℝ≥0∞) ≤
        ENNReal.ofReal (10 * (1 + 1 / ε) * D) := by
  have hab : r < (1 + ε) * r := by nlinarith
  have hmeasCount :
      Measurable fun y ↦
        (Submission.Coarea.fiberCount (boxShellParameter K c) (⋃ i, pieces i) y : ℝ≥0∞) := by
    have hbranch := Submission.Coarea.measurable_coe_branchFiberCount
      (boxShellParameter K c) g' pieces hmeas hderiv hinj
    simpa only [Submission.Coarea.fiberCount_iUnion_eq_branchFiberCount
      (boxShellParameter K c) pieces hdisj hinj] using hbranch
  have hmoment :
      ∫⁻ y, (Submission.Coarea.fiberCount
        (boxShellParameter K c) (⋃ i, pieces i) y : ℝ≥0∞) ≤
          ENNReal.ofReal (10 * ((1 + ε) * r) * D) := by
    rw [Submission.Coarea.lintegral_fiberCount_eq
      (boxShellParameter K c) g' pieces hmeas hderiv hdisj hinj]
    exact hlength
  obtain ⟨y, hy, -, hybound⟩ :=
    Submission.Coarea.exists_Ioc_notMem_le_of_lintegral_le hab
      hmeasCount.aemeasurable hmoment (N := ∅) (measure_empty)
  refine ⟨y, hy, ?_⟩
  rw [boxBoundaryCount, ← hcover]
  refine hybound.trans_eq ?_
  have hwidth : (1 + ε) * r - r = ε * r := by ring
  rw [hwidth]
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hε hr)]
  congr 1
  field_simp [ne_of_gt hε, ne_of_gt hr]
  ring

/-- The same selection theorem specialized to the actual distortion of the
knot. -/
theorem exists_boxBoundaryCount_le_distortion
    {ι : Type*} [Fintype ι]
    (K : Knot) (c : R3) (pieces : ι → Set ℝ) (g' : ℝ → ℝ)
    (hmeas : ∀ i, MeasurableSet (pieces i))
    (hderiv : ∀ i t, t ∈ pieces i →
      HasDerivWithinAt (boxShellParameter K c) (g' t) (pieces i) t)
    (hdisj : Pairwise fun i j ↦ Disjoint (pieces i) (pieces j))
    (hinj : ∀ i, InjOn (boxShellParameter K c) (pieces i))
    {s : Set ℝ} (hcover : ⋃ i, pieces i = s)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hlength :
      ∑ i, ∫⁻ t in pieces i, ENNReal.ofReal |g' t| ≤
        ENNReal.ofReal (10 * ((1 + ε) * r) * (distortion K).toReal)) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      (boxBoundaryCount K c s y : ℝ≥0∞) ≤
        ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
  exact exists_boxBoundaryCount_le K c pieces g' hmeas hderiv hdisj hinj
    hcover hr hε hlength

end

end PardonDistortion
end Submission
