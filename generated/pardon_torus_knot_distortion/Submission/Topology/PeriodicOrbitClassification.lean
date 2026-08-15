import Submission.Topology.OneManifoldCircleClassification
import Mathlib.GroupTheory.Archimedean

/-!
# Classification of a compact homogeneous local orbit

This is the topological endgame of the regular-level ODE route.  ODE uniqueness gives translation
homogeneity of one integral curve; a nonzero vector field makes its orbit map a local
homeomorphism; connectedness is used upstream to prove that the orbit is surjective.  The theorem
below then produces the cyclic parametrization required by the existing circle-classification
API.
-/

open Set Topology
open scoped Topology

noncomputable section

namespace Submission.SurfaceRegularValue

/-- The exact orbit data produced by a complete nonstationary autonomous integral curve after
showing that its orbit is a whole connected component. -/
structure HomogeneousLocalOrbit (X : Type*) [TopologicalSpace X] where
  curve : ℝ → X
  localHomeomorph_curve : IsLocalHomeomorph curve
  surjective_curve : Function.Surjective curve
  translate_eq_of_eq : ∀ {s t : ℝ}, curve s = curve t →
    ∀ u : ℝ, curve (s + u) = curve (t + u)

namespace HomogeneousLocalOrbit

variable {X : Type*} [TopologicalSpace X]

theorem continuous_curve (O : HomogeneousLocalOrbit X) : Continuous O.curve :=
  O.localHomeomorph_curve.continuous

/-- All periods of the orbit form an additive subgroup of `ℝ`. -/
def periodSubgroup (O : HomogeneousLocalOrbit X) : AddSubgroup ℝ where
  carrier := {p | Function.Periodic O.curve p}
  zero_mem' := fun u ↦ by simp
  add_mem' := by
    intro p q hp hq u
    calc
      O.curve (u + (p + q)) = O.curve ((u + p) + q) := by rw [add_assoc]
      _ = O.curve (u + p) := hq (u + p)
      _ = O.curve u := hp u
  neg_mem' := by
    intro p hp u
    have h := hp (u - p)
    rw [sub_add_cancel] at h
    exact h.symm

theorem mem_periodSubgroup_iff (O : HomogeneousLocalOrbit X) (p : ℝ) :
    p ∈ O.periodSubgroup ↔ Function.Periodic O.curve p :=
  Iff.rfl

/-- Equality at two times makes their difference a period.  This is exactly the consequence of
autonomous ODE uniqueness retained in `translate_eq_of_eq`. -/
theorem sub_mem_periodSubgroup_of_curve_eq (O : HomogeneousLocalOrbit X)
    {s t : ℝ} (hst : O.curve s = O.curve t) : s - t ∈ O.periodSubgroup := by
  have hshift := O.translate_eq_of_eq hst
  have hperiod : Function.Periodic O.curve (t - s) := by
    intro u
    have h := hshift (u - s)
    convert h.symm using 1 <;> ring_nf
  simpa [neg_sub] using O.periodSubgroup.neg_mem hperiod

/-- Local injectivity of the orbit isolates zero in its period subgroup. -/
theorem exists_isolated_zero_periods (O : HomogeneousLocalOrbit X) :
    ∃ ε > 0, Disjoint (O.periodSubgroup : Set ℝ) (Ioo 0 ε) := by
  obtain ⟨e, hzero, he⟩ := O.localHomeomorph_curve 0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_source.mem_nhds hzero)
  refine ⟨ε, hε, Set.disjoint_left.mpr ?_⟩
  intro p hp hprange
  have hpball : p ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hprange.1]
    exact hprange.2
  have hpsource := hball hpball
  have hcurve : O.curve p = O.curve 0 := by simpa using hp 0
  have hep : e p = e 0 := by
    simpa [he] using hcurve
  have : p = 0 := e.injOn hpsource hzero hep
  exact hprange.1.ne' this

private theorem real_not_compactSpace : ¬ CompactSpace ℝ := by
  intro hcompact
  let _ : CompactSpace ℝ := hcompact
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    (show Bornology.IsBounded (Set.univ : Set ℝ) from isCompact_univ.isBounded)
  have h := hC (mem_univ (0 : ℝ)) (mem_univ (|C| + 1))
  rw [Real.dist_eq, abs_sub_comm, sub_zero, abs_of_nonneg (by positivity)] at h
  linarith [le_abs_self C]

/-- Compactness forces the period subgroup to be nontrivial: otherwise the surjective local
homeomorphism would identify the real line with a compact space. -/
theorem periodSubgroup_ne_bot [CompactSpace X] (O : HomogeneousLocalOrbit X) :
    O.periodSubgroup ≠ ⊥ := by
  intro hbot
  have hinjective : Function.Injective O.curve := by
    intro s t hst
    have hmem := O.sub_mem_periodSubgroup_of_curve_eq hst
    rw [hbot, AddSubgroup.mem_bot] at hmem
    linarith
  let h := O.localHomeomorph_curve.toHomeomorphOfBijective
    ⟨hinjective, O.surjective_curve⟩
  apply real_not_compactSpace
  exact h.symm.compactSpace

/-- The isolated, nontrivial period subgroup has a nonzero cyclic generator. -/
theorem exists_period_generator [CompactSpace X] (O : HomogeneousLocalOrbit X) :
    ∃ p : ℝ, p ≠ 0 ∧ O.periodSubgroup = AddSubgroup.zmultiples p := by
  obtain ⟨ε, hε, hisolated⟩ := O.exists_isolated_zero_periods
  obtain ⟨p, hp⟩ := AddSubgroup.cyclic_of_isolated_zero hε hisolated
  have hp' : O.periodSubgroup = AddSubgroup.zmultiples p := by
    rw [AddSubgroup.zmultiples_eq_closure]
    exact hp
  refine ⟨p, ?_, hp'⟩
  intro hpzero
  subst p
  apply O.periodSubgroup_ne_bot
  simpa using hp'

/-- A generator of the full period subgroup gives a bijection from the corresponding additive
circle to the orbit. -/
theorem quotient_bijective_of_period_generator (O : HomogeneousLocalOrbit X)
    {p : ℝ} (hp : O.periodSubgroup = AddSubgroup.zmultiples p) :
    Function.Bijective
      ((show Function.Periodic O.curve p from by
        show p ∈ O.periodSubgroup
        rw [hp]
        exact AddSubgroup.mem_zmultiples p).lift) := by
  let hperiod : Function.Periodic O.curve p := by
    show p ∈ O.periodSubgroup
    rw [hp]
    exact AddSubgroup.mem_zmultiples p
  constructor
  · intro a b hab
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
    change O.curve s = O.curve t at hab
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← hp]
    exact O.sub_mem_periodSubgroup_of_curve_eq hab
  · intro x
    obtain ⟨t, rfl⟩ := O.surjective_curve x
    exact ⟨(t : AddCircle p), hperiod.lift_coe t⟩

/-- Every compact homogeneous local orbit has the cyclic parametrization required to classify it
as a circle. -/
def cyclicLineParametrization [CompactSpace X] (O : HomogeneousLocalOrbit X) :
    CyclicLineParametrization X := by
  let p := Classical.choose O.exists_period_generator
  have hpzero : p ≠ 0 := (Classical.choose_spec O.exists_period_generator).1
  have hp : O.periodSubgroup = AddSubgroup.zmultiples p :=
    (Classical.choose_spec O.exists_period_generator).2
  let hperiod : Function.Periodic O.curve p := by
    show p ∈ O.periodSubgroup
    rw [hp]
    exact AddSubgroup.mem_zmultiples p
  exact {
    period := p
    period_ne_zero := hpzero
    curve := O.curve
    continuous_curve := O.continuous_curve
    periodic_curve := hperiod
    quotient_bijective := O.quotient_bijective_of_period_generator hp
  }

end HomogeneousLocalOrbit

end Submission.SurfaceRegularValue
