import Mathlib.Topology.Subpath

/-!
# Embedded subarcs of an interval path

An injective path contained in another injective path and joining two ordered marked points is
exactly the corresponding subpath.  These elementary facts support cutting a finite alternating
cycle at two prescribed constituent edges.
-/

open Set Topology

noncomputable section

namespace Submission.Topology
namespace EmbeddedPathSubarc

variable {X : Type*} [TopologicalSpace X]

/-- A nonconstant subpath of an embedded path is embedded. -/
theorem subpath_injective_of_ne {a b : X} (p : Path a b)
    (hp : Function.Injective p) (s t : unitInterval) (hst : s ≠ t) :
    Function.Injective (p.subpath s t) := by
  intro u v huv
  have hparameter := hp huv
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  apply Subtype.ext
  have hgap : (t : ℝ) - s ≠ 0 := sub_ne_zero.mpr fun h ↦ hst (Subtype.ext h.symm)
  have hmul : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hgap)

variable [T2Space X]

/-- An embedded path inside another embedded path, with ordered marked endpoints, is exactly the
subpath between those endpoints. -/
theorem range_eq_subpath_of_range_subset {a b : X} (p : Path a b)
    (hp : Function.Injective p) (s t : unitInterval) (hst : s < t)
    (q : Path (p s) (p t)) (hq : Function.Injective q)
    (hsub : Set.range q ⊆ Set.range p) :
    Set.range q = Set.range (p.subpath s t) := by
  let E : unitInterval ≃ₜ Set.range p :=
    (p.continuous.isClosedEmbedding hp).isEmbedding.toHomeomorph
  let r : unitInterval → unitInterval := fun u ↦
    E.symm ⟨q u, hsub ⟨u, rfl⟩⟩
  have hr_apply (u : unitInterval) : p (r u) = q u := by
    change (E (E.symm ⟨q u, hsub ⟨u, rfl⟩⟩)).1 = q u
    rw [E.apply_symm_apply]
  have hr_continuous : Continuous r := by
    apply E.symm.continuous.comp
    exact continuous_induced_rng.mpr q.continuous
  have hr_injective : Function.Injective r := by
    intro u v huv
    apply hq
    rw [← hr_apply u, ← hr_apply v, huv]
  have hr_zero : r 0 = s := by
    apply hp
    rw [hr_apply, q.source]
  have hr_one : r 1 = t := by
    apply hp
    rw [hr_apply, q.target]
  have hr_mono : StrictMono r := by
    rcases hr_continuous.strictMono_of_inj_boundedOrder' hr_injective with hmono | hanti
    · exact hmono
    · exfalso
      have hbad := hanti (show (0 : unitInterval) < 1 by norm_num)
      rw [hr_zero, hr_one] at hbad
      exact (not_lt_of_ge hst.le) hbad
  rw [Path.range_subpath_of_le p s t hst.le]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨r u, ⟨?_, ?_⟩, hr_apply u⟩
    · rw [← hr_zero]
      exact hr_mono.monotone bot_le
    · rw [← hr_one]
      exact hr_mono.monotone le_top
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Set.Icc (r 0) (r 1) := by
      simpa only [hr_zero, hr_one]
    obtain ⟨u, _hu, huv⟩ :=
      intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
        hr_continuous.continuousOn hv'
    exact ⟨u, by rw [← hr_apply u, huv]⟩

omit [T2Space X] in
/-- Adjacent subpaths of an embedded path meet only at their common marked point. -/
theorem range_subpath_inter_range_subpath {a b : X} (p : Path a b)
    (hp : Function.Injective p) (r s t : unitInterval) (hrs : r ≤ s) (hst : s ≤ t) :
    Set.range (p.subpath r s) ∩ Set.range (p.subpath s t) = {p s} := by
  rw [Path.range_subpath_of_le p r s hrs,
    Path.range_subpath_of_le p s t hst]
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have huv : u = v := hp hvu.symm
    subst v
    have hus : u = s := le_antisymm hu.2 hv.1
    subst u
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨s, ⟨hrs, le_rfl⟩, rfl⟩, ⟨s, ⟨le_rfl, hst⟩, rfl⟩⟩

/-- An embedded contained arc determines two ordered parameters of the ambient embedded path.
The arc may traverse the resulting subpath in either orientation. -/
theorem exists_ordered_parameters_of_range_subset {a b c d : X}
    (p : Path a b) (hp : Function.Injective p)
    (q : Path c d) (hq : Function.Injective q)
    (hsub : Set.range q ⊆ Set.range p) :
    ∃ s t : unitInterval, s < t ∧
      Set.range q = Set.range (p.subpath s t) ∧
        ((c = p s ∧ d = p t) ∨ (c = p t ∧ d = p s)) := by
  obtain ⟨s, hs⟩ := hsub ⟨0, rfl⟩
  obtain ⟨t, ht⟩ := hsub ⟨1, rfl⟩
  have hc : c = p s := q.source.symm.trans hs.symm
  have hd : d = p t := q.target.symm.trans ht.symm
  have hst : s ≠ t := by
    intro hst
    have hzeroOne : (0 : unitInterval) = 1 := by
      apply hq
      rw [q.source, q.target, hc, hd, hst]
    norm_num at hzeroOne
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · let q' : Path (p s) (p t) := q.cast hc.symm hd.symm
    have hq' : Function.Injective q' := by
      simpa only [q', Path.cast_coe] using hq
    have hsub' : Set.range q' ⊆ Set.range p := by
      simpa only [q', Path.cast_coe] using hsub
    refine ⟨s, t, hlt, ?_, Or.inl ⟨hc, hd⟩⟩
    simpa only [q', Path.cast_coe] using
      range_eq_subpath_of_range_subset p hp s t hlt q' hq' hsub'
  · let q' : Path (p t) (p s) := q.symm.cast hd.symm hc.symm
    have hqSymm : Function.Injective q.symm := by
      intro u v huv
      apply unitInterval.symm_bijective.injective
      apply hq
      simpa only [Path.symm_apply, Function.comp_apply] using huv
    have hq' : Function.Injective q' := by
      simpa only [q', Path.cast_coe] using hqSymm
    have hsub' : Set.range q' ⊆ Set.range p := by
      simpa only [q', Path.cast_coe, Path.symm_range] using hsub
    refine ⟨t, s, hgt, ?_, Or.inr ⟨hc, hd⟩⟩
    rw [← Path.symm_range q]
    simpa only [q', Path.cast_coe] using
      range_eq_subpath_of_range_subset p hp t s hgt q' hq' hsub'

end EmbeddedPathSubarc
end Submission.Topology
