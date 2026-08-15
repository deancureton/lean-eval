import Submission.Topology.SL2ZIntersectionCertificate
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.DiscreteSubset

/-!
# Constructing the finite regular roots of a periodic circle lift

This file supplies the compactness and ordering part of the one-dimensional degree argument.
For a `C¹` real lift whose circle roots are regular, its roots in a compact interval form a
finite set.  In particular, the roots in the canonical half-open period have a canonical
strictly increasing enumeration.
-/

open Filter Set

noncomputable section

namespace Submission.Topology

/-- A continuous real function which avoids every integer on an interval has the same floor at
both endpoints.  This is the global gap lemma used between successive regular roots. -/
theorem floor_eq_of_forall_ne_intCast {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (havoid : ∀ t ∈ Icc a b, ∀ z : ℤ, f t ≠ z) :
    ⌊f a⌋ = ⌊f b⌋ := by
  apply le_antisymm
  · by_contra hnot
    have hfloor : ⌊f b⌋ < ⌊f a⌋ := lt_of_not_ge hnot
    let z : ℤ := ⌊f b⌋ + 1
    have hleft : f b ≤ (z : ℝ) := by
      simpa only [z, Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one (f b)).le
    have hzfloor : z ≤ ⌊f a⌋ := Int.add_one_le_iff.mpr hfloor
    have hright : (z : ℝ) ≤ f a := by
      exact (Int.cast_le.mpr hzfloor).trans (Int.floor_le (f a))
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hab hf ⟨hleft, hright⟩
    exact havoid t ht z hft
  · by_contra hnot
    have hfloor : ⌊f a⌋ < ⌊f b⌋ := lt_of_not_ge hnot
    let z : ℤ := ⌊f a⌋ + 1
    have hleft : f a ≤ (z : ℝ) := by
      simpa only [z, Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one (f a)).le
    have hzfloor : z ≤ ⌊f b⌋ := by
      exact Int.add_one_le_iff.mpr hfloor
    have hright : (z : ℝ) ≤ f b := by
      exact (Int.cast_le.mpr hzfloor).trans (Int.floor_le (f b))
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf ⟨hleft, hright⟩
    exact havoid t ht z hft

/-- Raw analytic hypotheses for a regular periodic real lift of a circle map. -/
structure RegularPeriodicCircleLift (theta : ℝ → ℝ) (winding : ℤ) : Prop where
  contDiff_theta : ContDiff ℝ 1 theta
  angle_add_period : ∀ t,
    theta (t + 2 * Real.pi) = theta t + (winding : ℝ) * (2 * Real.pi)
  regular_root : ∀ t, Circle.exp (theta t) = 1 → deriv theta t ≠ 0

namespace RegularPeriodicCircleLift

variable {theta : ℝ → ℝ} {winding : ℤ}

/-- The roots of the lifted circle coordinate on a set of real parameters. -/
def rootsOn (A : Set ℝ) : Set ℝ :=
  A ∩ {t | Circle.exp (theta t) = 1}

theorem rootsOn_mem (A : Set ℝ) {t : ℝ} :
    t ∈ rootsOn (theta := theta) A ↔ t ∈ A ∧ Circle.exp (theta t) = 1 :=
  Iff.rfl

theorem roots_isDiscrete (H : RegularPeriodicCircleLift theta winding) :
    IsDiscrete {t | Circle.exp (theta t) = 1} := by
  have htarget : IsDiscrete ({y : ℝ | Circle.exp y = 1}) := by
    rw [show {y : ℝ | Circle.exp y = 1} =
        (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) from ?_]
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance
    ext y
    change Circle.exp y = 1 ↔ y ∈ AddSubgroup.zmultiples (2 * Real.pi)
    rw [Circle.exp_eq_one]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  have hderiv : deriv theta x ≠ 0 := H.regular_root x hx
  have hnoAcc : ¬ AccPt (theta x)
      (Filter.principal {y : ℝ | Circle.exp y = 1}) := by
    rw [AccPt]
    exact Filter.not_neBot.mpr (isDiscrete_iff_nhdsNE.mp htarget (theta x) hx)
  have hout := H.contDiff_theta.differentiable one_ne_zero x |>.hasDerivAt.eventually_notMem
    hderiv {y : ℝ | Circle.exp y = 1} hnoAcc
  filter_upwards [hout] with z hz
  exact hz

theorem rootsOn_isDiscrete (H : RegularPeriodicCircleLift theta winding) (A : Set ℝ) :
    IsDiscrete (rootsOn (theta := theta) A) :=
  H.roots_isDiscrete.mono inter_subset_right

theorem rootsOn_isCompact (H : RegularPeriodicCircleLift theta winding)
    {A : Set ℝ} (hA : IsCompact A) : IsCompact (rootsOn (theta := theta) A) := by
  refine hA.inter_right ?_
  exact isClosed_singleton.preimage (Circle.exp.continuous.comp H.contDiff_theta.continuous)

theorem rootsOn_finite (H : RegularPeriodicCircleLift theta winding)
    {A : Set ℝ} (hA : IsCompact A) : (rootsOn (theta := theta) A).Finite :=
  (H.rootsOn_isCompact hA).finite (H.rootsOn_isDiscrete A)

/-- The finite set of roots in the canonical half-open period. -/
def rootFinset (H : RegularPeriodicCircleLift theta winding) : Finset ℝ :=
  (H.rootsOn_finite (A := Icc (0 : ℝ) (2 * Real.pi)) isCompact_Icc).toFinset.filter
    fun t ↦ t ∈ Ico (0 : ℝ) (2 * Real.pi)

theorem mem_rootFinset_iff (H : RegularPeriodicCircleLift theta winding) (t : ℝ) :
    t ∈ H.rootFinset ↔
      t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧ Circle.exp (theta t) = 1 := by
  rw [rootFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
  simp only [rootsOn_mem]
  constructor
  · rintro ⟨⟨ht, hroot⟩, ht'⟩
    exact ⟨ht', hroot⟩
  · rintro ⟨ht, hroot⟩
    exact ⟨⟨⟨ht.1, ht.2.le⟩, hroot⟩, ht⟩

/-- The canonical strictly increasing enumeration of the roots in one period. -/
def orderedRoot (H : RegularPeriodicCircleLift theta winding) :
    Fin H.rootFinset.card → ℝ :=
  H.rootFinset.orderEmbOfFin rfl

theorem orderedRoot_strictMono (H : RegularPeriodicCircleLift theta winding) :
    StrictMono H.orderedRoot :=
  (H.rootFinset.orderEmbOfFin rfl).strictMono

theorem orderedRoot_mem_period (H : RegularPeriodicCircleLift theta winding)
    (i : Fin H.rootFinset.card) : H.orderedRoot i ∈ Ico (0 : ℝ) (2 * Real.pi) :=
  (H.mem_rootFinset_iff (H.orderedRoot i)).mp
    (H.rootFinset.orderEmbOfFin_mem rfl i) |>.1

theorem orderedRoot_exp_eq_one (H : RegularPeriodicCircleLift theta winding)
    (i : Fin H.rootFinset.card) : Circle.exp (theta (H.orderedRoot i)) = 1 :=
  (H.mem_rootFinset_iff (H.orderedRoot i)).mp
    (H.rootFinset.orderEmbOfFin_mem rfl i) |>.2

theorem orderedRoot_complete (H : RegularPeriodicCircleLift theta winding)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hroot : Circle.exp (theta t) = 1) :
    ∃ i, H.orderedRoot i = t := by
  have htmem : t ∈ H.rootFinset := (H.mem_rootFinset_iff t).mpr ⟨ht, hroot⟩
  have htmem' : t ∈ (H.rootFinset : Set ℝ) := htmem
  rw [← H.rootFinset.range_orderEmbOfFin rfl] at htmem'
  rcases htmem' with ⟨i, hi⟩
  exact ⟨i, hi⟩

theorem orderedRoot_regular (H : RegularPeriodicCircleLift theta winding)
    (i : Fin H.rootFinset.card) : deriv theta (H.orderedRoot i) ≠ 0 :=
  H.regular_root _ (H.orderedRoot_exp_eq_one i)

/-- A regular periodic circle lift with no roots in a period has zero winding. -/
theorem winding_eq_zero_of_rootFinset_eq_empty
    (H : RegularPeriodicCircleLift theta winding) (hempty : H.rootFinset = ∅) :
    winding = 0 := by
  let period : ℝ := 2 * Real.pi
  let u : ℝ → ℝ := fun t ↦ theta t / period
  have hperiod_pos : 0 < period := Real.two_pi_pos
  have hperiod_ne : period ≠ 0 := hperiod_pos.ne'
  have havoid : ∀ t ∈ Icc (0 : ℝ) period, ∀ z : ℤ, u t ≠ z := by
    intro t ht z htz
    have htheta : theta t = (z : ℝ) * period := (div_eq_iff hperiod_ne).mp htz
    have hexp : Circle.exp (theta t) = 1 := by
      have hexpPeriod : Circle.exp period = 1 := by
        exact Circle.exp_eq_one.mpr ⟨1, by simp only [period]; ring⟩
      rw [htheta, Circle.exp_intCast_mul, hexpPeriod]
      simp
    by_cases htop : t = period
    · subst t
      have hzero : Circle.exp (theta 0) = 1 := by
        have hthetaPeriod : theta period = theta 0 + (winding : ℝ) * period := by
          simpa only [zero_add, period] using H.angle_add_period 0
        apply Circle.exp_eq_one.mpr
        obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp hexp
        refine ⟨k - winding, ?_⟩
        calc
          theta 0 = theta period - (winding : ℝ) * period := by linarith
          _ = (k : ℝ) * (2 * Real.pi) - (winding : ℝ) * period := by rw [hk]
          _ = ((k - winding : ℤ) : ℝ) * (2 * Real.pi) := by
            simp only [period, Int.cast_sub]
            ring
      have hmem : (0 : ℝ) ∈ H.rootFinset :=
        (H.mem_rootFinset_iff 0).mpr
          ⟨⟨le_rfl, by simpa only [period] using hperiod_pos⟩, hzero⟩
      rw [hempty] at hmem
      simp at hmem
    · have htlt : t < period := lt_of_le_of_ne ht.2 htop
      have hmem : t ∈ H.rootFinset :=
        (H.mem_rootFinset_iff t).mpr ⟨⟨ht.1, htlt⟩, hexp⟩
      rw [hempty] at hmem
      simp at hmem
  have hucont : ContinuousOn u (Icc (0 : ℝ) period) :=
    (H.contDiff_theta.continuous.div_const period).continuousOn
  have hfloor := floor_eq_of_forall_ne_intCast (f := u) hperiod_pos.le hucont havoid
  have huPeriod : u period = u 0 + winding := by
    dsimp only [u]
    have hthetaPeriod : theta period = theta 0 + (winding : ℝ) * period := by
      simpa only [zero_add, period] using H.angle_add_period 0
    rw [hthetaPeriod]
    field_simp
  rw [huPeriod, Int.floor_add_intCast] at hfloor
  omega

theorem rootFinset_nonempty_of_winding_ne_zero
    (H : RegularPeriodicCircleLift theta winding) (hwinding : winding ≠ 0) :
    H.rootFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  exact hwinding (H.winding_eq_zero_of_rootFinset_eq_empty hempty)

/-- The crossing sign sequence, extended by zero beyond the finite root enumeration. -/
def rootSignSequence (H : RegularPeriodicCircleLift theta winding) (i : ℕ) : ℤ :=
  if hi : i < H.rootFinset.card then
    realRootCrossingSign theta (H.orderedRoot ⟨i, hi⟩)
  else 0

/-- Construct all fields of `OrderedRegularCircleRootData` from the raw analytic hypotheses and
the single signed-degree conclusion.  Thus the only remaining nonlocal statement is displayed as
an equality, rather than being hidden among ordering or sheet fields. -/
def orderedRegularCircleRootDataOfSignedSum
    (H : RegularPeriodicCircleLift theta winding)
    (hsigned : ∑ i : Fin H.rootFinset.card,
      realRootCrossingSign theta (H.orderedRoot i) = winding) :
    OrderedRegularCircleRootData theta winding where
  contDiff_theta := H.contDiff_theta
  angle_add_period := H.angle_add_period
  count := H.rootFinset.card
  root := H.orderedRoot
  strictMono_root := H.orderedRoot_strictMono
  root_mem_period := H.orderedRoot_mem_period
  root_exp_eq_one := H.orderedRoot_exp_eq_one
  root_complete := H.orderedRoot_complete
  regular_root := H.orderedRoot_regular
  sheet k := ∑ i ∈ Finset.range k, H.rootSignSequence i
  sheet_jump i := by
    rw [Finset.sum_range_succ, add_sub_cancel_left]
    simp only [rootSignSequence, i.isLt, dite_true]
  sheet_end := by
    simp only [Finset.sum_range_zero, sub_zero]
    calc
      (∑ i ∈ Finset.range H.rootFinset.card, H.rootSignSequence i) =
          ∑ i : Fin H.rootFinset.card,
            realRootCrossingSign theta (H.orderedRoot i) := by
        symm
        simpa only [rootSignSequence, Fin.is_lt, dite_true] using
          Fin.sum_univ_eq_sum_range
            H.rootSignSequence H.rootFinset.card
      _ = winding := hsigned

/-- The empty-root case needs no separate signed-degree input: its winding is forced to vanish. -/
def orderedRegularCircleRootDataOfEmpty
    (H : RegularPeriodicCircleLift theta winding) (hempty : H.rootFinset = ∅) :
    OrderedRegularCircleRootData theta winding := by
  apply H.orderedRegularCircleRootDataOfSignedSum
  have hcard : H.rootFinset.card = 0 := by simp only [hempty, Finset.card_empty]
  calc
    (∑ i : Fin H.rootFinset.card,
        realRootCrossingSign theta (H.orderedRoot i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact Fin.elim0 (Fin.cast hcard i)
    _ = winding := (H.winding_eq_zero_of_rootFinset_eq_empty hempty).symm

end RegularPeriodicCircleLift

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology

/-- The raw `C¹` and transverse-root assumptions on a lifted torus loop, packaged as the regular
periodic scalar lift required by the one-dimensional construction. -/
theorem transformedRegularPeriodicCircleLift
    {gamma : ℝ → Circle × Circle} (p q : ℕ) (L : TorusLoopLift gamma)
    (hfirst : ContDiff ℝ 1 L.first.angle)
    (hsecond : ContDiff ℝ 1 L.second.angle)
    (hregular : ∀ t, Circle.exp (transformedSlopeAngle p q L t) = 1 →
      deriv (transformedSlopeAngle p q L) t ≠ 0) :
    RegularPeriodicCircleLift (transformedSlopeAngle p q L)
      (slopeIntersectionDet p q L.first.winding L.second.winding) where
  contDiff_theta := contDiff_transformedSlopeAngle p q L hfirst hsecond
  angle_add_period := transformedSlopeAngle_add_period p q L
  regular_root := hregular

/-- Strong direct certificate wrapper from raw loop smoothness, root transversality, embeddedness,
and the remaining one-dimensional signed-degree equality.  Compactness, finiteness, sorting,
root completeness, and every sheet field are constructed internally. -/
def transverseIntersectionCertificateOfRawRegularSignedDegree
    (p q : ℕ) (hc : p.Coprime q) {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma)
    (hfirst : ContDiff ℝ 1 L.first.angle)
    (hsecond : ContDiff ℝ 1 L.second.angle)
    (hregular : ∀ t, Circle.exp (transformedSlopeAngle p q L t) = 1 →
      deriv (transformedSlopeAngle p q L) t ≠ 0)
    (hinjective : Set.InjOn gamma (Set.Ico (0 : ℝ) (2 * Real.pi)))
    (hsigned : let H := transformedRegularPeriodicCircleLift p q L hfirst hsecond hregular
      ∑ i : Fin H.rootFinset.card,
        realRootCrossingSign (transformedSlopeAngle p q L) (H.orderedRoot i) =
          slopeIntersectionDet p q L.first.winding L.second.winding) :
    TransverseIntersectionCertificate p q gamma
      L.first.winding L.second.winding := by
  let H := transformedRegularPeriodicCircleLift p q L hfirst hsecond hregular
  let D := H.orderedRegularCircleRootDataOfSignedSum hsigned
  exact CircleRootKnotParameterization.transverseIntersectionCertificate_of_injective
    p q hc L D hinjective

end Submission.PardonDistortion
