import Submission.Topology.CyclicOrderConstruction

/-!
# Sorted regular crossings and cyclic successor intervals

This module begins directly from the canonical finite crossing finset.  For a nonempty crossing
set, `Finset.orderEmbOfFin` gives its increasing enumeration.  The cyclic right endpoint is the
next enumeration point, except at the last point where it is the first point in the next period.
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

/-- The genuinely local analytic input used after sorting: the height changes sign across every
crossing. -/
def HasLocalSignFlipAtCrossings
    (H : SmoothRegularLoopCutData frame d L) : Prop :=
  ∀ c ∈ H.crossings, ∃ ε > 0,
    ∀ x ∈ Ioo (c - ε) c, ∀ y ∈ Ioo c (c + ε),
      windingLoopCutHeight frame d L x * windingLoopCutHeight frame d L y < 0

/-- Increasing enumeration of the canonical crossing finset. -/
def sortedCrossing (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) : ℝ :=
  H.crossings.orderEmbOfFin rfl i

@[simp]
theorem sortedCrossing_mem (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) : sortedCrossing H i ∈ H.crossings :=
  H.crossings.orderEmbOfFin_mem rfl i

theorem strictMono_sortedCrossing (H : SmoothRegularLoopCutData frame d L) :
    StrictMono (sortedCrossing H) :=
  (H.crossings.orderEmbOfFin rfl).strictMono

theorem sortedCrossing_mem_period (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) :
    sortedCrossing H i ∈ Ico (0 : ℝ) (2 * Real.pi) :=
  H.crossings_subset_period (sortedCrossing_mem H i)

theorem sortedCrossing_height_eq_zero (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) :
    windingLoopCutHeight frame d L (sortedCrossing H i) = 0 :=
  (H.mem_crossings_iff _).mp (sortedCrossing_mem H i) |>.2

theorem crossings_card_pos_of_fin (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) : 0 < H.crossings.card :=
  H.crossings.card_pos.mpr ⟨sortedCrossing H i, sortedCrossing_mem H i⟩

/-- Next crossing in the lifted cyclic order. -/
def cyclicRight (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) : ℝ :=
  if hi : i.1 + 1 < H.crossings.card then
    sortedCrossing H ⟨i.1 + 1, hi⟩
  else sortedCrossing H ⟨0, crossings_card_pos_of_fin H i⟩ + 2 * Real.pi

theorem sortedCrossing_lt_cyclicRight
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) :
    sortedCrossing H i < cyclicRight H i := by
  unfold cyclicRight
  split_ifs with hi
  · apply strictMono_sortedCrossing H
    exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.1)
  · have hilast : i.1 + 1 = H.crossings.card := by omega
    have hip := sortedCrossing_mem_period H i
    have hzero := sortedCrossing_mem_period H ⟨0, crossings_card_pos_of_fin H i⟩
    exact hip.2.trans_le (by linarith [hzero.1])

theorem cyclicRight_le_add_period
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) :
    cyclicRight H i ≤ sortedCrossing H i + 2 * Real.pi := by
  unfold cyclicRight
  split_ifs with hi
  · have hip := sortedCrossing_mem_period H ⟨i.1 + 1, hi⟩
    have hi0 := sortedCrossing_mem_period H i
    exact hip.2.le.trans (le_add_of_nonneg_left hi0.1)
  · have hmono : sortedCrossing H
        ⟨0, crossings_card_pos_of_fin H i⟩ ≤
        sortedCrossing H i := by
      apply (H.crossings.orderEmbOfFin rfl).monotone
      exact Fin.mk_le_mk.mpr (Nat.zero_le i.1)
    linarith

theorem cyclicRight_height_eq_zero
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) :
    windingLoopCutHeight frame d L (cyclicRight H i) = 0 := by
  unfold cyclicRight
  split_ifs with hi
  · exact sortedCrossing_height_eq_zero H ⟨i.1 + 1, hi⟩
  · rw [H.periodic_height]
    exact sortedCrossing_height_eq_zero H _

/-- There is no base-period crossing strictly between a nonfinal crossing and its successor. -/
theorem no_crossing_between_successive
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) (hi : i.1 + 1 < H.crossings.card)
    {t : ℝ} (hlt : sortedCrossing H i < t)
    (hrt : t < sortedCrossing H ⟨i.1 + 1, hi⟩) :
    t ∉ H.crossings := by
  intro ht
  let j : Fin H.crossings.card :=
    (H.crossings.orderIsoOfFin rfl).symm ⟨t, ht⟩
  have hj : sortedCrossing H j = t := by
    exact congrArg Subtype.val
      ((H.crossings.orderIsoOfFin rfl).apply_symm_apply ⟨t, ht⟩)
  have hij : i < j := by
    apply (strictMono_sortedCrossing H).lt_iff_lt.mp
    simpa only [hj] using hlt
  have hji : j < ⟨i.1 + 1, hi⟩ := by
    apply (strictMono_sortedCrossing H).lt_iff_lt.mp
    simpa only [hj] using hrt
  have hijv : i.1 < j.1 := hij
  have hjiv : j.1 < i.1 + 1 := hji
  omega

/-- No crossing lies in the lifted seam interval from the last crossing to the first crossing in
the next period. -/
theorem no_crossing_in_seam
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) (hi : ¬ i.1 + 1 < H.crossings.card)
    {t : ℝ} (hlt : sortedCrossing H i < t)
    (hrt : t < sortedCrossing H ⟨0, crossings_card_pos_of_fin H i⟩ + 2 * Real.pi) :
    windingLoopCutHeight frame d L t ≠ 0 := by
  intro htzero
  have hilast : i.1 + 1 = H.crossings.card := by omega
  by_cases htperiod : t < 2 * Real.pi
  · have ht0 : 0 ≤ t :=
      (sortedCrossing_mem_period H i).1.trans hlt.le
    have htmem : t ∈ H.crossings :=
      (H.mem_crossings_iff t).mpr ⟨⟨ht0, htperiod⟩, htzero⟩
    let j : Fin H.crossings.card :=
      (H.crossings.orderIsoOfFin rfl).symm ⟨t, htmem⟩
    have hj : sortedCrossing H j = t := by
      exact congrArg Subtype.val
        ((H.crossings.orderIsoOfFin rfl).apply_symm_apply ⟨t, htmem⟩)
    have hij : i < j := by
      apply (strictMono_sortedCrossing H).lt_iff_lt.mp
      simpa only [hj] using hlt
    have hijv : i.1 < j.1 := hij
    omega
  · have htP : 2 * Real.pi ≤ t := le_of_not_gt htperiod
    let u := t - 2 * Real.pi
    have hu0 : 0 ≤ u := sub_nonneg.mpr htP
    have hufirst : u < sortedCrossing H
        ⟨0, crossings_card_pos_of_fin H i⟩ := by
      dsimp [u]
      linarith
    have huzero : windingLoopCutHeight frame d L u = 0 := by
      dsimp [u]
      rw [H.periodic_height.sub_eq]
      exact htzero
    have huperiod : u < 2 * Real.pi :=
      hufirst.trans (sortedCrossing_mem_period H _).2
    have humem : u ∈ H.crossings :=
      (H.mem_crossings_iff u).mpr ⟨⟨hu0, huperiod⟩, huzero⟩
    let j : Fin H.crossings.card :=
      (H.crossings.orderIsoOfFin rfl).symm ⟨u, humem⟩
    have hj : sortedCrossing H j = u := by
      exact congrArg Subtype.val
        ((H.crossings.orderIsoOfFin rfl).apply_symm_apply ⟨u, humem⟩)
    have hzero_le : sortedCrossing H
        ⟨0, crossings_card_pos_of_fin H i⟩ ≤ sortedCrossing H j := by
      apply (H.crossings.orderEmbOfFin rfl).monotone
      exact Fin.mk_le_mk.mpr (Nat.zero_le j.1)
    rw [hj] at hzero_le
    exact (not_lt_of_ge hzero_le) hufirst

/-- Every open cyclic successor interval, including the seam, is crossing-free. -/
theorem no_crossing_between_cyclic
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) {t : ℝ}
    (ht : t ∈ Ioo (sortedCrossing H i) (cyclicRight H i)) :
    windingLoopCutHeight frame d L t ≠ 0 := by
  unfold cyclicRight at ht
  split_ifs at ht with hi
  · intro hzero
    exact no_crossing_between_successive H i hi ht.1 ht.2
      ((H.mem_crossings_iff t).mpr
        ⟨⟨(sortedCrossing_mem_period H i).1.trans ht.1.le,
          ht.2.trans (sortedCrossing_mem_period H _).2⟩, hzero⟩)
  · exact no_crossing_in_seam H i hi ht.1 ht.2

/-- Integer translates of cyclic successor intervals remain crossing-free. -/
theorem no_crossing_between_cyclic_translate
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) (n : ℤ) {t : ℝ}
    (ht : t ∈ Ioo
      (sortedCrossing H i + (n : ℝ) * (2 * Real.pi))
      (cyclicRight H i + (n : ℝ) * (2 * Real.pi))) :
    windingLoopCutHeight frame d L t ≠ 0 := by
  let u := t - (n : ℝ) * (2 * Real.pi)
  have hu : u ∈ Ioo (sortedCrossing H i) (cyclicRight H i) := by
    dsimp [u]
    constructor <;> linarith [ht.1, ht.2]
  have hune := no_crossing_between_cyclic H i hu
  intro htzero
  apply hune
  calc
    windingLoopCutHeight frame d L u = windingLoopCutHeight frame d L t := by
      dsimp [u]
      exact H.periodic_height.sub_int_mul_eq n
    _ = 0 := htzero

/-- Every noncrossing point of the base period lies in a unique-looking successor interval; the
returned integer is `0`, except for points before the first crossing, which use the seam interval
translated by `-1`. -/
theorem exists_cyclic_interval_of_mem_period_of_ne_zero
    (H : SmoothRegularLoopCutData frame d L)
    (hcross : H.crossings.Nonempty) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hune : windingLoopCutHeight frame d L u ≠ 0) :
    ∃ (i : Fin H.crossings.card) (n : ℤ),
      u ∈ Ioo
        (sortedCrossing H i + (n : ℝ) * (2 * Real.pi))
        (cyclicRight H i + (n : ℝ) * (2 * Real.pi)) := by
  by_cases hbelow : ∃ a ∈ H.crossings, a < u
  · obtain ⟨a, haC, hau, hmax⟩ := H.crossings.exists_next_left hbelow
    let i : Fin H.crossings.card :=
      (H.crossings.orderIsoOfFin rfl).symm ⟨a, haC⟩
    have hiEq : sortedCrossing H i = a := by
      exact congrArg Subtype.val
        ((H.crossings.orderIsoOfFin rfl).apply_symm_apply ⟨a, haC⟩)
    by_cases hi : i.1 + 1 < H.crossings.card
    · refine ⟨i, 0, ?_⟩
      simp only [Int.cast_zero, zero_mul, add_zero]
      rw [hiEq]
      constructor
      · exact hau
      · unfold cyclicRight
        simp only [hi, ↓reduceDIte]
        apply lt_of_not_ge
        intro hnext
        have hnextNe : sortedCrossing H ⟨i.1 + 1, hi⟩ ≠ u := by
          intro heq
          apply hune
          rw [← heq]
          exact sortedCrossing_height_eq_zero H _
        have hnextLt : sortedCrossing H ⟨i.1 + 1, hi⟩ < u :=
          lt_of_le_of_ne hnext hnextNe
        have hle := hmax _ (sortedCrossing_mem H _) hnextLt
        have hind : i < (⟨i.1 + 1, hi⟩ : Fin H.crossings.card) := by
          exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.1)
        have hstrict := strictMono_sortedCrossing H hind
        rw [hiEq] at hstrict
        exact (not_lt_of_ge hle) hstrict
    · refine ⟨i, 0, ?_⟩
      simp only [Int.cast_zero, zero_mul, add_zero]
      rw [hiEq]
      constructor
      · exact hau
      · unfold cyclicRight
        simp only [hi, ↓reduceDIte]
        have hfirst0 := sortedCrossing_mem_period H
          ⟨0, H.crossings.card_pos.mpr hcross⟩
        exact hu.2.trans_le (by linarith [hfirst0.1])
  · let i : Fin H.crossings.card :=
      ⟨H.crossings.card - 1,
        Nat.sub_lt (H.crossings.card_pos.mpr hcross) Nat.zero_lt_one⟩
    have hi : ¬ i.1 + 1 < H.crossings.card := by
      dsimp [i]
      omega
    have hfirstNotLt : ¬ sortedCrossing H
        ⟨0, H.crossings.card_pos.mpr hcross⟩ < u := by
      intro h
      exact hbelow ⟨_, sortedCrossing_mem H _, h⟩
    have hfirstNe : sortedCrossing H
        ⟨0, H.crossings.card_pos.mpr hcross⟩ ≠ u := by
      intro heq
      apply hune
      rw [← heq]
      exact sortedCrossing_height_eq_zero H _
    have huFirst : u < sortedCrossing H
        ⟨0, H.crossings.card_pos.mpr hcross⟩ :=
      lt_of_le_of_ne (le_of_not_gt hfirstNotLt) hfirstNe.symm
    refine ⟨i, -1, ?_⟩
    have hilastP := sortedCrossing_mem_period H i
    constructor
    · norm_num
      linarith [hilastP.2, hu.1]
    · unfold cyclicRight
      simp only [hi, ↓reduceDIte]
      norm_num
      simpa using huFirst

/-- Integer translating the base-period location gives coverage of every noncrossing real
parameter. -/
theorem exists_cyclic_interval_of_ne_zero
    (H : SmoothRegularLoopCutData frame d L)
    (hcross : H.crossings.Nonempty) {t : ℝ}
    (htne : windingLoopCutHeight frame d L t ≠ 0) :
    ∃ (i : Fin H.crossings.card) (n : ℤ),
      t ∈ Ioo
        (sortedCrossing H i + (n : ℝ) * (2 * Real.pi))
        (cyclicRight H i + (n : ℝ) * (2 * Real.pi)) := by
  let u : ℝ := toIcoMod Real.two_pi_pos 0 t
  let k : ℤ := toIcoDiv Real.two_pi_pos 0 t
  have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 t
  have hukt : u + (k : ℝ) * (2 * Real.pi) = t := by
    exact toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 t
  have hune : windingLoopCutHeight frame d L u ≠ 0 := by
    intro huzero
    apply htne
    calc
      windingLoopCutHeight frame d L t =
          windingLoopCutHeight frame d L (u + (k : ℝ) * (2 * Real.pi)) := by rw [hukt]
      _ = windingLoopCutHeight frame d L u :=
        (H.periodic_height.int_mul k) u
      _ = 0 := huzero
  obtain ⟨i, n, hn⟩ :=
    exists_cyclic_interval_of_mem_period_of_ne_zero H hcross hu hune
  refine ⟨i, n + k, ?_⟩
  constructor
  · calc
      sortedCrossing H i + ((n + k : ℤ) : ℝ) * (2 * Real.pi) =
          (sortedCrossing H i + (n : ℝ) * (2 * Real.pi)) +
            (k : ℝ) * (2 * Real.pi) := by push_cast; ring
      _ < u + (k : ℝ) * (2 * Real.pi) := by
        simpa [add_comm] using add_lt_add_right hn.1 ((k : ℝ) * (2 * Real.pi))
      _ = t := hukt
  · calc
      t = u + (k : ℝ) * (2 * Real.pi) := hukt.symm
      _ < (cyclicRight H i + (n : ℝ) * (2 * Real.pi)) +
          (k : ℝ) * (2 * Real.pi) := by
        simpa [add_comm] using add_lt_add_right hn.2 ((k : ℝ) * (2 * Real.pi))
      _ = cyclicRight H i + ((n + k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring

/-- A translated sorted crossing is again a zero of the cutting height. -/
theorem translated_sortedCrossing_height_eq_zero
    (H : SmoothRegularLoopCutData frame d L)
    (i : Fin H.crossings.card) (n : ℤ) :
    windingLoopCutHeight frame d L
      (sortedCrossing H i + (n : ℝ) * (2 * Real.pi)) = 0 := by
  calc
    windingLoopCutHeight frame d L
        (sortedCrossing H i + (n : ℝ) * (2 * Real.pi)) =
        windingLoopCutHeight frame d L (sortedCrossing H i) :=
      (H.periodic_height.int_mul n) (sortedCrossing H i)
    _ = 0 := sortedCrossing_height_eq_zero H i

/-- Distinct translated cyclic successor intervals are disjoint. -/
theorem pairwise_disjoint_translated_cyclicIntervals
    (H : SmoothRegularLoopCutData frame d L) :
    Pairwise fun p q : Fin H.crossings.card × ℤ ↦
      Disjoint
        (Ioo (sortedCrossing H p.1 + (p.2 : ℝ) * (2 * Real.pi))
          (cyclicRight H p.1 + (p.2 : ℝ) * (2 * Real.pi)))
        (Ioo (sortedCrossing H q.1 + (q.2 : ℝ) * (2 * Real.pi))
          (cyclicRight H q.1 + (q.2 : ℝ) * (2 * Real.pi))) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro t htp htq
  let ap := sortedCrossing H p.1 + (p.2 : ℝ) * (2 * Real.pi)
  let aq := sortedCrossing H q.1 + (q.2 : ℝ) * (2 * Real.pi)
  have hap : ap < t := htp.1
  have haq : aq < t := htq.1
  have hapr : t < cyclicRight H p.1 + (p.2 : ℝ) * (2 * Real.pi) := htp.2
  have haqr : t < cyclicRight H q.1 + (q.2 : ℝ) * (2 * Real.pi) := htq.2
  have hae : ap = aq := by
    rcases lt_trichotomy ap aq with hpqlt | heq | hqplt
    · have haqIn : aq ∈ Ioo ap
          (cyclicRight H p.1 + (p.2 : ℝ) * (2 * Real.pi)) :=
        ⟨hpqlt, haq.trans hapr⟩
      exact False.elim <| no_crossing_between_cyclic_translate H p.1 p.2 haqIn
        (translated_sortedCrossing_height_eq_zero H q.1 q.2)
    · exact heq
    · have hapIn : ap ∈ Ioo aq
          (cyclicRight H q.1 + (q.2 : ℝ) * (2 * Real.pi)) :=
        ⟨hqplt, hap.trans haqr⟩
      exact False.elim <| no_crossing_between_cyclic_translate H q.1 q.2 hapIn
        (translated_sortedCrossing_height_eq_zero H p.1 p.2)
  have hn : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with hpqlt | heq | hqplt
    · have hcast : (p.2 : ℝ) + 1 ≤ (q.2 : ℝ) := by exact_mod_cast hpqlt
      have hpPeriod := sortedCrossing_mem_period H p.1
      have hqPeriod := sortedCrossing_mem_period H q.1
      dsimp [ap, aq] at hae
      have hmul := mul_le_mul_of_nonneg_right hcast Real.two_pi_pos.le
      have hlt : sortedCrossing H p.1 + (p.2 : ℝ) * (2 * Real.pi) <
          sortedCrossing H q.1 + (q.2 : ℝ) * (2 * Real.pi) := calc
        _ < (2 * Real.pi) + (p.2 : ℝ) * (2 * Real.pi) :=
          by simpa [add_comm] using
            add_lt_add_right hpPeriod.2 ((p.2 : ℝ) * (2 * Real.pi))
        _ = ((p.2 : ℝ) + 1) * (2 * Real.pi) := by ring
        _ ≤ (q.2 : ℝ) * (2 * Real.pi) := hmul
        _ ≤ sortedCrossing H q.1 + (q.2 : ℝ) * (2 * Real.pi) :=
          le_add_of_nonneg_left hqPeriod.1
      exact False.elim (ne_of_lt hlt hae)
    · exact heq
    · have hcast : (q.2 : ℝ) + 1 ≤ (p.2 : ℝ) := by exact_mod_cast hqplt
      have hpPeriod := sortedCrossing_mem_period H p.1
      have hqPeriod := sortedCrossing_mem_period H q.1
      dsimp [ap, aq] at hae
      have hmul := mul_le_mul_of_nonneg_right hcast Real.two_pi_pos.le
      have hlt : sortedCrossing H q.1 + (q.2 : ℝ) * (2 * Real.pi) <
          sortedCrossing H p.1 + (p.2 : ℝ) * (2 * Real.pi) := calc
        _ < (2 * Real.pi) + (q.2 : ℝ) * (2 * Real.pi) :=
          by simpa [add_comm] using
            add_lt_add_right hqPeriod.2 ((q.2 : ℝ) * (2 * Real.pi))
        _ = ((q.2 : ℝ) + 1) * (2 * Real.pi) := by ring
        _ ≤ (p.2 : ℝ) * (2 * Real.pi) := hmul
        _ ≤ sortedCrossing H p.1 + (p.2 : ℝ) * (2 * Real.pi) :=
          le_add_of_nonneg_left hpPeriod.1
      exact False.elim (ne_of_gt hlt hae)
  have hi : p.1 = q.1 := by
    apply (H.crossings.orderEmbOfFin rfl).injective
    dsimp [ap, aq] at hae
    rw [hn] at hae
    exact add_right_cancel hae
  apply hpq
  exact Prod.ext hi hn

/-- The local sign-flip hypothesis supplies opposite-sign samples in any two cyclic successor
intervals sharing an endpoint. -/
theorem opposite_signs_of_common_cyclic_endpoint
    (H : SmoothRegularLoopCutData frame d L)
    (hflip : HasLocalSignFlipAtCrossings H)
    {i j : Fin H.crossings.card}
    (hcommon : cyclicRight H i = sortedCrossing H j) :
    ∃ x ∈ Ioo (sortedCrossing H i) (cyclicRight H i),
      ∃ y ∈ Ioo (sortedCrossing H j) (cyclicRight H j),
        windingLoopCutHeight frame d L x *
          windingLoopCutHeight frame d L y < 0 := by
  let c := sortedCrossing H j
  obtain ⟨ε, hε, hsign⟩ := hflip c (sortedCrossing_mem H j)
  have hleft : sortedCrossing H i < c := by
    dsimp [c]
    rw [← hcommon]
    exact sortedCrossing_lt_cyclicRight H i
  have hright : c < cyclicRight H j := sortedCrossing_lt_cyclicRight H j
  let x := (max (sortedCrossing H i) (c - ε) + c) / 2
  let y := (c + min (cyclicRight H j) (c + ε)) / 2
  have hmaxlt : max (sortedCrossing H i) (c - ε) < c := by
    rw [max_lt_iff]
    exact ⟨hleft, by linarith⟩
  have hcltmin : c < min (cyclicRight H j) (c + ε) := by
    rw [lt_min_iff]
    exact ⟨hright, by linarith⟩
  have hxInterval : x ∈ Ioo (sortedCrossing H i) (cyclicRight H i) := by
    rw [hcommon]
    dsimp [x]
    constructor
    · have hle := le_max_left (sortedCrossing H i) (c - ε)
      linarith
    · linarith
  have hyInterval : y ∈ Ioo (sortedCrossing H j) (cyclicRight H j) := by
    dsimp [c, y] at hcltmin ⊢
    constructor
    · linarith
    · have hle := min_le_left (cyclicRight H j) (sortedCrossing H j + ε)
      linarith
  have hxLocal : x ∈ Ioo (c - ε) c := by
    dsimp [x]
    constructor
    · have hle := le_max_right (sortedCrossing H i) (c - ε)
      linarith
    · linarith
  have hyLocal : y ∈ Ioo c (c + ε) := by
    dsimp [y]
    constructor
    · linarith
    · have hle := min_le_right (cyclicRight H j) (c + ε)
      linarith
  exact ⟨x, hxInterval, y, hyInterval, hsign x hxLocal y hyLocal⟩

/-- The ordered cyclic skeleton constructed from the sorted canonical crossing finset.  Apart
from local sign reversal, every field is discharged by finite sorting and period arithmetic. -/
def orderedCyclicIntervalSkeleton_of_sortedCrossings
    (H : SmoothRegularLoopCutData frame d L)
    (hcross : H.crossings.Nonempty)
    (hflip : HasLocalSignFlipAtCrossings H) :
    OrderedCyclicIntervalSkeleton H where
  count := H.crossings.card
  count_pos := H.crossings.card_pos.mpr hcross
  left := sortedCrossing H
  right := cyclicRight H
  left_mem_period := sortedCrossing_mem_period H
  left_lt_right := sortedCrossing_lt_cyclicRight H
  right_le_next_period := cyclicRight_le_add_period H
  left_crossing := sortedCrossing_height_eq_zero H
  right_crossing := cyclicRight_height_eq_zero H
  translated_pairwise_disjoint := pairwise_disjoint_translated_cyclicIntervals H
  cover_noncrossings := fun _t ht ↦ exists_cyclic_interval_of_ne_zero H hcross ht
  no_crossing_in_interval := fun i n _t ht ↦
    no_crossing_between_cyclic_translate H i n ht
  opposite_signs_at_common_endpoint := fun _i _j _hij hcommon ↦
    opposite_signs_of_common_cyclic_endpoint H hflip hcommon

/-- Directly constructing the signed cyclic excursion bookkeeping from regular sorted crossings
and the sole local analytic sign-flip hypothesis. -/
def finiteCyclicExcursionBookkeeping_of_sortedCrossings
    (H : SmoothRegularLoopCutData frame d L)
    (hcross : H.crossings.Nonempty)
    (hflip : HasLocalSignFlipAtCrossings H) :
    FiniteCyclicExcursionBookkeeping H :=
  OrderedCyclicIntervalSkeleton.toFiniteCyclicExcursionBookkeeping
    (orderedCyclicIntervalSkeleton_of_sortedCrossings H hcross hflip)

end Submission.Topology
