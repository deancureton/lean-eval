import Submission.Topology.RegularCircleRootDegree

/-!
# Global signed degree of a regular periodic circle lift

This file constructs explicit midpoint gap points around the canonical sorted roots.  When the
period seam is not itself a root, those gaps turn the local floor-jump theorem into the global
signed-root formula.
-/

open Set

noncomputable section

namespace Submission.Topology

namespace RegularPeriodicCircleLift

variable {theta : ℝ → ℝ} {winding : ℤ}

/-- The normalized real lift, whose circle roots are precisely its integer values. -/
def normalizedLift (_H : RegularPeriodicCircleLift theta winding) (t : ℝ) : ℝ :=
  theta t / (2 * Real.pi)

/-- Endpoints and midpoints between the canonical ordered roots. -/
def canonicalGap (H : RegularPeriodicCircleLift theta winding)
    (i : Fin (H.rootFinset.card + 1)) : ℝ :=
  if hlast : i.1 = H.rootFinset.card then 2 * Real.pi
  else if hzero : i.1 = 0 then 0
  else
    (H.orderedRoot ⟨i.1 - 1, by omega⟩ + H.orderedRoot ⟨i.1, by omega⟩) / 2

@[simp] theorem canonicalGap_zero (H : RegularPeriodicCircleLift theta winding)
    (hcount : 0 < H.rootFinset.card) :
    H.canonicalGap 0 = 0 := by
  simp only [canonicalGap, Fin.val_zero, ne_of_lt hcount, ↓reduceDIte]

@[simp] theorem canonicalGap_last (H : RegularPeriodicCircleLift theta winding) :
    H.canonicalGap (Fin.last H.rootFinset.card) = 2 * Real.pi := by
  unfold canonicalGap
  simp only [Fin.val_last, ↓reduceDIte]

theorem canonicalGap_castSucc_lt_orderedRoot
    (H : RegularPeriodicCircleLift theta winding)
    (hseam : Circle.exp (theta 0) ≠ 1) (i : Fin H.rootFinset.card) :
    H.canonicalGap i.castSucc < H.orderedRoot i := by
  by_cases hi : i.1 = 0
  · have hroot_ne : H.orderedRoot i ≠ 0 := by
      intro hroot
      exact hseam (hroot ▸ H.orderedRoot_exp_eq_one i)
    have hroot_pos : 0 < H.orderedRoot i :=
      lt_of_le_of_ne (H.orderedRoot_mem_period i).1 hroot_ne.symm
    have hcount : 0 ≠ H.rootFinset.card := by omega
    simp only [canonicalGap, Fin.val_castSucc, hi, hcount, ↓reduceDIte]
    exact hroot_pos
  · have hilast : i.1 ≠ H.rootFinset.card := Nat.ne_of_lt i.isLt
    have hprev : H.orderedRoot ⟨i.1 - 1, by omega⟩ < H.orderedRoot i := by
      apply H.orderedRoot_strictMono
      exact Fin.mk_lt_mk.mpr (by omega)
    simp only [canonicalGap, Fin.val_castSucc, hilast, hi, ↓reduceDIte]
    linarith

theorem orderedRoot_lt_canonicalGap_succ
    (H : RegularPeriodicCircleLift theta winding) (i : Fin H.rootFinset.card) :
    H.orderedRoot i < H.canonicalGap i.succ := by
  by_cases hilast : i.1 + 1 = H.rootFinset.card
  · have hroot_lt := (H.orderedRoot_mem_period i).2
    simp only [canonicalGap, Fin.val_succ, hilast, ↓reduceDIte]
    exact hroot_lt
  · have hnext : H.orderedRoot i < H.orderedRoot ⟨i.1 + 1, by omega⟩ := by
      apply H.orderedRoot_strictMono
      exact Fin.mk_lt_mk.mpr (by omega)
    have hnonzero : i.1 + 1 ≠ 0 := Nat.succ_ne_zero i.1
    simp only [canonicalGap, Fin.val_succ, hilast, hnonzero, ↓reduceDIte]
    have hpred : i.1 + 1 - 1 = i.1 := by omega
    have hfinpred :
        (⟨i.1 + 1 - 1, by omega⟩ : Fin H.rootFinset.card) = i := by
      apply Fin.ext
      exact hpred
    rw [hfinpred]
    linarith

theorem orderedRoot_pred_lt_canonicalGap_castSucc
    (H : RegularPeriodicCircleLift theta winding) (i : Fin H.rootFinset.card)
    (hi : 0 < i.1) :
    H.orderedRoot ⟨i.1 - 1, by omega⟩ < H.canonicalGap i.castSucc := by
  have hilast : i.1 ≠ H.rootFinset.card := Nat.ne_of_lt i.isLt
  have hroots : H.orderedRoot ⟨i.1 - 1, by omega⟩ < H.orderedRoot i := by
    apply H.orderedRoot_strictMono
    exact Fin.mk_lt_mk.mpr (by omega)
  simp only [canonicalGap, Fin.val_castSucc, hilast, ne_of_gt hi, ↓reduceDIte]
  linarith

theorem canonicalGap_succ_lt_orderedRoot_succ
    (H : RegularPeriodicCircleLift theta winding) (i : Fin H.rootFinset.card)
    (hi : i.1 + 1 < H.rootFinset.card) :
    H.canonicalGap i.succ < H.orderedRoot ⟨i.1 + 1, hi⟩ := by
  have hilast : i.1 + 1 ≠ H.rootFinset.card := Nat.ne_of_lt hi
  have hnonzero : i.1 + 1 ≠ 0 := Nat.succ_ne_zero i.1
  have hroots : H.orderedRoot i < H.orderedRoot ⟨i.1 + 1, hi⟩ := by
    apply H.orderedRoot_strictMono
    exact Fin.mk_lt_mk.mpr (by omega)
  simp only [canonicalGap, Fin.val_succ, hilast, hnonzero, ↓reduceDIte]
  have hfinpred :
      (⟨i.1 + 1 - 1, by omega⟩ : Fin H.rootFinset.card) = i := by
    apply Fin.ext
    simp
  rw [hfinpred]
  linarith

theorem canonicalGap_mem_Icc
    (H : RegularPeriodicCircleLift theta winding) (hcount : 0 < H.rootFinset.card)
    (i : Fin (H.rootFinset.card + 1)) :
    H.canonicalGap i ∈ Icc (0 : ℝ) (2 * Real.pi) := by
  unfold canonicalGap
  split_ifs with hlast hzero
  · exact ⟨Real.two_pi_pos.le, le_rfl⟩
  · exact ⟨le_rfl, Real.two_pi_pos.le⟩
  · have hleft := H.orderedRoot_mem_period ⟨i.1 - 1, by omega⟩
    have hright := H.orderedRoot_mem_period ⟨i.1, by omega⟩
    constructor
    · linarith [hleft.1, hright.1]
    · linarith [hleft.2, hright.2]

/-- The canonical midpoint gaps package the sorted roots as regular integer crossings. -/
def canonicalOrderedRegularIntegerRootGaps
    (H : RegularPeriodicCircleLift theta winding)
    (hseam : Circle.exp (theta 0) ≠ 1) (hcount : 0 < H.rootFinset.card) :
    OrderedRegularIntegerRootGaps H.normalizedLift 0 (2 * Real.pi) where
  count := H.rootFinset.card
  root := H.orderedRoot
  gap := H.canonicalGap
  gap_zero := H.canonicalGap_zero hcount
  gap_last := H.canonicalGap_last
  gap_lt_root := H.canonicalGap_castSucc_lt_orderedRoot hseam
  root_lt_gap := H.orderedRoot_lt_canonicalGap_succ
  root_intCast i := by
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp (H.orderedRoot_exp_eq_one i)
    refine ⟨k, ?_⟩
    rw [normalizedLift, hk]
    field_simp
  regular_root i := by
    change deriv (fun t ↦ theta t / (2 * Real.pi)) (H.orderedRoot i) ≠ 0
    rw [deriv_div_const]
    exact div_ne_zero (H.orderedRoot_regular i) (ne_of_gt Real.two_pi_pos)
  unique_root_between i t ht hint := by
    obtain ⟨k, hk⟩ := hint
    have htheta : theta t = (k : ℝ) * (2 * Real.pi) := by
      exact (div_eq_iff (ne_of_gt Real.two_pi_pos)).mp hk
    have hexp : Circle.exp (theta t) = 1 := Circle.exp_eq_one.mpr ⟨k, htheta⟩
    have hgapLeft := H.canonicalGap_mem_Icc hcount i.castSucc
    have hgapRight := H.canonicalGap_mem_Icc hcount i.succ
    have htmem : t ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      refine ⟨hgapLeft.1.trans ht.1, lt_of_le_of_ne (ht.2.trans hgapRight.2) ?_⟩
      intro htTop
      have hthetaPeriod :
          theta (2 * Real.pi) = theta 0 + (winding : ℝ) * (2 * Real.pi) := by
        simpa only [zero_add] using H.angle_add_period 0
      apply hseam
      apply Circle.exp_eq_one.mpr
      refine ⟨k - winding, ?_⟩
      calc
        theta 0 = theta (2 * Real.pi) - (winding : ℝ) * (2 * Real.pi) := by
          linarith
        _ = theta t - (winding : ℝ) * (2 * Real.pi) := by rw [htTop]
        _ = (k : ℝ) * (2 * Real.pi) - (winding : ℝ) * (2 * Real.pi) := by
          rw [htheta]
        _ = ((k - winding : ℤ) : ℝ) * (2 * Real.pi) := by
          push_cast
          ring
    obtain ⟨j, hj⟩ := H.orderedRoot_complete t htmem hexp
    have htroot : t = H.orderedRoot j := hj.symm
    rcases lt_trichotomy j.1 i.1 with hji | hji | hji
    · have hi : 0 < i.1 := by omega
      have hjprev : H.orderedRoot j ≤ H.orderedRoot ⟨i.1 - 1, by omega⟩ := by
        apply H.orderedRoot_strictMono.monotone
        exact Fin.mk_le_mk.mpr (by omega)
      have hprevgap := H.orderedRoot_pred_lt_canonicalGap_castSucc i hi
      rw [htroot] at ht
      exact False.elim ((not_lt_of_ge ht.1) (hjprev.trans_lt hprevgap))
    · exact htroot.trans (congr_arg H.orderedRoot (Fin.ext hji))
    · have hi : i.1 + 1 < H.rootFinset.card := by omega
      have hnextj : H.orderedRoot ⟨i.1 + 1, hi⟩ ≤ H.orderedRoot j := by
        apply H.orderedRoot_strictMono.monotone
        exact Fin.mk_le_mk.mpr (by omega)
      have hgapnext := H.canonicalGap_succ_lt_orderedRoot_succ i hi
      rw [htroot] at ht
      exact False.elim ((not_lt_of_ge ht.2) (hgapnext.trans_le hnextj))

theorem crossingSign_normalizedLift
    (H : RegularPeriodicCircleLift theta winding) (t : ℝ) :
    realRootCrossingSign H.normalizedLift t = realRootCrossingSign theta t := by
  unfold realRootCrossingSign normalizedLift
  rw [deriv_div_const]
  have hnot : ¬ (2 * Real.pi < 0) := not_lt_of_ge Real.two_pi_pos.le
  simp only [div_pos_iff, Real.two_pi_pos, and_true, hnot, and_false, or_false]

/-- Global one-dimensional signed degree, including the empty-root case.  The sole seam hypothesis
ensures that the canonical half-open period has non-root endpoints for floor telescoping. -/
theorem sum_crossingSign_orderedRoot_eq_winding
    (H : RegularPeriodicCircleLift theta winding) (hseam : Circle.exp (theta 0) ≠ 1) :
    ∑ i : Fin H.rootFinset.card,
      realRootCrossingSign theta (H.orderedRoot i) = winding := by
  by_cases hempty : H.rootFinset = ∅
  · have hcard : H.rootFinset.card = 0 := by simp only [hempty, Finset.card_empty]
    have hwinding := H.winding_eq_zero_of_rootFinset_eq_empty hempty
    calc
      (∑ i : Fin H.rootFinset.card,
        realRootCrossingSign theta (H.orderedRoot i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact Fin.elim0 (Fin.cast hcard i)
      _ = winding := hwinding.symm
  · have hcount : 0 < H.rootFinset.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hempty)
    let G := H.canonicalOrderedRegularIntegerRootGaps hseam hcount
    have hdegree := G.sum_crossingSign_eq_floor_sub_floor
      (H.contDiff_theta.div_const (2 * Real.pi))
    have huPeriod : H.normalizedLift (2 * Real.pi) = H.normalizedLift 0 + winding := by
      unfold normalizedLift
      have hthetaPeriod :
          theta (2 * Real.pi) = theta 0 + (winding : ℝ) * (2 * Real.pi) := by
        simpa only [zero_add] using H.angle_add_period 0
      rw [hthetaPeriod]
      field_simp
    change (∑ i : Fin H.rootFinset.card,
      realRootCrossingSign H.normalizedLift (H.orderedRoot i)) =
        ⌊H.normalizedLift (2 * Real.pi)⌋ - ⌊H.normalizedLift 0⌋ at hdegree
    simp_rw [H.crossingSign_normalizedLift] at hdegree
    rw [huPeriod, Int.floor_add_intCast] at hdegree
    simpa only [add_sub_cancel_left] using hdegree

/-- Fully constructed ordered root data from raw regularity and a non-root period seam. -/
def orderedRegularCircleRootData
    (H : RegularPeriodicCircleLift theta winding) (hseam : Circle.exp (theta 0) ≠ 1) :
    OrderedRegularCircleRootData theta winding :=
  H.orderedRegularCircleRootDataOfSignedSum
    (H.sum_crossingSign_orderedRoot_eq_winding hseam)

end RegularPeriodicCircleLift

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology

/-- Final direct `SL(2,Z)` certificate from raw `C¹`, regular-root, seam, and embedded-loop
hypotheses.  No homotopy or prepackaged ordered-root datum is required. -/
def transverseIntersectionCertificateOfRawRegular
    (p q : ℕ) (hc : p.Coprime q) {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma)
    (hfirst : ContDiff ℝ 1 L.first.angle)
    (hsecond : ContDiff ℝ 1 L.second.angle)
    (hregular : ∀ t, Circle.exp (transformedSlopeAngle p q L t) = 1 →
      deriv (transformedSlopeAngle p q L) t ≠ 0)
    (hseam : Circle.exp (transformedSlopeAngle p q L 0) ≠ 1)
    (hinjective : Set.InjOn gamma (Set.Ico (0 : ℝ) (2 * Real.pi))) :
    TransverseIntersectionCertificate p q gamma
      L.first.winding L.second.winding := by
  let H := transformedRegularPeriodicCircleLift p q L hfirst hsecond hregular
  let D := H.orderedRegularCircleRootData hseam
  exact CircleRootKnotParameterization.transverseIntersectionCertificate_of_injective
    p q hc L D hinjective

end Submission.PardonDistortion
