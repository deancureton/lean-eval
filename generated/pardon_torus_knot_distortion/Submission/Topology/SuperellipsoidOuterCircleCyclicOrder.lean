import Submission.Topology.CrossingSignFlip
import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Cyclic height order on the outer superellipsoid circles

The finite barrier graph already decomposes the regular outer section into pairwise-disjoint
embedded circles.  A smooth regular parametrization of each such circle turns its intersections
with the cutting plane into the canonical finite crossing set of `SmoothRegularLoopCutData`.
The generic sorted-crossing construction then gives alternating lower and upper arcs.

This file deliberately stops before gluing outer arcs to the inward cutting-circle arcs.  It
packages the sorted outer arcs, proves exact coverage away from the seam, and proves that their
open ranges are pairwise disjoint.  The seam itself is identified exactly with the endpoints by
an equivalence, so a later finite graph-cycle construction has no hidden geometric premise.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

/-- Smooth regular cutting-height data on every parametrized outer circle.  This is the precise
regularity input not retained by the topological `EmbeddedTorusIntersectionCircle` interface. -/
structure OuterCircleTransverseHeightCyclicOrderFamily
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) where
  regular : ∀ i : outerIndex,
    SmoothRegularLoopCutData frame d (G.outer.circle i).windingLoop

namespace OuterCircleTransverseHeightCyclicOrderFamily

variable (F : OuterCircleTransverseHeightCyclicOrderFamily G)

/-- Outer circles which actually meet the cutting plane. -/
def ActiveOuterCircle :=
  {i : outerIndex // (F.regular i).crossings.Nonempty}

noncomputable instance activeOuterCircleFintype : Fintype F.ActiveOuterCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- One canonical cyclic gap on an active outer circle. -/
def GlobalOuterGap :=
  Σ i : F.ActiveOuterCircle, Fin (F.regular i.1).crossings.card

noncomputable instance globalOuterGapFintype : Fintype F.GlobalOuterGap := by
  classical
  exact Sigma.instFintype

/-- The generic sorted-crossing bookkeeping on one active outer circle. -/
noncomputable def bookkeeping (i : F.ActiveOuterCircle) :
    FiniteCyclicExcursionBookkeeping (F.regular i.1) :=
  (F.regular i.1).finiteCyclicExcursionBookkeeping i.2

/-- The signed cyclic excursion represented by a global outer gap. -/
noncomputable def excursion (g : F.GlobalOuterGap) :
    CyclicExcursionInterval (F.regular g.1.1) :=
  (F.bookkeeping g.1).excursion g.2

@[simp]
theorem excursion_left (i : F.ActiveOuterCircle)
    (q : Fin (F.regular i.1).crossings.card) :
    (F.excursion ⟨i, q⟩).left = sortedCrossing (F.regular i.1) q := rfl

@[simp]
theorem excursion_right (i : F.ActiveOuterCircle)
    (q : Fin (F.regular i.1).crossings.card) :
    (F.excursion ⟨i, q⟩).right = cyclicRight (F.regular i.1) q := rfl

/-- Canonical gap side indexed cyclically.  `true` is the strict upper side. -/
noncomputable def zmodGapSide (i : F.ActiveOuterCircle) :
    ZMod (F.regular i.1).crossings.card → Bool := by
  letI : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  exact fun q ↦
    (F.excursion ⟨i, ⟨q.val, ZMod.val_lt q⟩⟩).upper

/-- A simple zero changes the side at every cyclic successor, including across the chosen
period seam.  The non-wrap case is the generic sorted-crossing theorem.  At the wrap, the sample
on the last gap is translated back by one period before applying the same local sign flip. -/
theorem zmodGapSide_add_one_ne (i : F.ActiveOuterCircle)
    (qz : ZMod (F.regular i.1).crossings.card) :
    F.zmodGapSide i (qz + 1) ≠ F.zmodGapSide i qz := by
  let H := F.regular i.1
  let _ : NeZero H.crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  let q : Fin H.crossings.card := ⟨qz.val, ZMod.val_lt qz⟩
  let qnext : Fin H.crossings.card :=
    ⟨(qz + 1).val, ZMod.val_lt (qz + 1)⟩
  have hnextVal : (qz + 1).val = (qz.val + 1) % H.crossings.card := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    nth_rewrite 1 [← Nat.mod_eq_of_lt (ZMod.val_lt qz)]
    exact (Nat.add_mod qz.val 1 H.crossings.card).symm
  change (F.excursion ⟨i, qnext⟩).upper ≠
    (F.excursion ⟨i, q⟩).upper
  by_cases hnext : q.1 + 1 < H.crossings.card
  · have hqnext : qnext = ⟨q.1 + 1, hnext⟩ := by
      apply Fin.ext
      change (qz + 1).val = qz.val + 1
      rw [hnextVal, Nat.mod_eq_of_lt hnext]
    apply Ne.symm
    apply (F.bookkeeping i).alternating_at_common_endpoint q qnext
    · intro hqq
      have := congrArg Fin.val hqq
      rw [hqnext] at this
      change q.1 = q.1 + 1 at this
      omega
    · change cyclicRight H q = sortedCrossing H qnext
      rw [hqnext]
      simp [cyclicRight, hnext]
  · have hlast : q.1 + 1 = H.crossings.card := by omega
    have hqnext : qnext = ⟨0, Finset.card_pos.mpr i.2⟩ := by
      apply Fin.ext
      change (qz + 1).val = 0
      rw [hnextVal, show qz.val + 1 = H.crossings.card by
        simpa only [q] using hlast, Nat.mod_self]
    let first : Fin H.crossings.card := ⟨0, Finset.card_pos.mpr i.2⟩
    let left := sortedCrossing H q
    let crossing := sortedCrossing H first
    let right := cyclicRight H first
    have hleftCrossing : left < crossing + 2 * Real.pi := by
      have hleftPeriod := sortedCrossing_mem_period H q
      have hfirstPeriod := sortedCrossing_mem_period H first
      exact hleftPeriod.2.trans_le (by linarith [hfirstPeriod.1])
    have hcrossingRight : crossing < right :=
      sortedCrossing_lt_cyclicRight H first
    obtain ⟨ε, hε, hflip⟩ := H.hasLocalSignFlipAtCrossings crossing
      (sortedCrossing_mem H first)
    let δ := min (ε / 2)
      (min ((crossing + 2 * Real.pi - left) / 2) ((right - crossing) / 2))
    have hδ : 0 < δ := by
      exact lt_min (half_pos hε) <| lt_min
        (half_pos (sub_pos.mpr hleftCrossing))
        (half_pos (sub_pos.mpr hcrossingRight))
    have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hδleft : δ < crossing + 2 * Real.pi - left :=
      (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hleftCrossing))
    have hδright : δ < right - crossing :=
      (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hcrossingRight))
    let x := crossing - δ
    let xLast := x + 2 * Real.pi
    let y := crossing + δ
    have hxLocal : x ∈ Ioo (crossing - ε) crossing := by
      dsimp [x]
      constructor <;> linarith
    have hyLocal : y ∈ Ioo crossing (crossing + ε) := by
      dsimp [y]
      constructor <;> linarith
    have hxLastGap : xLast ∈ Ioo left (crossing + 2 * Real.pi) := by
      dsimp [xLast, x]
      constructor <;> linarith
    have hyGap : y ∈ Ioo crossing right := by
      dsimp [y]
      constructor <;> linarith
    have hxsign := (F.excursion ⟨i, q⟩).strict_side xLast (by
      rw [F.excursion_left, F.excursion_right]
      simpa [left, crossing, first, cyclicRight, hnext] using hxLastGap)
    have hysign := (F.excursion ⟨i, qnext⟩).strict_side y (by
      rw [hqnext, F.excursion_left, F.excursion_right]
      simpa [first, crossing, right] using hyGap)
    have hxperiod : windingLoopCutHeight frame d
        (G.outer.circle i.1).windingLoop xLast =
        windingLoopCutHeight frame d
          (G.outer.circle i.1).windingLoop x := by
      simpa only [xLast] using H.periodic_height x
    intro heq
    rw [heq] at hysign
    rw [hxperiod] at hxsign
    have hxy := hflip x hxLocal y hyLocal
    cases hs : (F.excursion ⟨i, q⟩).upper <;>
      simp only [hs, Bool.false_eq_true, if_false, if_true] at hxsign hysign
    · exact (not_lt_of_ge
        (mul_nonneg_of_nonpos_of_nonpos hxsign.le hysign.le)) hxy
    · exact (not_lt_of_ge (mul_nonneg hxsign.le hysign.le)) hxy

/-- Lower and upper outer gaps, selected by their derived strict side. -/
def LowerGap := {g : F.GlobalOuterGap // (F.excursion g).upper = false}
def UpperGap := {g : F.GlobalOuterGap // (F.excursion g).upper = true}

noncomputable instance lowerGapFintype : Fintype F.LowerGap := by
  classical exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance upperGapFintype : Fintype F.UpperGap := by
  classical exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Affine parameter on the lifted representative interval of an outer gap. -/
def gapParameter (g : F.GlobalOuterGap) (u : unitInterval) : ℝ :=
  (F.excursion g).left + (u : ℝ) *
    ((F.excursion g).right - (F.excursion g).left)

theorem gapParameter_mem_Icc (g : F.GlobalOuterGap) (u : unitInterval) :
    F.gapParameter g u ∈ Icc (F.excursion g).left (F.excursion g).right := by
  have hu0 : 0 ≤ (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  have hlr := (F.excursion g).left_lt_right
  constructor <;> unfold gapParameter <;> nlinarith

theorem gapParameter_mem_Ioo (g : F.GlobalOuterGap) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    F.gapParameter g u ∈ Ioo (F.excursion g).left (F.excursion g).right := by
  have hu0' : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
  have hu1' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu1
  have hlr := (F.excursion g).left_lt_right
  constructor <;> unfold gapParameter <;> nlinarith

/-- Closed parametrized outer half-arc associated to a cyclic gap. -/
noncomputable def gapPath (g : F.GlobalOuterGap) :
    Path
      ((G.outer.circle g.1.1).windingLoop.curve (F.excursion g).left)
      ((G.outer.circle g.1.1).windingLoop.curve (F.excursion g).right) where
  toContinuousMap := ⟨fun u ↦
      (G.outer.circle g.1.1).windingLoop.curve (F.gapParameter g u),
    (G.outer.circle g.1.1).windingLoop.continuous_curve.comp
      (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩
  source' := by simp [gapParameter]
  target' := by simp [gapParameter]

@[simp]
theorem gapPath_apply (g : F.GlobalOuterGap) (u : unitInterval) :
    F.gapPath g u =
      (G.outer.circle g.1.1).windingLoop.curve (F.gapParameter g u) := rfl

/-- Every gap path stays on its selected complete outer circle. -/
theorem gapPath_mem_outerCircle (g : F.GlobalOuterGap) (u : unitInterval) :
    ((F.gapPath g u : transportedTorus Phi) : R3) ∈
      Set.range (G.outer.circle g.1.1).circle := by
  exact ⟨Circle.exp (F.gapParameter g u),
    (G.outer.circle g.1.1).parametrization (F.gapParameter g u)⟩

/-- A lower selected gap lies in the closed lower halfspace, including its seam endpoints. -/
theorem lowerGapPath_mem (g : F.LowerGap) (u : unitInterval) :
    ((F.gapPath g.1 u : transportedTorus Phi) : R3) ∈
      lowerClosedHalfspace frame d := by
  exact ((F.excursion g.1).curve_mem_lower_of_mem_Icc g.2
    (F.gapParameter_mem_Icc g.1 u)).2

/-- An upper selected gap lies in the closed upper halfspace, including its seam endpoints. -/
theorem upperGapPath_mem (g : F.UpperGap) (u : unitInterval) :
    ((F.gapPath g.1 u : transportedTorus Phi) : R3) ∈
      upperClosedHalfspace frame d := by
  exact ((F.excursion g.1).curve_mem_upper_of_mem_Icc g.2
    (F.gapParameter_mem_Icc g.1 u)).2

/-- Open parameter range of one outer gap. -/
def openGapRange (g : F.GlobalOuterGap) : Set R3 :=
  ((fun u : unitInterval ↦ ((F.gapPath g u : transportedTorus Phi) : R3)) ''
    {u | (u : ℝ) ≠ 0 ∧ (u : ℝ) ≠ 1})

/-- Distinct open outer gaps have disjoint ambient ranges.  Different outer circles are disjoint
by the regular section decomposition; on one circle this is exactly the generic disjointness of
all integer translates of the sorted cyclic intervals. -/
theorem openGapRanges_pairwise_disjoint :
    Pairwise fun g h : F.GlobalOuterGap ↦
      Disjoint (F.openGapRange g) (F.openGapRange h) := by
  rintro ⟨i, q⟩ ⟨j, r⟩ hqr
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvEq⟩
  by_cases hij : i = j
  · subst j
    have hqne : q ≠ r := by
      intro h
      subst r
      exact hqr rfl
    let s := F.gapParameter (⟨i, q⟩ : F.GlobalOuterGap) u
    let t := F.gapParameter (⟨i, r⟩ : F.GlobalOuterGap) v
    have hs : s ∈ ((F.excursion ⟨i, q⟩).translatedParams 0) := by
      simpa [s, CyclicExcursionInterval.translatedParams] using
        F.gapParameter_mem_Ioo (⟨i, q⟩ : F.GlobalOuterGap) u hu.1 hu.2
    have ht : t ∈ Ioo (F.excursion ⟨i, r⟩).left
        (F.excursion ⟨i, r⟩).right :=
      F.gapParameter_mem_Ioo (⟨i, r⟩ : F.GlobalOuterGap) v hv.1 hv.2
    have hexp : Circle.exp s = Circle.exp t := by
      apply (G.outer.circle i.1).isEmbedding.injective
      rw [(G.outer.circle i.1).parametrization,
        (G.outer.circle i.1).parametrization]
      exact hvEq.symm
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    have htTranslated : s ∈
        ((F.excursion ⟨i, r⟩).translatedParams n) := by
      change s ∈ Ioo
        ((F.excursion ⟨i, r⟩).left + (n : ℝ) * (2 * Real.pi))
        ((F.excursion ⟨i, r⟩).right + (n : ℝ) * (2 * Real.pi))
      constructor <;> linarith [ht.1, ht.2]
    have hpq : (q, (0 : ℤ)) ≠ (r, n) := by
      intro hp
      exact hqne (congrArg Prod.fst hp)
    have hdisjoint := (F.bookkeeping i).translated_pairwise_disjoint hpq
    exact Set.disjoint_left.mp hdisjoint hs htTranslated
  · have hijVal : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
    have hcircles := G.outer.pairwise_disjoint hijVal
    change Disjoint (Set.range (G.outer.circle i.1).circle)
      (Set.range (G.outer.circle j.1).circle) at hcircles
    apply Set.disjoint_left.mp hcircles
    · exact F.gapPath_mem_outerCircle ⟨i, q⟩ u
    · have hvMem := F.gapPath_mem_outerCircle ⟨j, r⟩ v
      exact Eq.mp (congrArg
        (fun y : R3 ↦ y ∈ Set.range (G.outer.circle j.1).circle) hvEq) hvMem

/-- The strict part of the active outer family below the cutting plane. -/
def activeStrictLowerCarrier : Set R3 :=
  (⋃ i : F.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
    {x | x.ofLp (frame 2) < d}

/-- The strict part of the active outer family above the cutting plane. -/
def activeStrictUpperCarrier : Set R3 :=
  (⋃ i : F.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
    {x | d < x.ofLp (frame 2)}

/-- Exact coverage of the strict lower outer half-arcs.  Seam endpoints are intentionally
excluded here and are enumerated exactly by `activeOuterSeamVertexEquiv` below. -/
theorem iUnion_openLowerGapRange_eq_activeStrictLowerCarrier :
    (⋃ g : F.LowerGap, F.openGapRange g.1) = F.activeStrictLowerCarrier := by
  ext x
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨g, u, hu, rfl⟩
    refine ⟨Set.mem_iUnion.mpr ⟨g.1.1, F.gapPath_mem_outerCircle g.1 u⟩, ?_⟩
    have hside := (F.excursion g.1).strict_side (F.gapParameter g.1 u)
      (F.gapParameter_mem_Ioo g.1 u hu.1 hu.2)
    rw [g.2] at hside
    exact sub_neg.mp hside
  · rintro ⟨hxCircle, hxLower⟩
    simp only [Set.mem_iUnion] at hxCircle ⊢
    obtain ⟨i, z, hz⟩ := hxCircle
    let t := circlePhaseRepresentative z
    have htcurve : ((G.outer.circle i.1).windingLoop.curve t : R3) = x := by
      rw [← (G.outer.circle i.1).parametrization t,
        exp_circlePhaseRepresentative, hz]
    have hheight : windingLoopCutHeight frame d
        (G.outer.circle i.1).windingLoop t < 0 := by
      unfold windingLoopCutHeight
      rw [htcurve]
      exact sub_neg.mpr hxLower
    obtain ⟨q, n, hq⟩ := (F.bookkeeping i).cover_noncrossings t (ne_of_lt hheight)
    let E := F.excursion (⟨i, q⟩ : F.GlobalOuterGap)
    let a := E.left + (n : ℝ) * (2 * Real.pi)
    let b := E.right + (n : ℝ) * (2 * Real.pi)
    let uReal := (t - a) / (b - a)
    have hat : a < t := by simpa only [a, E, excursion] using hq.1
    have htb : t < b := by simpa only [b, E, excursion] using hq.2
    have hab : a < b := by dsimp [a, b]; linarith [E.left_lt_right]
    have hu0 : 0 < uReal := by
      dsimp [uReal]
      exact div_pos (sub_pos.mpr hat) (sub_pos.mpr hab)
    have hu1 : uReal < 1 := by
      dsimp [uReal]
      rw [div_lt_one (sub_pos.mpr hab)]
      linarith [htb]
    let u : unitInterval := ⟨uReal, hu0.le, hu1.le⟩
    have hside : E.upper = false := by
      let t₀ := t - (n : ℝ) * (2 * Real.pi)
      have ht₀ : t₀ ∈ Ioo E.left E.right := by
        dsimp [t₀]
        dsimp [a, b] at hat htb
        constructor <;> linarith [hat, htb]
      have hheight₀ : windingLoopCutHeight frame d
          (G.outer.circle i.1).windingLoop t₀ < 0 := by
        rw [(F.regular i.1).periodic_height.sub_int_mul_eq n]
        exact hheight
      by_cases hs : E.upper = true
      · have hpositive := E.strict_side t₀ ht₀
        rw [hs] at hpositive
        exact False.elim (not_lt_of_ge hpositive.le hheight₀)
      · exact Bool.eq_false_iff.mpr hs
    let g : F.LowerGap := ⟨⟨i, q⟩, hside⟩
    refine ⟨g, u, ⟨ne_of_gt hu0, ne_of_lt hu1⟩, ?_⟩
    change ((G.outer.circle i.1).windingLoop.curve (F.gapParameter g.1 u) : R3) = x
    have hparam : F.gapParameter g.1 u =
        t - (n : ℝ) * (2 * Real.pi) := by
      change E.left + uReal * (E.right - E.left) =
        t - (n : ℝ) * (2 * Real.pi)
      dsimp [uReal, a, b]
      field_simp [ne_of_gt (sub_pos.mpr E.left_lt_right)]; ring
    rw [hparam,
      (G.outer.circle i.1).windingLoop.periodic_curve.sub_int_mul_eq n,
      htcurve]

/-! The upper exact-coverage theorem is the order-dual argument through the same generic signed
bookkeeping; the proof below follows the lower proof with inequalities reversed. -/

/-- Exact coverage of the strict upper outer half-arcs. -/
theorem iUnion_openUpperGapRange_eq_activeStrictUpperCarrier :
    (⋃ g : F.UpperGap, F.openGapRange g.1) = F.activeStrictUpperCarrier := by
  ext x
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨g, u, hu, rfl⟩
    refine ⟨Set.mem_iUnion.mpr ⟨g.1.1, F.gapPath_mem_outerCircle g.1 u⟩, ?_⟩
    have hside := (F.excursion g.1).strict_side (F.gapParameter g.1 u)
      (F.gapParameter_mem_Ioo g.1 u hu.1 hu.2)
    rw [g.2] at hside
    exact sub_pos.mp hside
  · rintro ⟨hxCircle, hxUpper⟩
    simp only [Set.mem_iUnion] at hxCircle ⊢
    obtain ⟨i, z, hz⟩ := hxCircle
    let t := circlePhaseRepresentative z
    have htcurve : ((G.outer.circle i.1).windingLoop.curve t : R3) = x := by
      rw [← (G.outer.circle i.1).parametrization t,
        exp_circlePhaseRepresentative, hz]
    have hheight : 0 < windingLoopCutHeight frame d
        (G.outer.circle i.1).windingLoop t := by
      unfold windingLoopCutHeight
      rw [htcurve]
      exact sub_pos.mpr hxUpper
    obtain ⟨q, n, hq⟩ := (F.bookkeeping i).cover_noncrossings t (ne_of_gt hheight)
    let E := F.excursion (⟨i, q⟩ : F.GlobalOuterGap)
    let a := E.left + (n : ℝ) * (2 * Real.pi)
    let b := E.right + (n : ℝ) * (2 * Real.pi)
    let uReal := (t - a) / (b - a)
    have hat : a < t := by simpa only [a, E, excursion] using hq.1
    have htb : t < b := by simpa only [b, E, excursion] using hq.2
    have hab : a < b := by dsimp [a, b]; linarith [E.left_lt_right]
    have hu0 : 0 < uReal := by
      dsimp [uReal]
      exact div_pos (sub_pos.mpr hat) (sub_pos.mpr hab)
    have hu1 : uReal < 1 := by
      dsimp [uReal]
      rw [div_lt_one (sub_pos.mpr hab)]
      linarith [htb]
    let u : unitInterval := ⟨uReal, hu0.le, hu1.le⟩
    have hside : E.upper = true := by
      let t₀ := t - (n : ℝ) * (2 * Real.pi)
      have ht₀ : t₀ ∈ Ioo E.left E.right := by
        dsimp [t₀]
        dsimp [a, b] at hat htb
        constructor <;> linarith [hat, htb]
      have hheight₀ : 0 < windingLoopCutHeight frame d
          (G.outer.circle i.1).windingLoop t₀ := by
        rw [(F.regular i.1).periodic_height.sub_int_mul_eq n]
        exact hheight
      by_cases hs : E.upper = true
      · exact hs
      · have hnegative := E.strict_side t₀ ht₀
        have hsfalse : E.upper = false := Bool.eq_false_iff.mpr hs
        rw [hsfalse] at hnegative
        exact False.elim (not_lt_of_ge hheight₀.le hnegative)
    let g : F.UpperGap := ⟨⟨i, q⟩, hside⟩
    refine ⟨g, u, ⟨ne_of_gt hu0, ne_of_lt hu1⟩, ?_⟩
    change ((G.outer.circle i.1).windingLoop.curve (F.gapParameter g.1 u) : R3) = x
    have hparam : F.gapParameter g.1 u =
        t - (n : ℝ) * (2 * Real.pi) := by
      change E.left + uReal * (E.right - E.left) =
        t - (n : ℝ) * (2 * Real.pi)
      dsimp [uReal, a, b]
      field_simp [ne_of_gt (sub_pos.mpr E.left_lt_right)]; ring
    rw [hparam]
    rw [(G.outer.circle i.1).windingLoop.periodic_curve.sub_int_mul_eq n,
      htcurve]

/-! ## Exact seam endpoint enumeration -/

/-- Geometric seam points on one outer circle. -/
def OuterCircleSeamVertex (i : outerIndex) :=
  Set.range (G.outer.circle i).circle ∩
    superellipsoidTorusSeam Phi frame c R d

noncomputable instance outerCircleSeamVertexFintype (i : outerIndex) :
    Fintype (OuterCircleSeamVertex (G := G) i) :=
  (G.seam_finite.subset inter_subset_right).fintype

theorem mem_crossings_iff_curve_mem_seam (i : outerIndex) (t : ℝ) :
    t ∈ (F.regular i).crossings ↔
      t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
        ((G.outer.circle i).windingLoop.curve t : R3) ∈
          superellipsoidTorusSeam Phi frame c R d := by
  rw [(F.regular i).mem_crossings_iff]
  refine and_congr_right fun _ ↦ ?_
  have houter : ((G.outer.circle i).windingLoop.curve t : R3) ∈
      superellipsoidOuterTorusSection Phi frame c R := by
    apply G.outer.circle_mem_section i
    exact ⟨Circle.exp t, (G.outer.circle i).parametrization t⟩
  simp only [windingLoopCutHeight, sub_eq_zero,
    superellipsoidTorusSeam, superellipsoidOuterTorusSection,
    coordinateCuttingPlane, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro ht
    exact ⟨⟨houter.1, houter.2⟩, ht⟩
  · exact fun ht ↦ ht.2

/-- Evaluation of canonical sorted parameters is exactly the geometric seam on one outer circle. -/
noncomputable def crossingEquivOuterCircleSeamVertex (i : outerIndex) :
    {t // t ∈ (F.regular i).crossings} ≃
      OuterCircleSeamVertex (G := G) i := by
  let eval : {t // t ∈ (F.regular i).crossings} →
      OuterCircleSeamVertex (G := G) i := fun t ↦
    ⟨(G.outer.circle i).windingLoop.curve t.1, by
      have ht := (F.mem_crossings_iff_curve_mem_seam i t.1).mp t.2
      exact ⟨⟨Circle.exp t.1, (G.outer.circle i).parametrization t.1⟩, ht.2⟩⟩
  apply Equiv.ofBijective eval
  constructor
  · intro s t hst
    apply Subtype.ext
    apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    · exact (F.regular i).crossings_subset_period s.2
    · exact (F.regular i).crossings_subset_period t.2
    · apply (G.outer.circle i).isEmbedding.injective
      change (G.outer.circle i).circle (Circle.exp s.1) =
        (G.outer.circle i).circle (Circle.exp t.1)
      rw [(G.outer.circle i).parametrization,
        (G.outer.circle i).parametrization]
      exact congrArg (fun z ↦ (z.1 : R3)) hst
  · intro x
    obtain ⟨z, hz⟩ := x.2.1
    let t := circlePhaseRepresentative z
    have htcurve : (G.outer.circle i).windingLoop.curve t = x.1 := by
      rw [← (G.outer.circle i).parametrization t,
        exp_circlePhaseRepresentative, hz]
    have htmem : t ∈ (F.regular i).crossings :=
      (F.mem_crossings_iff_curve_mem_seam i t).mpr
        ⟨circlePhaseRepresentative_mem z, htcurve.symm ▸ x.2.2⟩
    refine ⟨⟨t, htmem⟩, ?_⟩
    apply Subtype.ext
    exact htcurve

/-- Every seam point lies on a unique active outer circle. -/
noncomputable def activeOuterSeamVertexEquiv :
    (Σ i : F.ActiveOuterCircle, OuterCircleSeamVertex (G := G) i.1) ≃
      SuperellipsoidSeamVertex Phi frame c R d := by
  let eval :
      (Σ i : F.ActiveOuterCircle, OuterCircleSeamVertex (G := G) i.1) →
      SuperellipsoidSeamVertex Phi frame c R d := fun x ↦ ⟨x.2.1, x.2.2.2⟩
  apply Equiv.ofBijective eval
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : x.1 = y.1 := congrArg Subtype.val hxy
    have hij : i.1 = j.1 := by
      by_contra hne
      have hdisjoint := G.outer.pairwise_disjoint hne
      change Disjoint (Set.range (G.outer.circle i.1).circle)
        (Set.range (G.outer.circle j.1).circle) at hdisjoint
      rw [Set.disjoint_left] at hdisjoint
      exact hdisjoint x.2.1 (hval.symm ▸ y.2.1)
    have hijSubtype : i = j := Subtype.ext hij
    subst j
    have hxy' : x = y := Subtype.ext hval
    subst y
    rfl
  · intro x
    have hxOuter : x.1 ∈ superellipsoidOuterTorusSection Phi frame c R :=
      ⟨x.2.1.1, x.2.1.2⟩
    rw [G.outer.section_exact] at hxOuter
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxOuter
    have hiRange := hi
    obtain ⟨z, hz⟩ := hi
    let t := circlePhaseRepresentative z
    have htcurve : (G.outer.circle i).windingLoop.curve t = x.1 := by
      rw [← (G.outer.circle i).parametrization t,
        exp_circlePhaseRepresentative, hz]
    have htCross : t ∈ (F.regular i).crossings :=
      (F.mem_crossings_iff_curve_mem_seam i t).mpr
        ⟨circlePhaseRepresentative_mem z, htcurve.symm ▸ x.2⟩
    let ia : F.ActiveOuterCircle := ⟨i, ⟨t, htCross⟩⟩
    let y : OuterCircleSeamVertex (G := G) i := ⟨x.1, ⟨hiRange, x.2⟩⟩
    exact ⟨⟨ia, y⟩, by apply Subtype.ext; rfl⟩

/-- Canonical cyclic crossing indices enumerate every seam endpoint on an active outer circle. -/
noncomputable def cyclicCrossingEquiv (i : F.ActiveOuterCircle) :
    ZMod (F.regular i.1).crossings.card ≃
      OuterCircleSeamVertex (G := G) i.1 := by
  letI : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  exact (ZMod.finEquiv (F.regular i.1).crossings.card).symm.toEquiv.trans
    (((F.regular i.1).crossings.orderIsoOfFin rfl).toEquiv.trans
      (F.crossingEquivOuterCircleSeamVertex i.1))

end OuterCircleTransverseHeightCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
