import Mathlib

/-!
# A circle assembled from two embedded arcs

Two oppositely oriented injective paths which meet exactly at their common endpoints form an
embedded circle in any Hausdorff space.  This module is the target-independent form of the
two-arc construction used in the planar Schoenflies development.  In particular, it applies to
paths obtained by concatenating the alternating outer and cutting arcs of a finite degree-two
graph.

The final local-carrier theorem deliberately takes the desired local germ equality as a premise.
Finite incidence and embeddedness determine the global circle, but do not by themselves determine
the ambient germ of the analytic branches at a vertex.
-/

open Set Function Topology

noncomputable section

namespace Submission.Topology.TwoArcCircle

variable {X : Type*} [TopologicalSpace X]
variable {a b : X}

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- Traverse `p` on the first half of `[0,2]` and `q` on the second half. -/
def loop (p : Path a b) (q : Path b a) (t : ℝ) : X :=
  if t ≤ 1 then
    p (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
  else
    q (Set.projIcc (0 : ℝ) 1 (by norm_num) (t - 1))

theorem loop_eq_first (p : Path a b) (q : Path b a) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    loop p q t = p ⟨t, ht⟩ := by
  rw [loop, if_pos ht.2]
  rw [Set.projIcc_of_mem _ ht]

private lemma sub_one_mem_Icc_of_mem_Ioc {t : ℝ} (ht : t ∈ Ioc (1 : ℝ) 2) :
    t - 1 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · linarith [ht.1]
  · linarith [ht.2]

theorem loop_eq_second (p : Path a b) (q : Path b a) {t : ℝ}
    (ht : t ∈ Ioc (1 : ℝ) 2) :
    loop p q t = q ⟨t - 1, sub_one_mem_Icc_of_mem_Ioc ht⟩ := by
  rw [loop, if_neg (not_le.mpr ht.1)]
  rw [Set.projIcc_of_mem _ (sub_one_mem_Icc_of_mem_Ioc ht)]

@[simp]
theorem loop_zero (p : Path a b) (q : Path b a) : loop p q 0 = a := by
  rw [loop_eq_first p q (by norm_num)]
  exact p.source

@[simp]
theorem loop_one (p : Path a b) (q : Path b a) : loop p q 1 = b := by
  rw [loop_eq_first p q (by norm_num)]
  exact p.target

@[simp]
theorem loop_two (p : Path a b) (q : Path b a) : loop p q 2 = a := by
  rw [loop_eq_second p q (by norm_num)]
  convert q.target using 1
  norm_num

theorem continuous_loop (p : Path a b) (q : Path b a) : Continuous (loop p q) := by
  let f : ℝ → X := fun t ↦ p (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
  let g : ℝ → X := fun t ↦ q (Set.projIcc (0 : ℝ) 1 (by norm_num) (t - 1))
  change Continuous (fun t : ℝ ↦ if t ≤ 1 then f t else g t)
  apply continuous_if_le continuous_id continuous_const
  · fun_prop
  · fun_prop
  · intro t ht
    change t = 1 at ht
    subst t
    dsimp [f, g]
    convert p.target.trans q.source.symm using 1 <;> norm_num

/-- The two-path loop descended to the additive circle of circumference two. -/
def addCircleMap (p : Path a b) (q : Path b a) : AddCircle (2 : ℝ) → X :=
  AddCircle.liftIco 2 0 (loop p q)

theorem continuous_addCircleMap (p : Path a b) (q : Path b a) :
    Continuous (addCircleMap p q) := by
  apply AddCircle.liftIco_zero_continuous
  · exact (loop_zero p q).trans (loop_two p q).symm
  · exact (continuous_loop p q).continuousOn

/-- The half-open representative of an additive-circle point. -/
private def representative (z : AddCircle (2 : ℝ)) : Ico (0 : ℝ) ((0 : ℝ) + 2) :=
  AddCircle.equivIco 2 0 z

private theorem addCircleMap_eq_loop_representative
    (p : Path a b) (q : Path b a) (z : AddCircle (2 : ℝ)) :
    addCircleMap p q z = loop p q (representative z) := rfl

/-- The additive-circle coordinate of a point on the first path. -/
def firstCoordinate (t : unitInterval) : AddCircle (2 : ℝ) :=
  (AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm
    ⟨t, ⟨t.2.1, by norm_num; linarith [t.2.2]⟩⟩

theorem addCircleMap_firstCoordinate (p : Path a b) (q : Path b a)
    (t : unitInterval) :
    addCircleMap p q (firstCoordinate t) = p t := by
  rw [addCircleMap_eq_loop_representative]
  have hrep : representative (firstCoordinate t) =
      ⟨(t : ℝ), ⟨t.2.1, by norm_num; linarith [t.2.2]⟩⟩ := by
    simp [representative, firstCoordinate]
  rw [hrep]
  exact loop_eq_first p q t.2

/-- The additive-circle coordinate of a point on the second path. -/
def secondCoordinate (t : unitInterval) : AddCircle (2 : ℝ) :=
  ((t : ℝ) + 1 : ℝ)

theorem addCircleMap_secondCoordinate (p : Path a b) (q : Path b a)
    (t : unitInterval) :
    addCircleMap p q (secondCoordinate t) = q t := by
  by_cases ht : t = 1
  · subst t
    have hcoord : secondCoordinate (1 : unitInterval) = 0 := by
      norm_num [secondCoordinate]
    rw [hcoord]
    rw [addCircleMap, show (0 : AddCircle (2 : ℝ)) =
      ((0 : ℝ) : AddCircle (2 : ℝ)) by rfl,
      AddCircle.liftIco_coe_apply (p := (2 : ℝ)) (a := (0 : ℝ))
        (x := (0 : ℝ)) (by norm_num),
      loop_zero, q.target]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (by
      intro h
      exact ht (Subtype.ext h))
    by_cases ht0 : t = 0
    · subst t
      have hcoord0 : secondCoordinate (0 : unitInterval) =
          ((1 : ℝ) : AddCircle (2 : ℝ)) := by
        norm_num [secondCoordinate]
      rw [hcoord0, addCircleMap,
        AddCircle.liftIco_coe_apply (p := (2 : ℝ)) (a := (0 : ℝ))
          (x := (1 : ℝ)) (by norm_num),
        loop_one, q.source]
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (by
      intro h
      exact ht0 (Subtype.ext h.symm))
    have hmem : (t : ℝ) + 1 ∈ Set.Ico (0 : ℝ) (0 + 2) := by
      constructor <;> linarith [t.2.1]
    rw [addCircleMap, secondCoordinate, AddCircle.liftIco_coe_apply hmem]
    have hloop := loop_eq_second p q (t := (t : ℝ) + 1)
      ⟨by linarith [htpos], by linarith [htlt]⟩
    rw [hloop]
    congr 1
    apply Subtype.ext
    simp

theorem addCircleMap_injective (p : Path a b) (q : Path b a)
    (hp : Injective p) (hq : Injective q)
    (hinter : range p ∩ range q = {a, b}) :
    Injective (addCircleMap p q) := by
  intro z w hzw
  let s := representative z
  let t := representative w
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs2 : (s : ℝ) < 2 := by simpa using s.2.2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht2 : (t : ℝ) < 2 := by simpa using t.2.2
  have hloop : loop p q s = loop p q t := by
    simpa only [addCircleMap_eq_loop_representative] using hzw
  have hcross (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Ioo (1 : ℝ) 2) :
      p ⟨u, hu⟩ ≠ q ⟨v - 1, ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩ := by
    intro heq
    let up : unitInterval := ⟨u, hu⟩
    let vq : unitInterval := ⟨v - 1, by constructor <;> linarith [hv.1, hv.2]⟩
    have hcommon : p up ∈ range p ∩ range q :=
      ⟨⟨up, rfl⟩, ⟨vq, heq.symm⟩⟩
    rw [hinter] at hcommon
    simp only [mem_insert_iff, mem_singleton_iff] at hcommon
    rcases hcommon with haValue | hbValue
    · have hup0 : up = 0 := hp (haValue.trans p.source.symm)
      have hvq1 : vq = 1 := hq (heq.symm.trans (haValue.trans q.target.symm))
      have hu0 := congrArg Subtype.val hup0
      have hv1 := congrArg Subtype.val hvq1
      dsimp [up, vq] at hu0 hv1
      linarith [hv.2]
    · have hup1 : up = 1 := hp (hbValue.trans p.target.symm)
      have hvq0 : vq = 0 := hq (heq.symm.trans (hbValue.trans q.source.symm))
      have hu1 := congrArg Subtype.val hup1
      have hv0 := congrArg Subtype.val hvq0
      dsimp [up, vq] at hu1 hv0
      linarith [hv.1]
  have hst : (s : ℝ) = (t : ℝ) := by
    by_cases hs1 : (s : ℝ) ≤ 1
    · have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
      rw [loop_eq_first p q hsI] at hloop
      by_cases ht1 : (t : ℝ) ≤ 1
      · have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
        rw [loop_eq_first p q htI] at hloop
        have heqI : (⟨(s : ℝ), hsI⟩ : unitInterval) = ⟨(t : ℝ), htI⟩ := hp hloop
        exact congrArg (fun u : unitInterval ↦ (u : ℝ)) heqI
      · have htI : (t : ℝ) ∈ Ioc (1 : ℝ) 2 :=
          ⟨lt_of_not_ge ht1, ht2.le⟩
        rw [loop_eq_second p q htI] at hloop
        exact False.elim (hcross s t hsI ⟨lt_of_not_ge ht1, ht2⟩ hloop)
    · have hsI : (s : ℝ) ∈ Ioc (1 : ℝ) 2 := ⟨lt_of_not_ge hs1, hs2.le⟩
      rw [loop_eq_second p q hsI] at hloop
      by_cases ht1 : (t : ℝ) ≤ 1
      · have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
        rw [loop_eq_first p q htI] at hloop
        exact False.elim (hcross t s htI ⟨lt_of_not_ge hs1, hs2⟩ hloop.symm)
      · have htI : (t : ℝ) ∈ Ioc (1 : ℝ) 2 := ⟨lt_of_not_ge ht1, ht2.le⟩
        rw [loop_eq_second p q htI] at hloop
        have heq : (s : ℝ) - 1 = (t : ℝ) - 1 :=
          congrArg (fun u : unitInterval ↦ (u : ℝ)) (hq hloop)
        linarith
  apply (AddCircle.equivIco (2 : ℝ) (0 : ℝ)).injective
  apply Subtype.ext
  simpa [s, t, representative] using hst

theorem range_addCircleMap (p : Path a b) (q : Path b a) :
    range (addCircleMap p q) = range p ∪ range q := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let s := representative z
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs2 : (s : ℝ) < 2 := by simpa using s.2.2
    rw [addCircleMap_eq_loop_representative]
    by_cases hs1 : (s : ℝ) ≤ 1
    · left
      have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
      rw [loop_eq_first p q hsI]
      exact ⟨⟨(s : ℝ), hsI⟩, rfl⟩
    · right
      have hsI : (s : ℝ) ∈ Ioc (1 : ℝ) 2 := ⟨lt_of_not_ge hs1, hs2.le⟩
      rw [loop_eq_second p q hsI]
      exact ⟨⟨(s : ℝ) - 1, ⟨by linarith [hsI.1], by linarith [hsI.2]⟩⟩, rfl⟩
  · rintro (hx | hx)
    · rcases hx with ⟨u, rfl⟩
      let v : Ico (0 : ℝ) ((0 : ℝ) + 2) :=
        ⟨(u : ℝ), ⟨u.2.1, by norm_num; linarith [u.2.2]⟩⟩
      let z : AddCircle (2 : ℝ) := (AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm v
      refine ⟨z, ?_⟩
      rw [addCircleMap_eq_loop_representative]
      have hz : representative z = v := by simp [z, representative, v]
      rw [hz]
      exact loop_eq_first p q u.2
    · rcases hx with ⟨u, rfl⟩
      by_cases hu0 : (u : ℝ) = 0
      · refine ⟨(AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm ⟨(1 : ℝ), by norm_num⟩, ?_⟩
        rw [addCircleMap_eq_loop_representative]
        have hz : representative
            ((AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm ⟨(1 : ℝ), by norm_num⟩) =
            ⟨(1 : ℝ), by norm_num⟩ := by
          simp [representative]
        rw [hz, loop_eq_first p q (by norm_num)]
        rw [show u = 0 from Subtype.ext hu0]
        exact p.target.trans q.source.symm
      · by_cases hu1 : (u : ℝ) = 1
        · refine ⟨(AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm
              ⟨(0 : ℝ), by norm_num⟩, ?_⟩
          rw [addCircleMap_eq_loop_representative]
          have hz : representative
              ((AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm ⟨(0 : ℝ), by norm_num⟩) =
              ⟨(0 : ℝ), by norm_num⟩ := by
            simp [representative]
          rw [hz, loop_eq_first p q (by norm_num)]
          rw [show u = 1 from Subtype.ext hu1]
          exact p.source.trans q.target.symm
        · have hu0' : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
          have hu1' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu1
          let v : Ico (0 : ℝ) ((0 : ℝ) + 2) :=
            ⟨(u : ℝ) + 1, by constructor <;> norm_num <;> linarith⟩
          let z : AddCircle (2 : ℝ) :=
            (AddCircle.equivIco (2 : ℝ) (0 : ℝ)).symm v
          refine ⟨z, ?_⟩
          rw [addCircleMap_eq_loop_representative]
          have hz : representative z = v := by simp [z, representative, v]
          rw [hz]
          have hvI : (v : ℝ) ∈ Ioc (1 : ℝ) 2 := by
            dsimp [v]
            constructor <;> linarith
          rw [loop_eq_second p q hvI]
          apply congrArg q
          apply Subtype.ext
          dsimp [v]
          linarith

/-- The standard identification of the additive circle of circumference two with `Circle`. -/
def circleHomeomorph : AddCircle (2 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle (by norm_num)

/-- Parametrize the union of the two paths by the standard circle. -/
def circleMap (p : Path a b) (q : Path b a) : Circle → X :=
  addCircleMap p q ∘ circleHomeomorph.symm

theorem continuous_circleMap (p : Path a b) (q : Path b a) :
    Continuous (circleMap p q) :=
  (continuous_addCircleMap p q).comp circleHomeomorph.symm.continuous

theorem range_circleMap (p : Path a b) (q : Path b a) :
    range (circleMap p q) = range p ∪ range q := by
  rw [circleMap, Set.range_comp]
  rw [circleHomeomorph.symm.surjective.range_eq, image_univ]
  exact range_addCircleMap p q

theorem circleMap_injective (p : Path a b) (q : Path b a)
    (hp : Injective p) (hq : Injective q)
    (hinter : range p ∩ range q = {a, b}) :
    Injective (circleMap p q) :=
  (addCircleMap_injective p q hp hq hinter).comp circleHomeomorph.symm.injective

/-- In a Hausdorff target, the resulting injective circle map is an embedding. -/
theorem circleMap_isEmbedding [T2Space X] (p : Path a b) (q : Path b a)
    (hp : Injective p) (hq : Injective q)
    (hinter : range p ∩ range q = {a, b}) :
    IsEmbedding (circleMap p q) :=
  ((continuous_circleMap p q).isClosedEmbedding
    (circleMap_injective p q hp hq hinter)).isEmbedding

/-- Any independently proved local germ equality transfers verbatim to the glued circle. -/
theorem range_circleMap_inter_eq (p : Path a b) (q : Path b a)
    (U germ : Set X) (hlocal : (range p ∪ range q) ∩ U = germ ∩ U) :
    range (circleMap p q) ∩ U = germ ∩ U := by
  rw [range_circleMap, hlocal]

/-- Bundle the global gluing hypotheses which finite alternating-path concatenation must provide. -/
structure Data (p : Path a b) (q : Path b a) : Prop where
  first_injective : Injective p
  second_injective : Injective q
  range_inter : range p ∩ range q = {a, b}

namespace Data

variable {p : Path a b} {q : Path b a}

theorem injective (D : Data p q) : Injective (circleMap p q) :=
  circleMap_injective p q D.first_injective D.second_injective D.range_inter

variable [T2Space X]

theorem isEmbedding (D : Data p q) : IsEmbedding (circleMap p q) :=
  circleMap_isEmbedding p q D.first_injective D.second_injective D.range_inter

end Data

end Submission.Topology.TwoArcCircle
