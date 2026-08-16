import Submission.Topology.FiniteAlternatingArcCycleDecomposition
import Submission.Topology.SuperellipsoidOuterCircleCyclicOrder

/-!
# Alternating outer/cut cycles for truncated superellipsoid sections

At every seam vertex there is exactly one selected outer half-gap and exactly one inward cut
gap.  Their endpoint equivalences therefore form a finite graph of degree two.  This file derives
the lower and upper cycle indices from the successor permutations of that graph.  In particular,
the component circles used below are not independently enumerated.

The final structure isolates the remaining purely topological realization theorem: concatenate
the finitely many embedded arcs in one derived graph cycle to a parametrized circle.  Its carrier
is prescribed exactly, so it cannot hide extra branches or omit an arc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph

universe idx

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type idx} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace OuterCircleTransverseHeightCyclicOrderFamily

variable (F : OuterCircleTransverseHeightCyclicOrderFamily G)

/-- The two endpoint labels as parameters of the closed unit interval. -/
def finTwoUnitInterval (e : Fin 2) : unitInterval :=
  ⟨e.1, by
    constructor
    · exact Nat.cast_nonneg e.1
    · exact_mod_cast Nat.le_of_lt_succ e.2⟩

@[simp] theorem finTwoUnitInterval_zero : finTwoUnitInterval 0 = 0 := by
  apply Subtype.ext
  norm_num [finTwoUnitInterval]

@[simp] theorem finTwoUnitInterval_one : finTwoUnitInterval 1 = 1 := by
  apply Subtype.ext
  norm_num [finTwoUnitInterval]

private theorem val_finEquiv_symm {n : ℕ} [NeZero n] (q : ZMod n) :
    ((ZMod.finEquiv n).symm q).val = q.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- Lower outer gaps as alternating cyclic side data on one active outer circle. -/
noncomputable def lowerSideData (i : F.ActiveOuterCircle) :
    AlternatingCyclicSideData (F.regular i.1).crossings.card where
  neZero := ⟨(Finset.card_pos.mpr i.2).ne'⟩
  side := F.zmodGapSide i
  changes := F.zmodGapSide_add_one_ne i

/-- Upper outer gaps are the complementary alternating side data. -/
noncomputable def upperSideData (i : F.ActiveOuterCircle) :
    AlternatingCyclicSideData (F.regular i.1).crossings.card where
  neZero := ⟨(Finset.card_pos.mpr i.2).ne'⟩
  side := fun q ↦ !(F.zmodGapSide i q)
  changes := by
    intro q h
    have hchange := F.zmodGapSide_add_one_ne i q
    cases hleft : F.zmodGapSide i (q + 1) <;>
      cases hright : F.zmodGapSide i q <;> simp_all

/-- Selected lower outer half-gaps, retaining their active-circle index. -/
def GlobalLowerOuterGap :=
  Σ i : F.ActiveOuterCircle, (F.lowerSideData i).InwardGap

/-- Selected upper outer half-gaps, retaining their active-circle index. -/
def GlobalUpperOuterGap :=
  Σ i : F.ActiveOuterCircle, (F.upperSideData i).InwardGap

noncomputable instance globalLowerOuterGapFintype : Fintype F.GlobalLowerOuterGap := by
  classical
  exact Sigma.instFintype

noncomputable instance globalUpperOuterGapFintype : Fintype F.GlobalUpperOuterGap := by
  classical
  exact Sigma.instFintype

/-- Product distributes over the dependent family of lower outer gaps. -/
def globalLowerEndpointDistrib :
    F.GlobalLowerOuterGap × Fin 2 ≃
      Σ i : F.ActiveOuterCircle, (F.lowerSideData i).InwardGap × Fin 2 where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun p := (⟨p.1, p.2.1⟩, p.2.2)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Product distributes over the dependent family of upper outer gaps. -/
def globalUpperEndpointDistrib :
    F.GlobalUpperOuterGap × Fin 2 ≃
      Σ i : F.ActiveOuterCircle, (F.upperSideData i).InwardGap × Fin 2 where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun p := (⟨p.1, p.2.1⟩, p.2.2)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The two endpoints of all selected lower outer gaps enumerate the seam exactly. -/
noncomputable def globalLowerEndpointEquiv :
    F.GlobalLowerOuterGap × Fin 2 ≃
      SuperellipsoidSeamVertex Phi frame c R d :=
  (F.globalLowerEndpointDistrib.trans
      (Equiv.sigmaCongrRight fun i ↦ (F.lowerSideData i).endpointEquiv) |>.trans
    (Equiv.sigmaCongrRight fun i ↦ F.cyclicCrossingEquiv i)).trans
      F.activeOuterSeamVertexEquiv

/-- The two endpoints of all selected upper outer gaps enumerate the seam exactly. -/
noncomputable def globalUpperEndpointEquiv :
    F.GlobalUpperOuterGap × Fin 2 ≃
      SuperellipsoidSeamVertex Phi frame c R d :=
  (F.globalUpperEndpointDistrib.trans
      (Equiv.sigmaCongrRight fun i ↦ (F.upperSideData i).endpointEquiv) |>.trans
    (Equiv.sigmaCongrRight fun i ↦ F.cyclicCrossingEquiv i)).trans
      F.activeOuterSeamVertexEquiv

/-- Evaluation of the outer cyclic crossing equivalence at its canonical representative. -/
theorem cyclicCrossingEquiv_val (i : F.ActiveOuterCircle)
    (q : ZMod (F.regular i.1).crossings.card) :
    (F.cyclicCrossingEquiv i q).1 =
      ((G.outer.circle i.1).windingLoop.curve
        (sortedCrossing (F.regular i.1)
          ⟨q.val, by
            let _ : NeZero (F.regular i.1).crossings.card :=
              ⟨(Finset.card_pos.mpr i.2).ne'⟩
            exact ZMod.val_lt q⟩) : R3) := by
  let _ : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  change ((G.outer.circle i.1).windingLoop.curve
      (((F.regular i.1).crossings.orderIsoOfFin rfl).toEquiv
        ((ZMod.finEquiv (F.regular i.1).crossings.card).symm.toEquiv q)).1 : R3) = _
  congr 2
  let k := (ZMod.finEquiv (F.regular i.1).crossings.card).symm q
  calc
    ↑(((F.regular i.1).crossings.orderIsoOfFin rfl).toEquiv
        ((ZMod.finEquiv (F.regular i.1).crossings.card).symm.toEquiv q)) =
        ↑((F.regular i.1).crossings.orderIsoOfFin rfl k) := rfl
    _ = (F.regular i.1).crossings.orderEmbOfFin rfl k :=
      Finset.coe_orderIsoOfFin_apply _ _ _
    _ = (F.regular i.1).crossings.orderEmbOfFin rfl
        ⟨q.val, ZMod.val_lt q⟩ := by
      apply congrArg
      apply Fin.ext
      exact val_finEquiv_symm q
    _ = sortedCrossing (F.regular i.1) ⟨q.val, ZMod.val_lt q⟩ := rfl

/-- The underlying canonical outer gap of a lower selected gap. -/
noncomputable def lowerGapAsGlobalOuterGap (g : F.GlobalLowerOuterGap) : F.GlobalOuterGap := by
  let _ := (F.lowerSideData g.1).neZero
  exact ⟨g.1, ⟨g.2.1.val, ZMod.val_lt g.2.1⟩⟩

/-- The underlying canonical outer gap of an upper selected gap. -/
noncomputable def upperGapAsGlobalOuterGap (g : F.GlobalUpperOuterGap) : F.GlobalOuterGap := by
  let _ := (F.upperSideData g.1).neZero
  exact ⟨g.1, ⟨g.2.1.val, ZMod.val_lt g.2.1⟩⟩

/-- The selected lower gap really is one of the lower gaps of the smooth outer family. -/
noncomputable def lowerGapAsLowerGap (g : F.GlobalLowerOuterGap) : F.LowerGap := by
  let _ := (F.lowerSideData g.1).neZero
  refine ⟨F.lowerGapAsGlobalOuterGap g, ?_⟩
  have hside := g.2.2
  change F.zmodGapSide g.1 g.2.1 = false at hside
  exact hside

/-- The selected upper gap really is one of the upper gaps of the smooth outer family. -/
noncomputable def upperGapAsUpperGap (g : F.GlobalUpperOuterGap) : F.UpperGap := by
  let _ := (F.upperSideData g.1).neZero
  refine ⟨F.upperGapAsGlobalOuterGap g, ?_⟩
  have hnot := g.2.2
  change (!(F.zmodGapSide g.1 g.2.1)) = false at hnot
  have hside : F.zmodGapSide g.1 g.2.1 = true := by
    cases hz : F.zmodGapSide g.1 g.2.1 <;> simp_all
  exact hside

/-- Actual closed outer arc represented by a selected lower gap. -/
noncomputable def globalLowerOuterPath (g : F.GlobalLowerOuterGap) :=
  F.gapPath (F.lowerGapAsGlobalOuterGap g)

/-- Actual closed outer arc represented by a selected upper gap. -/
noncomputable def globalUpperOuterPath (g : F.GlobalUpperOuterGap) :=
  F.gapPath (F.upperGapAsGlobalOuterGap g)

@[simp]
theorem globalLowerEndpointEquiv_zero_val (g : F.GlobalLowerOuterGap) :
    (F.globalLowerEndpointEquiv (g, (0 : Fin 2))).1 =
      ((F.globalLowerOuterPath g (0 : unitInterval) : transportedTorus Phi) : R3) := by
  let _ := (F.lowerSideData g.1).neZero
  change (F.cyclicCrossingEquiv g.1 g.2.1).1 = _
  rw [F.cyclicCrossingEquiv_val]
  exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
    (Path.source (F.globalLowerOuterPath g)).symm

@[simp]
theorem globalUpperEndpointEquiv_zero_val (g : F.GlobalUpperOuterGap) :
    (F.globalUpperEndpointEquiv (g, (0 : Fin 2))).1 =
      ((F.globalUpperOuterPath g (0 : unitInterval) : transportedTorus Phi) : R3) := by
  let _ := (F.upperSideData g.1).neZero
  change (F.cyclicCrossingEquiv g.1 g.2.1).1 = _
  rw [F.cyclicCrossingEquiv_val]
  exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
    (Path.source (F.globalUpperOuterPath g)).symm

/-- The cyclic successor crossing is the terminal endpoint of the represented outer gap. -/
theorem cyclicCrossingEquiv_add_one_val
    (i : F.ActiveOuterCircle)
    (qz : ZMod (F.regular i.1).crossings.card) :
    (F.cyclicCrossingEquiv i (qz + 1)).1 =
      ((G.outer.circle i.1).windingLoop.curve
        (cyclicRight (F.regular i.1)
          ⟨qz.val, by
            let _ : NeZero (F.regular i.1).crossings.card :=
              ⟨(Finset.card_pos.mpr i.2).ne'⟩
            exact ZMod.val_lt qz⟩) : R3) := by
  let _ : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  rw [F.cyclicCrossingEquiv_val]
  let n := (F.regular i.1).crossings.card
  let q : Fin n := ⟨qz.val, ZMod.val_lt qz⟩
  have hnextVal : (qz + 1).val = (qz.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    nth_rewrite 1 [← Nat.mod_eq_of_lt (ZMod.val_lt qz)]
    exact (Nat.add_mod qz.val 1 n).symm
  by_cases hnext : q.1 + 1 < n
  · have hval : (qz + 1).val = q.1 + 1 := by
      rw [hnextVal]
      exact Nat.mod_eq_of_lt hnext
    rw [show (⟨(qz + 1).val, ZMod.val_lt (qz + 1)⟩ : Fin n) =
        ⟨q.1 + 1, hnext⟩ by ext; exact hval]
    change
      (((G.outer.circle i.1).windingLoop.curve
        (sortedCrossing (F.regular i.1) ⟨q.1 + 1, hnext⟩) :
          transportedTorus Phi) : R3) =
        (((G.outer.circle i.1).windingLoop.curve
          (cyclicRight (F.regular i.1) q) : transportedTorus Phi) : R3)
    rw [cyclicRight, dif_pos hnext]
  · have hlast : q.1 + 1 = n := by omega
    have hval : (qz + 1).val = 0 := by
      rw [hnextVal, show qz.val + 1 = n by simpa only [q] using hlast,
        Nat.mod_self]
    rw [show (⟨(qz + 1).val, ZMod.val_lt (qz + 1)⟩ : Fin n) =
        ⟨0, Finset.card_pos.mpr i.2⟩ by ext; exact hval]
    change
      (((G.outer.circle i.1).windingLoop.curve
        (sortedCrossing (F.regular i.1) ⟨0, Finset.card_pos.mpr i.2⟩) :
          transportedTorus Phi) : R3) =
        (((G.outer.circle i.1).windingLoop.curve
          (cyclicRight (F.regular i.1) q) : transportedTorus Phi) : R3)
    rw [cyclicRight, dif_neg hnext]
    exact congrArg Subtype.val <|
      ((G.outer.circle i.1).windingLoop.periodic_curve
        (sortedCrossing (F.regular i.1)
          ⟨0, Finset.card_pos.mpr i.2⟩)).symm

@[simp]
theorem globalLowerEndpointEquiv_one_val (g : F.GlobalLowerOuterGap) :
    (F.globalLowerEndpointEquiv (g, (1 : Fin 2))).1 =
      ((F.globalLowerOuterPath g (1 : unitInterval) : transportedTorus Phi) : R3) := by
  let _ := (F.lowerSideData g.1).neZero
  change (F.cyclicCrossingEquiv g.1 (g.2.1 + 1)).1 = _
  rw [F.cyclicCrossingEquiv_add_one_val]
  exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
    (Path.target (F.globalLowerOuterPath g)).symm

@[simp]
theorem globalUpperEndpointEquiv_one_val (g : F.GlobalUpperOuterGap) :
    (F.globalUpperEndpointEquiv (g, (1 : Fin 2))).1 =
      ((F.globalUpperOuterPath g (1 : unitInterval) : transportedTorus Phi) : R3) := by
  let _ := (F.upperSideData g.1).neZero
  change (F.cyclicCrossingEquiv g.1 (g.2.1 + 1)).1 = _
  rw [F.cyclicCrossingEquiv_add_one_val]
  exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
    (Path.target (F.globalUpperOuterPath g)).symm

/-- The derived lower endpoint equivalence is geometrically the endpoint map of its outer arcs. -/
theorem globalLowerEndpointEquiv_val_eq_path_endpoint
    (g : F.GlobalLowerOuterGap) (e : Fin 2) :
    (F.globalLowerEndpointEquiv (g, e)).1 =
      ((F.globalLowerOuterPath g (finTwoUnitInterval e) : transportedTorus Phi) : R3) := by
  fin_cases e <;> simp

/-- The derived upper endpoint equivalence is geometrically the endpoint map of its outer arcs. -/
theorem globalUpperEndpointEquiv_val_eq_path_endpoint
    (g : F.GlobalUpperOuterGap) (e : Fin 2) :
    (F.globalUpperEndpointEquiv (g, e)).1 =
      ((F.globalUpperOuterPath g (finTwoUnitInterval e) : transportedTorus Phi) : R3) := by
  fin_cases e <;> simp

end OuterCircleTransverseHeightCyclicOrderFamily

/-! ## Seam-free whole-circle components -/

namespace OuterCircleTransverseHeightCyclicOrderFamily

variable (F : OuterCircleTransverseHeightCyclicOrderFamily G)

/-- Outer circles not incident to the seam graph. -/
def InactiveOuterCircle :=
  {i : outerIndex // ¬(F.regular i).crossings.Nonempty}

noncomputable instance inactiveOuterCircleFintype : Fintype F.InactiveOuterCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- An inactive outer circle has no zero of the cutting height, even outside the chosen period. -/
theorem inactiveOuter_height_ne_zero (i : F.InactiveOuterCircle) (t : ℝ) :
    windingLoopCutHeight frame d (G.outer.circle i.1).windingLoop t ≠ 0 := by
  change {i : outerIndex // ¬(F.regular i).crossings.Nonempty} at i
  intro ht
  let s := circlePhaseRepresentative (Circle.exp t)
  have hsPeriod : s ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    circlePhaseRepresentative_mem (Circle.exp t)
  have hcurve : ((G.outer.circle i.1).windingLoop.curve s : R3) =
      ((G.outer.circle i.1).windingLoop.curve t : R3) := by
    rw [← (G.outer.circle i.1).parametrization s,
      ← (G.outer.circle i.1).parametrization t,
      exp_circlePhaseRepresentative]
  have hsZero : windingLoopCutHeight frame d
      (G.outer.circle i.1).windingLoop s = 0 := by
    simpa only [windingLoopCutHeight, hcurve] using ht
  have hsCross : s ∈ (F.regular i.1).crossings :=
    ((F.regular i.1).mem_crossings_iff s).mpr ⟨hsPeriod, hsZero⟩
  exact i.2 ⟨s, hsCross⟩

/-- A seam-free outer circle has one strict cutting-height sign on its whole parametrization. -/
theorem inactiveOuter_all_lower_or_all_upper (i : F.InactiveOuterCircle) :
    (∀ t, windingLoopCutHeight frame d
        (G.outer.circle i.1).windingLoop t < 0) ∨
      (∀ t, 0 < windingLoopCutHeight frame d
        (G.outer.circle i.1).windingLoop t) := by
  let h := windingLoopCutHeight frame d (G.outer.circle i.1).windingLoop
  have hcontinuous : Continuous h := (F.regular i.1).contDiff_height.continuous
  rcases lt_or_gt_of_ne (F.inactiveOuter_height_ne_zero i 0) with hneg | hpos
  · left
    intro t
    by_contra hnot
    have ht : 0 ≤ h t := le_of_not_gt hnot
    obtain ⟨u, hu⟩ := intermediate_value_univ (0 : ℝ) t hcontinuous
      ⟨hneg.le, ht⟩
    exact F.inactiveOuter_height_ne_zero i u hu
  · right
    intro t
    by_contra hnot
    have ht : h t ≤ 0 := le_of_not_gt hnot
    obtain ⟨u, hu⟩ := intermediate_value_univ t (0 : ℝ) hcontinuous
      ⟨ht, hpos.le⟩
    exact F.inactiveOuter_height_ne_zero i u hu

/-- Seam-free outer circles belonging wholly to the lower child. -/
def LowerWholeOuterCircle :=
  {i : F.InactiveOuterCircle //
    windingLoopCutHeight frame d (G.outer.circle i.1).windingLoop 0 < 0}

/-- Seam-free outer circles belonging wholly to the upper child. -/
def UpperWholeOuterCircle :=
  {i : F.InactiveOuterCircle //
    0 < windingLoopCutHeight frame d (G.outer.circle i.1).windingLoop 0}

noncomputable instance lowerWholeOuterCircleFintype :
    Fintype F.LowerWholeOuterCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance upperWholeOuterCircleFintype :
    Fintype F.UpperWholeOuterCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

theorem lowerWholeOuterCircle_all_lower (i : F.LowerWholeOuterCircle) (t : ℝ) :
    windingLoopCutHeight frame d (G.outer.circle i.1.1).windingLoop t < 0 := by
  rcases F.inactiveOuter_all_lower_or_all_upper i.1 with hlower | hupper
  · exact hlower t
  · exact False.elim (not_lt_of_ge (hupper 0).le i.2)

theorem upperWholeOuterCircle_all_upper (i : F.UpperWholeOuterCircle) (t : ℝ) :
    0 < windingLoopCutHeight frame d (G.outer.circle i.1.1).windingLoop t := by
  rcases F.inactiveOuter_all_lower_or_all_upper i.1 with hlower | hupper
  · exact False.elim (not_lt_of_ge (hlower 0).le i.2)
  · exact hupper t

/-- Every seam-free outer circle belongs to exactly one child. -/
theorem inactiveOuter_eq_lower_or_upper (i : F.InactiveOuterCircle) :
    (∃ k : F.LowerWholeOuterCircle, k.1 = i) ∨
      (∃ k : F.UpperWholeOuterCircle, k.1 = i) := by
  rcases F.inactiveOuter_all_lower_or_all_upper i with hlower | hupper
  · exact Or.inl ⟨⟨i, hlower 0⟩, rfl⟩
  · exact Or.inr ⟨⟨i, hupper 0⟩, rfl⟩

end OuterCircleTransverseHeightCyclicOrderFamily

/-- Cutting circles not incident to the seam graph. -/
def InactiveCutCircle
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :=
  {j : cutIndex // ¬(G.cutCircleSeamCrossings j).Nonempty}

noncomputable instance inactiveCutCircleFintype : Fintype G.InactiveCutCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- An inactive cut circle has no zero of the outer polynomial difference. -/
theorem inactiveCut_difference_ne_zero (hR : 0 ≤ R)
    (j : G.InactiveCutCircle) (t : ℝ) :
    G.cutCircleOuterPolynomialDifference j.1 t ≠ 0 := by
  change {j : cutIndex // ¬(G.cutCircleSeamCrossings j).Nonempty} at j
  intro ht
  have htSeam :=
    (G.cutCircleOuterPolynomialDifference_eq_zero_iff_seam j.1 hR t).mp ht
  let s := circlePhaseRepresentative (Circle.exp t)
  have hsPeriod : s ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    circlePhaseRepresentative_mem (Circle.exp t)
  have hcurve : ((G.cut.circle j.1).windingLoop.curve s : R3) =
      ((G.cut.circle j.1).windingLoop.curve t : R3) := by
    rw [← (G.cut.circle j.1).parametrization s,
      ← (G.cut.circle j.1).parametrization t,
      exp_circlePhaseRepresentative]
  have hsSeam : ((G.cut.circle j.1).windingLoop.curve s : R3) ∈
      superellipsoidTorusSeam Phi frame c R d := by
    simpa only [hcurve] using htSeam
  have hsCross : s ∈ G.cutCircleSeamCrossings j.1 :=
    (G.mem_cutCircleSeamCrossings_iff j.1 s).mpr ⟨hsPeriod, hsSeam⟩
  exact j.2 ⟨s, hsCross⟩

/-- A seam-free cut circle has one strict outer-polynomial sign. -/
theorem inactiveCut_all_inward_or_all_outward (hR : 0 ≤ R)
    (j : G.InactiveCutCircle) :
    (∀ t, G.cutCircleOuterPolynomialDifference j.1 t < 0) ∨
      (∀ t, 0 < G.cutCircleOuterPolynomialDifference j.1 t) := by
  let h := G.cutCircleOuterPolynomialDifference j.1
  have hcontinuous : Continuous h := G.continuous_cutCircleOuterPolynomialDifference j.1
  rcases lt_or_gt_of_ne (inactiveCut_difference_ne_zero hR j 0) with hneg | hpos
  · left
    intro t
    by_contra hnot
    have ht : 0 ≤ h t := le_of_not_gt hnot
    obtain ⟨u, hu⟩ := intermediate_value_univ (0 : ℝ) t hcontinuous
      ⟨hneg.le, ht⟩
    exact inactiveCut_difference_ne_zero hR j u hu
  · right
    intro t
    by_contra hnot
    have ht : h t ≤ 0 := le_of_not_gt hnot
    obtain ⟨u, hu⟩ := intermediate_value_univ t (0 : ℝ) hcontinuous
      ⟨ht, hpos.le⟩
    exact inactiveCut_difference_ne_zero hR j u hu

/-- Seam-free cutting circles lying wholly in the open superellipsoid body. -/
def InwardWholeCutCircle
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :=
  {j : G.InactiveCutCircle // G.cutCircleOuterPolynomialDifference j.1 0 < 0}

noncomputable instance inwardWholeCutCircleFintype :
    Fintype G.InwardWholeCutCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

theorem inwardWholeCutCircle_all_inward (hR : 0 ≤ R)
    (j : G.InwardWholeCutCircle) (t : ℝ) :
    G.cutCircleOuterPolynomialDifference j.1.1 t < 0 := by
  rcases inactiveCut_all_inward_or_all_outward hR j.1 with hin | hout
  · exact hin t
  · exact False.elim (not_lt_of_ge (hout 0).le j.2)

namespace TruncatedSphereAlternatingCycles

variable
  (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
  (cutOrder : CutCircleTransverseCyclicOrderFamily G)

variable [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

/-- The lower selected outer arcs form the first perfect seam pairing. -/
noncomputable def lowerOuterPairing
    (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G) :
    FiniteEndpointPairing (SuperellipsoidSeamVertex Phi frame c R d) where
  edge := outerOrder.GlobalLowerOuterGap
  finite_edge := inferInstance
  endpointEquiv := outerOrder.globalLowerEndpointEquiv

/-- The upper selected outer arcs form the first perfect seam pairing. -/
noncomputable def upperOuterPairing
    (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G) :
    FiniteEndpointPairing (SuperellipsoidSeamVertex Phi frame c R d) where
  edge := outerOrder.GlobalUpperOuterGap
  finite_edge := inferInstance
  endpointEquiv := outerOrder.globalUpperEndpointEquiv

/-- The inward cut arcs form the second perfect seam pairing. -/
noncomputable def inwardCutPairing
    (cutOrder : CutCircleTransverseCyclicOrderFamily G) :
    FiniteEndpointPairing (SuperellipsoidSeamVertex Phi frame c R d) where
  edge := cutOrder.GlobalInwardGap
  finite_edge := inferInstance
  endpointEquiv := cutOrder.globalEndpointEquiv

/-- Finite alternating graph whose cycles are the active lower truncated-section components. -/
noncomputable def lowerSystem
    (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
    (cutOrder : CutCircleTransverseCyclicOrderFamily G) :
    FiniteAlternatingEndpointSystem
      (SuperellipsoidSeamVertex Phi frame c R d) where
  first := lowerOuterPairing outerOrder
  second := inwardCutPairing cutOrder

/-- Finite alternating graph whose cycles are the active upper truncated-section components. -/
noncomputable def upperSystem
    (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
    (cutOrder : CutCircleTransverseCyclicOrderFamily G) :
    FiniteAlternatingEndpointSystem
      (SuperellipsoidSeamVertex Phi frame c R d) where
  first := upperOuterPairing outerOrder
  second := inwardCutPairing cutOrder

/-! ## Canonical oriented ambient arcs -/

/-- Lower outer arcs with endpoints expressed through the derived seam pairing. -/
noncomputable def lowerOuterEndpointPaths :
    FiniteAlternatingEndpointSystem.EndpointPathFamily
    (lowerOuterPairing outerOrder)
    (fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3)) where
  path g := by
    change outerOrder.GlobalLowerOuterGap at g
    exact ((outerOrder.globalLowerOuterPath g).map continuous_subtype_val).cast (by
      change (outerOrder.globalLowerEndpointEquiv (g, 0)).1 = _
      rw [outerOrder.globalLowerEndpointEquiv_zero_val]
      exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
        (Path.source (outerOrder.globalLowerOuterPath g))) (by
      change (outerOrder.globalLowerEndpointEquiv (g, 1)).1 = _
      rw [outerOrder.globalLowerEndpointEquiv_one_val]
      exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
        (Path.target (outerOrder.globalLowerOuterPath g)))

/-- Upper outer arcs with endpoints expressed through the derived seam pairing. -/
noncomputable def upperOuterEndpointPaths :
    FiniteAlternatingEndpointSystem.EndpointPathFamily
    (upperOuterPairing outerOrder)
    (fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3)) where
  path g := by
    change outerOrder.GlobalUpperOuterGap at g
    exact ((outerOrder.globalUpperOuterPath g).map continuous_subtype_val).cast (by
      change (outerOrder.globalUpperEndpointEquiv (g, 0)).1 = _
      rw [outerOrder.globalUpperEndpointEquiv_zero_val]
      exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
        (Path.source (outerOrder.globalUpperOuterPath g))) (by
      change (outerOrder.globalUpperEndpointEquiv (g, 1)).1 = _
      rw [outerOrder.globalUpperEndpointEquiv_one_val]
      exact congrArg (fun x : transportedTorus Phi ↦ (x : R3))
        (Path.target (outerOrder.globalUpperOuterPath g)))

/-- Inward cutting arcs with endpoints expressed through their derived seam pairing. -/
noncomputable def inwardCutEndpointPaths :
    FiniteAlternatingEndpointSystem.EndpointPathFamily
    (inwardCutPairing cutOrder)
    (fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3)) where
  path g := by
    change cutOrder.GlobalInwardGap at g
    exact ((cutOrder.globalInwardExcursionPath g).map continuous_subtype_val).cast (by
      change (cutOrder.globalEndpointEquiv (g, 0)).1 = _
      rw [cutOrder.globalEndpointEquiv_zero_val]) (by
      change (cutOrder.globalEndpointEquiv (g, 1)).1 = _
      rw [cutOrder.globalEndpointEquiv_one_val])

/-- The canonical lower alternating arcs, oriented by the successor permutation. -/
noncomputable def lowerOrientedArcs :
    FiniteAlternatingEndpointSystem.OrientedAlternatingArcFamily
    (lowerSystem outerOrder cutOrder)
    (fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3)) :=
  FiniteAlternatingEndpointSystem.OrientedAlternatingArcFamily.ofEndpointPathFamilies
    (lowerOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder)

/-- The canonical upper alternating arcs, oriented by the successor permutation. -/
noncomputable def upperOrientedArcs :
    FiniteAlternatingEndpointSystem.OrientedAlternatingArcFamily
    (upperSystem outerOrder cutOrder)
    (fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3)) :=
  FiniteAlternatingEndpointSystem.OrientedAlternatingArcFamily.ofEndpointPathFamilies
    (upperOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder)

abbrev LowerCycleIndex := (lowerSystem outerOrder cutOrder).CycleIndex
abbrev UpperCycleIndex := (upperSystem outerOrder cutOrder).CycleIndex

/-- The lower cycle containing a specified lower outer half-gap. -/
noncomputable def lowerCycleOfOuterGap
    (g : outerOrder.GlobalLowerOuterGap) : LowerCycleIndex outerOrder cutOrder :=
  (lowerSystem outerOrder cutOrder).cycleOfVertex
    (outerOrder.globalLowerEndpointEquiv (g, 0))

/-- The lower cycle containing a specified inward cut gap. -/
noncomputable def lowerCycleOfCutGap
    (g : cutOrder.GlobalInwardGap) : LowerCycleIndex outerOrder cutOrder :=
  (lowerSystem outerOrder cutOrder).cycleOfVertex
    (cutOrder.globalEndpointEquiv (g, 0))

/-- The upper cycle containing a specified upper outer half-gap. -/
noncomputable def upperCycleOfOuterGap
    (g : outerOrder.GlobalUpperOuterGap) : UpperCycleIndex outerOrder cutOrder :=
  (upperSystem outerOrder cutOrder).cycleOfVertex
    (outerOrder.globalUpperEndpointEquiv (g, 0))

/-- The upper cycle containing a specified inward cut gap. -/
noncomputable def upperCycleOfCutGap
    (g : cutOrder.GlobalInwardGap) : UpperCycleIndex outerOrder cutOrder :=
  (upperSystem outerOrder cutOrder).cycleOfVertex
    (cutOrder.globalEndpointEquiv (g, 0))

/-- Exact active lower carrier assigned to one derived alternating graph cycle. -/
noncomputable def lowerCycleCarrier (q : LowerCycleIndex outerOrder cutOrder) : Set R3 := by
  classical
  exact (⋃ g : outerOrder.GlobalLowerOuterGap,
      if lowerCycleOfOuterGap outerOrder cutOrder g = q then
        Set.range (fun u ↦
          ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3))
      else ∅) ∪
    (⋃ g : cutOrder.GlobalInwardGap,
      if lowerCycleOfCutGap outerOrder cutOrder g = q then
        Set.range (fun u ↦
          ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3))
      else ∅)

/-- Exact active upper carrier assigned to one derived alternating graph cycle. -/
noncomputable def upperCycleCarrier (q : UpperCycleIndex outerOrder cutOrder) : Set R3 := by
  classical
  exact (⋃ g : outerOrder.GlobalUpperOuterGap,
      if upperCycleOfOuterGap outerOrder cutOrder g = q then
        Set.range (fun u ↦
          ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3))
      else ∅) ∪
    (⋃ g : cutOrder.GlobalInwardGap,
      if upperCycleOfCutGap outerOrder cutOrder g = q then
        Set.range (fun u ↦
          ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3))
      else ∅)

/-- Narrow topological realization boundary for the two finite successor systems.

The curve index types and their exact ranges are derived above.  Thus this datum asks only for
the standard theorem that a finite alternating cycle of embedded arcs, whose open interiors are
pairwise disjoint and meet the other colour only at matched endpoints, is a Jordan circle. -/
structure ActiveCycleRealizationData where
  lowerCurve : LowerCycleIndex outerOrder cutOrder → Circle → R3
  lower_continuous : ∀ q, Continuous (lowerCurve q)
  lower_injective : ∀ q, Function.Injective (lowerCurve q)
  lower_mem_torus : ∀ q z, lowerCurve q z ∈ transportedTorus Phi
  lower_pairwise : Pairwise fun q r ↦
    Disjoint (Set.range (lowerCurve q)) (Set.range (lowerCurve r))
  lower_range : ∀ q, Set.range (lowerCurve q) =
    lowerCycleCarrier outerOrder cutOrder q
  lower_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ q z i j U, IsOpen U ∧ p ∈ U ∧ lowerCurve q z = p ∧
      Set.range (lowerCurve q) ∩ U =
        ((Set.range (G.outer.circle i).circle ∩ lowerClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U
  upperCurve : UpperCycleIndex outerOrder cutOrder → Circle → R3
  upper_continuous : ∀ q, Continuous (upperCurve q)
  upper_injective : ∀ q, Function.Injective (upperCurve q)
  upper_mem_torus : ∀ q z, upperCurve q z ∈ transportedTorus Phi
  upper_pairwise : Pairwise fun q r ↦
    Disjoint (Set.range (upperCurve q)) (Set.range (upperCurve r))
  upper_range : ∀ q, Set.range (upperCurve q) =
    upperCycleCarrier outerOrder cutOrder q
  upper_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ q z i j U, IsOpen U ∧ p ∈ U ∧ upperCurve q z = p ∧
      Set.range (upperCurve q) ∩ U =
        ((Set.range (G.outer.circle i).circle ∩ upperClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U

/-- Global embeddedness and exact-range facts for the canonical concatenations.  Unlike
`ActiveCycleRealizationData`, this datum contains no ambient local-germ assertion.  Its fields are
the endpoint-incidence consequences of the closed outer/cut arc packages; the actual curves are
fixed above by finite successor concatenation and `TwoArcCircle.circleMap`. -/
structure ActiveCycleConcatenationData where
  lower_twoArc : ∀ q, (lowerOrientedArcs outerOrder cutOrder).TwoArcData q
  lower_pairwise : Pairwise fun q r : LowerCycleIndex outerOrder cutOrder ↦
    Disjoint
      (Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q))
      (Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap r))
  lower_range : ∀ q,
    Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) =
      lowerCycleCarrier outerOrder cutOrder q
  upper_twoArc : ∀ q, (upperOrientedArcs outerOrder cutOrder).TwoArcData q
  upper_pairwise : Pairwise fun q r : UpperCycleIndex outerOrder cutOrder ↦
    Disjoint
      (Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q))
      (Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap r))
  upper_range : ∀ q,
    Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) =
      upperCycleCarrier outerOrder cutOrder q

/-- The sole genuinely ambient input left after the finite alternating concatenation. -/
structure ActiveCycleLocalGermData where
  lower_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ q z i j U, IsOpen U ∧ p ∈ U ∧
      (lowerOrientedArcs outerOrder cutOrder).circleMap q z = p ∧
      Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) ∩ U =
        ((Set.range (G.outer.circle i).circle ∩ lowerClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U
  upper_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ q z i j U, IsOpen U ∧ p ∈ U ∧
      (upperOrientedArcs outerOrder cutOrder).circleMap q z = p ∧
      Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) ∩ U =
        ((Set.range (G.outer.circle i).circle ∩ upperClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U

/-- The canonical finite concatenations instantiate every active-cycle field except for the
explicit ambient local germ.  Completion by seam-free whole circles remains separate below. -/
noncomputable def ActiveCycleRealizationData.ofCanonicalConcatenations
    (C : ActiveCycleConcatenationData outerOrder cutOrder)
    (localGerm : ActiveCycleLocalGermData outerOrder cutOrder) :
    ActiveCycleRealizationData outerOrder cutOrder where
  lowerCurve := (lowerOrientedArcs outerOrder cutOrder).circleMap
  lower_continuous := (lowerOrientedArcs outerOrder cutOrder).continuous_circleMap
  lower_injective := fun q ↦
    (lowerOrientedArcs outerOrder cutOrder).circleMap_injective q (C.lower_twoArc q)
  lower_mem_torus := by
    intro q z
    have hz : (lowerOrientedArcs outerOrder cutOrder).circleMap q z ∈
        Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) := ⟨z, rfl⟩
    rw [C.lower_range q] at hz
    rw [lowerCycleCarrier] at hz
    rcases hz with hz | hz
    · rcases Set.mem_iUnion.mp hz with ⟨g, hz⟩
      split at hz
      · rcases hz with ⟨u, hu⟩
        rw [← hu]
        exact Subtype.property _
      · exact hz.elim
    · rcases Set.mem_iUnion.mp hz with ⟨g, hz⟩
      split at hz
      · rcases hz with ⟨u, hu⟩
        rw [← hu]
        exact Subtype.property _
      · exact hz.elim
  lower_pairwise := C.lower_pairwise
  lower_range := C.lower_range
  lower_local_v := localGerm.lower_local_v
  upperCurve := (upperOrientedArcs outerOrder cutOrder).circleMap
  upper_continuous := (upperOrientedArcs outerOrder cutOrder).continuous_circleMap
  upper_injective := fun q ↦
    (upperOrientedArcs outerOrder cutOrder).circleMap_injective q (C.upper_twoArc q)
  upper_mem_torus := by
    intro q z
    have hz : (upperOrientedArcs outerOrder cutOrder).circleMap q z ∈
        Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) := ⟨z, rfl⟩
    rw [C.upper_range q] at hz
    rw [upperCycleCarrier] at hz
    rcases hz with hz | hz
    · rcases Set.mem_iUnion.mp hz with ⟨g, hz⟩
      split at hz
      · rcases hz with ⟨u, hu⟩
        rw [← hu]
        exact Subtype.property _
      · exact hz.elim
    · rcases Set.mem_iUnion.mp hz with ⟨g, hz⟩
      split at hz
      · rcases hz with ⟨u, hu⟩
        rw [← hu]
        exact Subtype.property _
      · exact hz.elim
  upper_pairwise := C.upper_pairwise
  upper_range := C.upper_range
  upper_local_v := localGerm.upper_local_v

variable (realization : ActiveCycleRealizationData outerOrder cutOrder)

/-- Complete lower component index: active alternating cycles, seam-free lower outer circles,
and seam-free inward cutting circles. -/
abbrev LowerComponentIndex :=
  LowerCycleIndex outerOrder cutOrder ⊕
    (outerOrder.LowerWholeOuterCircle ⊕ G.InwardWholeCutCircle)

/-- Complete upper component index: active alternating cycles, seam-free upper outer circles,
and the same seam-free inward cutting circles. -/
abbrev UpperComponentIndex :=
  UpperCycleIndex outerOrder cutOrder ⊕
    (outerOrder.UpperWholeOuterCircle ⊕ G.InwardWholeCutCircle)

/-- Canonical lower curves.  No new curve is chosen for a seam-free component: its already
embedded outer or cut circle is retained verbatim. -/
def lowerComponentCurve : LowerComponentIndex outerOrder cutOrder → Circle → R3
  | Sum.inl q => realization.lowerCurve q
  | Sum.inr (Sum.inl i) => (G.outer.circle i.1.1).circle
  | Sum.inr (Sum.inr j) => (G.cut.circle j.1.1).circle

/-- Canonical upper curves, with seam-free components retained verbatim. -/
def upperComponentCurve : UpperComponentIndex outerOrder cutOrder → Circle → R3
  | Sum.inl q => realization.upperCurve q
  | Sum.inr (Sum.inl i) => (G.outer.circle i.1.1).circle
  | Sum.inr (Sum.inr j) => (G.cut.circle j.1.1).circle

theorem lowerComponentCurve_continuous
    (k : LowerComponentIndex outerOrder cutOrder) :
    Continuous (lowerComponentCurve outerOrder cutOrder realization k) := by
  rcases k with q | i
  · exact realization.lower_continuous q
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).isEmbedding.continuous
    · exact (G.cut.circle j.1.1).isEmbedding.continuous

theorem upperComponentCurve_continuous
    (k : UpperComponentIndex outerOrder cutOrder) :
    Continuous (upperComponentCurve outerOrder cutOrder realization k) := by
  rcases k with q | i
  · exact realization.upper_continuous q
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).isEmbedding.continuous
    · exact (G.cut.circle j.1.1).isEmbedding.continuous

theorem lowerComponentCurve_injective
    (k : LowerComponentIndex outerOrder cutOrder) :
    Function.Injective (lowerComponentCurve outerOrder cutOrder realization k) := by
  rcases k with q | i
  · exact realization.lower_injective q
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).isEmbedding.injective
    · exact (G.cut.circle j.1.1).isEmbedding.injective

theorem upperComponentCurve_injective
    (k : UpperComponentIndex outerOrder cutOrder) :
    Function.Injective (upperComponentCurve outerOrder cutOrder realization k) := by
  rcases k with q | i
  · exact realization.upper_injective q
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).isEmbedding.injective
    · exact (G.cut.circle j.1.1).isEmbedding.injective

/-- Set-theoretic completion facts needed after the generic active-cycle realization theorem.
They are consequences of the exact range fields, the original pairwise circle decompositions,
and the seam-free constant-sign lemmas above.  Bundling them here keeps the final constructor
independent of any arbitrary component enumeration. -/
structure CanonicalCompletionProofs where
  lower_mem_torus : ∀ k z,
    lowerComponentCurve outerOrder cutOrder realization k z ∈ transportedTorus Phi
  lower_pairwise : Pairwise fun k l ↦
    Disjoint
      (Set.range (lowerComponentCurve outerOrder cutOrder realization k))
      (Set.range (lowerComponentCurve outerOrder cutOrder realization l))
  lower_mem : ∀ k,
    Set.range (lowerComponentCurve outerOrder cutOrder realization k) ⊆
      lowerTruncatedSeamVCarrier Phi frame c R d
  lower_outer_covered : ∀ i,
    Set.range (G.outer.circle i).circle ∩ lowerClosedHalfspace frame d ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k)
  lower_cut_covered : ∀ j,
    Set.range (G.cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k)
  upper_mem_torus : ∀ k z,
    upperComponentCurve outerOrder cutOrder realization k z ∈ transportedTorus Phi
  upper_pairwise : Pairwise fun k l ↦
    Disjoint
      (Set.range (upperComponentCurve outerOrder cutOrder realization k))
      (Set.range (upperComponentCurve outerOrder cutOrder realization l))
  upper_mem : ∀ k,
    Set.range (upperComponentCurve outerOrder cutOrder realization k) ⊆
      upperTruncatedSeamVCarrier Phi frame c R d
  upper_outer_covered : ∀ i,
    Set.range (G.outer.circle i).circle ∩ upperClosedHalfspace frame d ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k)
  upper_cut_covered : ∀ j,
    Set.range (G.cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k)

/-- The derived finite cycles plus the explicitly retained seam-free circles construct the exact
lower/upper `V`-gluing package. -/
def toTruncatedSphereSeamVGluingData
    (completion : CanonicalCompletionProofs outerOrder cutOrder realization) :
    TruncatedSphereSeamVGluingData
      (lowerIndex := LowerComponentIndex outerOrder cutOrder)
      (upperIndex := UpperComponentIndex outerOrder cutOrder) G.outer G.cut where
  lowerCurve := lowerComponentCurve outerOrder cutOrder realization
  lower_continuous := lowerComponentCurve_continuous outerOrder cutOrder realization
  lower_injective := lowerComponentCurve_injective outerOrder cutOrder realization
  lower_mem_torus := completion.lower_mem_torus
  lower_pairwise := completion.lower_pairwise
  lower_local_v := by
    intro p hp
    obtain ⟨q, z, i, j, U, hU, hpU, hcurve, hrange⟩ :=
      realization.lower_local_v p hp
    exact ⟨Sum.inl q, z, i, j, U, hU, hpU, hcurve, hrange⟩
  lower_mem := completion.lower_mem
  lower_outer_covered := completion.lower_outer_covered
  lower_cut_covered := completion.lower_cut_covered
  upperCurve := upperComponentCurve outerOrder cutOrder realization
  upper_continuous := upperComponentCurve_continuous outerOrder cutOrder realization
  upper_injective := upperComponentCurve_injective outerOrder cutOrder realization
  upper_mem_torus := completion.upper_mem_torus
  upper_pairwise := completion.upper_pairwise
  upper_local_v := by
    intro p hp
    obtain ⟨q, z, i, j, U, hU, hpU, hcurve, hrange⟩ :=
      realization.upper_local_v p hp
    exact ⟨Sum.inl q, z, i, j, U, hU, hpU, hcurve, hrange⟩
  upper_mem := completion.upper_mem
  upper_outer_covered := completion.upper_outer_covered
  upper_cut_covered := completion.upper_cut_covered

end TruncatedSphereAlternatingCycles

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
