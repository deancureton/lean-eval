import Submission.Topology.SuperellipsoidActiveCycleLocalGerm

/-!
# Canonical finite sections of the two truncated superellipsoids

This file composes the canonical active alternating cycles with their exact local seam germs,
then adds the seam-free outer and cutting circles.  All completion facts are derived from the
original pairwise circle sections, exact closed-gap coverage, and constant-sign lemmas.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
  (cutOrder : CutCircleTransverseCyclicOrderFamily G)

variable [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

/-- Exact closed coverage supplies the last input to the canonical active-cycle realization. -/
noncomputable def canonicalActiveCycleRealizationData_of_closedCoverage (hR : 0 < R) :
    ActiveCycleRealizationData outerOrder cutOrder :=
  canonicalActiveCycleRealizationData outerOrder cutOrder
    (ActiveCycleConcatenationData.toActiveCycleLocalGermData_of_closedCoverage
      outerOrder cutOrder
      (canonicalActiveCycleConcatenationData outerOrder cutOrder) hR)

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem mem_seam_of_mem_outerCircle_of_mem_cutCircle
    {i : outerIndex} {j : cutIndex} {x : R3}
    (hxOuter : x ∈ Set.range (G.outer.circle i).circle)
    (hxCut : x ∈ Set.range (G.cut.circle j).circle) :
    x ∈ superellipsoidTorusSeam Phi frame c R d := by
  have ho := G.outer.circle_mem_section i hxOuter
  have hc := G.cut.circle_mem_section j hxCut
  exact ⟨ho, hc.2⟩

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem inactiveOuterCircle_range_disjoint_seam
    (i : outerOrder.InactiveOuterCircle) :
    Disjoint (Set.range (G.outer.circle i.1).circle)
      (superellipsoidTorusSeam Phi frame c R d) := by
  rw [Set.disjoint_left]
  intro x hxCircle hxSeam
  obtain ⟨z, rfl⟩ := hxCircle
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  apply outerOrder.inactiveOuter_height_ne_zero i t
  unfold windingLoopCutHeight
  rw [← (G.outer.circle i.1).parametrization]
  exact sub_eq_zero.mpr hxSeam.2

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem inactiveCutCircle_range_disjoint_seam
    (hR : 0 ≤ R) (j : G.InactiveCutCircle) :
    Disjoint (Set.range (G.cut.circle j.1).circle)
      (superellipsoidTorusSeam Phi frame c R d) := by
  rw [Set.disjoint_left]
  intro x hxCircle hxSeam
  obtain ⟨z, rfl⟩ := hxCircle
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  apply G.inactiveCut_difference_ne_zero hR j t
  apply (G.cutCircleOuterPolynomialDifference_eq_zero_iff_seam j.1 hR t).mpr
  rw [← (G.cut.circle j.1).parametrization]
  exact hxSeam

private theorem lowerActive_range_subset_branches
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : LowerCycleIndex outerOrder cutOrder) :
    Set.range (realization.lowerCurve q) ⊆
      (((⋃ i : outerOrder.ActiveOuterCircle,
          Set.range (G.outer.circle i.1).circle) ∩ lowerClosedHalfspace frame d) ∪
        ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
          closedSuperellipsoidBody frame c R)) := by
  intro x hx
  have hxCarrier : x ∈ lowerCycleCarrier outerOrder cutOrder q := by
    rw [← realization.lower_range q]
    exact hx
  have hxTotal := lowerCycleCarrier_subset_totalClosedArcCarrier
    outerOrder cutOrder q hxCarrier
  rw [lowerTotalClosedArcCarrier_eq_activeBranches outerOrder cutOrder hR] at hxTotal
  exact hxTotal

private theorem upperActive_range_subset_branches
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : UpperCycleIndex outerOrder cutOrder) :
    Set.range (realization.upperCurve q) ⊆
      (((⋃ i : outerOrder.ActiveOuterCircle,
          Set.range (G.outer.circle i.1).circle) ∩ upperClosedHalfspace frame d) ∪
        ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
          closedSuperellipsoidBody frame c R)) := by
  intro x hx
  have hxCarrier : x ∈ upperCycleCarrier outerOrder cutOrder q := by
    rw [← realization.upper_range q]
    exact hx
  have hxTotal := upperCycleCarrier_subset_totalClosedArcCarrier
    outerOrder cutOrder q hxCarrier
  rw [upperTotalClosedArcCarrier_eq_activeBranches outerOrder cutOrder hR] at hxTotal
  exact hxTotal

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem activeOuter_ne_inactiveOuter
    (i : outerOrder.ActiveOuterCircle) (k : outerOrder.InactiveOuterCircle) :
    i.1 ≠ k.1 := by
  intro hik
  apply k.2
  simpa [hik] using i.2

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem activeCut_ne_inactiveCut
    (j : G.ActiveCutCircle) (k : G.InactiveCutCircle) : j.1 ≠ k.1 := by
  intro hjk
  apply k.2
  simpa [hjk] using j.2

private theorem lowerActive_disjoint_lowerWholeOuter
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : LowerCycleIndex outerOrder cutOrder)
    (k : outerOrder.LowerWholeOuterCircle) :
    Disjoint (Set.range (realization.lowerCurve q))
      (Set.range (G.outer.circle k.1.1).circle) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lowerActive_range_subset_branches outerOrder cutOrder realization hR q hx with
      hxOuter | hxCut
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxOuter.1
    exact Set.disjoint_left.mp
      (G.outer.pairwise_disjoint (activeOuter_ne_inactiveOuter outerOrder i k.1)) hi hy
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut.1
    have hxSeam := mem_seam_of_mem_outerCircle_of_mem_cutCircle hy hj
    exact Set.disjoint_left.mp
      (inactiveOuterCircle_range_disjoint_seam outerOrder k.1) hy hxSeam

private theorem lowerActive_disjoint_inwardWholeCut
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : LowerCycleIndex outerOrder cutOrder)
    (k : G.InwardWholeCutCircle) :
    Disjoint (Set.range (realization.lowerCurve q))
      (Set.range (G.cut.circle k.1.1).circle) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lowerActive_range_subset_branches outerOrder cutOrder realization hR q hx with
      hxOuter | hxCut
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxOuter.1
    have hxSeam := mem_seam_of_mem_outerCircle_of_mem_cutCircle hi hy
    exact Set.disjoint_left.mp
      (inactiveCutCircle_range_disjoint_seam hR.le k.1) hy hxSeam
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut.1
    exact Set.disjoint_left.mp
      (G.cut.pairwise_disjoint (activeCut_ne_inactiveCut j k.1)) hj hy

private theorem upperActive_disjoint_upperWholeOuter
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : UpperCycleIndex outerOrder cutOrder)
    (k : outerOrder.UpperWholeOuterCircle) :
    Disjoint (Set.range (realization.upperCurve q))
      (Set.range (G.outer.circle k.1.1).circle) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases upperActive_range_subset_branches outerOrder cutOrder realization hR q hx with
      hxOuter | hxCut
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxOuter.1
    exact Set.disjoint_left.mp
      (G.outer.pairwise_disjoint (activeOuter_ne_inactiveOuter outerOrder i k.1)) hi hy
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut.1
    have hxSeam := mem_seam_of_mem_outerCircle_of_mem_cutCircle hy hj
    exact Set.disjoint_left.mp
      (inactiveOuterCircle_range_disjoint_seam outerOrder k.1) hy hxSeam

private theorem upperActive_disjoint_inwardWholeCut
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (q : UpperCycleIndex outerOrder cutOrder)
    (k : G.InwardWholeCutCircle) :
    Disjoint (Set.range (realization.upperCurve q))
      (Set.range (G.cut.circle k.1.1).circle) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases upperActive_range_subset_branches outerOrder cutOrder realization hR q hx with
      hxOuter | hxCut
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxOuter.1
    have hxSeam := mem_seam_of_mem_outerCircle_of_mem_cutCircle hi hy
    exact Set.disjoint_left.mp
      (inactiveCutCircle_range_disjoint_seam hR.le k.1) hy hxSeam
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut.1
    exact Set.disjoint_left.mp
      (G.cut.pairwise_disjoint (activeCut_ne_inactiveCut j k.1)) hj hy

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem wholeOuter_disjoint_wholeCut
    (i : outerOrder.InactiveOuterCircle) (j : G.InactiveCutCircle) :
    Disjoint (Set.range (G.outer.circle i.1).circle)
      (Set.range (G.cut.circle j.1).circle) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hxSeam := mem_seam_of_mem_outerCircle_of_mem_cutCircle hx hy
  exact Set.disjoint_left.mp
    (inactiveOuterCircle_range_disjoint_seam outerOrder i) hx hxSeam

private theorem lowerComponentCurve_pairwise
    (realization : ActiveCycleRealizationData outerOrder cutOrder) (hR : 0 < R) :
    Pairwise fun k l ↦
      Disjoint (Set.range (lowerComponentCurve outerOrder cutOrder realization k))
        (Set.range (lowerComponentCurve outerOrder cutOrder realization l)) := by
  rintro (q | a) (r | b) hne
  · apply realization.lower_pairwise
    intro hqr
    exact hne (congrArg Sum.inl hqr)
  · rcases b with i | j
    · exact lowerActive_disjoint_lowerWholeOuter outerOrder cutOrder realization hR q i
    · exact lowerActive_disjoint_inwardWholeCut outerOrder cutOrder realization hR q j
  · rcases a with i | j
    · exact (lowerActive_disjoint_lowerWholeOuter
        outerOrder cutOrder realization hR r i).symm
    · exact (lowerActive_disjoint_inwardWholeCut
        outerOrder cutOrder realization hR r j).symm
  · rcases a with i | j <;> rcases b with k | l
    · apply G.outer.pairwise_disjoint
      intro hik
      apply hne
      exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext (Subtype.ext hik)))
    · exact wholeOuter_disjoint_wholeCut outerOrder i.1 l.1
    · exact (wholeOuter_disjoint_wholeCut outerOrder k.1 j.1).symm
    · apply G.cut.pairwise_disjoint
      intro hjl
      apply hne
      exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext (Subtype.ext hjl)))

private theorem upperComponentCurve_pairwise
    (realization : ActiveCycleRealizationData outerOrder cutOrder) (hR : 0 < R) :
    Pairwise fun k l ↦
      Disjoint (Set.range (upperComponentCurve outerOrder cutOrder realization k))
        (Set.range (upperComponentCurve outerOrder cutOrder realization l)) := by
  rintro (q | a) (r | b) hne
  · apply realization.upper_pairwise
    intro hqr
    exact hne (congrArg Sum.inl hqr)
  · rcases b with i | j
    · exact upperActive_disjoint_upperWholeOuter outerOrder cutOrder realization hR q i
    · exact upperActive_disjoint_inwardWholeCut outerOrder cutOrder realization hR q j
  · rcases a with i | j
    · exact (upperActive_disjoint_upperWholeOuter
        outerOrder cutOrder realization hR r i).symm
    · exact (upperActive_disjoint_inwardWholeCut
        outerOrder cutOrder realization hR r j).symm
  · rcases a with i | j <;> rcases b with k | l
    · apply G.outer.pairwise_disjoint
      intro hik
      apply hne
      exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext (Subtype.ext hik)))
    · exact wholeOuter_disjoint_wholeCut outerOrder i.1 l.1
    · exact (wholeOuter_disjoint_wholeCut outerOrder k.1 j.1).symm
    · apply G.cut.pairwise_disjoint
      intro hjl
      apply hne
      exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext (Subtype.ext hjl)))

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem lowerWholeOuter_range_mem
    (i : outerOrder.LowerWholeOuterCircle) :
    Set.range (G.outer.circle i.1.1).circle ⊆
      lowerTruncatedSeamVCarrier Phi frame c R d := by
  intro x hx
  refine Or.inl ⟨G.outer.circle_mem_section i.1.1 hx, ?_⟩
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  change ((G.outer.circle i.1.1).circle (Circle.exp t)).ofLp (frame 2) ≤ d
  rw [(G.outer.circle i.1.1).parametrization]
  have h := outerOrder.lowerWholeOuterCircle_all_lower i t
  unfold windingLoopCutHeight at h
  linarith

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem upperWholeOuter_range_mem
    (i : outerOrder.UpperWholeOuterCircle) :
    Set.range (G.outer.circle i.1.1).circle ⊆
      upperTruncatedSeamVCarrier Phi frame c R d := by
  intro x hx
  refine Or.inl ⟨G.outer.circle_mem_section i.1.1 hx, ?_⟩
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  change d ≤ ((G.outer.circle i.1.1).circle (Circle.exp t)).ofLp (frame 2)
  rw [(G.outer.circle i.1.1).parametrization]
  have h := outerOrder.upperWholeOuterCircle_all_upper i t
  unfold windingLoopCutHeight at h
  linarith

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem inwardWholeCut_range_mem
    (hR : 0 < R) (j : G.InwardWholeCutCircle) :
    Set.range (G.cut.circle j.1.1).circle ⊆
      superellipsoidCutTorusSection Phi frame d ∩ closedSuperellipsoidBody frame c R := by
  intro x hx
  refine ⟨G.cut.circle_mem_section j.1.1 hx, ?_⟩
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [(G.cut.circle j.1.1).parametrization]
  change superellipsoidGauge frame c _ ≤ R
  exact ((G.cutCircleOuterPolynomialDifference_neg_iff_body j.1.1 hR t).mp
    (G.inwardWholeCutCircle_all_inward hR.le j t)).le

private theorem lowerComponentCurve_mem
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (k : LowerComponentIndex outerOrder cutOrder) :
    Set.range (lowerComponentCurve outerOrder cutOrder realization k) ⊆
      lowerTruncatedSeamVCarrier Phi frame c R d := by
  rcases k with q | i
  · intro x hx
    rcases lowerActive_range_subset_branches outerOrder cutOrder realization hR q hx with
        hxOuter | hxCut
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxOuter.1
      exact Or.inl ⟨G.outer.circle_mem_section a.1 ha, hxOuter.2⟩
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxCut.1
      exact Or.inr ⟨G.cut.circle_mem_section a.1 ha, hxCut.2⟩
  · rcases i with i | j
    · exact lowerWholeOuter_range_mem outerOrder i
    · exact fun x hx ↦ Or.inr (inwardWholeCut_range_mem hR j hx)

private theorem upperComponentCurve_mem
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (k : UpperComponentIndex outerOrder cutOrder) :
    Set.range (upperComponentCurve outerOrder cutOrder realization k) ⊆
      upperTruncatedSeamVCarrier Phi frame c R d := by
  rcases k with q | i
  · intro x hx
    rcases upperActive_range_subset_branches outerOrder cutOrder realization hR q hx with
        hxOuter | hxCut
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxOuter.1
      exact Or.inl ⟨G.outer.circle_mem_section a.1 ha, hxOuter.2⟩
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxCut.1
      exact Or.inr ⟨G.cut.circle_mem_section a.1 ha, hxCut.2⟩
  · rcases i with i | j
    · exact upperWholeOuter_range_mem outerOrder i
    · exact fun x hx ↦ Or.inr (inwardWholeCut_range_mem hR j hx)

private theorem lowerComponentCurve_mem_torus
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (k : LowerComponentIndex outerOrder cutOrder) (z : Circle) :
    lowerComponentCurve outerOrder cutOrder realization k z ∈ transportedTorus Phi := by
  rcases k with q | i
  · exact realization.lower_mem_torus q z
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).range_subset_transportedTorus ⟨z, rfl⟩
    · exact (G.cut.circle j.1.1).range_subset_transportedTorus ⟨z, rfl⟩

private theorem upperComponentCurve_mem_torus
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (k : UpperComponentIndex outerOrder cutOrder) (z : Circle) :
    upperComponentCurve outerOrder cutOrder realization k z ∈ transportedTorus Phi := by
  rcases k with q | i
  · exact realization.upper_mem_torus q z
  · rcases i with i | j
    · exact (G.outer.circle i.1.1).range_subset_transportedTorus ⟨z, rfl⟩
    · exact (G.cut.circle j.1.1).range_subset_transportedTorus ⟨z, rfl⟩

private theorem activeLowerGap_mem_componentUnion
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (g : outerOrder.GlobalLowerOuterGap) :
    Set.range (fun u ↦
      ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3)) ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  let q := lowerCycleOfOuterGap outerOrder cutOrder g
  refine Set.mem_iUnion.mpr ⟨Sum.inl q, ?_⟩
  change x ∈ Set.range (realization.lowerCurve q)
  rw [realization.lower_range q, lowerCycleCarrier]
  apply Or.inl
  refine Set.mem_iUnion.mpr ⟨g, ?_⟩
  simp only [q]
  exact hx

private theorem activeUpperGap_mem_componentUnion
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (g : outerOrder.GlobalUpperOuterGap) :
    Set.range (fun u ↦
      ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3)) ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  let q := upperCycleOfOuterGap outerOrder cutOrder g
  refine Set.mem_iUnion.mpr ⟨Sum.inl q, ?_⟩
  change x ∈ Set.range (realization.upperCurve q)
  rw [realization.upper_range q, upperCycleCarrier]
  apply Or.inl
  refine Set.mem_iUnion.mpr ⟨g, ?_⟩
  simp only [q]
  exact hx

private theorem activeCutGap_mem_lowerComponentUnion
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (g : cutOrder.GlobalInwardGap) :
    Set.range (fun u ↦
      ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3)) ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  let q := lowerCycleOfCutGap outerOrder cutOrder g
  refine Set.mem_iUnion.mpr ⟨Sum.inl q, ?_⟩
  change x ∈ Set.range (realization.lowerCurve q)
  rw [realization.lower_range q, lowerCycleCarrier]
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨g, ?_⟩
  simp only [q]
  exact hx

private theorem activeCutGap_mem_upperComponentUnion
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (g : cutOrder.GlobalInwardGap) :
    Set.range (fun u ↦
      ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3)) ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  let q := upperCycleOfCutGap outerOrder cutOrder g
  refine Set.mem_iUnion.mpr ⟨Sum.inl q, ?_⟩
  change x ∈ Set.range (realization.upperCurve q)
  rw [realization.upper_range q, upperCycleCarrier]
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨g, ?_⟩
  simp only [q]
  exact hx

private theorem lowerOuter_covered
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (i : outerIndex) :
    Set.range (G.outer.circle i).circle ∩ lowerClosedHalfspace frame d ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  by_cases hi : (outerOrder.regular i).crossings.Nonempty
  · have hxActive : x ∈
        (⋃ a : outerOrder.ActiveOuterCircle,
          Set.range (G.outer.circle a.1).circle) ∩ lowerClosedHalfspace frame d :=
      ⟨Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx.1⟩, hx.2⟩
    rw [← outerOrder.iUnion_range_globalLowerOuterPath_eq] at hxActive
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxActive
    exact activeLowerGap_mem_componentUnion outerOrder cutOrder realization g hg
  · let inactive : outerOrder.InactiveOuterCircle := ⟨i, hi⟩
    rcases outerOrder.inactiveOuter_eq_lower_or_upper inactive with hLower | hUpper
    · obtain ⟨k, hk⟩ := hLower
      have hki : k.1.1 = i := congrArg Subtype.val hk
      refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl k), ?_⟩
      simpa only [lowerComponentCurve, hki] using hx.1
    · obtain ⟨k, hk⟩ := hUpper
      obtain ⟨z, hz⟩ := hx.1
      obtain ⟨t, ht⟩ := Circle.exp_surjective z
      subst z
      rw [(G.outer.circle i).parametrization] at hz
      have hpos := outerOrder.upperWholeOuterCircle_all_upper k t
      unfold windingLoopCutHeight at hpos
      have hxLower := hx.2
      change x.ofLp (frame 2) ≤ d at hxLower
      have hki : k.1.1 = i := congrArg Subtype.val hk
      rw [hki] at hpos
      rw [hz] at hpos
      linarith [hxLower]

private theorem upperOuter_covered
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (i : outerIndex) :
    Set.range (G.outer.circle i).circle ∩ upperClosedHalfspace frame d ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  by_cases hi : (outerOrder.regular i).crossings.Nonempty
  · have hxActive : x ∈
        (⋃ a : outerOrder.ActiveOuterCircle,
          Set.range (G.outer.circle a.1).circle) ∩ upperClosedHalfspace frame d :=
      ⟨Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx.1⟩, hx.2⟩
    rw [← outerOrder.iUnion_range_globalUpperOuterPath_eq] at hxActive
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxActive
    exact activeUpperGap_mem_componentUnion outerOrder cutOrder realization g hg
  · let inactive : outerOrder.InactiveOuterCircle := ⟨i, hi⟩
    rcases outerOrder.inactiveOuter_eq_lower_or_upper inactive with hLower | hUpper
    · obtain ⟨k, hk⟩ := hLower
      obtain ⟨z, hz⟩ := hx.1
      obtain ⟨t, ht⟩ := Circle.exp_surjective z
      subst z
      rw [(G.outer.circle i).parametrization] at hz
      have hneg := outerOrder.lowerWholeOuterCircle_all_lower k t
      unfold windingLoopCutHeight at hneg
      have hxUpper := hx.2
      change d ≤ x.ofLp (frame 2) at hxUpper
      have hki : k.1.1 = i := congrArg Subtype.val hk
      rw [hki] at hneg
      rw [hz] at hneg
      linarith [hxUpper]
    · obtain ⟨k, hk⟩ := hUpper
      have hki : k.1.1 = i := congrArg Subtype.val hk
      refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl k), ?_⟩
      simpa only [upperComponentCurve, hki] using hx.1

private theorem cut_covered_lower
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (j : cutIndex) :
    Set.range (G.cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (lowerComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  by_cases hj : (G.cutCircleSeamCrossings j).Nonempty
  · have hxActive : x ∈
        (⋃ a : G.ActiveCutCircle, Set.range (G.cut.circle a.1).circle) ∩
          closedSuperellipsoidBody frame c R :=
      ⟨Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx.1⟩, hx.2⟩
    rw [← cutOrder.iUnion_range_globalInwardExcursionPath_eq hR] at hxActive
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxActive
    exact activeCutGap_mem_lowerComponentUnion outerOrder cutOrder realization g hg
  · let inactive : G.InactiveCutCircle := ⟨j, hj⟩
    obtain ⟨z, hz⟩ := hx.1
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    rw [(G.cut.circle j).parametrization] at hz
    rw [← hz] at hx ⊢
    have hne := G.inactiveCut_difference_ne_zero hR.le inactive t
    have hgaugeNe : superellipsoidGauge frame c
        ((G.cut.circle j).windingLoop.curve t : R3) ≠ R := by
      intro heq
      apply hne
      exact sub_eq_zero.mpr
        ((mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp heq)
    have hbody : ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidBody frame c R :=
      lt_of_le_of_ne hx.2 hgaugeNe
    have hneg := (G.cutCircleOuterPolynomialDifference_neg_iff_body j hR t).mpr
      hbody
    have hneg0 : G.cutCircleOuterPolynomialDifference j 0 < 0 := by
      rcases G.inactiveCut_all_inward_or_all_outward hR.le inactive with hin | hout
      · exact hin 0
      · exact False.elim (not_lt_of_ge (hout t).le hneg)
    let k : G.InwardWholeCutCircle := ⟨inactive, hneg0⟩
    exact Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr k), hx.1⟩

private theorem cut_covered_upper
    (realization : ActiveCycleRealizationData outerOrder cutOrder)
    (hR : 0 < R) (j : cutIndex) :
    Set.range (G.cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (upperComponentCurve outerOrder cutOrder realization k) := by
  intro x hx
  by_cases hj : (G.cutCircleSeamCrossings j).Nonempty
  · have hxActive : x ∈
        (⋃ a : G.ActiveCutCircle, Set.range (G.cut.circle a.1).circle) ∩
          closedSuperellipsoidBody frame c R :=
      ⟨Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx.1⟩, hx.2⟩
    rw [← cutOrder.iUnion_range_globalInwardExcursionPath_eq hR] at hxActive
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxActive
    exact activeCutGap_mem_upperComponentUnion outerOrder cutOrder realization g hg
  · let inactive : G.InactiveCutCircle := ⟨j, hj⟩
    obtain ⟨z, hz⟩ := hx.1
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    rw [(G.cut.circle j).parametrization] at hz
    rw [← hz] at hx ⊢
    have hne := G.inactiveCut_difference_ne_zero hR.le inactive t
    have hgaugeNe : superellipsoidGauge frame c
        ((G.cut.circle j).windingLoop.curve t : R3) ≠ R := by
      intro heq
      apply hne
      exact sub_eq_zero.mpr
        ((mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp heq)
    have hbody : ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidBody frame c R :=
      lt_of_le_of_ne hx.2 hgaugeNe
    have hneg := (G.cutCircleOuterPolynomialDifference_neg_iff_body j hR t).mpr
      hbody
    have hneg0 : G.cutCircleOuterPolynomialDifference j 0 < 0 := by
      rcases G.inactiveCut_all_inward_or_all_outward hR.le inactive with hin | hout
      · exact hin 0
      · exact False.elim (not_lt_of_ge (hout t).le hneg)
    let k : G.InwardWholeCutCircle := ⟨inactive, hneg0⟩
    exact Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr k), hx.1⟩

/-- The active canonical cycles and all seam-free whole circles satisfy every completion fact. -/
theorem canonicalCompletionProofs_of_closedCoverage
    (hR : 0 < R)
    (realization := canonicalActiveCycleRealizationData_of_closedCoverage
      outerOrder cutOrder hR) :
    CanonicalCompletionProofs outerOrder cutOrder realization where
  lower_mem_torus := lowerComponentCurve_mem_torus outerOrder cutOrder realization
  lower_pairwise := lowerComponentCurve_pairwise outerOrder cutOrder realization hR
  lower_mem := lowerComponentCurve_mem outerOrder cutOrder realization hR
  lower_outer_covered := lowerOuter_covered outerOrder cutOrder realization
  lower_cut_covered := cut_covered_lower outerOrder cutOrder realization hR
  upper_mem_torus := upperComponentCurve_mem_torus outerOrder cutOrder realization
  upper_pairwise := upperComponentCurve_pairwise outerOrder cutOrder realization hR
  upper_mem := upperComponentCurve_mem outerOrder cutOrder realization hR
  upper_outer_covered := upperOuter_covered outerOrder cutOrder realization
  upper_cut_covered := cut_covered_upper outerOrder cutOrder realization hR

/-- Unconditional canonical local `V`-gluing data for both truncated children. -/
noncomputable def canonicalTruncatedSphereSeamVGluingData (hR : 0 < R) :
    TruncatedSphereSeamVGluingData
      (lowerIndex := LowerComponentIndex outerOrder cutOrder)
      (upperIndex := UpperComponentIndex outerOrder cutOrder) G.outer G.cut :=
  toTruncatedSphereSeamVGluingData outerOrder cutOrder
    (canonicalActiveCycleRealizationData_of_closedCoverage outerOrder cutOrder hR)
    (canonicalCompletionProofs_of_closedCoverage outerOrder cutOrder hR)

/-- Canonical finite lower truncated-superellipsoid circle section. -/
noncomputable def canonicalLowerFiniteSection (hR : 0 < R) :
    FiniteEmbeddedTorusCircleSection Phi
      (lowerTruncatedSuperellipsoidTorusSection Phi frame c R d)
      (LowerComponentIndex outerOrder cutOrder) :=
  (canonicalTruncatedSphereSeamVGluingData outerOrder cutOrder hR).lowerFiniteSection hR

/-- Canonical finite upper truncated-superellipsoid circle section. -/
noncomputable def canonicalUpperFiniteSection (hR : 0 < R) :
    FiniteEmbeddedTorusCircleSection Phi
      (upperTruncatedSuperellipsoidTorusSection Phi frame c R d)
      (UpperComponentIndex outerOrder cutOrder) :=
  (canonicalTruncatedSphereSeamVGluingData outerOrder cutOrder hR).upperFiniteSection hR

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
