import Submission.Topology.SuperellipsoidTruncatedSphereCycleGluing

/-!
# Closed outer-gap arcs

This module upgrades the open-gap statements for a transverse outer superellipsoid section to
closed embedded arcs.  The two endpoint equivalences are used essentially: they rule out a
one-crossing full-period arc and show that distinct selected arcs have distinct endpoints.

The results are global set-theoretic inputs for the later finite alternating-cycle construction.
They do not assert an ambient local `V` model.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph
namespace OuterCircleTransverseHeightCyclicOrderFamily

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (F : OuterCircleTransverseHeightCyclicOrderFamily G)

private theorem gapPath_ambient_injective_of_endpoints_ne
    (g : F.GlobalOuterGap)
    (hend :
      ((F.gapPath g 0 : transportedTorus Phi) : R3) ≠
        ((F.gapPath g 1 : transportedTorus Phi) : R3)) :
    Function.Injective fun u ↦ ((F.gapPath g u : transportedTorus Phi) : R3) := by
  intro u v huv
  let left := (F.excursion g).left
  let right := (F.excursion g).right
  let period := 2 * Real.pi
  have hlr : left < right := (F.excursion g).left_lt_right
  have hrightLe : right ≤ left + period := by
    simpa [left, right, period] using (F.excursion g).right_le_next_period
  have hrightLt : right < left + period := by
    apply lt_of_le_of_ne hrightLe
    intro heq
    apply hend
    rw [F.gapPath_apply, F.gapPath_apply]
    have hleft : F.gapParameter g 0 = left := by
      simp [gapParameter, left]
    have hright : F.gapParameter g 1 = right := by
      simp [gapParameter, right]
    rw [hleft, hright]
    rw [heq]
    apply congrArg Subtype.val
    convert ((G.outer.circle g.1.1).windingLoop.periodic_curve left).symm using 1
  let su := F.gapParameter g u
  let sv := F.gapParameter g v
  have hsu : su ∈ Icc left right := by
    simpa [su, left, right] using F.gapParameter_mem_Icc g u
  have hsv : sv ∈ Icc left right := by
    simpa [sv, left, right] using F.gapParameter_mem_Icc g v
  have hexp : Circle.exp su = Circle.exp sv := by
    apply (G.outer.circle g.1.1).isEmbedding.injective
    rw [(G.outer.circle g.1.1).parametrization,
      (G.outer.circle g.1.1).parametrization]
    simpa [su, sv, F.gapPath_apply] using huv
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hnzero : n = 0 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · have hnleInt : n ≤ -1 := by omega
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast hnleInt
      have hshift : (n : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by
        simpa only [neg_mul, one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      dsimp [period] at hrightLt
      linarith [hsu.1, hsv.2, hn, hshift]
    · exact hnzero
    · have hnleInt : 1 ≤ n := by omega
      have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hnleInt
      have hshift : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      dsimp [period] at hrightLt
      linarith [hsv.1, hsu.2, hn, hshift]
  rw [hnzero, Int.cast_zero, zero_mul, add_zero] at hn
  apply Subtype.ext
  change left + (u : ℝ) * (right - left) =
    left + (v : ℝ) * (right - left) at hn
  nlinarith

/-- A selected lower outer gap has distinct endpoints. -/
theorem globalLowerOuterPath_endpoints_ne (g : F.GlobalLowerOuterGap) :
    ((F.globalLowerOuterPath g 0 : transportedTorus Phi) : R3) ≠
      ((F.globalLowerOuterPath g 1 : transportedTorus Phi) : R3) := by
  intro h
  have hp : (g, (0 : Fin 2)) = (g, (1 : Fin 2)) :=
    F.globalLowerEndpointEquiv.injective (by
      apply Subtype.ext
      simpa using h)
  have he : (0 : Fin 2) = 1 := congrArg Prod.snd hp
  norm_num at he

/-- A selected upper outer gap has distinct endpoints. -/
theorem globalUpperOuterPath_endpoints_ne (g : F.GlobalUpperOuterGap) :
    ((F.globalUpperOuterPath g 0 : transportedTorus Phi) : R3) ≠
      ((F.globalUpperOuterPath g 1 : transportedTorus Phi) : R3) := by
  intro h
  have hp : (g, (0 : Fin 2)) = (g, (1 : Fin 2)) :=
    F.globalUpperEndpointEquiv.injective (by
      apply Subtype.ext
      simpa using h)
  have he : (0 : Fin 2) = 1 := congrArg Prod.snd hp
  norm_num at he

/-- Every selected closed lower outer gap is an embedded arc. -/
theorem globalLowerOuterPath_injective (g : F.GlobalLowerOuterGap) :
    Function.Injective fun u ↦
      ((F.globalLowerOuterPath g u : transportedTorus Phi) : R3) := by
  apply F.gapPath_ambient_injective_of_endpoints_ne
  exact F.globalLowerOuterPath_endpoints_ne g

/-- Every selected closed upper outer gap is an embedded arc. -/
theorem globalUpperOuterPath_injective (g : F.GlobalUpperOuterGap) :
    Function.Injective fun u ↦
      ((F.globalUpperOuterPath g u : transportedTorus Phi) : R3) := by
  apply F.gapPath_ambient_injective_of_endpoints_ne
  exact F.globalUpperOuterPath_endpoints_ne g

/-- The endpoint map of the lower selected gaps is injective in ambient coordinates. -/
theorem globalLower_path_endpoint_injective :
    Function.Injective fun p : F.GlobalLowerOuterGap × Fin 2 ↦
      ((F.globalLowerOuterPath p.1 (finTwoUnitInterval p.2) :
        transportedTorus Phi) : R3) := by
  intro p q hpq
  apply F.globalLowerEndpointEquiv.injective
  apply Subtype.ext
  rw [F.globalLowerEndpointEquiv_val_eq_path_endpoint,
    F.globalLowerEndpointEquiv_val_eq_path_endpoint]
  exact hpq

/-- The endpoint map of the upper selected gaps is injective in ambient coordinates. -/
theorem globalUpper_path_endpoint_injective :
    Function.Injective fun p : F.GlobalUpperOuterGap × Fin 2 ↦
      ((F.globalUpperOuterPath p.1 (finTwoUnitInterval p.2) :
        transportedTorus Phi) : R3) := by
  intro p q hpq
  apply F.globalUpperEndpointEquiv.injective
  apply Subtype.ext
  rw [F.globalUpperEndpointEquiv_val_eq_path_endpoint,
    F.globalUpperEndpointEquiv_val_eq_path_endpoint]
  exact hpq

theorem gapPath_interior_not_mem_seam
    (g : F.GlobalOuterGap) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((F.gapPath g u : transportedTorus Phi) : R3) ∉
      superellipsoidTorusSeam Phi frame c R d := by
  intro hseam
  have hzero : windingLoopCutHeight frame d
      (G.outer.circle g.1.1).windingLoop (F.gapParameter g u) = 0 := by
    unfold windingLoopCutHeight
    exact sub_eq_zero.mpr hseam.2
  have hstrict := (F.excursion g).strict_side (F.gapParameter g u)
    (F.gapParameter_mem_Ioo g u hu0 hu1)
  cases hside : (F.excursion g).upper <;>
    simp only [hside, Bool.false_eq_true, if_false, if_true] at hstrict
  · exact (ne_of_lt hstrict) hzero
  · exact (ne_of_gt hstrict) hzero

/-- Both endpoints of every closed outer gap are seam points. -/
theorem gapPath_endpoint_mem_seam (g : F.GlobalOuterGap) (e : Fin 2) :
    ((F.gapPath g (finTwoUnitInterval e) : transportedTorus Phi) : R3) ∈
      superellipsoidTorusSeam Phi frame c R d := by
  have hcircle := F.gapPath_mem_outerCircle g (finTwoUnitInterval e)
  have hsection := G.outer.circle_mem_section g.1.1 hcircle
  refine ⟨⟨hsection.1, hsection.2⟩, ?_⟩
  change ((F.gapPath g (finTwoUnitInterval e) : transportedTorus Phi) : R3).ofLp
      (frame 2) = d
  have hheight : windingLoopCutHeight frame d
      (G.outer.circle g.1.1).windingLoop
        (F.gapParameter g (finTwoUnitInterval e)) = 0 := by
    fin_cases e
    · simpa [gapParameter] using (F.excursion g).left_crossing
    · simpa [gapParameter] using (F.excursion g).right_crossing
  unfold windingLoopCutHeight at hheight
  rw [F.gapPath_apply]
  exact sub_eq_zero.mp hheight

/-- Distinct closed outer gaps can meet only at their seam endpoints. -/
theorem gapPath_range_inter_subset_seam :
    Pairwise fun g h : F.GlobalOuterGap ↦
      Set.range (fun u ↦ ((F.gapPath g u : transportedTorus Phi) : R3)) ∩
          Set.range (fun u ↦ ((F.gapPath h u : transportedTorus Phi) : R3)) ⊆
        superellipsoidTorusSeam Phi frame c R d := by
  intro g h hgh x hx
  obtain ⟨u, rfl⟩ := hx.1
  obtain ⟨v, hv⟩ := hx.2
  by_cases hu0 : (u : ℝ) = 0
  · have hu : u = (0 : unitInterval) := Subtype.ext hu0
    subst u
    simpa only [finTwoUnitInterval_zero] using F.gapPath_endpoint_mem_seam g 0
  · by_cases hu1 : (u : ℝ) = 1
    · have hu : u = (1 : unitInterval) := Subtype.ext hu1
      subst u
      simpa only [finTwoUnitInterval_one] using F.gapPath_endpoint_mem_seam g 1
    · by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        have hend := F.gapPath_endpoint_mem_seam h 0
        have hend' : ((F.gapPath h 0 : transportedTorus Phi) : R3) ∈
            superellipsoidTorusSeam Phi frame c R d := by
          simpa only [finTwoUnitInterval_zero] using hend
        exact Eq.mp (congrArg
          (fun y : R3 ↦ y ∈ superellipsoidTorusSeam Phi frame c R d) hv) hend'
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          have hend := F.gapPath_endpoint_mem_seam h 1
          have hend' : ((F.gapPath h 1 : transportedTorus Phi) : R3) ∈
              superellipsoidTorusSeam Phi frame c R d := by
            simpa only [finTwoUnitInterval_one] using hend
          exact Eq.mp (congrArg
            (fun y : R3 ↦ y ∈ superellipsoidTorusSeam Phi frame c R d) hv) hend'
        · have hopen := F.openGapRanges_pairwise_disjoint hgh
          exfalso
          exact Set.disjoint_left.mp hopen
            ⟨u, ⟨hu0, hu1⟩, rfl⟩ ⟨v, ⟨hv0, hv1⟩, hv⟩

/-- No lower-gap seam endpoint is an interior point of any lower selected gap. -/
theorem globalLower_path_endpoint_ne_interior
    (g h : F.GlobalLowerOuterGap) (e : Fin 2) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((F.globalLowerOuterPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ≠
      ((F.globalLowerOuterPath h u : transportedTorus Phi) : R3) := by
  intro heq
  have hend : ((F.globalLowerOuterPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
    rw [← F.globalLowerEndpointEquiv_val_eq_path_endpoint]
    exact (F.globalLowerEndpointEquiv (g, e)).2
  exact F.gapPath_interior_not_mem_seam (F.lowerGapAsGlobalOuterGap h) u hu0 hu1
    (heq.symm ▸ hend)

/-- No upper-gap seam endpoint is an interior point of any upper selected gap. -/
theorem globalUpper_path_endpoint_ne_interior
    (g h : F.GlobalUpperOuterGap) (e : Fin 2) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((F.globalUpperOuterPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ≠
      ((F.globalUpperOuterPath h u : transportedTorus Phi) : R3) := by
  intro heq
  have hend : ((F.globalUpperOuterPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
    rw [← F.globalUpperEndpointEquiv_val_eq_path_endpoint]
    exact (F.globalUpperEndpointEquiv (g, e)).2
  exact F.gapPath_interior_not_mem_seam (F.upperGapAsGlobalOuterGap h) u hu0 hu1
    (heq.symm ▸ hend)

private theorem lowerGapAsGlobalOuterGap_injective :
    Function.Injective F.lowerGapAsGlobalOuterGap := by
  rintro ⟨i, g⟩ ⟨j, h⟩ hgh
  have hij : i = j := congrArg Sigma.fst hgh
  subst j
  let _ : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  have hgh' : g = h := by
    apply Subtype.ext
    apply ZMod.val_injective
    exact congrArg (fun x ↦ x.2.1) hgh
  exact Sigma.ext rfl (heq_of_eq hgh')

private theorem upperGapAsGlobalOuterGap_injective :
    Function.Injective F.upperGapAsGlobalOuterGap := by
  rintro ⟨i, g⟩ ⟨j, h⟩ hgh
  have hij : i = j := congrArg Sigma.fst hgh
  subst j
  let _ : NeZero (F.regular i.1).crossings.card :=
    ⟨(Finset.card_pos.mpr i.2).ne'⟩
  have hgh' : g = h := by
    apply Subtype.ext
    apply ZMod.val_injective
    exact congrArg (fun x ↦ x.2.1) hgh
  exact Sigma.ext rfl (heq_of_eq hgh')

/-- Distinct lower selected closed gaps are disjoint, including at their seam endpoints. -/
theorem globalLowerOuterPath_ranges_pairwise_disjoint :
    Pairwise fun g h : F.GlobalLowerOuterGap ↦
      Disjoint
        (Set.range fun u ↦
          ((F.globalLowerOuterPath g u : transportedTorus Phi) : R3))
        (Set.range fun u ↦
          ((F.globalLowerOuterPath h u : transportedTorus Phi) : R3)) := by
  intro g h hgh
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  by_cases hu0 : (u : ℝ) = 0
  · have hu : u = (0 : unitInterval) := Subtype.ext hu0
    subst u
    by_cases hv0 : (v : ℝ) = 0
    · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
      subst v
      have hp : (g, (0 : Fin 2)) = (h, (0 : Fin 2)) :=
        F.globalLower_path_endpoint_injective (by simpa using hv.symm)
      exact hgh (congrArg Prod.fst hp)
    · by_cases hv1 : (v : ℝ) = 1
      · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
        subst v
        have hp : (g, (0 : Fin 2)) = (h, (1 : Fin 2)) :=
          F.globalLower_path_endpoint_injective (by simpa using hv.symm)
        exact hgh (congrArg Prod.fst hp)
      · exact F.globalLower_path_endpoint_ne_interior g h 0 v hv0 hv1
          (by simpa using hv.symm)
  · by_cases hu1 : (u : ℝ) = 1
    · have hu : u = (1 : unitInterval) := Subtype.ext hu1
      subst u
      by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        have hp : (g, (1 : Fin 2)) = (h, (0 : Fin 2)) :=
          F.globalLower_path_endpoint_injective (by simpa using hv.symm)
        exact hgh (congrArg Prod.fst hp)
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          have hp : (g, (1 : Fin 2)) = (h, (1 : Fin 2)) :=
            F.globalLower_path_endpoint_injective (by simpa using hv.symm)
          exact hgh (congrArg Prod.fst hp)
        · exact F.globalLower_path_endpoint_ne_interior g h 1 v hv0 hv1
            (by simpa using hv.symm)
    · by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        exact F.globalLower_path_endpoint_ne_interior h g 0 u hu0 hu1
          (by simpa using hv)
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          exact F.globalLower_path_endpoint_ne_interior h g 1 u hu0 hu1
            (by simpa using hv)
        · have hbase : F.lowerGapAsGlobalOuterGap g ≠
              F.lowerGapAsGlobalOuterGap h := fun hbase ↦
            hgh (F.lowerGapAsGlobalOuterGap_injective hbase)
          have hopen := F.openGapRanges_pairwise_disjoint hbase
          apply Set.disjoint_left.mp hopen
          · exact ⟨u, ⟨hu0, hu1⟩, rfl⟩
          · exact ⟨v, ⟨hv0, hv1⟩, hv⟩

/-- Distinct upper selected closed gaps are disjoint, including at their seam endpoints. -/
theorem globalUpperOuterPath_ranges_pairwise_disjoint :
    Pairwise fun g h : F.GlobalUpperOuterGap ↦
      Disjoint
        (Set.range fun u ↦
          ((F.globalUpperOuterPath g u : transportedTorus Phi) : R3))
        (Set.range fun u ↦
          ((F.globalUpperOuterPath h u : transportedTorus Phi) : R3)) := by
  intro g h hgh
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  by_cases hu0 : (u : ℝ) = 0
  · have hu : u = (0 : unitInterval) := Subtype.ext hu0
    subst u
    by_cases hv0 : (v : ℝ) = 0
    · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
      subst v
      have hp : (g, (0 : Fin 2)) = (h, (0 : Fin 2)) :=
        F.globalUpper_path_endpoint_injective (by simpa using hv.symm)
      exact hgh (congrArg Prod.fst hp)
    · by_cases hv1 : (v : ℝ) = 1
      · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
        subst v
        have hp : (g, (0 : Fin 2)) = (h, (1 : Fin 2)) :=
          F.globalUpper_path_endpoint_injective (by simpa using hv.symm)
        exact hgh (congrArg Prod.fst hp)
      · exact F.globalUpper_path_endpoint_ne_interior g h 0 v hv0 hv1
          (by simpa using hv.symm)
  · by_cases hu1 : (u : ℝ) = 1
    · have hu : u = (1 : unitInterval) := Subtype.ext hu1
      subst u
      by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        have hp : (g, (1 : Fin 2)) = (h, (0 : Fin 2)) :=
          F.globalUpper_path_endpoint_injective (by simpa using hv.symm)
        exact hgh (congrArg Prod.fst hp)
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          have hp : (g, (1 : Fin 2)) = (h, (1 : Fin 2)) :=
            F.globalUpper_path_endpoint_injective (by simpa using hv.symm)
          exact hgh (congrArg Prod.fst hp)
        · exact F.globalUpper_path_endpoint_ne_interior g h 1 v hv0 hv1
            (by simpa using hv.symm)
    · by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        exact F.globalUpper_path_endpoint_ne_interior h g 0 u hu0 hu1
          (by simpa using hv)
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          exact F.globalUpper_path_endpoint_ne_interior h g 1 u hu0 hu1
            (by simpa using hv)
        · have hbase : F.upperGapAsGlobalOuterGap g ≠
              F.upperGapAsGlobalOuterGap h := fun hbase ↦
            hgh (F.upperGapAsGlobalOuterGap_injective hbase)
          have hopen := F.openGapRanges_pairwise_disjoint hbase
          apply Set.disjoint_left.mp hopen
          · exact ⟨u, ⟨hu0, hu1⟩, rfl⟩
          · exact ⟨v, ⟨hv0, hv1⟩, hv⟩

/-- Closed selected lower gaps cover exactly the active outer circles in the lower halfspace. -/
theorem iUnion_range_globalLowerOuterPath_eq :
    (⋃ g : F.GlobalLowerOuterGap,
      Set.range fun u ↦
        ((F.globalLowerOuterPath g u : transportedTorus Phi) : R3)) =
      (⋃ i : F.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
        lowerClosedHalfspace frame d := by
  ext x
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨g, u, rfl⟩
    exact ⟨Set.mem_iUnion.mpr
        ⟨g.1, F.gapPath_mem_outerCircle (F.lowerGapAsGlobalOuterGap g) u⟩,
      F.lowerGapPath_mem (F.lowerGapAsLowerGap g) u⟩
  · rintro ⟨hxCircle, hxLower⟩
    by_cases hxPlane : x.ofLp (frame 2) = d
    · have hxSeam : x ∈ superellipsoidTorusSeam Phi frame c R d := by
        simp only [superellipsoidTorusSeam, coordinateCuttingPlane,
          Set.mem_inter_iff, Set.mem_ofPred_eq]
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxCircle
        have hsection := G.outer.circle_mem_section i.1 hi
        exact ⟨⟨hsection.1, hsection.2⟩, hxPlane⟩
      let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
      let ge := F.globalLowerEndpointEquiv.symm p
      refine Set.mem_iUnion.mpr ⟨ge.1, ?_⟩
      refine ⟨finTwoUnitInterval ge.2, ?_⟩
      change ((F.globalLowerOuterPath ge.1 (finTwoUnitInterval ge.2) :
        transportedTorus Phi) : R3) = x
      rw [← F.globalLowerEndpointEquiv_val_eq_path_endpoint]
      exact congrArg Subtype.val (F.globalLowerEndpointEquiv.apply_symm_apply p)
    · have hxStrict : x ∈ F.activeStrictLowerCarrier := by
        change x.ofLp (frame 2) ≤ d at hxLower
        exact ⟨hxCircle, lt_of_le_of_ne hxLower hxPlane⟩
      rw [← F.iUnion_openLowerGapRange_eq_activeStrictLowerCarrier] at hxStrict
      obtain ⟨g, u, hu, hux⟩ := Set.mem_iUnion.mp hxStrict
      let _ : NeZero (F.regular g.1.1.1).crossings.card :=
        ⟨(Finset.card_pos.mpr g.1.1.2).ne'⟩
      let q : ZMod (F.regular g.1.1.1).crossings.card := g.1.2.1
      have hqval : q.val = g.1.2.1 := by
        dsimp [q]
        exact ZMod.val_natCast_of_lt g.1.2.2
      have hside : F.zmodGapSide g.1.1 q = false := by
        unfold zmodGapSide
        change (F.excursion ⟨g.1.1, ⟨q.val, ZMod.val_lt q⟩⟩).upper = false
        convert g.2 using 1
        have hfin : (⟨q.val, ZMod.val_lt q⟩ :
            Fin (F.regular g.1.1.1).crossings.card) = g.1.2 :=
          Fin.ext hqval
        have hgap : (⟨g.1.1, ⟨q.val, ZMod.val_lt q⟩⟩ : F.GlobalOuterGap) =
            g.1 := Sigma.ext rfl (heq_of_eq hfin)
        exact congrArg (fun k : F.GlobalOuterGap ↦ (F.excursion k).upper) hgap
      let gg : F.GlobalLowerOuterGap := ⟨g.1.1, ⟨q, hside⟩⟩
      refine Set.mem_iUnion.mpr ⟨gg, u, ?_⟩
      have hgg : F.lowerGapAsGlobalOuterGap gg = g.1 := by
        have hfin : (F.lowerGapAsGlobalOuterGap gg).2 = g.1.2 := by
          apply Fin.ext
          simpa only [gg, lowerGapAsGlobalOuterGap] using hqval
        exact Sigma.ext rfl (heq_of_eq hfin)
      change ((F.gapPath (F.lowerGapAsGlobalOuterGap gg) u :
        transportedTorus Phi) : R3) = x
      rw [hgg]
      exact hux

/-- Closed selected upper gaps cover exactly the active outer circles in the upper halfspace. -/
theorem iUnion_range_globalUpperOuterPath_eq :
    (⋃ g : F.GlobalUpperOuterGap,
      Set.range fun u ↦
        ((F.globalUpperOuterPath g u : transportedTorus Phi) : R3)) =
      (⋃ i : F.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
        upperClosedHalfspace frame d := by
  ext x
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨g, u, rfl⟩
    exact ⟨Set.mem_iUnion.mpr
        ⟨g.1, F.gapPath_mem_outerCircle (F.upperGapAsGlobalOuterGap g) u⟩,
      F.upperGapPath_mem (F.upperGapAsUpperGap g) u⟩
  · rintro ⟨hxCircle, hxUpper⟩
    by_cases hxPlane : x.ofLp (frame 2) = d
    · have hxSeam : x ∈ superellipsoidTorusSeam Phi frame c R d := by
        simp only [superellipsoidTorusSeam, coordinateCuttingPlane,
          Set.mem_inter_iff, Set.mem_ofPred_eq]
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxCircle
        have hsection := G.outer.circle_mem_section i.1 hi
        exact ⟨⟨hsection.1, hsection.2⟩, hxPlane⟩
      let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
      let ge := F.globalUpperEndpointEquiv.symm p
      refine Set.mem_iUnion.mpr ⟨ge.1, ?_⟩
      refine ⟨finTwoUnitInterval ge.2, ?_⟩
      change ((F.globalUpperOuterPath ge.1 (finTwoUnitInterval ge.2) :
        transportedTorus Phi) : R3) = x
      rw [← F.globalUpperEndpointEquiv_val_eq_path_endpoint]
      exact congrArg Subtype.val (F.globalUpperEndpointEquiv.apply_symm_apply p)
    · have hxStrict : x ∈ F.activeStrictUpperCarrier := by
        change d ≤ x.ofLp (frame 2) at hxUpper
        exact ⟨hxCircle, lt_of_le_of_ne hxUpper (Ne.symm hxPlane)⟩
      rw [← F.iUnion_openUpperGapRange_eq_activeStrictUpperCarrier] at hxStrict
      obtain ⟨g, u, hu, hux⟩ := Set.mem_iUnion.mp hxStrict
      let _ : NeZero (F.regular g.1.1.1).crossings.card :=
        ⟨(Finset.card_pos.mpr g.1.1.2).ne'⟩
      let q : ZMod (F.regular g.1.1.1).crossings.card := g.1.2.1
      have hqval : q.val = g.1.2.1 := by
        dsimp [q]
        exact ZMod.val_natCast_of_lt g.1.2.2
      have hz : F.zmodGapSide g.1.1 q = true := by
        unfold zmodGapSide
        change (F.excursion ⟨g.1.1, ⟨q.val, ZMod.val_lt q⟩⟩).upper = true
        convert g.2 using 1
        have hfin : (⟨q.val, ZMod.val_lt q⟩ :
            Fin (F.regular g.1.1.1).crossings.card) = g.1.2 :=
          Fin.ext hqval
        have hgap : (⟨g.1.1, ⟨q.val, ZMod.val_lt q⟩⟩ : F.GlobalOuterGap) =
            g.1 := Sigma.ext rfl (heq_of_eq hfin)
        exact congrArg (fun k : F.GlobalOuterGap ↦ (F.excursion k).upper) hgap
      have hside : (F.upperSideData g.1.1).side q = false := by
        simp [upperSideData, hz]
      let gg : F.GlobalUpperOuterGap := ⟨g.1.1, ⟨q, hside⟩⟩
      refine Set.mem_iUnion.mpr ⟨gg, u, ?_⟩
      have hgg : F.upperGapAsGlobalOuterGap gg = g.1 := by
        have hfin : (F.upperGapAsGlobalOuterGap gg).2 = g.1.2 := by
          apply Fin.ext
          simpa only [gg, upperGapAsGlobalOuterGap] using hqval
        exact Sigma.ext rfl (heq_of_eq hfin)
      change ((F.gapPath (F.upperGapAsGlobalOuterGap gg) u :
        transportedTorus Phi) : R3) = x
      rw [hgg]
      exact hux

end OuterCircleTransverseHeightCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
