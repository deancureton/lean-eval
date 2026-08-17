import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Closed inward-gap coverage on the cutting circles

This is the cutting-circle analogue of `SuperellipsoidOuterClosedGapPackage`.  It upgrades the
strict inward-gap facts to an exact equality for the closed inward part of every active cutting
circle, including the seam endpoints.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

/-- Every nonzero polynomial-difference parameter lies in an integer translate of one cyclic
successor interval. -/
theorem exists_cutCircleCyclic_interval_of_ne_zero
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hR : 0 ≤ R)
    (hne : (G.cutCircleSeamCrossings j).Nonempty) {t : ℝ}
    (htne : G.cutCircleOuterPolynomialDifference j t ≠ 0) :
    ∃ (i : Fin (G.cutCircleSeamCrossings j).card) (n : ℤ),
      t ∈ Ioo
        (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi))
        (G.cutCircleCyclicRight j hne i + (n : ℝ) * (2 * Real.pi)) := by
  let u : ℝ := toIcoMod Real.two_pi_pos 0 t
  let k : ℤ := toIcoDiv Real.two_pi_pos 0 t
  have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 t
  have hukt : u + (k : ℝ) * (2 * Real.pi) = t :=
    toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 t
  have hune : G.cutCircleOuterPolynomialDifference j u ≠ 0 := by
    intro huzero
    apply htne
    calc
      G.cutCircleOuterPolynomialDifference j t =
          G.cutCircleOuterPolynomialDifference j
            (u + (k : ℝ) * (2 * Real.pi)) := by rw [hukt]
      _ = G.cutCircleOuterPolynomialDifference j u :=
        (G.periodic_cutCircleOuterPolynomialDifference j).int_mul k u
      _ = 0 := huzero
  have hbase : ∃ (i : Fin (G.cutCircleSeamCrossings j).card) (n : ℤ),
      u ∈ Ioo
        (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi))
        (G.cutCircleCyclicRight j hne i + (n : ℝ) * (2 * Real.pi)) := by
    by_cases hbelow : ∃ a ∈ G.cutCircleSeamCrossings j, a < u
    · obtain ⟨a, haC, hau, hmax⟩ :=
        (G.cutCircleSeamCrossings j).exists_next_left hbelow
      let i : Fin (G.cutCircleSeamCrossings j).card :=
        ((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).symm ⟨a, haC⟩
      have hiEq : G.cutCircleSortedCrossing j i = a :=
        congrArg Subtype.val
          (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).apply_symm_apply ⟨a, haC⟩)
      by_cases hi : i.1 + 1 < (G.cutCircleSeamCrossings j).card
      · refine ⟨i, 0, ?_⟩
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [hiEq]
        constructor
        · exact hau
        · unfold cutCircleCyclicRight
          simp only [hi, ↓reduceDIte]
          apply lt_of_not_ge
          intro hnext
          have hnextNe : G.cutCircleSortedCrossing j ⟨i.1 + 1, hi⟩ ≠ u := by
            intro heq
            apply hune
            rw [← heq]
            exact sub_eq_zero.mpr <|
              (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mp
                ((G.mem_cutCircleSeamCrossings_iff j _).mp
                  (G.cutCircleSortedCrossing_mem j _)).2.1.2
          have hnextLt : G.cutCircleSortedCrossing j ⟨i.1 + 1, hi⟩ < u :=
            lt_of_le_of_ne hnext hnextNe
          have hle := hmax _ (G.cutCircleSortedCrossing_mem j _) hnextLt
          have hstrict := G.strictMono_cutCircleSortedCrossing j
            (show i < (⟨i.1 + 1, hi⟩ : Fin _) from
              Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.1))
          rw [hiEq] at hstrict
          exact (not_lt_of_ge hle) hstrict
      · refine ⟨i, 0, ?_⟩
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [hiEq]
        constructor
        · exact hau
        · unfold cutCircleCyclicRight
          simp only [hi, ↓reduceDIte]
          have hfirst0 := G.cutCircleSortedCrossing_mem_period j
            ⟨0, Finset.card_pos.mpr hne⟩
          exact hu.2.trans_le (by linarith [hfirst0.1])
    · let i : Fin (G.cutCircleSeamCrossings j).card :=
        ⟨(G.cutCircleSeamCrossings j).card - 1,
          Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩
      have hi : ¬i.1 + 1 < (G.cutCircleSeamCrossings j).card := by
        dsimp [i]
        omega
      have hfirstNotLt : ¬G.cutCircleSortedCrossing j
          ⟨0, Finset.card_pos.mpr hne⟩ < u := by
        intro h
        exact hbelow ⟨_, G.cutCircleSortedCrossing_mem j _, h⟩
      have hfirstNe : G.cutCircleSortedCrossing j
          ⟨0, Finset.card_pos.mpr hne⟩ ≠ u := by
        intro heq
        apply hune
        rw [← heq]
        exact sub_eq_zero.mpr <|
          (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mp
            ((G.mem_cutCircleSeamCrossings_iff j _).mp
              (G.cutCircleSortedCrossing_mem j _)).2.1.2
      have huFirst : u < G.cutCircleSortedCrossing j
          ⟨0, Finset.card_pos.mpr hne⟩ :=
        lt_of_le_of_ne (le_of_not_gt hfirstNotLt) hfirstNe.symm
      refine ⟨i, -1, ?_⟩
      constructor
      · have hilastP := G.cutCircleSortedCrossing_mem_period j i
        norm_num
        linarith [hilastP.2, hu.1]
      · unfold cutCircleCyclicRight
        simp only [hi, ↓reduceDIte]
        norm_num
        simpa using huFirst
  obtain ⟨i, n, hn⟩ := hbase
  refine ⟨i, n + k, ?_⟩
  constructor
  · calc
      G.cutCircleSortedCrossing j i + ((n + k : ℤ) : ℝ) * (2 * Real.pi) =
          (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi)) +
            (k : ℝ) * (2 * Real.pi) := by push_cast; ring
      _ < u + (k : ℝ) * (2 * Real.pi) := by
        simpa [add_comm] using add_lt_add_right hn.1 ((k : ℝ) * (2 * Real.pi))
      _ = t := hukt
  · calc
      t = u + (k : ℝ) * (2 * Real.pi) := hukt.symm
      _ < (G.cutCircleCyclicRight j hne i + (n : ℝ) * (2 * Real.pi)) +
          (k : ℝ) * (2 * Real.pi) := by
        simpa [add_comm] using add_lt_add_right hn.2 ((k : ℝ) * (2 * Real.pi))
      _ = G.cutCircleCyclicRight j hne i +
          ((n + k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring

namespace CutCircleTransverseCyclicOrderFamily

variable (F : CutCircleTransverseCyclicOrderFamily G)

/-- The closed inward excursions cover exactly the inward part of the active cutting circles. -/
theorem iUnion_range_globalInwardExcursionPath_eq
    (hR : 0 < R) :
    (⋃ g : F.GlobalInwardGap,
      Set.range fun u ↦
        ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3)) =
      (⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
        closedSuperellipsoidBody frame c R := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, u, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨Set.mem_iUnion.mpr
      ⟨g.1, F.globalInwardExcursionPath_mem_cutCircle g u⟩, ?_⟩
    by_cases hu0 : (u : ℝ) = 0
    · have hu : u = (0 : unitInterval) := Subtype.ext hu0
      subst u
      have hseam : ((F.globalInwardExcursionPath g 0 : transportedTorus Phi) : R3) ∈
          superellipsoidTorusSeam Phi frame c R d := by
        have hval := F.globalEndpointEquiv_val_eq_path_endpoint g (0 : Fin 2)
        rw [finTwoUnitInterval_zero] at hval
        exact hval ▸ (F.globalEndpointEquiv (g, (0 : Fin 2))).2
      change superellipsoidGauge frame c _ ≤ R
      exact hseam.1.2.le
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = (1 : unitInterval) := Subtype.ext hu1
        subst u
        have hseam : ((F.globalInwardExcursionPath g 1 : transportedTorus Phi) : R3) ∈
            superellipsoidTorusSeam Phi frame c R d := by
          have hval := F.globalEndpointEquiv_val_eq_path_endpoint g (1 : Fin 2)
          rw [finTwoUnitInterval_one] at hval
          exact hval ▸ (F.globalEndpointEquiv (g, (1 : Fin 2))).2
        change superellipsoidGauge frame c _ ≤ R
        exact hseam.1.2.le
      · change superellipsoidGauge frame c _ ≤ R
        exact (F.globalInwardExcursionPath_mem_body g u hu0 hu1).le
  · rintro ⟨hxActive, hxClosed⟩
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hxActive
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    rw [(G.cut.circle j.1).parametrization] at hz
    rw [← hz] at hxClosed ⊢
    let delta := G.cutCircleOuterPolynomialDifference j.1 t
    by_cases hzero : delta = 0
    · have hseam : ((G.cut.circle j.1).windingLoop.curve t : R3) ∈
          superellipsoidTorusSeam Phi frame c R d :=
        (G.cutCircleOuterPolynomialDifference_eq_zero_iff_seam j.1 hR.le t).mp hzero
      let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨_, hseam⟩
      let ge := F.globalEndpointEquiv.symm p
      refine Set.mem_iUnion.mpr ⟨ge.1, finTwoUnitInterval ge.2, ?_⟩
      calc
        ((F.globalInwardExcursionPath ge.1 (finTwoUnitInterval ge.2) :
            transportedTorus Phi) : R3) =
            (F.globalEndpointEquiv (ge.1, ge.2)).1 :=
          (F.globalEndpointEquiv_val_eq_path_endpoint ge.1 ge.2).symm
        _ = (p : R3) := congrArg Subtype.val
          (F.globalEndpointEquiv.apply_symm_apply p)
        _ = ((G.cut.circle j.1).windingLoop.curve t : R3) := rfl
    · have hgaugeNe : superellipsoidGauge frame c
          ((G.cut.circle j.1).windingLoop.curve t : R3) ≠ R := by
        intro heq
        apply hzero
        exact sub_eq_zero.mpr <|
          (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp heq
      have hbody : ((G.cut.circle j.1).windingLoop.curve t : R3) ∈
          superellipsoidBody frame c R := by
        exact lt_of_le_of_ne hxClosed hgaugeNe
      have hneg : delta < 0 :=
        (G.cutCircleOuterPolynomialDifference_neg_iff_body j.1 hR t).mpr hbody
      obtain ⟨i, n, hti⟩ := G.exists_cutCircleCyclic_interval_of_ne_zero
        j.1 hR.le (F.order j).crossings_nonempty hzero
      let q : ZMod (G.cutCircleSeamCrossings j.1).card := i.1
      let _ : NeZero (G.cutCircleSeamCrossings j.1).card :=
        ⟨(Finset.card_pos.mpr (F.order j).crossings_nonempty).ne'⟩
      have hqval : q.val = i.1 := by
        exact ZMod.val_natCast_of_lt i.2
      let left := G.cutCircleSortedCrossing j.1 i
      let right := G.cutCircleCyclicRight j.1 (F.order j).crossings_nonempty i
      let s := t - (n : ℝ) * (2 * Real.pi)
      have hs : s ∈ Ioo left right := by
        dsimp [s, left, right]
        constructor <;> linarith [hti.1, hti.2]
      have hdeltaS : G.cutCircleOuterPolynomialDifference j.1 s = delta := by
        have hp := (G.periodic_cutCircleOuterPolynomialDifference j.1).int_mul n s
        rw [show s + (n : ℝ) * (2 * Real.pi) = t by dsimp [s]; ring] at hp
        exact hp.symm
      have hsideEq :
          G.cutCircleZModGapSide j.1 (F.order j).crossings_nonempty q =
            G.cutCircleCyclicGapSide j.1 (F.order j).crossings_nonempty i := by
        unfold cutCircleZModGapSide
        congr 1
        apply Fin.ext
        exact hqval
      have hside : G.cutCircleZModGapSide j.1 (F.order j).crossings_nonempty q = false := by
        have hstrict := G.cutCircleCyclicGapSide_strict j.1 hR.le
          (F.order j).crossings_nonempty i s (by simpa [left, right] using hs)
        rw [← hsideEq] at hstrict
        rw [hdeltaS] at hstrict
        by_cases hb : G.cutCircleZModGapSide j.1
            (F.order j).crossings_nonempty q = false
        · exact hb
        · have hbtrue : G.cutCircleZModGapSide j.1
              (F.order j).crossings_nonempty q = true :=
            Bool.eq_true_of_not_eq_false hb
          rw [hbtrue] at hstrict
          exact False.elim ((not_lt_of_ge hneg.le) hstrict)
      let g : F.GlobalInwardGap := ⟨j, ⟨q, by
        simpa [CutCircleTransverseCyclicOrder.sideData] using hside⟩⟩
      let u : unitInterval := ⟨(s - left) / (right - left), by
        have hlr := G.cutCircleSortedCrossing_lt_cyclicRight j.1
          (F.order j).crossings_nonempty i
        constructor
        · exact div_nonneg (sub_nonneg.mpr hs.1.le) (sub_nonneg.mpr hlr.le)
        · rw [div_le_one (sub_pos.mpr hlr)]
          linarith [hs.2]⟩
      refine Set.mem_iUnion.mpr ⟨g, u, ?_⟩
      change ((G.cut.circle j.1).windingLoop.curve
          (F.globalInwardExcursionParameter g u) : R3) =
        ((G.cut.circle j.1).windingLoop.curve t : R3)
      have hindex : F.globalGapFinIndex g = i := by
        apply Fin.ext
        exact hqval
      have hparam : F.globalInwardExcursionParameter g u = s := by
        rw [globalInwardExcursionParameter, hindex]
        dsimp [u, left, right]
        have hlr := G.cutCircleSortedCrossing_lt_cyclicRight j.1
          (F.order j).crossings_nonempty i
        field_simp [ne_of_gt (sub_pos.mpr hlr)]
        ring
      rw [hparam]
      have hcurve : (G.cut.circle j.1).windingLoop.curve s =
          (G.cut.circle j.1).windingLoop.curve t := by
        calc
          (G.cut.circle j.1).windingLoop.curve s =
              (G.cut.circle j.1).windingLoop.curve
                (s + (n : ℝ) * (2 * Real.pi)) :=
            ((G.cut.circle j.1).windingLoop.periodic_curve.int_mul n s).symm
          _ = (G.cut.circle j.1).windingLoop.curve t := by
            congr 1
            dsimp [s]
            ring
      exact congrArg Subtype.val hcurve

end CutCircleTransverseCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
