import Submission.Coarea.OrientedBoundarySelection
import Submission.SardMoreira.Planar

/-!
# Outer-boundary selection regular on all transported-torus faces

The oriented box-shell coordinate along the knot is only Lipschitz, while each of the six signed
transported-torus face lifts is smooth.  We extend the Lipschitz coarea selector so that it avoids
an additional null set, and take that set to be the finite union of all face critical values.
This changes neither the knot first moment nor its boundary-fiber count, so the original `80D`
bound is retained exactly.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Submission.Coarea

/-- A Lipschitz coarea level can avoid an additional prescribed null set without changing its
fiber-count estimate. -/
theorem exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact_avoiding
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ y ∈ Ioc a b,
      y ∉ f '' lipschitzExceptionalSet f ∧ y ∉ N ∧
      (fiberSet f s y).Finite ∧
      (fiberCount f s y : ℝ≥0∞) ≤
        (∫⁻ x in s, ENNReal.ofReal |deriv f x|) /
          ENNReal.ofReal (b - a) := by
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover, hmoment⟩ :=
    exists_countableBranchFiberMass_lintegral_eq_of_continuous
      hf.continuous hs.measurableSet
  have hpieceRegular (n : ℕ) {x : ℝ} (hx : x ∈ pieces n) :
      x ∈ differentiableRegularSet f := by
    have hxunion : x ∈ ⋃ n, pieces n := mem_iUnion.mpr ⟨n, hx⟩
    rw [hcover] at hxunion
    exact hxunion.2
  have hnull : volume (f '' lipschitzExceptionalSet f ∪ N) = 0 :=
    measure_union_null (volume_image_lipschitzExceptionalSet_eq_zero hf) hN
  obtain ⟨y, hyIoc, hyexceptional, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab
      (measurable_countableBranchFiberMass f (deriv f) pieces hmeas
        (fun n x hx ↦ (hpieceRegular n hx).1.hasDerivAt.hasDerivWithinAt)
        hinj).aemeasurable
      hmoment.le hnull
  have hyLipschitzExceptional : y ∉ f '' lipschitzExceptionalSet f :=
    fun hy ↦ hyexceptional (Or.inl hy)
  have hyN : y ∉ N := fun hy ↦ hyexceptional (Or.inr hy)
  have hyRegular (x : ℝ) (hxy : f x = y) : x ∈ differentiableRegularSet f := by
    by_contra hx
    have hxExceptional : x ∈ lipschitzExceptionalSet f := by
      rw [← compl_differentiableRegularSet]
      exact hx
    exact hyLipschitzExceptional ⟨x, hxExceptional, hxy⟩
  have hfiber : fiberSet f (⋃ n, pieces n) y = fiberSet f s y := by
    ext x
    simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxpieces, hxy⟩
      have hxsr : x ∈ s ∩ differentiableRegularSet f := by
        rw [← hcover]
        exact hxpieces
      exact ⟨hxsr.1, hxy⟩
    · rintro ⟨hxs, hxy⟩
      refine ⟨?_, hxy⟩
      rw [hcover]
      exact ⟨hxs, hyRegular x hxy⟩
  have hmassEnc : countableBranchFiberMass f pieces y =
      ((fiberSet f s y).encard : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          ((fiberSet f (⋃ n, pieces n) y).encard : ℝ≥0∞) :=
        countableBranchFiberMass_eq_encard hf.continuous pieces hmeas hdisj hinj y
      _ = ((fiberSet f s y).encard : ℝ≥0∞) := by rw [hfiber]
  have hright_ne :
      (∫⁻ x in s, ENNReal.ofReal |deriv f x|) /
          ENNReal.ofReal (b - a) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact lintegral_abs_deriv_ne_top_of_lipschitz_of_isCompact hf hs
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hmass_ne : countableBranchFiberMass f pieces y ≠ ⊤ :=
    ne_top_of_le_ne_top hright_ne hybound
  have hencard_ne : (fiberSet f s y).encard ≠ ⊤ := by
    rw [← ENat.toENNReal_ne_top, ← hmassEnc]
    exact hmass_ne
  have hfinite : (fiberSet f s y).Finite := encard_ne_top_iff.mp hencard_ne
  have hfinitePieces : (fiberSet f (⋃ n, pieces n) y).Finite := by
    rw [hfiber]
    exact hfinite
  have hmassCount : countableBranchFiberMass f pieces y =
      (fiberCount f s y : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          (fiberCount f (⋃ n, pieces n) y : ℝ≥0∞) :=
        countableBranchFiberMass_eq_fiberCount hf.continuous pieces hmeas hdisj hinj y
          hfinitePieces
      _ = (fiberCount f s y : ℝ≥0∞) := by
        change ((fiberSet f (⋃ n, pieces n) y).ncard : ℝ≥0∞) =
          ((fiberSet f s y).ncard : ℝ≥0∞)
        rw [hfiber]
  rw [hmassCount] at hybound
  exact ⟨y, hyIoc, hyLipschitzExceptional, hyN, hfinite, hybound⟩

end Submission.Coarea

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.SurfaceRegularValue

/-- Oriented-shell selector avoiding an arbitrary null set. -/
theorem exists_orientedShellRegularValue_fiberCount_le_integral_of_isCompact_avoiding
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {a b : ℝ} (hab : a < b)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ y ∈ Ioc a b,
      y ∉ (orientedShellParameter K frame c) ''
        Submission.Coarea.lipschitzExceptionalSet
          (orientedShellParameter K frame c) ∧
      y ∉ N ∧
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c) s y).Finite ∧
      (Submission.Coarea.fiberCount (orientedShellParameter K frame c) s y : ℝ≥0∞) ≤
        (∫⁻ t in s, ENNReal.ofReal
          |deriv (orientedShellParameter K frame c) t|) /
            ENNReal.ofReal (b - a) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_orientedShellParameter K frame c
  exact
    Submission.Coarea.exists_lipschitzRegularValue_fiberCount_le_integral_of_isCompact_avoiding
      hC hs hab hN

/-- Outer oriented-box boundary selection with the usual distortion bound, while avoiding an
arbitrary additional null set of scale values. -/
theorem exists_orientedOuterBoundary_count_le_distortion_avoiding
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hfinite : distortion K ≠ ⊤) {N : Set ℝ} (hN : volume N = 0) :
    ∃ y ∈ Ioc r ((1 + ε) * r),
      y ∉ (orientedShellParameter K frame c) ''
        Submission.Coarea.lipschitzExceptionalSet
          (orientedShellParameter K frame c) ∧
      y ∉ N ∧
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite ∧
      (orientedBoundaryCount K frame c
        (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
          ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
  have houter : 0 < (1 + ε) * r := mul_pos (by linarith) hr
  have hwidth : (1 + ε) * r - r = ε * r := by ring
  obtain ⟨y, hy, hyExceptional, hyN, hfiniteCompact, hybound⟩ :=
    exists_orientedShellRegularValue_fiberCount_le_integral_of_isCompact_avoiding
      K frame c
        (isCompact_closedOrientedBoxParameters K frame c ((1 + ε) * r))
        (show r < (1 + ε) * r by nlinarith) hN
  have hsub :
      Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (Ico (0 : ℝ) (2 * Real.pi)) y ⊆
        Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y := by
    intro t ht
    rw [Submission.Coarea.fiberSet] at ht ⊢
    rcases ht with ⟨htIco, htlevel⟩
    refine ⟨⟨⟨htIco.1, htIco.2.le⟩, ?_⟩, htlevel⟩
    change orientedBoxGauge frame c (K.curve t) ≤ (1 + ε) * r
    change orientedBoxGauge frame c (K.curve t) = y at htlevel
    rw [htlevel]
    exact hy.2
  have hfiniteHalfOpen :
      (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
        (Ico (0 : ℝ) (2 * Real.pi)) y).Finite :=
    hfiniteCompact.subset hsub
  refine ⟨y, hy, hyExceptional, hyN, hfiniteHalfOpen, ?_⟩
  have hcount :
      (orientedBoundaryCount K frame c
          (Ico (0 : ℝ) (2 * Real.pi)) y : ℝ≥0∞) ≤
        (Submission.Coarea.fiberCount (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y : ℝ≥0∞) := by
    change ((Submission.Coarea.fiberSet (orientedShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) y).ncard : ℝ≥0∞) ≤
        ((Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (closedOrientedBoxParameters K frame c ((1 + ε) * r)) y).ncard : ℝ≥0∞)
    exact_mod_cast Set.ncard_le_ncard hsub hfiniteCompact
  refine hcount.trans (hybound.trans ?_)
  calc
    (∫⁻ t in closedOrientedBoxParameters K frame c ((1 + ε) * r),
        ENNReal.ofReal |deriv (orientedShellParameter K frame c) t|) /
          ENNReal.ofReal ((1 + ε) * r - r) ≤
        ENNReal.ofReal (10 * ((1 + ε) * r) * (distortion K).toReal) /
          ENNReal.ofReal ((1 + ε) * r - r) := by
      exact ENNReal.div_le_div
        (lintegral_abs_deriv_orientedShellParameter_closedParameters_le
          K houter hfinite) le_rfl
    _ = ENNReal.ofReal (10 * (1 + 1 / ε) * (distortion K).toReal) := by
      rw [hwidth]
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hε hr)]
      congr 1
      field_simp [ne_of_gt hε, ne_of_gt hr]
      ring

/-- The selected outer scale, its knot-boundary count, and simultaneous regularity of all six
signed transported-torus face lifts. -/
structure FacewiseRegularOuterBoundarySelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  level : ℝ
  level_mem : level ∈ Ioc r ((8 / 7) * r)
  knotNonexceptional :
    level ∉ (orientedShellParameter K frame c) ''
      Submission.Coarea.lipschitzExceptionalSet
        (orientedShellParameter K frame c)
  knotFiberFinite :
    (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) level).Finite
  knotBoundaryCount_le :
    (orientedBoundaryCount K frame c
      (Ico (0 : ℝ) (2 * Real.pi)) level : ℝ≥0∞) ≤
        ENNReal.ofReal (80 * (distortion K).toReal)
  facewiseRegular : FacewiseRegularValue Phi frame c level

/-- Choose the outer oriented box with the exact existing `80D` knot count and with all six
transported-torus face lifts regular at the same scale. -/
theorem exists_facewiseRegularOuterBoundarySelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    Nonempty (FacewiseRegularOuterBoundarySelection K Phi frame c r) := by
  have hfaceSard (face : Fin 3 × Bool) :
      CriticalValuesNull (signedOrientedFaceLift Phi frame c face) :=
    criticalValuesNull_of_sardMoreiraConclusion
      (planarSardTheorem _ (signedOrientedFaceLift_contDiff Phi frame c face))
  have hfaceNull : volume (orientedFaceCriticalValues Phi frame c) = 0 :=
    orientedFaceCriticalValues_null Phi frame c hfaceSard
  obtain ⟨y, hy, hyKexceptional, hyFaceExceptional, hfiniteFiber, hybound⟩ :=
    exists_orientedOuterBoundary_count_le_distortion_avoiding
      K frame c hr (show (0 : ℝ) < 1 / 7 by norm_num) hfinite hfaceNull
  have hscale : (8 / 7 : ℝ) = 1 + 1 / 7 := by norm_num
  have hconstant : (10 * (1 + 1 / ((1 : ℝ) / 7)) : ℝ) = 80 := by norm_num
  refine ⟨{
    level := y
    level_mem := ?_
    knotNonexceptional := hyKexceptional
    knotFiberFinite := hfiniteFiber
    knotBoundaryCount_le := ?_
    facewiseRegular :=
      (facewiseRegularValue_iff_not_mem Phi frame c y).2 hyFaceExceptional
  }⟩
  · rw [hscale]
    exact hy
  · rw [hconstant] at hybound
    exact hybound

end Submission.PardonDistortion
