import Submission.Topology.SmoothLoopCarrier
import Submission.Coarea.PlaneSlice

/-!
# Cutting planes regular for a knot and two smooth carrier loops

The first-moment coarea estimate can avoid any additional null set without changing its bound.
We apply this to the union of the critical values of the two smooth carrier-loop long
coordinates.  The resulting cutting height is regular for the knot and both loops, while the
knot fiber retains the original `5(1+ε⁻¹)D = 40D` estimate.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Submission.Coarea

/-! ## Coarea while avoiding an additional null set -/

/-- The compact-set one-dimensional coarea selector can simultaneously avoid any prescribed
null set, without changing its fiber-count estimate. -/
theorem exists_regularValue_fiberCount_le_integral_of_isCompact_avoiding
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s) (hsmooth : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) {N : Set ℝ} (hN : volume N = 0) :
    ∃ y ∈ Ioc a b, IsRegularValue f y ∧ y ∉ N ∧
      (fiberCount f s y : ℝ≥0∞) ≤
        (∫⁻ x in s, ENNReal.ofReal |deriv f x|) / ENNReal.ofReal (b - a) := by
  have hsmeas : MeasurableSet s := hs.measurableSet
  obtain ⟨pieces, hmeas, hdisj, hinj, hcover, hmoment⟩ :=
    exists_countableBranchFiberMass_lintegral_eq hsmooth hsmeas
  have hcriticalUnion : volume (criticalValues f ∪ N) = 0 :=
    measure_union_null (volume_criticalValues_eq_zero hsmooth) hN
  obtain ⟨y, hyIoc, hyexceptional, hybound⟩ :=
    exists_Ioc_notMem_le_of_lintegral_le hab
      (measurable_countableBranchFiberMass f (deriv f) pieces hmeas
        (fun n x hx ↦ (hsmooth.differentiable_one x).hasDerivAt.hasDerivWithinAt)
        hinj).aemeasurable
      hmoment.le hcriticalUnion
  have hycrit : y ∉ criticalValues f := fun hy ↦ hyexceptional (Or.inl hy)
  have hyN : y ∉ N := fun hy ↦ hyexceptional (Or.inr hy)
  have hyreg : IsRegularValue f y := not_mem_criticalValues_iff.mp hycrit
  have hfiber : fiberSet f (⋃ n, pieces n) y = fiberSet f s y := by
    ext x
    simp only [fiberSet, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxpieces, hfx⟩
      have hxsr : x ∈ s ∩ regularSet f := by
        rw [← hcover]
        exact hxpieces
      exact ⟨hxsr.1, hfx⟩
    · rintro ⟨hxs, hfx⟩
      have hxreg : x ∈ regularSet f := hyreg x hfx
      refine ⟨?_, hfx⟩
      rw [hcover]
      exact ⟨hxs, hxreg⟩
  have hfiniteS : (fiberSet f s y).Finite :=
    finite_fiberSet_of_isCompact_of_regularValue hs hsmooth hyreg
  have hfinitePieces : (fiberSet f (⋃ n, pieces n) y).Finite := by
    rw [hfiber]
    exact hfiniteS
  have hmass : countableBranchFiberMass f pieces y = (fiberCount f s y : ℝ≥0∞) := by
    calc
      countableBranchFiberMass f pieces y =
          (fiberCount f (⋃ n, pieces n) y : ℝ≥0∞) :=
        countableBranchFiberMass_eq_fiberCount hsmooth.continuous pieces hmeas hdisj hinj y
          hfinitePieces
      _ = (fiberCount f s y : ℝ≥0∞) := by
        change ((fiberSet f (⋃ n, pieces n) y).ncard : ℝ≥0∞) =
          ((fiberSet f s y).ncard : ℝ≥0∞)
        rw [hfiber]
  rw [hmass] at hybound
  exact ⟨y, hyIoc, hyreg, hyN, hybound⟩

end Submission.Coarea

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-! ## Long coordinates of smooth carrier loops -/

/-- The cutting-plane coordinate along a winding loop on the transported torus. -/
def windingLoopLongCoordinate {Phi : AmbientIsotopy}
    {a : Set R3} (frame : Equiv.Perm (Fin 3))
    (L : TransportedWindingLoop Phi (transportedTorusPart Phi a)) (t : ℝ) : ℝ :=
  (L.curve t : R3).ofLp (frame 2)

lemma contDiff_windingLoopLongCoordinate {Phi : AmbientIsotopy}
    {a : Set R3} (frame : Equiv.Perm (Fin 3))
    (L : TransportedWindingLoop Phi (transportedTorusPart Phi a))
    (hL : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (L.curve t : R3))) :
    ContDiff ℝ (⊤ : ℕ∞) (windingLoopLongCoordinate frame L) := by
  exact (coordinateCLM (frame 2)).contDiff.comp hL

/-- Output of a cutting-plane selection that is regular for the knot and both loops of a fixed
smooth carrier witness. -/
structure SmoothCarrierPlaneSelection (K : Knot) {Phi : AmbientIsotopy}
    {a : Set R3} (frame : Equiv.Perm (Fin 3)) (c : R3) (s : Set ℝ) (r D : ℝ)
    (W : SmoothLoopCarrierWitness Phi a) where
  height : ℝ
  height_mem : height ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
    (c.ofLp (frame 2) + shellEpsilon * r)
  knotRegular : Submission.Coarea.IsRegularValue (longCoordinate K frame) height
  firstLoopRegular : Submission.Coarea.IsRegularValue
    (windingLoopLongCoordinate frame W.first) height
  secondLoopRegular : Submission.Coarea.IsRegularValue
    (windingLoopLongCoordinate frame W.second) height
  knotFiberBound :
    (Submission.Coarea.fiberCount (longCoordinate K frame) s height : ℝ≥0∞) ≤
      ENNReal.ofReal (40 * D)

/-- Select a nearly central cutting plane which is simultaneously regular for the knot and both
smooth carrier loops.  The only counted fiber is the knot fiber on `s`, and its quantitative
bound is exactly the original one. -/
theorem exists_longPlane_fiberCount_le_regular_for_smoothCarrier
    (K : Knot) {Phi : AmbientIsotopy} {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (_hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D)) :
    ∃ d ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
        (c.ofLp (frame 2) + shellEpsilon * r),
      Submission.Coarea.IsRegularValue (longCoordinate K frame) d ∧
      Submission.Coarea.IsRegularValue
        (windingLoopLongCoordinate frame W.first) d ∧
      Submission.Coarea.IsRegularValue
        (windingLoopLongCoordinate frame W.second) d ∧
      (Submission.Coarea.fiberCount (longCoordinate K frame) s d : ℝ≥0∞) ≤
        ENNReal.ofReal (5 * (1 + shellEpsilon⁻¹) * D) := by
  have hwidth :
      c.ofLp (frame 2) - shellEpsilon * r <
        c.ofLp (frame 2) + shellEpsilon * r := by
    nlinarith [mul_pos shellEpsilon_pos hr]
  let f₁ := windingLoopLongCoordinate frame W.first
  let f₂ := windingLoopLongCoordinate frame W.second
  have hf₁ : ContDiff ℝ 1 f₁ :=
    (contDiff_windingLoopLongCoordinate frame W.first
      W.first_ambientCurve_contDiff).of_le (by simp)
  have hf₂ : ContDiff ℝ 1 f₂ :=
    (contDiff_windingLoopLongCoordinate frame W.second
      W.second_ambientCurve_contDiff).of_le (by simp)
  let exceptional := Submission.Coarea.criticalValues f₁ ∪
    Submission.Coarea.criticalValues f₂
  have hexceptional : volume exceptional = 0 :=
    measure_union_null
      (Submission.Coarea.volume_criticalValues_eq_zero hf₁)
      (Submission.Coarea.volume_criticalValues_eq_zero hf₂)
  obtain ⟨d, hd, hdKreg, hdexceptional, hcount⟩ :=
    Submission.Coarea.exists_regularValue_fiberCount_le_integral_of_isCompact_avoiding
      hs (contDiff_longCoordinate K frame) hwidth hexceptional
  have hd₁ : Submission.Coarea.IsRegularValue f₁ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inl hdcrit))
  have hd₂ : Submission.Coarea.IsRegularValue f₂ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inr hdcrit))
  refine ⟨d, hd, hdKreg, hd₁, hd₂, ?_⟩
  have hintegral :
      ∫⁻ t in s, ENNReal.ofReal |deriv (longCoordinate K frame) t| ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D) := by
    refine (setLIntegral_mono' hs.measurableSet ?_).trans hlength
    intro t _ht
    exact ENNReal.ofReal_le_ofReal (abs_deriv_longCoordinate_le_speed K frame t)
  have hden :
      (c.ofLp (frame 2) + shellEpsilon * r) -
        (c.ofLp (frame 2) - shellEpsilon * r) = 2 * shellEpsilon * r := by
    ring
  calc
    (Submission.Coarea.fiberCount (longCoordinate K frame) s d : ℝ≥0∞) ≤
        (∫⁻ t in s, ENNReal.ofReal |deriv (longCoordinate K frame) t|) /
          ENNReal.ofReal
            ((c.ofLp (frame 2) + shellEpsilon * r) -
              (c.ofLp (frame 2) - shellEpsilon * r)) := hcount
    _ ≤ ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D) /
          ENNReal.ofReal
            ((c.ofLp (frame 2) + shellEpsilon * r) -
              (c.ofLp (frame 2) - shellEpsilon * r)) :=
      ENNReal.div_le_div_right hintegral _
    _ = ENNReal.ofReal (5 * (1 + shellEpsilon⁻¹) * D) := by
      rw [hden, ← ENNReal.ofReal_div_of_pos
        (mul_pos (mul_pos (by norm_num) shellEpsilon_pos) hr)]
      congr 1
      field_simp [ne_of_gt shellEpsilon_pos, ne_of_gt hr]
      ring

/-- Published-constant form of the simultaneous selector.  Adding the two loop critical-value
null sets does not charge either loop to the coarea moment: the counted knot fiber still satisfies
the original `40D` bound. -/
theorem exists_longPlane_fiberCount_le_forty_regular_for_smoothCarrier
    (K : Knot) {Phi : AmbientIsotopy} {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D)) :
    ∃ d ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
        (c.ofLp (frame 2) + shellEpsilon * r),
      Submission.Coarea.IsRegularValue (longCoordinate K frame) d ∧
      Submission.Coarea.IsRegularValue
        (windingLoopLongCoordinate frame W.first) d ∧
      Submission.Coarea.IsRegularValue
        (windingLoopLongCoordinate frame W.second) d ∧
      (Submission.Coarea.fiberCount (longCoordinate K frame) s d : ℝ≥0∞) ≤
        ENNReal.ofReal (40 * D) := by
  obtain ⟨d, hd, hdK, hd₁, hd₂, hbound⟩ :=
    exists_longPlane_fiberCount_le_regular_for_smoothCarrier
      K W frame c hs hr hD hlength
  have hconstant : 5 * (1 + shellEpsilon⁻¹) * D = 40 * D := by
    rw [five_mul_one_add_inv_shellEpsilon]
  rw [hconstant] at hbound
  exact ⟨d, hd, hdK, hd₁, hd₂, hbound⟩

/-- Packaged simultaneous selector, explicitly dependent on the chosen smooth carrier witness. -/
theorem exists_smoothCarrierPlaneSelection
    (K : Knot) {Phi : AmbientIsotopy} {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D)) :
    Nonempty (SmoothCarrierPlaneSelection K frame c s r D W) := by
  obtain ⟨d, hd, hdK, hd₁, hd₂, hbound⟩ :=
    exists_longPlane_fiberCount_le_forty_regular_for_smoothCarrier
      K W frame c hs hr hD hlength
  exact ⟨{
    height := d
    height_mem := hd
    knotRegular := hdK
    firstLoopRegular := hd₁
    secondLoopRegular := hd₂
    knotFiberBound := hbound
  }⟩

/-- Starting from an oriented-loop carrier, first smooth its two winding loops inside the same
open box and then select a cutting height regular for the knot and both smoothed loops. -/
theorem exists_smoothCarrierPlaneSelection_of_orientedLoopCarrier
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hcarrier : OrientedLoopCarrier Phi frame c r)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D)) :
    ∃ W : SmoothLoopCarrierWitness Phi (orientedBox frame c r),
      Nonempty (SmoothCarrierPlaneSelection K frame c s r D W) := by
  obtain ⟨W⟩ := exists_smoothLoopCarrierWitness_of_orientedLoopCarrier
    Phi frame c hr hcarrier
  exact ⟨W, exists_smoothCarrierPlaneSelection K W frame c hs hr hD hlength⟩

end Submission.PardonDistortion
