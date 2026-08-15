import Submission.BasedRegularDoubleBubbleSelection
import Submission.SardMoreira.Planar

/-!
# Based double-bubble cuts regular for the transported torus

The based selector already avoids the common carrier basepoint and is regular for the knot and
the two smooth carrier loops.  Here the same coarea choice also avoids the critical values of the
planar lift of the transported-torus cutting coordinate.  Planar Sard makes that extra exceptional
set null, so neither the knot first moment nor the exact `40D` bound changes.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology
open Submission.SurfaceRegularValue

/-- A smooth-carrier cut can avoid an arbitrary null set without changing its exact `40D`
knot-fiber estimate. -/
theorem exists_smoothCarrierPlaneSelection_avoiding_nullSet
    (K : Knot) {Phi : AmbientIsotopy} {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (_hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D))
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ S : SmoothCarrierPlaneSelection K frame c s r D W,
      S.height ∉ N := by
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
    Submission.Coarea.criticalValues f₂ ∪ N
  have hexceptional : volume exceptional = 0 :=
    measure_union_null
      (measure_union_null
        (Submission.Coarea.volume_criticalValues_eq_zero hf₁)
        (Submission.Coarea.volume_criticalValues_eq_zero hf₂)) hN
  obtain ⟨d, hd, hdKreg, hdexceptional, hcount⟩ :=
    Submission.Coarea.exists_regularValue_fiberCount_le_integral_of_isCompact_avoiding
      hs (contDiff_longCoordinate K frame) hwidth hexceptional
  have hd₁ : Submission.Coarea.IsRegularValue f₁ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inl (Or.inl hdcrit)))
  have hd₂ : Submission.Coarea.IsRegularValue f₂ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inl (Or.inr hdcrit)))
  have hdN : d ∉ N := fun hdmem ↦ hdexceptional (Or.inr hdmem)
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
  have hbound :
      (Submission.Coarea.fiberCount (longCoordinate K frame) s d : ℝ≥0∞) ≤
        ENNReal.ofReal (40 * D) := by
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
      _ = ENNReal.ofReal (40 * D) := by
        rw [hden, ← ENNReal.ofReal_div_of_pos
          (mul_pos (mul_pos (by norm_num) shellEpsilon_pos) hr)]
        congr 1
        field_simp [ne_of_gt shellEpsilon_pos, ne_of_gt hr]
        norm_num [shellEpsilon]
        ring
  exact ⟨{
    height := d
    height_mem := hd
    knotRegular := hdKreg
    firstLoopRegular := hd₁
    secondLoopRegular := hd₂
    knotFiberBound := hbound
  }, hdN⟩

/-- Simultaneous surface regularity and avoidance of one prescribed height, still with the same
smooth-carrier and knot-count conclusions. -/
theorem exists_smoothCarrierPlaneSelection_surfaceRegular_avoiding_value
    (K : Knot) (Phi : AmbientIsotopy) {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D))
    (forbidden : ℝ) :
    ∃ S : SmoothCarrierPlaneSelection K frame c s r D W,
      IsRegularValue (orientedCoordinateLift Phi frame 2) S.height ∧
      S.height ≠ forbidden := by
  let f := orientedCoordinateLift Phi frame 2
  let N := criticalValues f ∪ {forbidden}
  have hfNull : CriticalValuesNull f :=
    criticalValuesNull_of_sardMoreiraConclusion
      (planarSardTheorem f (orientedCoordinateLift_contDiff Phi frame 2))
  have hN : volume N = 0 :=
    measure_union_null hfNull (measure_singleton forbidden)
  obtain ⟨S, hS⟩ := exists_smoothCarrierPlaneSelection_avoiding_nullSet
    K W frame c hs hr hD hlength hN
  refine ⟨S, (isRegularValue_iff_not_mem_criticalValues f S.height).2 ?_, ?_⟩
  · exact fun hcritical ↦ hS (Or.inl hcritical)
  · intro heq
    exact hS (Or.inr (by simp [heq]))

/-- The existing based double-bubble package, strengthened by retaining that its exact cutting
height is a regular value of the transported-torus planar coordinate lift. -/
structure SurfaceRegularBasedDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  toBasedRegularDoubleBubbleSelection :
    BasedRegularDoubleBubbleSelection K Phi frame c r
  cutSurfaceRegular : IsRegularValue
    (orientedCoordinateLift Phi frame 2)
    toBasedRegularDoubleBubbleSelection.cut.height

namespace SurfaceRegularBasedDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ}

abbrev carrier (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame c r) :=
  S.toBasedRegularDoubleBubbleSelection.carrier

abbrev outer (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame c r) :=
  S.toBasedRegularDoubleBubbleSelection.outer

abbrev cut (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame c r) :=
  S.toBasedRegularDoubleBubbleSelection.cut

theorem weightedEventCount_le
    (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame c r) :
    (S.outer.knotFiberFinite.toFinset.card : ℝ) +
        2 * (S.toBasedRegularDoubleBubbleSelection.cutFiberFinite.toFinset.card : ℝ) ≤
      160 * (distortion K).toReal :=
  S.toBasedRegularDoubleBubbleSelection.weightedEventCount_le

end SurfaceRegularBasedDoubleBubbleSelection

private lemma local_speed_bound_for_surfaceRegularBasedOuterLevel
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r R : ℝ} (hr : 0 < r) (hR : R ∈ Ioc r ((8 / 7) * r))
    (hfinite : distortion K ≠ ⊤) :
    (∫⁻ t in closedOrientedBoxParameters K frame c R,
        ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal
        (10 * (1 + shellEpsilon) * r * (distortion K).toReal) := by
  have hRpos : 0 < R := hr.trans hR.1
  calc
    (∫⁻ t in closedOrientedBoxParameters K frame c R,
        ENNReal.ofReal (speed K t)) =
        ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedOrientedBox frame c R,
          ENNReal.ofReal (speed K t) :=
      lintegral_closedOrientedBoxParameters_speed_eq_halfOpen K frame c R
    _ ≤ ENNReal.ofReal (10 * R * (distortion K).toReal) :=
      lintegral_speed_preimage_closedOrientedBox_le K hRpos hfinite
    _ ≤ ENNReal.ofReal
        (10 * (1 + shellEpsilon) * r * (distortion K).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      have heps : (1 + shellEpsilon) = (8 / 7 : ℝ) := by
        norm_num [shellEpsilon]
      rw [heps]
      have hscaled : 10 * R ≤ 10 * ((8 / 7 : ℝ) * r) :=
        mul_le_mul_of_nonneg_left hR.2 (by norm_num)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hscaled ENNReal.toReal_nonneg

/-- A positive based-loop-carrying box admits the full selector with surface regularity
at the same cut height. The knot boundary counts remain exactly `80D` and `40D`. -/
theorem exists_surfaceRegularBasedDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : OrientedBasedLoopCarrier Phi frame c r)
    (hfinite : distortion K ≠ ⊤) :
    Nonempty (SurfaceRegularBasedDoubleBubbleSelection K Phi frame c r) := by
  obtain ⟨W⟩ := exists_smoothBasedLoopCarrierWitness_of_orientedBasedLoopCarrier
    Phi frame c hr hcarrier
  obtain ⟨outer⟩ := exists_facewiseRegularOuterBoundarySelection
    K Phi frame c hr hfinite
  let s := closedOrientedBoxParameters K frame c outer.level
  have hs : IsCompact s :=
    isCompact_closedOrientedBoxParameters K frame c outer.level
  have hlength :
      (∫⁻ t in s, ENNReal.ofReal (speed K t)) ≤
        ENNReal.ofReal
          (10 * (1 + shellEpsilon) * r * (distortion K).toReal) :=
    local_speed_bound_for_surfaceRegularBasedOuterLevel
      K frame c hr outer.level_mem hfinite
  obtain ⟨cut, hcutSurface, hcutBasepoint⟩ :=
    exists_smoothCarrierPlaneSelection_surfaceRegular_avoiding_value
      K Phi W.toSmoothLoopCarrierWitness frame c hs hr ENNReal.toReal_nonneg hlength
        ((W.basepoint : R3).ofLp (frame 2))
  have hcutFinite :
      (orientedCutParameterSet K frame c outer.level cut.height).Finite :=
    Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
      hs (contDiff_longCoordinate K frame) cut.knotRegular
  exact ⟨{
    toBasedRegularDoubleBubbleSelection := {
      carrier := W
      outer := outer
      cut := cut
      cutHeight_ne_basepoint := hcutBasepoint
      cutFiberFinite := hcutFinite
    }
    cutSurfaceRegular := hcutSurface
  }⟩

end Submission.PardonDistortion
