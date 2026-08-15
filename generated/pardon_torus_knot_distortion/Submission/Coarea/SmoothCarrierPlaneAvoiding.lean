import Submission.Coarea.SmoothCarrierPlaneSelection

/-!
# A carrier-regular cutting plane avoiding one prescribed height

For based rerouting, the common basepoint must lie strictly on one side of the cutting plane.
Avoiding its long coordinate costs nothing in the coarea estimate because a singleton is null.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-- Select a cutting height regular for the knot and both smooth carrier loops, different from a
prescribed value, while retaining the exact `40D` knot-fiber bound. -/
theorem exists_smoothCarrierPlaneSelection_avoiding_value
    (K : Knot) {Phi : AmbientIsotopy} {a : Set R3}
    (W : SmoothLoopCarrierWitness Phi a)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (_hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D))
    (forbidden : ℝ) :
    ∃ S : SmoothCarrierPlaneSelection K frame c s r D W,
      S.height ≠ forbidden := by
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
    Submission.Coarea.criticalValues f₂ ∪ {forbidden}
  have hexceptional : volume exceptional = 0 := by
    exact measure_union_null
      (measure_union_null
        (Submission.Coarea.volume_criticalValues_eq_zero hf₁)
        (Submission.Coarea.volume_criticalValues_eq_zero hf₂))
      (measure_singleton forbidden)
  obtain ⟨d, hd, hdKreg, hdexceptional, hcount⟩ :=
    Submission.Coarea.exists_regularValue_fiberCount_le_integral_of_isCompact_avoiding
      hs (contDiff_longCoordinate K frame) hwidth hexceptional
  have hd₁ : Submission.Coarea.IsRegularValue f₁ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inl (Or.inl hdcrit)))
  have hd₂ : Submission.Coarea.IsRegularValue f₂ d :=
    Submission.Coarea.not_mem_criticalValues_iff.mp
      (fun hdcrit ↦ hdexceptional (Or.inl (Or.inr hdcrit)))
  have hdForbidden : d ≠ forbidden := by
    intro h
    apply hdexceptional
    exact Or.inr (by simp [h])
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
  }, hdForbidden⟩

end Submission.PardonDistortion
