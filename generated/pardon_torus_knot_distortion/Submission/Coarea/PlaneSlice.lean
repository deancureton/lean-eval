import Submission.Coarea.General
import Submission.OrientedBox

open MeasureTheory Set
open scoped ENNReal

namespace Submission
namespace PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- Continuous linear projection onto one Euclidean coordinate. -/
def coordinateCLM (i : Fin 3) : R3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).toContinuousLinearMap

@[simp] lemma coordinateCLM_apply (i : Fin 3) (x : R3) :
    coordinateCLM i x = x.ofLp i := rfl

/-- The knot coordinate perpendicular to the long faces of an oriented box. -/
def longCoordinate (K : Knot) (frame : Equiv.Perm (Fin 3)) (t : ℝ) : ℝ :=
  K.curve t |>.ofLp (frame 2)

lemma contDiff_longCoordinate (K : Knot) (frame : Equiv.Perm (Fin 3)) :
    ContDiff ℝ 1 (longCoordinate K frame) := by
  exact (coordinateCLM (frame 2)).contDiff.comp (K.smooth.of_le (by simp))

lemma deriv_longCoordinate (K : Knot) (frame : Equiv.Perm (Fin 3)) (t : ℝ) :
    deriv (longCoordinate K frame) t = (deriv K.curve t).ofLp (frame 2) := by
  have hcurve : HasDerivAt K.curve (deriv K.curve t) t :=
    (K.smooth.differentiable (by simp) t).hasDerivAt
  exact ((coordinateCLM (frame 2)).hasFDerivAt.comp_hasDerivAt t hcurve).deriv

lemma abs_deriv_longCoordinate_le_speed
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (t : ℝ) :
    |deriv (longCoordinate K frame) t| ≤ speed K t := by
  rw [deriv_longCoordinate, speed, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (deriv K.curve t) (frame 2)

/-- Choose a plane within `shellEpsilon * r` of the box center.  A local
arclength integral bounded by `10(1+ε)rD` gives the exact plane-intersection
bound `5(1+1/ε)D`. -/
theorem exists_longPlane_fiberCount_le
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {s : Set ℝ} (hs : IsCompact s) {r D : ℝ} (hr : 0 < r) (_hD : 0 ≤ D)
    (hlength :
      ∫⁻ t in s, ENNReal.ofReal (speed K t) ≤
        ENNReal.ofReal (10 * (1 + shellEpsilon) * r * D)) :
    ∃ d ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
        (c.ofLp (frame 2) + shellEpsilon * r),
      Submission.Coarea.IsRegularValue (longCoordinate K frame) d ∧
      (Submission.Coarea.fiberCount (longCoordinate K frame) s d : ℝ≥0∞) ≤
        ENNReal.ofReal (5 * (1 + shellEpsilon⁻¹) * D) := by
  have hwidth :
      c.ofLp (frame 2) - shellEpsilon * r <
        c.ofLp (frame 2) + shellEpsilon * r := by
    nlinarith [mul_pos shellEpsilon_pos hr]
  obtain ⟨d, hd, hdreg, hcount⟩ :=
    Submission.Coarea.exists_regularValue_fiberCount_le_integral_of_isCompact
      hs (contDiff_longCoordinate K frame) hwidth
  refine ⟨d, hd, hdreg, ?_⟩
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

/-- The selected cutting plane is within the offset required by the oriented
half-box containment lemmas. -/
lemma abs_sub_center_le_of_mem_longPlane_interval
    {frame : Equiv.Perm (Fin 3)} {c : R3} {r d : ℝ}
    (hd : d ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
      (c.ofLp (frame 2) + shellEpsilon * r)) :
    |d - c.ofLp (frame 2)| ≤ shellEpsilon * r := by
  rw [abs_le]
  constructor <;> linarith [hd.1, hd.2]

end

end PardonDistortion
end Submission
