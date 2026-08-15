import Submission.Coarea.OrientedBoundarySelection
import Submission.Coarea.PlaneSlice
import Submission.NestedCarrier

/-!
# Simultaneous outer-boundary and cutting-plane selection

The branch-free coarea theorems are assembled here in exactly the form used
by Pardon's double bubble.  At every positive box scale they produce an
outer oriented box and a nearly central long-axis plane with weighted knot
intersection count at most `160 * distortion`.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- Knot parameters on the selected long-axis cutting plane and inside the
selected closed outer box. -/
def orientedCutParameterSet (K : Knot) (frame : Equiv.Perm (Fin 3))
    (c : R3) (outerScale cutHeight : ℝ) : Set ℝ :=
  Submission.Coarea.fiberSet (longCoordinate K frame)
    (closedOrientedBoxParameters K frame c outerScale) cutHeight

/-- All quantitative output of the two coarea selections. -/
structure DoubleBubbleSelection (K : Knot) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  outerScale : ℝ
  outerScale_mem : outerScale ∈ Ioc r ((8 / 7) * r)
  outerFinite :
    (Submission.Coarea.fiberSet (orientedShellParameter K frame c)
      (Ico (0 : ℝ) (2 * Real.pi)) outerScale).Finite
  outerBound :
    (orientedBoundaryCount K frame c (Ico (0 : ℝ) (2 * Real.pi))
      outerScale : ℝ≥0∞) ≤ ENNReal.ofReal (80 * (distortion K).toReal)
  cutHeight : ℝ
  cutHeight_mem : cutHeight ∈
    Ioc (c.ofLp (frame 2) - shellEpsilon * r)
      (c.ofLp (frame 2) + shellEpsilon * r)
  cutRegular : Submission.Coarea.IsRegularValue
    (longCoordinate K frame) cutHeight
  cutFinite : (orientedCutParameterSet K frame c outerScale cutHeight).Finite
  cutBound :
    ((orientedCutParameterSet K frame c outerScale cutHeight).ncard : ℝ≥0∞) ≤
      ENNReal.ofReal (40 * (distortion K).toReal)

private lemma local_speed_bound_for_outerScale
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

/-- Select the entire double-bubble geometry with the exact `80D` and `40D`
bounds. -/
theorem exists_doubleBubbleSelection
    (K : Knot) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤) :
    Nonempty (DoubleBubbleSelection K frame c r) := by
  obtain ⟨R, hR, _hRExceptional, houterFinite, houterBound⟩ :=
    exists_orientedOuterBoundary_count_le_eighty_mul_distortion
      K frame c hr hfinite
  let s := closedOrientedBoxParameters K frame c R
  have hs : IsCompact s := isCompact_closedOrientedBoxParameters K frame c R
  have hlength :
      (∫⁻ t in s, ENNReal.ofReal (speed K t)) ≤
        ENNReal.ofReal
          (10 * (1 + shellEpsilon) * r * (distortion K).toReal) :=
    local_speed_bound_for_outerScale K frame c hr hR hfinite
  obtain ⟨d, hd, hdreg, hcutBound⟩ :=
    exists_longPlane_fiberCount_le K frame c hs hr ENNReal.toReal_nonneg hlength
  have hcutFinite : (orientedCutParameterSet K frame c R d).Finite := by
    exact Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
      hs (contDiff_longCoordinate K frame) hdreg
  have hconstant :
      (5 * (1 + shellEpsilon⁻¹) * (distortion K).toReal : ℝ) =
        40 * (distortion K).toReal := by
    rw [five_mul_one_add_inv_shellEpsilon]
  rw [hconstant] at hcutBound
  exact ⟨{
    outerScale := R
    outerScale_mem := hR
    outerFinite := houterFinite
    outerBound := houterBound
    cutHeight := d
    cutHeight_mem := hd
    cutRegular := hdreg
    cutFinite := hcutFinite
    cutBound := hcutBound
  }⟩

private lemma natCast_le_of_coe_le_ofReal {n : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (h : (n : ℝ≥0∞) ≤ ENNReal.ofReal x) :
    (n : ℝ) ≤ x := by
  have htop : (n : ℝ≥0∞) ≠ ⊤ := by simp
  have := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 h
  simpa [ENNReal.toReal_ofReal hx] using this

/-- The two selected counts combine to the published real bound `160D`. -/
theorem DoubleBubbleSelection.weightedCount_le
    {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : DoubleBubbleSelection K frame c r) :
    (S.outerFinite.toFinset.card : ℝ) +
        2 * (S.cutFinite.toFinset.card : ℝ) ≤
      160 * (distortion K).toReal := by
  have houter : (S.outerFinite.toFinset.card : ℝ) ≤
      80 * (distortion K).toReal := by
    rw [← Set.ncard_eq_toFinset_card _ S.outerFinite]
    exact natCast_le_of_coe_le_ofReal (by positivity) (by
      simpa [orientedBoundaryCount, Submission.Coarea.fiberCount] using S.outerBound)
  have hcut : (S.cutFinite.toFinset.card : ℝ) ≤
      40 * (distortion K).toReal := by
    rw [← Set.ncard_eq_toFinset_card _ S.cutFinite]
    exact natCast_le_of_coe_le_ofReal (by positivity) S.cutBound
  linarith

/-- Under the contradiction hypothesis, the selected weighted count is
strictly smaller than `min p q`. -/
theorem DoubleBubbleSelection.weightedCount_lt_min
    {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : DoubleBubbleSelection K frame c r) (p q : ℕ)
    (hcontra : 160 * (distortion K).toReal <
      ((Nat.min p q : ℕ) : ℝ)) :
    (S.outerFinite.toFinset.card : ℝ) +
        2 * (S.cutFinite.toFinset.card : ℝ) <
      ((Nat.min p q : ℕ) : ℝ) :=
  S.weightedCount_le.trans_lt hcontra

end

end Submission.PardonDistortion
