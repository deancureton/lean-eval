import Submission.Coarea.FacewiseRegularOuterBoundarySelection
import Submission.Coarea.SmoothCarrierPlaneSelection
import Submission.DoubleBubbleSelection

/-!
# A regular double-bubble selection with a smooth carrier

This module integrates the independently verified selectors.  Starting from an oriented box
which carries loop genus, it packages:

* two independent ambient-smooth winding loops in the original box;
* an outer level with the exact `80D` knot count and simultaneous regularity of all six faces;
* a cut level with the exact `40D` knot count, regular for the knot and both smooth loops;
* the ordinary `DoubleBubbleSelection`, hence the existing exact weighted `160D` arithmetic;
* the offset, nesting, half-box containment, positivity, and shrink estimates used downstream.

No topological cutting or rerouting conclusion is assumed here.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-- All regularity and quantitative selection data attached to one carrying oriented box. -/
structure RegularDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  carrier : SmoothLoopCarrierWitness Phi (orientedBox frame c r)
  outer : FacewiseRegularOuterBoundarySelection K Phi frame c r
  cut : SmoothCarrierPlaneSelection K frame c
    (closedOrientedBoxParameters K frame c outer.level) r
      (distortion K).toReal carrier
  cutFiberFinite :
    (orientedCutParameterSet K frame c outer.level cut.height).Finite

namespace RegularDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ}

/-- Forget the added smooth-carrier and face-regularity data.  This produces exactly the existing
double-bubble selector, so all its downstream arithmetic can be reused without duplication. -/
def toDoubleBubbleSelection
    (S : RegularDoubleBubbleSelection K Phi frame c r) :
    DoubleBubbleSelection K frame c r where
  outerScale := S.outer.level
  outerScale_mem := S.outer.level_mem
  outerFinite := S.outer.knotFiberFinite
  outerBound := S.outer.knotBoundaryCount_le
  cutHeight := S.cut.height
  cutHeight_mem := S.cut.height_mem
  cutRegular := S.cut.knotRegular
  cutFinite := S.cutFiberFinite
  cutBound := S.cut.knotFiberBound

/-- Exact weighted event count, inherited from `DoubleBubbleSelection.weightedCount_le`. -/
theorem weightedEventCount_le
    (S : RegularDoubleBubbleSelection K Phi frame c r) :
    (S.outer.knotFiberFinite.toFinset.card : ℝ) +
        2 * (S.cutFiberFinite.toFinset.card : ℝ) ≤
      160 * (distortion K).toReal := by
  exact S.toDoubleBubbleSelection.weightedCount_le

/-- The selected outer box has positive scale. -/
theorem outerLevel_pos (S : RegularDoubleBubbleSelection K Phi frame c r)
    (hr : 0 < r) :
    0 < S.outer.level :=
  hr.trans S.outer.level_mem.1

/-- The selected outer scale is at most `(1 + shellEpsilon) r`. -/
theorem outerLevel_le (S : RegularDoubleBubbleSelection K Phi frame c r) :
    S.outer.level ≤ (1 + shellEpsilon) * r := by
  have heps : (1 + shellEpsilon : ℝ) = 8 / 7 := by
    norm_num [shellEpsilon]
  rw [heps]
  exact S.outer.level_mem.2

/-- The original carrying box lies inside the selected outer box. -/
theorem originalBox_subset_outer
    (S : RegularDoubleBubbleSelection K Phi frame c r) :
    orientedBox frame c r ⊆ orientedBox frame c S.outer.level := by
  intro x hx
  rw [mem_orientedBox_iff] at hx ⊢
  intro i
  exact (hx i).trans
    (mul_lt_mul_of_pos_left S.outer.level_mem.1 (axisWeight_pos i))

/-- The cut is within the central offset needed by both half-box containment lemmas. -/
theorem cutOffset_le (S : RegularDoubleBubbleSelection K Phi frame c r) :
    |S.cut.height - c.ofLp (frame 2)| ≤ shellEpsilon * r :=
  abs_sub_center_le_of_mem_longPlane_interval S.cut.height_mem

/-- The lower closed half of the selected outer box lies in its controlled successor box. -/
theorem selectedLowerHalf_subset_successor
    (S : RegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    orientedBox frame c S.outer.level ∩
        {x | x.ofLp (frame 2) ≤ S.cut.height} ⊆
      orientedBox (axisCycle.trans frame)
        (lowerHalfCenter frame c S.outer.level S.cut.height)
        (successorScale S.outer.level r) :=
  Submission.PardonDistortion.lowerHalf_subset_successor frame c
    (S.outerLevel_pos hr) hr S.cutOffset_le

/-- The upper closed half of the selected outer box lies in its controlled successor box. -/
theorem selectedUpperHalf_subset_successor
    (S : RegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    orientedBox frame c S.outer.level ∩
        {x | S.cut.height ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame)
        (upperHalfCenter frame c S.outer.level S.cut.height)
        (successorScale S.outer.level r) :=
  Submission.PardonDistortion.upperHalf_subset_successor frame c
    (S.outerLevel_pos hr) hr S.cutOffset_le

/-- The successor scale is positive. -/
theorem selectedSuccessorScale_pos
    (S : RegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    0 < successorScale S.outer.level r :=
  Submission.PardonDistortion.successorScale_pos (S.outerLevel_pos hr) hr

/-- The successor scale obeys the exact shrinking estimate used by the nested-box engine. -/
theorem selectedSuccessorScale_le
    (S : RegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    successorScale S.outer.level r ≤ shrinkFactor * r :=
  successorScale_le_shrinkFactor_mul hr.le S.outerLevel_le

end RegularDoubleBubbleSelection

/-! ## Construction -/

/-- Local knot arclength in the selected outer box, in the form needed by the regular cut
selector.  This is the short public-lemma bridge hidden as a private helper in the original
`DoubleBubbleSelection` construction. -/
private lemma local_speed_bound_for_facewiseOuterLevel
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

/-- A carrying positive-scale oriented box admits the full regular double-bubble selection. -/
theorem exists_regularDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hcarrier : OrientedLoopCarrier Phi frame c r)
    (hfinite : distortion K ≠ ⊤) :
    Nonempty (RegularDoubleBubbleSelection K Phi frame c r) := by
  obtain ⟨W⟩ := exists_smoothLoopCarrierWitness_of_orientedLoopCarrier
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
    local_speed_bound_for_facewiseOuterLevel K frame c hr outer.level_mem hfinite
  obtain ⟨cut⟩ := exists_smoothCarrierPlaneSelection
    K W frame c hs hr ENNReal.toReal_nonneg hlength
  have hcutFinite :
      (orientedCutParameterSet K frame c outer.level cut.height).Finite := by
    exact Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
      hs (contDiff_longCoordinate K frame) cut.knotRegular
  exact ⟨{
    carrier := W
    outer := outer
    cut := cut
    cutFiberFinite := hcutFinite
  }⟩

end Submission.PardonDistortion
