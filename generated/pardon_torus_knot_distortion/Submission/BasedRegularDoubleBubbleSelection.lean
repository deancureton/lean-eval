import Submission.RegularDoubleBubbleSelection
import Submission.Coarea.SmoothCarrierPlaneAvoiding
import Submission.Topology.BasedSmoothLoopCarrier

/-!
# Regular double-bubble data with a connected based carrier

The ordinary loop-carrier predicate permits its two independent loops to lie
in different connected components.  The cutting argument needs more: the two
loops meet at one recorded point.  This module repeats only the final selector
packaging with the basepoint-preserving Fourier approximation, while reusing
all quantitative and face-regularity results.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-- The complete regular selection, retaining two smooth independent loops
through one exact common basepoint. -/
structure BasedRegularDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ) where
  carrier : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)
  outer : FacewiseRegularOuterBoundarySelection K Phi frame c r
  cut : SmoothCarrierPlaneSelection K frame c
    (closedOrientedBoxParameters K frame c outer.level) r
      (distortion K).toReal carrier.toSmoothLoopCarrierWitness
  cutHeight_ne_basepoint : cut.height ≠ (carrier.basepoint : R3).ofLp (frame 2)
  cutFiberFinite :
    (orientedCutParameterSet K frame c outer.level cut.height).Finite

namespace BasedRegularDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ}

/-- Forget the common basepoint while preserving the exact selected levels
and every regularity certificate. -/
def toRegularDoubleBubbleSelection
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    RegularDoubleBubbleSelection K Phi frame c r where
  carrier := S.carrier.toSmoothLoopCarrierWitness
  outer := S.outer
  cut := S.cut
  cutFiberFinite := S.cutFiberFinite

/-- The exact ordinary event selector used by compression charging. -/
def toDoubleBubbleSelection
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    DoubleBubbleSelection K frame c r :=
  S.toRegularDoubleBubbleSelection.toDoubleBubbleSelection

theorem weightedEventCount_le
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    (S.outer.knotFiberFinite.toFinset.card : ℝ) +
        2 * (S.cutFiberFinite.toFinset.card : ℝ) ≤
      160 * (distortion K).toReal :=
  S.toRegularDoubleBubbleSelection.weightedEventCount_le

theorem originalBox_subset_outer
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    orientedBox frame c r ⊆ orientedBox frame c S.outer.level :=
  S.toRegularDoubleBubbleSelection.originalBox_subset_outer

/-- The retained common basepoint lies in the original carrying box. -/
theorem basepoint_mem_originalBox
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    (S.carrier.basepoint : R3) ∈ orientedBox frame c r := by
  have hfirst := S.carrier.first.curve_mem 0
  rw [S.carrier.first_zero] at hfirst
  exact hfirst

/-- Hence the common basepoint also lies in the selected expanded outer box. -/
theorem basepoint_mem_outerBox
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    (S.carrier.basepoint : R3) ∈ orientedBox frame c S.outer.level :=
  S.originalBox_subset_outer S.basepoint_mem_originalBox

/-- Because the selector avoids the basepoint height, that point lies strictly on one side of the
cutting plane. -/
theorem cutHeight_lt_basepoint_or_basepoint_lt
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    S.cut.height < (S.carrier.basepoint : R3).ofLp (frame 2) ∨
      (S.carrier.basepoint : R3).ofLp (frame 2) < S.cut.height :=
  lt_or_gt_of_ne S.cutHeight_ne_basepoint

/-- The common basepoint belongs to one of the two *open* half-boxes, never merely to their
interface. -/
theorem basepoint_mem_strictLower_or_strictUpper
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) :
    ((S.carrier.basepoint : R3) ∈ orientedBox frame c S.outer.level ∩
      {x | x.ofLp (frame 2) < S.cut.height}) ∨
    ((S.carrier.basepoint : R3) ∈ orientedBox frame c S.outer.level ∩
      {x | S.cut.height < x.ofLp (frame 2)}) := by
  rcases S.cutHeight_lt_basepoint_or_basepoint_lt with hupper | hlower
  · exact Or.inr ⟨S.basepoint_mem_outerBox, hupper⟩
  · exact Or.inl ⟨S.basepoint_mem_outerBox, hlower⟩

theorem selectedLowerHalf_subset_successor
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    orientedBox frame c S.outer.level ∩
        {x | x.ofLp (frame 2) ≤ S.cut.height} ⊆
      orientedBox (axisCycle.trans frame)
        (lowerHalfCenter frame c S.outer.level S.cut.height)
        (successorScale S.outer.level r) :=
  S.toRegularDoubleBubbleSelection.selectedLowerHalf_subset_successor hr

theorem selectedUpperHalf_subset_successor
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    orientedBox frame c S.outer.level ∩
        {x | S.cut.height ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame)
        (upperHalfCenter frame c S.outer.level S.cut.height)
        (successorScale S.outer.level r) :=
  S.toRegularDoubleBubbleSelection.selectedUpperHalf_subset_successor hr

theorem selectedSuccessorScale_pos
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    0 < successorScale S.outer.level r :=
  S.toRegularDoubleBubbleSelection.selectedSuccessorScale_pos hr

theorem selectedSuccessorScale_le
    (S : BasedRegularDoubleBubbleSelection K Phi frame c r) (hr : 0 < r) :
    successorScale S.outer.level r ≤ shrinkFactor * r :=
  S.toRegularDoubleBubbleSelection.selectedSuccessorScale_le hr

end BasedRegularDoubleBubbleSelection

private lemma local_speed_bound_for_basedFacewiseOuterLevel
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

/-- A positive based-loop-carrying box admits the full regular selection with
the same exact common basepoint retained by its two smooth carrier loops. -/
theorem exists_basedRegularDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : OrientedBasedLoopCarrier Phi frame c r)
    (hfinite : distortion K ≠ ⊤) :
    Nonempty (BasedRegularDoubleBubbleSelection K Phi frame c r) := by
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
    local_speed_bound_for_basedFacewiseOuterLevel
      K frame c hr outer.level_mem hfinite
  obtain ⟨cut, hcutBasepoint⟩ := exists_smoothCarrierPlaneSelection_avoiding_value
    K W.toSmoothLoopCarrierWitness frame c hs hr ENNReal.toReal_nonneg hlength
      ((W.basepoint : R3).ofLp (frame 2))
  have hcutFinite :
      (orientedCutParameterSet K frame c outer.level cut.height).Finite :=
    Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
      hs (contDiff_longCoordinate K frame) cut.knotRegular
  exact ⟨{
    carrier := W
    outer := outer
    cut := cut
    cutHeight_ne_basepoint := hcutBasepoint
    cutFiberFinite := hcutFinite
  }⟩

end Submission.PardonDistortion
