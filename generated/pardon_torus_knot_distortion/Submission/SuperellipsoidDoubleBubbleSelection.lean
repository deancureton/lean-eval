import Submission.Coarea.SuperellipsoidCriticalScales
import Submission.Coarea.SuperellipsoidSeamSard

/-!
# The smooth superellipsoid double-bubble selection

This file packages the two quantitative selections without any polyhedral face or ridge
bookkeeping.  The outer surface costs at most `76 D`, the cutting disk costs at most `40 D`, and
the weighted event total is therefore at most `156 D`, leaving four units of slack below the
published `160 D` constant.
-/

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-- Knot parameters counted on the selected cutting disk. -/
def superellipsoidCutParameterSet
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    {outer : SuperellipsoidOuterSelection K Phi frame c r}
    (cut : SuperellipsoidRegularCutSelection K Phi frame c r
      (distortion K).toReal W outer) : Set ℝ :=
  Submission.Coarea.fiberSet (longCoordinate K frame)
    (closedSuperellipsoidParameters K frame c outer.scale) cut.height

/-- Both stages of the smooth double-bubble selector. -/
structure SuperellipsoidDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r : ℝ)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)) where
  outer : SuperellipsoidOuterSelection K Phi frame c r
  cut : SuperellipsoidRegularCutSelection K Phi frame c r
    (distortion K).toReal W outer

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- The outer knot-event parameters. -/
abbrev outerEventSet
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) : Set ℝ :=
  outerKnotSeamParameters S.outer

/-- The cutting-disk knot-event parameters. -/
abbrev cutEventSet
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) : Set ℝ :=
  superellipsoidCutParameterSet S.cut

lemma outerEventSet_finite
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    S.outerEventSet.Finite :=
  S.outer.knotFiberFinite

lemma cutEventSet_finite
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    S.cutEventSet.Finite := by
  exact Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
    (isCompact_closedSuperellipsoidParameters K frame c S.outer.scale)
    (contDiff_longCoordinate K frame) S.cut.toSmoothCarrierPlaneSelection.knotRegular

/-- Avoiding the finitely many knot/outer seam heights makes the outer and cutting event sets
literally disjoint.  Thus no knot point is charged to both kinds of boundary event. -/
lemma outerEventSet_disjoint_cutEventSet
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    Disjoint S.outerEventSet S.cutEventSet := by
  rw [Set.disjoint_left]
  intro t htOuter htCut
  apply S.cut.avoidsKnotOuterSeam
  change t ∈ Submission.Coarea.fiberSet (longCoordinate K frame)
    (closedSuperellipsoidParameters K frame c S.outer.scale) S.cut.height at htCut
  rw [Submission.Coarea.fiberSet] at htCut
  exact ⟨t, htOuter, htCut.2⟩

private lemma natCast_le_of_coe_le_ofReal {n : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (h : (n : ℝ≥0∞) ≤ ENNReal.ofReal x) :
    (n : ℝ) ≤ x := by
  have htop : (n : ℝ≥0∞) ≠ ⊤ := by simp
  have hreal := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 h
  simpa [ENNReal.toReal_ofReal hx] using hreal

/-- Exact real outer-event count inherited from the `76D` coarea estimate. -/
lemma outerEventCount_le
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    (S.outerEventSet_finite.toFinset.card : ℝ) ≤
      76 * (distortion K).toReal := by
  rw [← Set.ncard_eq_toFinset_card _ S.outerEventSet_finite]
  apply natCast_le_of_coe_le_ofReal (by positivity)
  simpa [outerKnotSeamParameters, Submission.Coarea.fiberCount] using
    S.outer.knotBoundaryCount_le

/-- Exact real cutting-event count inherited from the `40D` coarea estimate. -/
lemma cutEventCount_le
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    (S.cutEventSet_finite.toFinset.card : ℝ) ≤
      40 * (distortion K).toReal := by
  rw [← Set.ncard_eq_toFinset_card _ S.cutEventSet_finite]
  exact natCast_le_of_coe_le_ofReal (by positivity) S.cut.knotFiberBound

/-- Weighted outer-plus-two-cuts event count.  The strict geometric improvement gives `156D`. -/
theorem weightedEventCount_le
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    (S.outerEventSet_finite.toFinset.card : ℝ) +
        2 * (S.cutEventSet_finite.toFinset.card : ℝ) ≤
      156 * (distortion K).toReal := by
  linarith [S.outerEventCount_le, S.cutEventCount_le]

/-- Published constant, with four units of explicit slack. -/
theorem weightedEventCount_le_oneSixty
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    (S.outerEventSet_finite.toFinset.card : ℝ) +
        2 * (S.cutEventSet_finite.toFinset.card : ℝ) ≤
      160 * (distortion K).toReal := by
  exact S.weightedEventCount_le.trans (by
    gcongr
    norm_num)

lemma outerScale_mem
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    S.outer.scale ∈ Ioc (superellipsoidInnerFactor * r)
      (superellipsoidOuterFactor * r) :=
  S.outer.scale_mem

lemma cutHeight_mem
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    S.cut.height ∈ Ioc (c.ofLp (frame 2) - shellEpsilon * r)
      (c.ofLp (frame 2) + shellEpsilon * r) :=
  S.cut.toSmoothCarrierPlaneSelection.height_mem

lemma originalBox_subset_outerBody
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) (hr : 0 < r) :
    orientedBox frame c r ⊆ superellipsoidBody frame c S.outer.scale :=
  S.outer.orientedBox_subset_body hr

lemma cutOffset_le
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    |S.cut.height - c.ofLp (frame 2)| ≤ shellEpsilon * r :=
  abs_sub_center_le_of_mem_longPlane_interval S.cutHeight_mem

lemma lowerHalf_subset_successor
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) (hr : 0 < r) :
    superellipsoidBody frame c S.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ S.cut.height} ⊆
      orientedBox (axisCycle.trans frame)
        (lowerHalfCenter frame c S.outer.scale S.cut.height)
        (successorScale S.outer.scale r) :=
  S.outer.lowerHalf_subset_successor hr S.cutOffset_le

lemma upperHalf_subset_successor
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) (hr : 0 < r) :
    superellipsoidBody frame c S.outer.scale ∩
        {x | S.cut.height ≤ x.ofLp (frame 2)} ⊆
      orientedBox (axisCycle.trans frame)
        (upperHalfCenter frame c S.outer.scale S.cut.height)
        (successorScale S.outer.scale r) :=
  S.outer.upperHalf_subset_successor hr S.cutOffset_le

end SuperellipsoidDoubleBubbleSelection

/-- Existence of the complete smooth selector once the finite regular-seam chart decomposition is
supplied for the outer surface chosen by planar Sard and coarea. -/
theorem exists_superellipsoidDoubleBubbleSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r))
    (hcharts : ∀ outer : SuperellipsoidOuterSelection K Phi frame c r,
      Nonempty (FiniteSuperellipsoidSeamCriticalChartCover
        Phi frame c outer.scale)) :
    Nonempty (SuperellipsoidDoubleBubbleSelection K Phi frame c r W) := by
  obtain ⟨outer⟩ := exists_superellipsoidOuterSelection K Phi frame c hr hfinite
  obtain ⟨charts⟩ := hcharts outer
  obtain ⟨cut⟩ := exists_superellipsoidRegularCutSelection_of_seamChartCover
    K Phi frame c hr hfinite W outer charts
  exact ⟨⟨outer, cut⟩⟩

/-- Natural geometric wrapper: it is enough to classify the regular outer seam into finitely
many complete rotated-gradient orbits modulo deck translation. -/
theorem exists_superellipsoidDoubleBubbleSelection_of_orbitCover
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r))
    (horbits : ∀ outer : SuperellipsoidOuterSelection K Phi frame c r,
      Nonempty (FiniteSuperellipsoidSeamOrbitCover
        Phi frame c outer.scale)) :
    Nonempty (SuperellipsoidDoubleBubbleSelection K Phi frame c r W) := by
  apply exists_superellipsoidDoubleBubbleSelection K Phi frame c hr hfinite W
  intro outer
  obtain ⟨orbits⟩ := horbits outer
  exact ⟨orbits.toCriticalChartCover⟩

end Submission.PardonDistortion
