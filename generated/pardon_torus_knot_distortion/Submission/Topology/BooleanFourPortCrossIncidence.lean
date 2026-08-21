import Submission.Topology.BooleanFourPortLocalPaths
import Submission.Topology.StandardFourPortRectangle

/-!
# Incidence between the two Boolean four-port resolutions

The vertical and horizontal paths in one chart meet exactly at their labelled common corner.
-/

open Set

noncomputable section

namespace Submission.Topology

namespace PairedSeamBandChart

variable (B : PairedSeamBandChart)

private theorem mapped_range_inter_singleton
    {a b c d z : Submission.SurfaceRegularValue.Plane} (p : Path a b) (q : Path c d)
    (hinter : Set.range p ∩ Set.range q = {z}) :
    Set.range (p.map B.chartEmbedding.continuous) ∩
        Set.range (q.map B.chartEmbedding.continuous) = {B.chart z} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    change B.chart (p u) = x at hu
    change B.chart (q v) = x at hv
    have hpq : p u = q v := B.chartEmbedding.injective (hu.trans hv.symm)
    have hz : p u ∈ Set.range p ∩ Set.range q :=
      ⟨⟨u, rfl⟩, ⟨v, hpq.symm⟩⟩
    rw [hinter] at hz
    exact hu.symm.trans (congrArg B.chart hz)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hz : z ∈ Set.range p ∩ Set.range q := by
      rw [hinter]
      rfl
    obtain ⟨u, hu⟩ := hz.1
    obtain ⟨v, hv⟩ := hz.2
    exact ⟨⟨u, by simpa only [Path.map_coe, Function.comp_apply] using congrArg B.chart hu⟩,
      ⟨v, by simpa only [Path.map_coe, Function.comp_apply] using congrArg B.chart hv⟩⟩

theorem range_leftPath_inter_bottomPath :
    Set.range B.leftPath ∩ Set.range B.bottomPath = {B.leftBottom} := by
  convert B.mapped_range_inter_singleton bandLeftPath bandBottomPath
    range_bandLeftPath_inter_bandBottomPath_eq using 1
  <;> rfl

theorem range_leftPath_inter_topPath :
    Set.range B.leftPath ∩ Set.range B.topPath = {B.leftTop} := by
  convert B.mapped_range_inter_singleton bandLeftPath bandTopPath
    range_bandLeftPath_inter_bandTopPath_eq using 1
  <;> rfl

theorem range_rightPath_inter_bottomPath :
    Set.range B.rightPath ∩ Set.range B.bottomPath = {B.rightBottom} := by
  convert B.mapped_range_inter_singleton bandRightPath bandBottomPath
    range_bandRightPath_inter_bandBottomPath_eq using 1
  <;> rfl

theorem range_rightPath_inter_topPath :
    Set.range B.rightPath ∩ Set.range B.topPath = {B.rightTop} := by
  convert B.mapped_range_inter_singleton bandRightPath bandTopPath (by
      rw [Set.inter_comm]
      exact range_bandTopPath_inter_bandRightPath_eq) using 1
  <;> rfl

end PairedSeamBandChart

private theorem finTwo_one_eq_succ_zero : (1 : Fin 2) = Fin.succ 0 := rfl

theorem booleanFourPortLocalPath_false_zero_apply
    {n : ℕ} (chart : Fin n → PairedSeamBandChart)
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = false)
    (t : unitInterval) :
    booleanFourPortLocalPath chart choice (b, 0) t = (chart b).leftPath t := by
  simp [booleanFourPortLocalPath, hb]

theorem booleanFourPortLocalPath_false_one_apply
    {n : ℕ} (chart : Fin n → PairedSeamBandChart)
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = false)
    (t : unitInterval) :
    booleanFourPortLocalPath chart choice (b, 1) t = (chart b).rightPath t := by
  unfold booleanFourPortLocalPath
  simp only
  rw [dif_neg (by simp [hb])]
  simp only [finTwo_one_eq_succ_zero, Fin.cases_succ, Fin.cases_zero, Path.cast_coe]

theorem booleanFourPortLocalPath_true_zero_apply
    {n : ℕ} (chart : Fin n → PairedSeamBandChart)
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = true)
    (t : unitInterval) :
    booleanFourPortLocalPath chart choice (b, 0) t = (chart b).bottomPath t := by
  simp [booleanFourPortLocalPath, hb]

theorem booleanFourPortLocalPath_true_one_apply
    {n : ℕ} (chart : Fin n → PairedSeamBandChart)
    (choice : Fin n → Bool) (b : Fin n) (hb : choice b = true)
    (t : unitInterval) :
    booleanFourPortLocalPath chart choice (b, 1) t = (chart b).topPath t := by
  unfold booleanFourPortLocalPath
  simp only
  rw [dif_pos hb]
  simp only [finTwo_one_eq_succ_zero, Fin.cases_succ, Fin.cases_zero, Path.cast_coe]

private theorem finTwo_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

/-- A vertical path and a horizontal path in the same Boolean chart meet at their common port. -/
theorem range_falseLocalPath_inter_trueLocalPath
    {n : ℕ} (chart : Fin n → PairedSeamBandChart)
    (falseChoice trueChoice : Fin n → Bool) (b : Fin n)
    (hfalse : falseChoice b = false) (htrue : trueChoice b = true)
    (side level : Fin 2) :
    Set.range (booleanFourPortLocalPath chart falseChoice (b, side)) ∩
        Set.range (booleanFourPortLocalPath chart trueChoice (b, level)) =
      {fourPortChartPoint chart (b, side, level)} := by
  rcases finTwo_eq_zero_or_one side with rfl | rfl <;>
    rcases finTwo_eq_zero_or_one level with rfl | rfl
  · rw [show Set.range (booleanFourPortLocalPath chart falseChoice (b, 0)) =
        Set.range (chart b).leftPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_false_zero_apply chart falseChoice b hfalse t]
    rw [show Set.range (booleanFourPortLocalPath chart trueChoice (b, 0)) =
        Set.range (chart b).bottomPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_true_zero_apply chart trueChoice b htrue t]
    simpa only [fourPortChartPoint_zero_zero] using
      (chart b).range_leftPath_inter_bottomPath
  · rw [show Set.range (booleanFourPortLocalPath chart falseChoice (b, 0)) =
        Set.range (chart b).leftPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_false_zero_apply chart falseChoice b hfalse t]
    rw [show Set.range (booleanFourPortLocalPath chart trueChoice (b, 1)) =
        Set.range (chart b).topPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_true_one_apply chart trueChoice b htrue t]
    simpa only [fourPortChartPoint_zero_one] using
      (chart b).range_leftPath_inter_topPath
  · rw [show Set.range (booleanFourPortLocalPath chart falseChoice (b, 1)) =
        Set.range (chart b).rightPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_false_one_apply chart falseChoice b hfalse t]
    rw [show Set.range (booleanFourPortLocalPath chart trueChoice (b, 0)) =
        Set.range (chart b).bottomPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_true_zero_apply chart trueChoice b htrue t]
    simpa only [fourPortChartPoint_one_zero] using
      (chart b).range_rightPath_inter_bottomPath
  · rw [show Set.range (booleanFourPortLocalPath chart falseChoice (b, 1)) =
        Set.range (chart b).rightPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_false_one_apply chart falseChoice b hfalse t]
    rw [show Set.range (booleanFourPortLocalPath chart trueChoice (b, 1)) =
        Set.range (chart b).topPath from congrArg Set.range <| funext fun t ↦
          booleanFourPortLocalPath_true_one_apply chart trueChoice b htrue t]
    simpa only [fourPortChartPoint_one_one] using
      (chart b).range_rightPath_inter_topPath

end Submission.Topology
