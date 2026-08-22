import Submission.Topology.FiniteAlternatingTorusCircleSection
import Submission.Topology.PlanarFourPortDiagonalObstruction

/-!
# The three canonical cycles of a diagonal four-port graph

The diagonal six-edge graph has three distinguished embedded cycles: the vertical resolution,
the horizontal resolution, and the local rectangle.  Exact `K₄` incidence proves embeddedness of
all three cycles.  This packages their winding-zero hypotheses for the covering-plane argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy}

namespace FourPortDiagonalPathSystem

variable (G : FourPortDiagonalPathSystem (transportedTorus Phi))

/-- The three-edge part of the vertical-resolution cycle. -/
def preFirst : Path G.leftBottom G.rightTop :=
  (G.left.trans G.lower).trans G.right

/-- The three-edge part of the horizontal-resolution cycle. -/
def postFirst : Path G.leftBottom G.rightTop :=
  (G.bottom.trans G.lower.symm).trans G.top

/-- The first half of the local rectangle cycle. -/
def rectangleFirst : Path G.leftBottom G.rightTop :=
  G.left.trans G.top

/-- The oppositely oriented second half of the local rectangle cycle. -/
def rectangleSecond : Path G.rightTop G.leftBottom :=
  (G.bottom.trans G.right).symm

private theorem left_inter_lower :
    range G.left ∩ range G.lower = {G.leftTop} := by
  rw [inter_comm]
  exact G.lower_inter_left

private theorem bottom_inter_lower_symm :
    range G.bottom ∩ range G.lower.symm = {G.rightBottom} := by
  rw [Path.symm_range, inter_comm]
  exact G.lower_inter_bottom

private theorem left_lower_inter_right :
    range (G.left.trans G.lower) ∩ range G.right = {G.rightBottom} := by
  rw [Path.trans_range, union_inter_distrib_right, G.left_inter_right,
    G.lower_inter_right, empty_union]

private theorem bottom_lower_inter_top :
    range (G.bottom.trans G.lower.symm) ∩ range G.top = {G.leftTop} := by
  have hbottomTop : range G.bottom ∩ range G.top = ∅ := by
    rw [inter_comm]
    exact G.top_inter_bottom
  rw [Path.trans_range, Path.symm_range, union_inter_distrib_right,
    hbottomTop, G.lower_inter_top, empty_union]

theorem preFirst_injective : Function.Injective G.preFirst := by
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
  · exact LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      G.left G.lower G.left_injective G.lower_injective G.left_inter_lower
  · exact G.right_injective
  · exact G.left_lower_inter_right

theorem postFirst_injective : Function.Injective G.postFirst := by
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
  · apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    · exact G.bottom_injective
    · intro s t hst
      apply unitInterval.symm_bijective.injective
      apply G.lower_injective
      simpa only [Path.symm_apply, Function.comp_apply] using hst
    · exact G.bottom_inter_lower_symm
  · exact G.top_injective
  · exact G.bottom_lower_inter_top

theorem rectangleFirst_injective : Function.Injective G.rectangleFirst :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    G.left G.top G.left_injective G.top_injective G.left_inter_top

theorem rectangleSecond_injective : Function.Injective G.rectangleSecond := by
  intro s t hst
  apply unitInterval.symm_bijective.injective
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    G.bottom G.right G.bottom_injective G.right_injective G.bottom_inter_right
  simpa only [rectangleSecond, Path.symm_apply, Function.comp_apply] using hst

private theorem left_inter_upper :
    range G.left ∩ range G.upper = {G.leftBottom} := by
  rw [inter_comm]
  exact G.upper_inter_left

private theorem right_inter_upper :
    range G.right ∩ range G.upper = {G.rightTop} := by
  rw [inter_comm]
  exact G.upper_inter_right

private theorem bottom_inter_upper :
    range G.bottom ∩ range G.upper = {G.leftBottom} := by
  rw [inter_comm]
  exact G.upper_inter_bottom

private theorem top_inter_upper :
    range G.top ∩ range G.upper = {G.rightTop} := by
  rw [inter_comm]
  exact G.upper_inter_top

theorem preFirst_inter_upper :
    range G.preFirst ∩ range G.upper = {G.leftBottom, G.rightTop} := by
  rw [preFirst, Path.trans_range, Path.trans_range, union_inter_distrib_right,
    union_inter_distrib_right, G.left_inter_upper, G.lower_inter_upper,
    G.right_inter_upper, union_empty]
  ext x
  simp only [mem_union, mem_singleton_iff, mem_insert_iff]

theorem postFirst_inter_upper :
    range G.postFirst ∩ range G.upper = {G.leftBottom, G.rightTop} := by
  rw [postFirst, Path.trans_range, Path.trans_range, Path.symm_range,
    union_inter_distrib_right, union_inter_distrib_right, G.bottom_inter_upper,
    G.lower_inter_upper, G.top_inter_upper, union_empty]
  ext x
  simp only [mem_union, mem_singleton_iff, mem_insert_iff]

theorem rectangleFirst_inter_rectangleSecond :
    range G.rectangleFirst ∩ range G.rectangleSecond =
      {G.leftBottom, G.rightTop} := by
  rw [rectangleFirst, rectangleSecond, Path.symm_range, Path.trans_range,
    Path.trans_range, union_inter_distrib_right, inter_union_distrib_left,
    inter_union_distrib_left, G.left_inter_bottom, G.left_inter_right,
    G.top_inter_bottom, G.top_inter_right, union_empty, empty_union]
  ext x
  simp only [mem_union, mem_singleton_iff, mem_insert_iff]

/-- Exact two-arc data for the vertical-resolution cycle. -/
theorem preData : TwoArcCircle.Data G.preFirst G.upper where
  first_injective := G.preFirst_injective
  second_injective := G.upper_injective
  range_inter := G.preFirst_inter_upper

/-- Exact two-arc data for the horizontal-resolution cycle. -/
theorem postData : TwoArcCircle.Data G.postFirst G.upper where
  first_injective := G.postFirst_injective
  second_injective := G.upper_injective
  range_inter := G.postFirst_inter_upper

/-- Exact two-arc data for the local rectangle cycle. -/
theorem rectangleData : TwoArcCircle.Data G.rectangleFirst G.rectangleSecond where
  first_injective := G.rectangleFirst_injective
  second_injective := G.rectangleSecond_injective
  range_inter := G.rectangleFirst_inter_rectangleSecond

/-- The vertical-resolution circle in the transported torus. -/
def preCircle : Circle → transportedTorus Phi :=
  TwoArcCircle.circleMap G.preFirst G.upper

/-- The horizontal-resolution circle in the transported torus. -/
def postCircle : Circle → transportedTorus Phi :=
  TwoArcCircle.circleMap G.postFirst G.upper

/-- The local rectangle circle in the transported torus. -/
def rectangleCircle : Circle → transportedTorus Phi :=
  TwoArcCircle.circleMap G.rectangleFirst G.rectangleSecond

theorem preCircle_isEmbedding : IsEmbedding G.preCircle :=
  G.preData.isEmbedding

theorem postCircle_isEmbedding : IsEmbedding G.postCircle :=
  G.postData.isEmbedding

theorem rectangleCircle_isEmbedding : IsEmbedding G.rectangleCircle :=
  G.rectangleData.isEmbedding

/-- The vertical-resolution cycle as an embedded torus-intersection circle. -/
def preTorusCircle : EmbeddedTorusIntersectionCircle Phi :=
  EmbeddedTorusIntersectionCircle.ofTorusEmbedding G.preCircle G.preCircle_isEmbedding

/-- The horizontal-resolution cycle as an embedded torus-intersection circle. -/
def postTorusCircle : EmbeddedTorusIntersectionCircle Phi :=
  EmbeddedTorusIntersectionCircle.ofTorusEmbedding G.postCircle G.postCircle_isEmbedding

/-- The local rectangle as an embedded torus-intersection circle. -/
def rectangleTorusCircle : EmbeddedTorusIntersectionCircle Phi :=
  EmbeddedTorusIntersectionCircle.ofTorusEmbedding G.rectangleCircle
    G.rectangleCircle_isEmbedding

@[simp] theorem preTorusCircle_apply (z : Circle) :
    G.preTorusCircle.circle z = G.preCircle z := rfl

@[simp] theorem postTorusCircle_apply (z : Circle) :
    G.postTorusCircle.circle z = G.postCircle z := rfl

@[simp] theorem rectangleTorusCircle_apply (z : Circle) :
    G.rectangleTorusCircle.circle z = G.rectangleCircle z := rfl

theorem range_preCircle :
    range G.preCircle =
      ((range G.left ∪ range G.lower) ∪ range G.right) ∪ range G.upper := by
  rw [preCircle, TwoArcCircle.range_circleMap, preFirst, Path.trans_range,
    Path.trans_range]

theorem range_postCircle :
    range G.postCircle =
      ((range G.bottom ∪ range G.lower) ∪ range G.top) ∪ range G.upper := by
  rw [postCircle, TwoArcCircle.range_circleMap, postFirst, Path.trans_range,
    Path.trans_range, Path.symm_range]

theorem range_rectangleCircle :
    range G.rectangleCircle =
      (range G.left ∪ range G.top) ∪ (range G.bottom ∪ range G.right) := by
  rw [rectangleCircle, TwoArcCircle.range_circleMap, rectangleFirst, rectangleSecond,
    Path.trans_range, Path.symm_range, Path.trans_range]

/-- The exact winding hypotheses used to align all six edges in one covering-plane sheet. -/
structure ZeroWindingData : Prop where
  pre : G.preTorusCircle.windingLoop.windingPair = (0, 0)
  post : G.postTorusCircle.windingLoop.windingPair = (0, 0)
  rectangle : G.rectangleTorusCircle.windingLoop.windingPair = (0, 0)

end FourPortDiagonalPathSystem
end Submission.Topology
