import Submission.Torus.AmbientTransfer

/-!
# Local planar charts for the transported torus

The circle exponential is a local homeomorphism.  Taking two chosen local inverses gives a
product chart on `Circle × Circle`; transporting this chart through the global torus
homeomorphism gives a planar chart at every point of the embedded transported torus.

Because the chart source is open, it contains a positive-radius ball in the subtype metric.  The
underlying ambient points of this ball are exactly the intersection of the transported torus with
the corresponding ambient ball in `R3`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-- A chosen real coordinate chart around a point of the unit circle. -/
def circleChartAt (z : Circle) : OpenPartialHomeomorph Circle ℝ :=
  isLocalHomeomorph_circleExp.localInverseAt (z : ℂ).arg

theorem mem_circleChartAt_source (z : Circle) : z ∈ (circleChartAt z).source := by
  simpa only [circleChartAt, Circle.exp_arg] using
    (isLocalHomeomorph_circleExp.apply_self_mem_localInverseAt_source (x := (z : ℂ).arg))

/-- The product of the two chosen circle charts. -/
def circleProductChartAt (z : Circle × Circle) :
    OpenPartialHomeomorph (Circle × Circle) (ℝ × ℝ) :=
  (circleChartAt z.1).prod (circleChartAt z.2)

theorem mem_circleProductChartAt_source (z : Circle × Circle) :
    z ∈ (circleProductChartAt z).source := by
  rw [circleProductChartAt, OpenPartialHomeomorph.prod_source]
  exact ⟨mem_circleChartAt_source z.1, mem_circleChartAt_source z.2⟩

/-- A local planar chart on the transported torus at `x`. -/
def transportedTorusChart (Phi : AmbientIsotopy) (x : transportedTorus Phi) :
    OpenPartialHomeomorph (transportedTorus Phi) (ℝ × ℝ) :=
  (transportedTorusHomeomorph Phi).symm.toOpenPartialHomeomorph.trans
    (circleProductChartAt ((transportedTorusHomeomorph Phi).symm x))

theorem mem_transportedTorusChart_source (Phi : AmbientIsotopy)
    (x : transportedTorus Phi) : x ∈ (transportedTorusChart Phi x).source := by
  rw [transportedTorusChart, OpenPartialHomeomorph.trans_source]
  exact ⟨mem_univ x,
    mem_circleProductChartAt_source ((transportedTorusHomeomorph Phi).symm x)⟩

/-- Every point of the transported torus has a positive-radius surface ball contained in one
planar chart. -/
theorem exists_pos_ball_subset_transportedTorusChart_source
    (Phi : AmbientIsotopy) (x : transportedTorus Phi) :
    ∃ r > 0, Metric.ball x r ⊆ (transportedTorusChart Phi x).source := by
  exact Metric.mem_nhds_iff.mp <|
    (transportedTorusChart Phi x).open_source.mem_nhds
      (mem_transportedTorusChart_source Phi x)

/-- A subtype ball on the transported torus is exactly an ambient ball intersected with that
torus, after forgetting the subtype proof. -/
theorem image_subtype_ball_eq_ambient_ball_inter_transportedTorus
    (Phi : AmbientIsotopy) (x : transportedTorus Phi) (r : ℝ) :
    ((fun y : transportedTorus Phi ↦ (y : R3)) '' Metric.ball x r) =
      Metric.ball (x : R3) r ∩ transportedTorus Phi := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by simpa [Metric.mem_ball, Subtype.dist_eq] using hz, z.property⟩
  · rintro ⟨hyball, hytorus⟩
    refine ⟨⟨y, hytorus⟩, ?_, rfl⟩
    simpa [Metric.mem_ball, Subtype.dist_eq] using hyball

/-- A positive-radius surface ball has open image in the coordinate plane. -/
theorem exists_planar_open_image_of_transportedTorus_ball
    (Phi : AmbientIsotopy) (x : transportedTorus Phi) :
    ∃ r > 0,
      Metric.ball x r ⊆ (transportedTorusChart Phi x).source ∧
      IsOpen (transportedTorusChart Phi x '' Metric.ball x r) := by
  obtain ⟨r, hr, hrsub⟩ :=
    exists_pos_ball_subset_transportedTorusChart_source Phi x
  exact ⟨r, hr, hrsub,
    (transportedTorusChart Phi x).isOpen_image_of_subset_source Metric.isOpen_ball hrsub⟩

/-- On the positive-radius chart ball, the planar coordinates are one-to-one. -/
theorem exists_pos_ball_injOn_transportedTorusChart
    (Phi : AmbientIsotopy) (x : transportedTorus Phi) :
    ∃ r > 0,
      Metric.ball x r ⊆ (transportedTorusChart Phi x).source ∧
      InjOn (transportedTorusChart Phi x) (Metric.ball x r) := by
  obtain ⟨r, hr, hrsub⟩ :=
    exists_pos_ball_subset_transportedTorusChart_source Phi x
  exact ⟨r, hr, hrsub, (transportedTorusChart Phi x).injOn.mono hrsub⟩

/-- Restrict the transported-torus chart to a subtype-metric ball. -/
def transportedTorusBallChart (Phi : AmbientIsotopy) (x : transportedTorus Phi) (r : ℝ) :
    OpenPartialHomeomorph (transportedTorus Phi) (ℝ × ℝ) :=
  (transportedTorusChart Phi x).restr (Metric.ball x r)

theorem transportedTorusBallChart_source_eq (Phi : AmbientIsotopy)
    (x : transportedTorus Phi) {r : ℝ}
    (hr : Metric.ball x r ⊆ (transportedTorusChart Phi x).source) :
    (transportedTorusBallChart Phi x r).source = Metric.ball x r := by
  change ((transportedTorusChart Phi x).restr (Metric.ball x r)).source =
    Metric.ball x r
  calc
    ((transportedTorusChart Phi x).restr (Metric.ball x r)).source =
        (transportedTorusChart Phi x).source ∩ Metric.ball x r :=
      OpenPartialHomeomorph.restr_source' _ _ Metric.isOpen_ball
    _ = Metric.ball x r := inter_eq_right.mpr hr

/-- The positive-radius surface ball is homeomorphic to an open subset of the coordinate plane. -/
def transportedTorusBallHomeomorph (Phi : AmbientIsotopy)
    (x : transportedTorus Phi) {r : ℝ}
    (hr : Metric.ball x r ⊆ (transportedTorusChart Phi x).source) :
    Metric.ball x r ≃ₜ (transportedTorusBallChart Phi x r).target :=
  (Homeomorph.setCongr (transportedTorusBallChart_source_eq Phi x hr).symm).trans
    (transportedTorusBallChart Phi x r).toHomeomorphSourceTarget

/-- Local flatness in an existential form: every transported-torus point has a positive-radius
surface ball homeomorphic to an open subset of `ℝ × ℝ`. -/
theorem exists_pos_ball_homeomorphic_to_open_plane
    (Phi : AmbientIsotopy) (x : transportedTorus Phi) :
    ∃ r > 0, ∃ v : Set (ℝ × ℝ), IsOpen v ∧ Nonempty (Metric.ball x r ≃ₜ v) := by
  obtain ⟨r, hr, hrsub⟩ :=
    exists_pos_ball_subset_transportedTorusChart_source Phi x
  refine ⟨r, hr, (transportedTorusBallChart Phi x r).target,
    (transportedTorusBallChart Phi x r).open_target, ?_⟩
  exact ⟨transportedTorusBallHomeomorph Phi x hrsub⟩

/-- Compactness upgrades the pointwise chart radii to one uniform Lebesgue radius: every
surface ball of this radius lies in some planar coordinate chart. -/
theorem exists_uniform_pos_ball_subset_transportedTorusChart_source
    (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ y : transportedTorus Phi, ∃ x : transportedTorus Phi,
      Metric.ball y δ ⊆ (transportedTorusChart Phi x).source := by
  let _ : CompactSpace (transportedTorus Phi) :=
    (transportedTorusHomeomorph Phi).compactSpace
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set (transportedTorus Phi)))
      (c := fun x : transportedTorus Phi ↦ (transportedTorusChart Phi x).source)
      isCompact_univ
      (fun x ↦ (transportedTorusChart Phi x).open_source)
      (fun y _ ↦ mem_iUnion.mpr ⟨y, mem_transportedTorusChart_source Phi y⟩)
  exact ⟨δ, hδ, fun y ↦ hball y (mem_univ y)⟩

end Submission.Topology
