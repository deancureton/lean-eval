import Submission.Topology.GlobalBandLiftedTubularChart
import Submission.Topology.FourPortSixEdgeBandRotation
import Submission.Topology.JordanTranslate

/-!
# The lifted local rectangle lies in the global four-port band

The coherent six-edge rectangle and the rectangle obtained by lifting its projection through the
global band chart are two lifts of the same parametrized Jordan circle.  They therefore differ by
one deck translation.  The retained chart sheet has preconnected unbounded complement, so the
whole closed disk of the chart lift stays in that sheet.  Deck invariance then puts the original
closed rectangle disk in the four-port band.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData EmbeddedTorusIntersectionCircle

namespace FourPortRawSixEdgeBandPresentation

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : G.CutCircleTransverseCyclicOrderFamily}
  {b : Fin F.toPairedSeamEnumeration.bandCount}
  (T : F.LiftedGlobalBandTubularChartData b)
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {C : FourPortRawCircleData raw}
  (P : FourPortRawSixEdgeBandPresentation C)

private theorem projected_plane_localRectangle_subset_graph_localRectangle :
    torusCoveringProjectionToTorus Phi '' P.planePathSystem.localRectangleCarrier ⊆
      P.graph.localRectangleCarrier := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [P.planePathSystem.localRectangleCarrier_eq] at hy
  rw [P.graph.localRectangleCarrier_eq]
  rcases hy with ((hy | hy) | hy) | hy
  · obtain ⟨t, rfl⟩ := hy
    left
    left
    left
    exact ⟨t,
      (P.toFourPortRawSixEdgePresentation.zeroWindingData.projection_leftPlanePath t).symm⟩
  · obtain ⟨t, rfl⟩ := hy
    left
    left
    right
    exact ⟨t,
      (P.toFourPortRawSixEdgePresentation.zeroWindingData.projection_topPlanePath t).symm⟩
  · obtain ⟨t, rfl⟩ := hy
    left
    right
    exact ⟨t,
      (P.toFourPortRawSixEdgePresentation.zeroWindingData.projection_rightPlanePath t).symm⟩
  · obtain ⟨t, rfl⟩ := hy
    right
    exact ⟨t,
      (P.toFourPortRawSixEdgePresentation.zeroWindingData.projection_bottomPlanePath t).symm⟩

private theorem graph_localRectangle_subset_surfacePatch :
    P.graph.localRectangleCarrier ⊆ T.surfacePatch := by
  intro x hx
  rw [P.graph.localRectangleCarrier_eq] at hx
  have hxBand :
      x ∈ fourPortParallelPart
          T.toGlobalBandTubularChartData.toPairedSeamBandChart ∪
        fourPortSurgeryPart
          T.toGlobalBandTubularChartData.toPairedSeamBandChart := by
    rcases hx with ((hx | hx) | hx) | hx
    · left
      rw [← P.parallelCarrier_eq]
      exact Or.inl hx
    · right
      rw [← P.surgeryCarrier_eq]
      exact Or.inr hx
    · left
      rw [← P.parallelCarrier_eq]
      exact Or.inr hx
    · right
      rw [← P.surgeryCarrier_eq]
      exact Or.inl hx
  rcases hxBand with hxParallel | hxSurgery
  · change (x : R3) ∈
      T.toGlobalBandTubularChartData.toPairedSeamBandChart.parallelPatch at hxParallel
    rcases hxParallel with hxLeft | hxRight
    · obtain ⟨t, ht⟩ := hxLeft
      have hvalue : x = T.strip (bandLeftPath t) := by
        apply Subtype.ext
        exact ht.symm
      rw [hvalue]
      exact (T.strip (bandLeftPath t)).2
    · obtain ⟨t, ht⟩ := hxRight
      have hvalue : x = T.strip (bandRightPath t) := by
        apply Subtype.ext
        exact ht.symm
      rw [hvalue]
      exact (T.strip (bandRightPath t)).2
  · change (x : R3) ∈
      T.toGlobalBandTubularChartData.toPairedSeamBandChart.surgeryPatch at hxSurgery
    rcases hxSurgery with hxBottom | hxTop
    · obtain ⟨t, ht⟩ := hxBottom
      have hvalue : x = T.strip (bandBottomPath t) := by
        apply Subtype.ext
        exact ht.symm
      rw [hvalue]
      exact (T.strip (bandBottomPath t)).2
    · obtain ⟨t, ht⟩ := hxTop
      have hvalue : x = T.strip (bandTopPath t) := by
        apply Subtype.ext
        exact ht.symm
      rw [hvalue]
      exact (T.strip (bandTopPath t)).2

private theorem projected_planeRectangle_subset_surfacePatch :
    torusCoveringProjectionToTorus Phi ''
        (P.planePathSystem.localRectangleJordanCircle
          P.planePathSystem.localRectangleData).carrier ⊆
      T.surfacePatch := by
  rw [P.planePathSystem.carrier_localRectangleJordanCircle]
  exact P.projected_plane_localRectangle_subset_graph_localRectangle.trans
    (P.graph_localRectangle_subset_surfacePatch T)

private theorem projection_plane_localRectangleUpperPath (t : unitInterval) :
    torusCoveringProjectionToTorus Phi
        (P.planePathSystem.localRectangleUpperPath t) =
      P.graph.localRectangleUpperPath t := by
  let Z := P.toFourPortRawSixEdgePresentation.zeroWindingData
  change torusCoveringProjectionToTorus Phi
      (((Z.planePathSystem.left.trans Z.planePathSystem.top).trans
        Z.planePathSystem.right.symm) t) =
    ((P.graph.left.trans P.graph.top).trans P.graph.right.symm) t
  simp only [Path.trans_apply]
  split
  · split
    · exact Z.projection_leftPlanePath _
    · exact Z.projection_topPlanePath _
  · change torusCoveringProjectionToTorus Phi (Z.rightPlanePath.symm _) =
      P.graph.right.symm _
    simpa only [Path.symm_apply, Function.comp_apply] using
      Z.projection_rightPlanePath _

private theorem projection_plane_localRectangleParametrization
    (z : Metric.sphere (0 : Schoenflies.Plane) 1) :
    torusCoveringProjectionToTorus Phi
        ((P.planePathSystem.localRectangleJordanCircle
          P.planePathSystem.localRectangleData).parametrization z) =
      P.graph.localRectangleCircle P.graph.localRectangleData
        (JordanCurve.Arcs.spherePlaneHomeoCircle z) := by
  change torusCoveringProjectionToTorus Phi
      (TwoArcCircle.circleMap P.planePathSystem.localRectangleUpperPath
        P.planePathSystem.bottom.symm
        (JordanCurve.Arcs.spherePlaneHomeoCircle z)) = _
  apply TwoArcCircle.map_circleMap_of_pointwise
  · exact P.projection_plane_localRectangleUpperPath _
  · intro t
    change torusCoveringProjectionToTorus Phi
        (P.toFourPortRawSixEdgePresentation.zeroWindingData.bottomPlanePath
          (unitInterval.symm t)) =
      P.graph.bottom (unitInterval.symm t)
    simpa only [Path.symm_apply, Function.comp_apply] using
      P.toFourPortRawSixEdgePresentation.zeroWindingData.projection_bottomPlanePath
        (unitInterval.symm t)

private def projectedPlaneRectangleInSurface
    (z : Metric.sphere (0 : Schoenflies.Plane) 1) : T.surfacePatch :=
  ⟨torusCoveringProjectionToTorus Phi
      ((P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).parametrization z),
    P.projected_planeRectangle_subset_surfacePatch T
      ⟨_, ⟨z, rfl⟩, rfl⟩⟩

private theorem continuous_projectedPlaneRectangleInSurface :
    Continuous (P.projectedPlaneRectangleInSurface T) := by
  apply Continuous.subtype_mk
  exact (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.comp
    (P.planePathSystem.localRectangleJordanCircle
      P.planePathSystem.localRectangleData).continuous

private def chartRectangleLiftParametrization
    (z : Metric.sphere (0 : Schoenflies.Plane) 1) : TorusCoveringPlane :=
  T.liftedStrip
    (T.strip.symm (P.projectedPlaneRectangleInSurface T z))

private theorem continuous_chartRectangleLiftParametrization :
    Continuous (P.chartRectangleLiftParametrization T) :=
  by
    unfold chartRectangleLiftParametrization
    exact (continuous_subtype_val.comp
      (T.liftedStrip.continuous.comp (T.strip.symm.continuous.comp
        (P.continuous_projectedPlaneRectangleInSurface T)))).congr
          (fun _ ↦ rfl)

private theorem projection_chartRectangleLiftParametrization
    (z : Metric.sphere (0 : Schoenflies.Plane) 1) :
    torusCoveringProjectionToTorus Phi
        (P.chartRectangleLiftParametrization T z) =
      torusCoveringProjectionToTorus Phi
        ((P.planePathSystem.localRectangleJordanCircle
          P.planePathSystem.localRectangleData).parametrization z) := by
  rw [chartRectangleLiftParametrization, T.projection_liftedStrip,
    T.strip.apply_symm_apply]
  rfl

private theorem chartRectangleLiftParametrization_injective :
    Function.Injective (P.chartRectangleLiftParametrization T) := by
  intro z w hzw
  unfold chartRectangleLiftParametrization at hzw
  have hcoordinate := T.liftedStrip.injective (Subtype.ext hzw)
  have hsurface := T.strip.symm.injective hcoordinate
  have hprojection := congrArg Subtype.val hsurface
  change torusCoveringProjectionToTorus Phi
      ((P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).parametrization z) =
    torusCoveringProjectionToTorus Phi
      ((P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).parametrization w) at hprojection
  rw [P.projection_plane_localRectangleParametrization,
    P.projection_plane_localRectangleParametrization] at hprojection
  exact JordanCurve.Arcs.spherePlaneHomeoCircle.injective <|
    P.graph.localRectangleCircle_injective P.graph.localRectangleData hprojection

private def chartRectangleLiftJordanCircle : Schoenflies.JordanCircle where
  parametrization := P.chartRectangleLiftParametrization T
  continuous := P.continuous_chartRectangleLiftParametrization T
  injective := P.chartRectangleLiftParametrization_injective T

private theorem chartRectangleLiftJordanCircle_carrier_subset_liftedPatch :
    (P.chartRectangleLiftJordanCircle T).carrier ⊆ T.liftedPatch := by
  rintro _ ⟨z, rfl⟩
  exact (T.liftedStrip (T.strip.symm
    (P.projectedPlaneRectangleInSurface T z))).2

private def planeRectangleCircleLift (z : Circle) : TorusCoveringPlane :=
  (P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData).parametrization
      (JordanCurve.Arcs.spherePlaneHomeoCircle.symm z)

private def chartRectangleCircleLift (z : Circle) : TorusCoveringPlane :=
  (P.chartRectangleLiftJordanCircle T).parametrization
    (JordanCurve.Arcs.spherePlaneHomeoCircle.symm z)

private theorem continuous_planeRectangleCircleLift :
    Continuous P.planeRectangleCircleLift :=
  (P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData).continuous.comp
      JordanCurve.Arcs.spherePlaneHomeoCircle.symm.continuous

private theorem continuous_chartRectangleCircleLift :
    Continuous (P.chartRectangleCircleLift T) :=
  (P.chartRectangleLiftJordanCircle T).continuous.comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.symm.continuous

private theorem exists_rectangleParametrization_eq_chart_add_lattice :
    ∃ k : Fin 2 → ℤ, ∀ z,
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).parametrization z =
      (P.chartRectangleLiftJordanCircle T).parametrization z +
        torusLatticeVector k := by
  obtain ⟨k, hk⟩ := exists_planeCircleLift_eq_add_lattice
    P.planeRectangleCircleLift (P.chartRectangleCircleLift T)
    P.continuous_planeRectangleCircleLift
    (P.continuous_chartRectangleCircleLift T) (by
      intro z
      exact P.projection_chartRectangleLiftParametrization T
        (JordanCurve.Arcs.spherePlaneHomeoCircle.symm z) |>.symm)
  refine ⟨k, fun z ↦ ?_⟩
  simpa only [planeRectangleCircleLift, chartRectangleCircleLift,
    Homeomorph.symm_apply_apply] using
      hk (JordanCurve.Arcs.spherePlaneHomeoCircle z)

private theorem planeRectangle_carrier_eq_chart_translate
    (k : Fin 2 → ℤ)
    (hk : ∀ z,
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).parametrization z =
      (P.chartRectangleLiftJordanCircle T).parametrization z +
        torusLatticeVector k) :
    (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).carrier =
      ((P.chartRectangleLiftJordanCircle T).translate
        (torusLatticeVector k)).carrier := by
  rw [Schoenflies.JordanCircle.carrier_translate]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, (hk z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, hk z⟩

/-- The retained global covering sheet supplies the exact chart input needed to orient the
coherent six-edge rectangle. -/
theorem rectangleBandContainmentData : P.RectangleBandContainmentData := by
  obtain ⟨k, hk⟩ := P.exists_rectangleParametrization_eq_chart_add_lattice T
  let J := P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData
  let K := P.chartRectangleLiftJordanCircle T
  have hcarrier : J.carrier = (K.translate (torusLatticeVector k)).carrier :=
    P.planeRectangle_carrier_eq_chart_translate T k hk
  have hinside : J.inside = (K.translate (torusLatticeVector k)).inside :=
    Schoenflies.JordanCircle.inside_eq_of_carrier_eq J
      (K.translate (torusLatticeVector k)) hcarrier
  refine ⟨?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxTranslated : x ∈ closure (K.translate (torusLatticeVector k)).inside := by
    rwa [← hinside]
  rw [Schoenflies.JordanCircle.closure_inside_translate] at hxTranslated
  obtain ⟨y, hy, rfl⟩ := hxTranslated
  have hyPatch : y ∈ T.liftedPatch :=
    T.closure_inside_subset_liftedPatch K
      (P.chartRectangleLiftJordanCircle_carrier_subset_liftedPatch T) hy
  rw [torusCoveringProjectionToTorus_add_lattice]
  obtain ⟨u, hu⟩ := T.liftedStrip.surjective ⟨y, hyPatch⟩
  have hyEq : y = T.liftedStrip u := by
    exact (congrArg Subtype.val hu).symm
  have hprojection : torusCoveringProjectionToTorus Phi y = T.strip u := by
    rw [hyEq]
    exact T.projection_liftedStrip u
  change ((torusCoveringProjectionToTorus Phi y : transportedTorus Phi) : R3) ∈
    T.toGlobalBandTubularChartData.toPairedSeamBandChart.support
  rw [hprojection]
  exact T.strip_mem_neighborhood ⟨u, rfl⟩

end FourPortRawSixEdgeBandPresentation
end Submission.Topology
