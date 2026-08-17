import Submission.Topology.FourPortQuadraticLabelChange
import Submission.Topology.FourPortSixEdgeLiftedBandContainment

/-!
# The quadratic four-port rectangle as the lifted chart disk

The retained global chart carries the standard closed coordinate rectangle to a compact regular
closed disk in the torus covering plane.  Its frontier is exactly the lifted coherent rectangle
circle.  Consequently the entire chart rectangle lies on the closed bounded side of that circle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

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

/-- The standard closed rectangle transported through the retained covering-plane chart. -/
def chartClosedRectangle : Set TorusCoveringPlane :=
  (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) '' fourPortClosedRectangle

private theorem continuous_chartMap :
    Continuous (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) :=
  continuous_subtype_val.comp T.liftedStrip.continuous

private theorem chartMap_injective :
    Function.Injective (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) := by
  intro u v huv
  exact T.liftedStrip.injective (Subtype.ext huv)

private theorem chartMap_isOpenEmbedding :
    IsOpenEmbedding (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) :=
  T.liftedPatch_open.isOpenEmbedding_subtypeVal.comp T.liftedStrip.isOpenEmbedding

theorem isCompact_chartClosedRectangle : IsCompact (chartClosedRectangle T) :=
  isCompact_fourPortClosedRectangle.image (continuous_chartMap T)

theorem isClosed_chartClosedRectangle : IsClosed (chartClosedRectangle T) :=
  isCompact_chartClosedRectangle T |>.isClosed

theorem isBounded_chartClosedRectangle :
    Bornology.IsBounded (chartClosedRectangle T) :=
  isCompact_chartClosedRectangle T |>.isBounded

theorem interior_chartClosedRectangle :
    interior (chartClosedRectangle T) =
      (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) ''
        interior fourPortClosedRectangle := by
  let f : FourPortPlane → TorusCoveringPlane :=
    fun u ↦ (T.liftedStrip u : TorusCoveringPlane)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, _, rfl⟩ := interior_subset hx
    refine ⟨u, ?_, rfl⟩
    have hopen : IsOpen (f ⁻¹' interior (chartClosedRectangle T)) :=
      isOpen_interior.preimage (continuous_chartMap T)
    apply interior_maximal _ hopen hx
    intro v hv
    obtain ⟨w, hw, heq⟩ := interior_subset hv
    have hwv : w = v := chartMap_injective T heq
    simpa only [hwv] using hw
  · apply interior_maximal
    · exact image_mono interior_subset
    · exact chartMap_isOpenEmbedding T |>.isOpenMap _ isOpen_interior

theorem closure_interior_chartClosedRectangle :
    closure (interior (chartClosedRectangle T)) = chartClosedRectangle T := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (isClosed_chartClosedRectangle T)
  · rw [interior_chartClosedRectangle T]
    rintro _ ⟨u, hu, rfl⟩
    rw [← closure_interior_fourPortClosedRectangle] at hu
    exact image_closure_subset_closure_image (continuous_chartMap T)
      ⟨u, hu, rfl⟩

theorem frontier_chartClosedRectangle :
    frontier (chartClosedRectangle T) =
      (fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) ''
        frontier fourPortClosedRectangle := by
  rw [frontier, (isClosed_chartClosedRectangle T).closure_eq]
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hnotInterior⟩
    refine ⟨u, ?_, rfl⟩
    rw [frontier, isClosed_fourPortClosedRectangle.closure_eq]
    refine ⟨hu, ?_⟩
    intro huInterior
    apply hnotInterior
    rw [interior_chartClosedRectangle T]
    exact ⟨u, huInterior, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rw [frontier, isClosed_fourPortClosedRectangle.closure_eq] at hu
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    intro huInterior
    rw [interior_chartClosedRectangle T] at huInterior
    obtain ⟨v, hv, hvu⟩ := huInterior
    exact hu.2 <| by
      have hvu' : v = u := chartMap_injective T hvu
      simpa only [hvu'] using hv

private theorem image_chartMap_frontier_eq_graph_localRectangleCarrier :
    torusCoveringProjectionToTorus Phi ''
        ((fun u ↦ (T.liftedStrip u : TorusCoveringPlane)) ''
          frontier fourPortClosedRectangle) =
      P.graph.localRectangleCarrier := by
  have hvertical :
      (fun u ↦ (T.strip u : transportedTorus Phi)) '' fourPortVerticalCarrier =
        fourPortParallelPart
          T.toGlobalBandTubularChartData.toPairedSeamBandChart := by
    ext x
    change (∃ u ∈ fourPortVerticalCarrier,
        (T.strip u : transportedTorus Phi) = x) ↔
      (x : R3) ∈
        T.toGlobalBandTubularChartData.toPairedSeamBandChart.parallelPatch
    rw [← image_chart_fourPortVerticalCarrier
      T.toGlobalBandTubularChartData]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, Subtype.ext hux⟩
  have hhorizontal :
      (fun u ↦ (T.strip u : transportedTorus Phi)) '' fourPortHorizontalCarrier =
        fourPortSurgeryPart
          T.toGlobalBandTubularChartData.toPairedSeamBandChart := by
    ext x
    change (∃ u ∈ fourPortHorizontalCarrier,
        (T.strip u : transportedTorus Phi) = x) ↔
      (x : R3) ∈
        T.toGlobalBandTubularChartData.toPairedSeamBandChart.surgeryPatch
    rw [← image_chart_fourPortHorizontalCarrier
      T.toGlobalBandTubularChartData]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, Subtype.ext hux⟩
  rw [frontier_fourPortClosedRectangle]
  simp only [image_union, image_image]
  simp_rw [T.projection_liftedStrip]
  change
    (fun u ↦ (T.strip u : transportedTorus Phi)) '' fourPortVerticalCarrier ∪
        (fun u ↦ (T.strip u : transportedTorus Phi)) '' fourPortHorizontalCarrier = _
  rw [hvertical, hhorizontal, ← P.parallelCarrier_eq, ← P.surgeryCarrier_eq,
    P.graph.localRectangleCarrier_eq]
  ext x
  simp only [mem_union]
  tauto

theorem projection_image_frontier_chartClosedRectangle :
    torusCoveringProjectionToTorus Phi '' frontier (chartClosedRectangle T) =
      P.graph.localRectangleCarrier := by
  rw [frontier_chartClosedRectangle T]
  exact P.image_chartMap_frontier_eq_graph_localRectangleCarrier T

theorem projection_image_chartRectangleLiftJordanCircle_carrier :
    torusCoveringProjectionToTorus Phi ''
        (P.chartRectangleLiftJordanCircle T).carrier =
      P.graph.localRectangleCarrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [P.projection_chartRectangleLiftJordanCircle_parametrization_eq_graph T]
    rw [← P.graph.range_localRectangleCircle P.graph.localRectangleData]
    exact ⟨JordanCurve.Arcs.spherePlaneHomeoCircle z, rfl⟩
  · rw [← P.graph.range_localRectangleCircle P.graph.localRectangleData]
    rintro ⟨z, rfl⟩
    let w := JordanCurve.Arcs.spherePlaneHomeoCircle.symm z
    refine ⟨(P.chartRectangleLiftJordanCircle T).parametrization w,
      ⟨w, rfl⟩, ?_⟩
    rw [P.projection_chartRectangleLiftJordanCircle_parametrization_eq_graph T]
    simp only [w, Homeomorph.apply_symm_apply]

/-- The covering projection is injective on the retained chart sheet. -/
theorem torusCoveringProjection_injOn_liftedPatch :
    Set.InjOn (torusCoveringProjectionToTorus Phi) T.liftedPatch := by
  intro x hx y hy hxy
  obtain ⟨u, hu⟩ := T.liftedStrip.surjective ⟨x, hx⟩
  obtain ⟨v, hv⟩ := T.liftedStrip.surjective ⟨y, hy⟩
  have hxu : x = T.liftedStrip u := (congrArg Subtype.val hu).symm
  have hyv : y = T.liftedStrip v := (congrArg Subtype.val hv).symm
  subst x
  subst y
  have hstrip : T.strip u = T.strip v := by
    apply Subtype.ext
    simpa only [T.projection_liftedStrip] using hxy
  have huv : u = v := T.strip.injective hstrip
  simp only [huv]

private theorem chartClosedRectangle_subset_liftedPatch :
    chartClosedRectangle T ⊆ T.liftedPatch := by
  rintro _ ⟨u, _, rfl⟩
  exact (T.liftedStrip u).2

/-- The retained-chart lift is exactly the frontier of the transported closed rectangle. -/
theorem chartRectangleLiftJordanCircle_carrier_eq_frontier :
    (P.chartRectangleLiftJordanCircle T).carrier =
      frontier (chartClosedRectangle T) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxPatch := P.chartRectangleLiftJordanCircle_carrier_subset_liftedPatch T hx
    have hxProjection : torusCoveringProjectionToTorus Phi x ∈
        P.graph.localRectangleCarrier := by
      rw [← P.projection_image_chartRectangleLiftJordanCircle_carrier T]
      exact ⟨x, hx, rfl⟩
    rw [← P.projection_image_frontier_chartClosedRectangle T] at hxProjection
    obtain ⟨y, hy, hprojection⟩ := hxProjection
    have hyClosed := frontier_subset_closure hy
    rw [(isClosed_chartClosedRectangle T).closure_eq] at hyClosed
    have hyPatch : y ∈ T.liftedPatch :=
      chartClosedRectangle_subset_liftedPatch T hyClosed
    have hxy := torusCoveringProjection_injOn_liftedPatch T
      hxPatch hyPatch hprojection.symm
    simpa only [hxy] using hy
  · intro x hx
    have hxClosed := frontier_subset_closure hx
    rw [(isClosed_chartClosedRectangle T).closure_eq] at hxClosed
    have hxPatch := chartClosedRectangle_subset_liftedPatch T hxClosed
    have hxProjection : torusCoveringProjectionToTorus Phi x ∈
        P.graph.localRectangleCarrier := by
      rw [← P.projection_image_frontier_chartClosedRectangle T]
      exact ⟨x, hx, rfl⟩
    rw [← P.projection_image_chartRectangleLiftJordanCircle_carrier T] at hxProjection
    obtain ⟨y, hy, hprojection⟩ := hxProjection
    have hyPatch := P.chartRectangleLiftJordanCircle_carrier_subset_liftedPatch T hy
    have hyx := torusCoveringProjection_injOn_liftedPatch T
      hyPatch hxPatch hprojection
    simpa only [hyx] using hy

/-- The entire transported rectangle lies in the closed bounded side of its lifted Jordan
circle. -/
theorem chartClosedRectangle_subset_closure_inside :
    chartClosedRectangle T ⊆ closure (P.chartRectangleLiftJordanCircle T).inside :=
  subset_closure_inside_of_carrier_eq_frontier
    (P.chartRectangleLiftJordanCircle T)
    (isClosed_chartClosedRectangle T) (isBounded_chartClosedRectangle T)
    (closure_interior_chartClosedRectangle T)
    (P.chartRectangleLiftJordanCircle_carrier_eq_frontier T)

/-- Projecting the explicit chart rectangle lands in the closed bounded face of the coherent
six-edge rectangle lift. -/
theorem projection_chartClosedRectangle_subset_planeRectangleClosedFace :
    torusCoveringProjectionToTorus Phi '' chartClosedRectangle T ⊆
      torusCoveringProjectionToTorus Phi ''
        closure
          (P.planePathSystem.localRectangleJordanCircle
            P.planePathSystem.localRectangleData).inside := by
  obtain ⟨k, hk⟩ := P.exists_rectangleParametrization_eq_chart_add_lattice T
  let J := P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData
  let K := P.chartRectangleLiftJordanCircle T
  have hcarrier : J.carrier = (K.translate (torusLatticeVector k)).carrier :=
    P.planeRectangle_carrier_eq_chart_translate T k hk
  have hinside : J.inside = (K.translate (torusLatticeVector k)).inside :=
    Schoenflies.JordanCircle.inside_eq_of_carrier_eq J
      (K.translate (torusLatticeVector k)) hcarrier
  rintro _ ⟨y, hy, rfl⟩
  have hyInside : y ∈ closure K.inside :=
    P.chartClosedRectangle_subset_closure_inside T hy
  have hyTranslated : y + torusLatticeVector k ∈
      closure (K.translate (torusLatticeVector k)).inside := by
    rw [Schoenflies.JordanCircle.closure_inside_translate]
    exact ⟨y, hyInside, rfl⟩
  rw [← hinside] at hyTranslated
  refine ⟨y + torusLatticeVector k, hyTranslated, ?_⟩
  exact torusCoveringProjectionToTorus_add_lattice y k

end FourPortRawSixEdgeBandPresentation
end Submission.Topology
