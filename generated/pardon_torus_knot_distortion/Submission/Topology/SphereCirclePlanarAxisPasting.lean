import Submission.Topology.SphereCirclePlanarCoreConnectivity
import Submission.Topology.FiniteClosedCoverPasting

/-!
# Pasting doubled coordinates across a planar sphere decomposition

The punctured outer sphere disk inherits an ambient map from the common stereographic chart.
When that map lies on one closed side of the transported torus, the corresponding doubled
coordinate gives a continuous map on the remainder.  This file records its exact values along
the selected inner boundary circles, matching the canonical inessential cap maps.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota]
  {F : FiniteSphereSurgeryIntersectionSystem Phi iota}
  {S : EmbeddedTopologicalSphereInR3}

/-- A transported torus point is recovered from its product-torus coordinates. -/
theorem windingLoop_curve_eq_transportedTorusMap_coordinates
    (C : EmbeddedTorusIntersectionCircle Phi) (t : ℝ) :
    (C.windingLoop.curve t : R3) = transportedTorusMap Phi
      (transportedLoopCoordinates Phi C.windingLoop.curve t) := by
  change (C.windingLoop.curve t : R3) =
    (((transportedTorusHomeomorph Phi)
      ((transportedTorusHomeomorph Phi).symm (C.windingLoop.curve t))) :
        transportedTorus Phi)
  exact congrArg Subtype.val <|
    ((transportedTorusHomeomorph Phi).apply_symm_apply
      (C.windingLoop.curve t)).symm

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable
  (D : FiniteEmbeddedSphereCircleCommonPoleData S F.circle)
  (hpairwise : Pairwise fun i j ↦
    Disjoint (Set.range (F.circle i).circle) (Set.range (F.circle j).circle))
  (outer : iota)

/-- The gauge of the ambient sphere map on the punctured outer remainder. -/
def outerDiskRemainderGauge : D.outerDiskRemainder outer → ℝ :=
  fun x ↦ tubeGauge (Phi.H 1 (D.outerDiskRemainderAmbientMap outer x))

theorem continuous_outerDiskRemainderGauge :
    Continuous (D.outerDiskRemainderGauge outer) :=
  continuous_tubeGauge.comp <|
    (continuous_timeOne_map Phi).comp (D.continuous_outerDiskRemainderAmbientMap outer)

/-- A connected dense core of the punctured sphere disk whose ambient image misses the torus.
This is the precise planar-topology input needed for the one-side argument. -/
structure ConnectedTorusFreeRemainderCoreData where
  core : Set (D.outerDiskRemainder outer)
  isConnected_core : IsConnected core
  dense_core : closure core = Set.univ
  core_disjoint_torus : ∀ x ∈ core,
    D.outerDiskRemainderAmbientMap outer x ∉ transportedTorus Phi

include hpairwise in
/-- The canonical punctured core misses the transported torus.  Exact sphere intersection
reduces a hypothetical torus point to one of the listed circles; strict planar nesting then
places that circle in a selected maximal inner disk, contradicting core membership. -/
theorem outerDiskRemainderCore_disjoint_torus
    (hSphere : S.carrier ⊆ F.sphereFamily.carrier)
    (x : D.outerDiskRemainder outer) (hx : x ∈ D.outerDiskRemainderCore outer) :
    D.outerDiskRemainderAmbientMap outer x ∉ transportedTorus Phi := by
  intro hxTorus
  have hxSphere : D.outerDiskRemainderAmbientMap outer x ∈ S.carrier := by
    exact ⟨(stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane), rfl⟩
  have hxIntersection : D.outerDiskRemainderAmbientMap outer x ∈
      F.sphereFamily.carrier ∩ transportedTorus Phi :=
    ⟨hSphere hxSphere, hxTorus⟩
  rw [F.intersection_exact] at hxIntersection
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hxIntersection
  have hsphereEq :
      (stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane) =
        (D.circleData j).sphereCircle z := by
    apply S.isEmbedding.injective
    rw [(D.circleData j).sphere_parametrization_sphereCircle]
    exact hz.symm
  have hxPlane : (x : JordanCurve.Arcs.Plane) = (D.circleData j).planeCircle z := by
    calc
      (x : JordanCurve.Arcs.Plane) =
          (stereographic' 2 D.pole)
            ((stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane)) := by
        symm
        apply (stereographic' 2 D.pole).right_inv
        rw [stereographic'_target]
        trivial
      _ = (stereographic' 2 D.pole) ((D.circleData j).sphereCircle z) :=
        congrArg (stereographic' 2 D.pole) hsphereEq
      _ = (D.circleData j).planeCircle z := rfl
  have hxCarrier : (x : JordanCurve.Arcs.Plane) ∈
      (D.circleData j).planeJordanCircle.carrier := by
    rw [(D.circleData j).carrier_planeJordanCircle]
    exact ⟨z, hxPlane.symm⟩
  change (x : JordanCurve.Arcs.Plane) ∈ D.outerDiskOpenCore outer at hx
  obtain ⟨hxOuter, hxNotClosed⟩ := hx
  by_cases hjo : j = outer
  · subst j
    exact (D.circleData outer).planeJordanCircle.inside_subset_compl
      hxOuter hxCarrier
  · have hjInside := D.closedPlaneDisk_subset_inside_of_carrier_meets_inside
      hpairwise hjo hxOuter hxCarrier
    obtain ⟨k, hk, hjk⟩ :=
      D.exists_inclusionMaximalInnerClosedPlaneDisk_superset outer j hjInside
    have hxJDisk : (x : JordanCurve.Arcs.Plane) ∈ D.closedPlaneDisk j := by
      rw [show D.closedPlaneDisk j =
        closure (D.circleData j).planeJordanCircle.inside by rfl,
        (D.circleData j).planeJordanCircle.closure_inside]
      exact Or.inr hxCarrier
    apply hxNotClosed
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hjk hxJDisk⟩⟩

include hpairwise in
/-- Once connectivity and density of the canonical planar core are supplied, its torus-free
property is automatic from exact intersection and nesting. -/
def connectedTorusFreeRemainderCoreDataOfCanonicalCore
    (hSphere : S.carrier ⊆ F.sphereFamily.carrier)
    (hconnected : IsConnected (D.outerDiskRemainderCore outer))
    (hdense : closure (D.outerDiskRemainderCore outer) = Set.univ) :
    D.ConnectedTorusFreeRemainderCoreData outer where
  core := D.outerDiskRemainderCore outer
  isConnected_core := hconnected
  dense_core := hdense
  core_disjoint_torus := D.outerDiskRemainderCore_disjoint_torus
    hpairwise outer hSphere

include hpairwise in
/-- The canonical punctured core supplies its own density; only connectivity remains as a
planar-topology input to the side-localization argument. -/
def canonicalConnectedTorusFreeRemainderCoreData
    (hSphere : S.carrier ⊆ F.sphereFamily.carrier)
    (hconnected : IsConnected (D.outerDiskRemainderCore outer)) :
    D.ConnectedTorusFreeRemainderCoreData outer :=
  D.connectedTorusFreeRemainderCoreDataOfCanonicalCore hpairwise outer hSphere hconnected
    (dense_iff_closure_eq.mp (D.dense_outerDiskRemainderCore hpairwise outer))

namespace ConnectedTorusFreeRemainderCoreData

variable (G : D.ConnectedTorusFreeRemainderCoreData outer)

include G in
/-- A connected dense torus-free core forces the entire closed punctured disk onto one of the
two closed sides of the transported torus. -/
theorem liesOnOneTorusSide :
    (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) ∨
      (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) := by
  let low : Set (D.outerDiskRemainder outer) :=
    {x | D.outerDiskRemainderGauge outer x < 1}
  let high : Set (D.outerDiskRemainder outer) :=
    {x | 1 < D.outerDiskRemainderGauge outer x}
  have hlowOpen : IsOpen low :=
    isOpen_lt (D.continuous_outerDiskRemainderGauge outer) continuous_const
  have hhighOpen : IsOpen high :=
    isOpen_lt continuous_const (D.continuous_outerDiskRemainderGauge outer)
  have hdisjoint : Disjoint low high := by
    rw [Set.disjoint_left]
    intro x hxLow hxHigh
    change D.outerDiskRemainderGauge outer x < 1 at hxLow
    change 1 < D.outerDiskRemainderGauge outer x at hxHigh
    linarith
  have hcover : ConnectedTorusFreeRemainderCoreData.core G ⊆ low ∪ high := by
    intro x hx
    have hne : D.outerDiskRemainderGauge outer x ≠ 1 := by
      intro heq
      exact ConnectedTorusFreeRemainderCoreData.core_disjoint_torus G x hx <|
        mem_transportedTorus_of_tubeGauge_timeOne_eq_one Phi heq
    rcases lt_or_gt_of_ne hne with hlow | hhigh
    · exact Or.inl hlow
    · exact Or.inr hhigh
  rcases (ConnectedTorusFreeRemainderCoreData.isConnected_core G).isPreconnected.subset_or_subset
      hlowOpen hhighOpen hdisjoint hcover with hlow | hhigh
  · left
    have hclosed : IsClosed
        {x : D.outerDiskRemainder outer | D.outerDiskRemainderGauge outer x ≤ 1} :=
      isClosed_le (D.continuous_outerDiskRemainderGauge outer) continuous_const
    have hclosure : closure (ConnectedTorusFreeRemainderCoreData.core G) ⊆
        {x : D.outerDiskRemainder outer | D.outerDiskRemainderGauge outer x ≤ 1} :=
      closure_minimal (by
        intro x hx
        have hxLow := hlow hx
        change D.outerDiskRemainderGauge outer x < 1 at hxLow
        exact hxLow.le) hclosed
    rw [ConnectedTorusFreeRemainderCoreData.dense_core G] at hclosure
    intro x
    exact hclosure (Set.mem_univ x)
  · right
    have hclosed : IsClosed
        {x : D.outerDiskRemainder outer | 1 ≤ D.outerDiskRemainderGauge outer x} :=
      isClosed_le continuous_const (D.continuous_outerDiskRemainderGauge outer)
    have hclosure : closure (ConnectedTorusFreeRemainderCoreData.core G) ⊆
        {x : D.outerDiskRemainder outer | 1 ≤ D.outerDiskRemainderGauge outer x} :=
      closure_minimal (by
        intro x hx
        have hxHigh := hhigh hx
        change 1 < D.outerDiskRemainderGauge outer x at hxHigh
        exact hxHigh.le) hclosed
    rw [ConnectedTorusFreeRemainderCoreData.dense_core G] at hclosure
    intro x
    exact hclosure (Set.mem_univ x)

end ConnectedTorusFreeRemainderCoreData

include hpairwise in
/-- Once the canonical planar core is known to be connected, exact sphere intersection and
planar density force the entire punctured disk onto one closed torus side. -/
theorem canonicalOuterDiskRemainder_liesOnOneTorusSide
    (hSphere : S.carrier ⊆ F.sphereFamily.carrier)
    (hconnected : IsConnected (D.outerDiskRemainderCore outer)) :
    (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) ∨
      (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :=
  (D.canonicalConnectedTorusFreeRemainderCoreData hpairwise outer
    hSphere hconnected).liesOnOneTorusSide

include hpairwise in
/-- The finite planar pushout supplies the connectivity needed to place the entire canonical
punctured disk on one closed torus side. -/
theorem canonicalOuterDiskRemainder_liesOnOneTorusSide_of_planarPushout
    (hSphere : S.carrier ⊆ F.sphereFamily.carrier) :
    (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) ∨
      (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :=
  D.canonicalOuterDiskRemainder_liesOnOneTorusSide hpairwise outer hSphere
    (D.isConnected_outerDiskRemainderCore hpairwise outer)

/-- The doubled longitude coordinate on a punctured outer disk lying on the tube side. -/
def firstOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    D.outerDiskRemainder outer → Circle :=
  fun x ↦ transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer x, hside x⟩

theorem continuous_firstOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    Continuous (D.firstOuterDiskRemainderDoubledCoordinateMap outer hside) := by
  apply (continuous_transportedTubeLongitudeCoordinate Phi).comp
  exact (D.continuous_outerDiskRemainderAmbientMap outer).subtype_mk hside

/-- On a selected inner boundary, the remainder's tube-side coordinate equals the canonical
first doubled-coordinate cap boundary. -/
theorem firstOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (t : ℝ) :
    D.firstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (F.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (F.circle i).windingLoop.curve t
  change transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)),
      hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)),
      hside _⟩ : transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_innerCircleRemainderPoint
      hpairwise outer hi (Circle.exp t)).trans <|
        ((F.circle i).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates (F.circle i) t]
  exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2

/-- The doubled meridian coordinate on a punctured outer disk lying on the exterior side. -/
def secondOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    D.outerDiskRemainder outer → Circle :=
  fun x ↦ transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer x, hside x⟩

theorem continuous_secondOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    Continuous (D.secondOuterDiskRemainderDoubledCoordinateMap outer hside) := by
  apply (continuous_transportedExteriorMeridianCoordinate Phi).comp
  exact (D.continuous_outerDiskRemainderAmbientMap outer).subtype_mk hside

/-- On a selected inner boundary, the remainder's exterior-side coordinate equals the canonical
second doubled-coordinate cap boundary. -/
theorem secondOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (t : ℝ) :
    D.secondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (F.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (F.circle i).windingLoop.curve t
  change transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)),
      hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t)),
      hside _⟩ : transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_innerCircleRemainderPoint
      hpairwise outer hi (Circle.exp t)).trans <|
        ((F.circle i).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates (F.circle i) t]
  exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2

end FiniteEmbeddedSphereCircleCommonPoleData
end Submission.Topology
