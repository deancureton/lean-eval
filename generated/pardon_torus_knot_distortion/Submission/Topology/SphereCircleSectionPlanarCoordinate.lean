import Submission.Topology.SphereCircleSectionPlanarSide

/-!
# Component-local doubled coordinates on a planar sphere remainder

The canonical punctured outer disk carries the doubled longitude or meridian coordinate after
side localization.  Their exact values on every inner and outer boundary circle match the
pointwise zero-winding cap formulas.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {S : EmbeddedTopologicalSphereInR3}
  {iota : Type*} [Fintype iota]

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable
  {circleSection : FiniteEmbeddedTorusCircleSection Phi
    (S.carrier ∩ transportedTorus Phi) iota}
  (D : FiniteEmbeddedSphereCircleCommonPoleData S circleSection.circle)
  (outer : iota)

/-- The doubled longitude coordinate on a component remainder lying on the tube side. -/
def sectionFirstOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    D.outerDiskRemainder outer → Circle :=
  fun x ↦ transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer x, hside x⟩

theorem continuous_sectionFirstOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    Continuous (D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside) := by
  apply (continuous_transportedTubeLongitudeCoordinate Phi).comp
  exact (D.continuous_outerDiskRemainderAmbientMap outer).subtype_mk hside

/-- The tube-side remainder coordinate agrees with the first cap formula on an inner circle. -/
theorem sectionFirstOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (t : ℝ) :
    D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi
          (Circle.exp t)) =
      ((transportedLoopCoordinates Phi
        (circleSection.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (circleSection.circle i).windingLoop.curve t
  change transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi (Circle.exp t)),
      hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi (Circle.exp t)),
      hside _⟩ : transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_innerCircleRemainderPoint
      circleSection.pairwise_disjoint outer hi (Circle.exp t)).trans <|
        ((circleSection.circle i).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates
            (circleSection.circle i) t]
  exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2

/-- The doubled meridian coordinate on a component remainder lying on the exterior side. -/
def sectionSecondOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    D.outerDiskRemainder outer → Circle :=
  fun x ↦ transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer x, hside x⟩

theorem continuous_sectionSecondOuterDiskRemainderDoubledCoordinateMap
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    Continuous (D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside) := by
  apply (continuous_transportedExteriorMeridianCoordinate Phi).comp
  exact (D.continuous_outerDiskRemainderAmbientMap outer).subtype_mk hside

/-- The exterior-side remainder coordinate agrees with the second cap formula on an inner
circle. -/
theorem sectionSecondOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (t : ℝ) :
    D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi
          (Circle.exp t)) =
      ((transportedLoopCoordinates Phi
        (circleSection.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (circleSection.circle i).windingLoop.curve t
  change transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi (Circle.exp t)),
      hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi (Circle.exp t)),
      hside _⟩ : transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_innerCircleRemainderPoint
      circleSection.pairwise_disjoint outer hi (Circle.exp t)).trans <|
        ((circleSection.circle i).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates
            (circleSection.circle i) t]
  exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2

/-- A point of the outer circle regarded as a point of its punctured planar remainder. -/
def sectionOuterCircleRemainderPoint (z : Circle) : D.outerDiskRemainder outer := by
  let p := (D.circleData outer).planeCirclePoint z
  refine ⟨p, p.2, ?_⟩
  intro hp
  obtain ⟨i, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨hi, hpi⟩ := Set.mem_iUnion.mp hp
  have hpOuter : (p : JordanCurve.Arcs.Plane) ∈
      (D.circleData outer).planeJordanCircle.inside :=
    D.inclusionMaximalInnerClosedPlaneDisk_inside outer hi (subset_closure hpi)
  have hpCarrier : (p : JordanCurve.Arcs.Plane) ∈
      (D.circleData outer).planeJordanCircle.carrier := by
    rw [(D.circleData outer).carrier_planeJordanCircle]
    exact ⟨z, (D.circleData outer).coe_planeCirclePoint z |>.symm⟩
  exact (D.circleData outer).planeJordanCircle.inside_subset_compl hpOuter hpCarrier

@[simp]
theorem coe_sectionOuterCircleRemainderPoint (z : Circle) :
    (D.sectionOuterCircleRemainderPoint outer z : JordanCurve.Arcs.Plane) =
      (D.circleData outer).planeCircle z :=
  (D.circleData outer).coe_planeCirclePoint z

@[simp]
theorem outerDiskRemainderAmbientMap_sectionOuterCircleRemainderPoint (z : Circle) :
    D.outerDiskRemainderAmbientMap outer (D.sectionOuterCircleRemainderPoint outer z) =
      (circleSection.circle outer).circle z := by
  change (D.circleData outer).planarDiskAmbientMap
    ((D.circleData outer).planeCirclePoint z) = _
  exact (D.circleData outer).planarDiskAmbientMap_planeCirclePoint z

/-- The tube-side remainder coordinate has the required first value on the outer circle. -/
theorem sectionFirstOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (t : ℝ) :
    D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)) =
      ((transportedLoopCoordinates Phi
        (circleSection.circle outer).windingLoop.curve t).1)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (circleSection.circle outer).windingLoop.curve t
  change transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)), hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)), hside _⟩ :
      transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_sectionOuterCircleRemainderPoint
      outer (Circle.exp t)).trans <|
        ((circleSection.circle outer).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates
            (circleSection.circle outer) t]
  exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2

/-- The exterior-side remainder coordinate has the required second value on the outer circle. -/
theorem sectionSecondOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (t : ℝ) :
    D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)) =
      ((transportedLoopCoordinates Phi
        (circleSection.circle outer).windingLoop.curve t).2)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (circleSection.circle outer).windingLoop.curve t
  change transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)), hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.sectionOuterCircleRemainderPoint outer (Circle.exp t)), hside _⟩ :
      transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_sectionOuterCircleRemainderPoint
      outer (Circle.exp t)).trans <|
        ((circleSection.circle outer).parametrization t).trans <|
          windingLoop_curve_eq_transportedTorusMap_coordinates
            (circleSection.circle outer) t]
  exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
