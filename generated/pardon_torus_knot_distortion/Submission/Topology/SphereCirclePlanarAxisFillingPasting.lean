import Submission.Topology.SphereCirclePlanarAxisPasting

/-!
# Pasting the planar remainder filling to the inner cap fillings

The canonical closed outer disk is the finite closed cover consisting of its punctured
remainder and the selected maximal inner disks.  The remainder doubled-coordinate map agrees
with the corresponding canonical inessential cap map on every overlap circle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]
  {F : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {S : EmbeddedTopologicalSphereInR3}

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable (D : FiniteEmbeddedSphereCircleCommonPoleData S F.circle)
  (hpairwise : Pairwise fun i j ↦
    Disjoint (Set.range (F.circle i).circle) (Set.range (F.circle j).circle))
  (outer : ι)

/-- The remainder piece together with one piece for every selected maximal inner disk. -/
def axisFillingPiece : Option (D.maximalInnerDiskIndex outer) → Set (D.closedPlaneDisk outer)
  | none => Subtype.val ⁻¹' D.outerDiskRemainder outer
  | some i => Subtype.val ⁻¹' D.closedPlaneDisk i.1

theorem isClosed_axisFillingPiece (k : Option (D.maximalInnerDiskIndex outer)) :
    IsClosed (D.axisFillingPiece outer k) := by
  cases k with
  | none => exact (D.isClosed_outerDiskRemainder outer).preimage continuous_subtype_val
  | some i => exact isClosed_closure.preimage continuous_subtype_val

/-- The remainder and maximal inner disks cover the selected outer closed disk. -/
theorem axisFillingPiece_cover : ⋃ k, D.axisFillingPiece outer k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (x : JordanCurve.Arcs.Plane) ∈
      D.outerDiskRemainder outer ∪
        ⋃ i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer,
          D.closedPlaneDisk i := by
    rw [D.outerDiskRemainder_union_maximalInnerClosedPlaneDisks outer]
    exact x.2
  rcases hx with hxRemainder | hxInner
  · exact Set.mem_iUnion.mpr ⟨none, hxRemainder⟩
  · obtain ⟨i, hxInner⟩ := Set.mem_iUnion.mp hxInner
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxInner
    exact Set.mem_iUnion.mpr ⟨some ⟨i, hi⟩, hxi⟩

include hpairwise in
/-- On a remainder/inner-disk overlap, the first doubled-coordinate formulas agree. -/
theorem firstRemainderCap_compatible
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    {i : ι} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (x : JordanCurve.Arcs.Plane) (hxRemainder : x ∈ D.outerDiskRemainder outer)
    (hxDisk : x ∈ D.closedPlaneDisk i) :
    D.firstOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, hxRemainder⟩ =
      F.firstPlanarizedInessentialDoubledCapMap hzero i (D.circleData i) ⟨x, hxDisk⟩ := by
  have hxCarrier : x ∈ (D.circleData i).planeJordanCircle.carrier := by
    rw [← D.outerDiskRemainder_inter_maximalInnerClosedPlaneDisk hpairwise outer hi]
    exact ⟨hxRemainder, hxDisk⟩
  obtain ⟨t, ht⟩ :=
    (D.circleData i).exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier hxCarrier
  have hplane : (D.circleData i).planeCircle (Circle.exp t) = x := by
    rw [← (D.circleData i).planeDisk_boundary t]
    exact ht
  rw [show (⟨x, hxRemainder⟩ : D.outerDiskRemainder outer) =
      D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  rw [D.firstOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    hpairwise outer hside hi t]
  change _ = F.firstPlanarizedInessentialDoubledCapMap hzero i (D.circleData i)
    ⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩
  rw [show (⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩ :
      closure (D.circleData i).planeJordanCircle.inside) =
      (D.circleData i).planeCirclePoint (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  exact (F.firstPlanarizedInessentialDoubledCapMap_planeCirclePoint_exp
    hzero i (D.circleData i) t).symm

include hpairwise in
/-- On a remainder/inner-disk overlap, the second doubled-coordinate formulas agree. -/
theorem secondRemainderCap_compatible
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    {i : ι} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (x : JordanCurve.Arcs.Plane) (hxRemainder : x ∈ D.outerDiskRemainder outer)
    (hxDisk : x ∈ D.closedPlaneDisk i) :
    D.secondOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, hxRemainder⟩ =
      F.secondPlanarizedInessentialDoubledCapMap hzero i (D.circleData i) ⟨x, hxDisk⟩ := by
  have hxCarrier : x ∈ (D.circleData i).planeJordanCircle.carrier := by
    rw [← D.outerDiskRemainder_inter_maximalInnerClosedPlaneDisk hpairwise outer hi]
    exact ⟨hxRemainder, hxDisk⟩
  obtain ⟨t, ht⟩ :=
    (D.circleData i).exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier hxCarrier
  have hplane : (D.circleData i).planeCircle (Circle.exp t) = x := by
    rw [← (D.circleData i).planeDisk_boundary t]
    exact ht
  rw [show (⟨x, hxRemainder⟩ : D.outerDiskRemainder outer) =
      D.innerCircleRemainderPoint hpairwise outer hi (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  rw [D.secondOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    hpairwise outer hside hi t]
  change _ = F.secondPlanarizedInessentialDoubledCapMap hzero i (D.circleData i)
    ⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩
  rw [show (⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩ :
      closure (D.circleData i).planeJordanCircle.inside) =
      (D.circleData i).planeCirclePoint (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  exact (F.secondPlanarizedInessentialDoubledCapMap_planeCirclePoint_exp
    hzero i (D.circleData i) t).symm

/-- Piecewise first-coordinate values on the finite closed cover. -/
def firstAxisFillingPieceValue
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    ∀ k, D.axisFillingPiece outer k → Circle
  | none, x => D.firstOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, x.2⟩
  | some i, x => F.firstPlanarizedInessentialDoubledCapMap hzero i.1 (D.circleData i.1)
      ⟨x, (show (x : JordanCurve.Arcs.Plane) ∈
        closure (D.circleData i.1).planeJordanCircle.inside from x.2)⟩

theorem continuous_firstAxisFillingPieceValue
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (k : Option (D.maximalInnerDiskIndex outer)) :
    Continuous (D.firstAxisFillingPieceValue outer hzero hside k) := by
  cases k with
  | none =>
      exact (D.continuous_firstOuterDiskRemainderDoubledCoordinateMap outer hside).comp <|
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  | some i =>
      exact (F.continuous_firstPlanarizedInessentialDoubledCapMap
        hzero i.1 (D.circleData i.1)).comp <|
          Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

include hpairwise in
/-- The first-coordinate piece values agree on all pairwise overlaps. -/
theorem firstAxisFillingPieceValue_compatible
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (a b : Option (D.maximalInnerDiskIndex outer))
    (x : D.closedPlaneDisk outer) (hxa : x ∈ D.axisFillingPiece outer a)
    (hxb : x ∈ D.axisFillingPiece outer b) :
    D.firstAxisFillingPieceValue outer hzero hside a ⟨x, hxa⟩ =
      D.firstAxisFillingPieceValue outer hzero hside b ⟨x, hxb⟩ := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j =>
          exact D.firstRemainderCap_compatible hpairwise outer hzero hside j.2 x hxa hxb
  | some i =>
      cases b with
      | none =>
          exact (D.firstRemainderCap_compatible hpairwise outer hzero hside
            i.2 x hxb hxa).symm
      | some j =>
          by_cases hij : i = j
          · subst j
            rfl
          · exfalso
            have hijVal : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
            exact Set.disjoint_left.mp
              (D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
                hpairwise outer i.2 j.2 hijVal) hxa hxb

/-- The first-coordinate finite closed-cover pasting package. -/
def firstAxisFillingPastingData
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    FiniteClosedCoverPastingData (Option (D.maximalInnerDiskIndex outer))
      (D.closedPlaneDisk outer) Circle where
  piece := D.axisFillingPiece outer
  isClosed_piece := D.isClosed_axisFillingPiece outer
  cover := D.axisFillingPiece_cover outer
  value := D.firstAxisFillingPieceValue outer hzero hside
  continuous_value := D.continuous_firstAxisFillingPieceValue outer hzero hside
  compatible := D.firstAxisFillingPieceValue_compatible hpairwise outer hzero hside

/-- The continuous first-coordinate filling on the whole outer closed disk. -/
def firstAxisFillingMap
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    D.closedPlaneDisk outer → Circle :=
  (D.firstAxisFillingPastingData hpairwise outer hzero hside).glued

theorem continuous_firstAxisFillingMap
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    Continuous (D.firstAxisFillingMap hpairwise outer hzero hside) :=
  (D.firstAxisFillingPastingData hpairwise outer hzero hside).continuous_glued

/-- Piecewise second-coordinate values on the finite closed cover. -/
def secondAxisFillingPieceValue
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    ∀ k, D.axisFillingPiece outer k → Circle
  | none, x => D.secondOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, x.2⟩
  | some i, x => F.secondPlanarizedInessentialDoubledCapMap hzero i.1 (D.circleData i.1)
      ⟨x, (show (x : JordanCurve.Arcs.Plane) ∈
        closure (D.circleData i.1).planeJordanCircle.inside from x.2)⟩

theorem continuous_secondAxisFillingPieceValue
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (k : Option (D.maximalInnerDiskIndex outer)) :
    Continuous (D.secondAxisFillingPieceValue outer hzero hside k) := by
  cases k with
  | none =>
      exact (D.continuous_secondOuterDiskRemainderDoubledCoordinateMap outer hside).comp <|
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  | some i =>
      exact (F.continuous_secondPlanarizedInessentialDoubledCapMap
        hzero i.1 (D.circleData i.1)).comp <|
          Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

include hpairwise in
/-- The second-coordinate piece values agree on all pairwise overlaps. -/
theorem secondAxisFillingPieceValue_compatible
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (a b : Option (D.maximalInnerDiskIndex outer))
    (x : D.closedPlaneDisk outer) (hxa : x ∈ D.axisFillingPiece outer a)
    (hxb : x ∈ D.axisFillingPiece outer b) :
    D.secondAxisFillingPieceValue outer hzero hside a ⟨x, hxa⟩ =
      D.secondAxisFillingPieceValue outer hzero hside b ⟨x, hxb⟩ := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j =>
          exact D.secondRemainderCap_compatible hpairwise outer hzero hside j.2 x hxa hxb
  | some i =>
      cases b with
      | none =>
          exact (D.secondRemainderCap_compatible hpairwise outer hzero hside
            i.2 x hxb hxa).symm
      | some j =>
          by_cases hij : i = j
          · subst j
            rfl
          · exfalso
            have hijVal : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
            exact Set.disjoint_left.mp
              (D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
                hpairwise outer i.2 j.2 hijVal) hxa hxb

/-- The second-coordinate finite closed-cover pasting package. -/
def secondAxisFillingPastingData
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    FiniteClosedCoverPastingData (Option (D.maximalInnerDiskIndex outer))
      (D.closedPlaneDisk outer) Circle where
  piece := D.axisFillingPiece outer
  isClosed_piece := D.isClosed_axisFillingPiece outer
  cover := D.axisFillingPiece_cover outer
  value := D.secondAxisFillingPieceValue outer hzero hside
  continuous_value := D.continuous_secondAxisFillingPieceValue outer hzero hside
  compatible := D.secondAxisFillingPieceValue_compatible hpairwise outer hzero hside

/-- The continuous second-coordinate filling on the whole outer closed disk. -/
def secondAxisFillingMap
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    D.closedPlaneDisk outer → Circle :=
  (D.secondAxisFillingPastingData hpairwise outer hzero hside).glued

theorem continuous_secondAxisFillingMap
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    Continuous (D.secondAxisFillingMap hpairwise outer hzero hside) :=
  (D.secondAxisFillingPastingData hpairwise outer hzero hside).continuous_glued

/-- A point of the outer boundary, canonically regarded as a point of the punctured remainder. -/
def outerCircleRemainderPoint (z : Circle) : D.outerDiskRemainder outer := by
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
theorem coe_outerCircleRemainderPoint (z : Circle) :
    (D.outerCircleRemainderPoint outer z : JordanCurve.Arcs.Plane) =
      (D.circleData outer).planeCircle z := by
  exact (D.circleData outer).coe_planeCirclePoint z

@[simp]
theorem outerDiskRemainderAmbientMap_outerCircleRemainderPoint (z : Circle) :
    D.outerDiskRemainderAmbientMap outer (D.outerCircleRemainderPoint outer z) =
      (F.circle outer).circle z := by
  change (D.circleData outer).planarDiskAmbientMap
    ((D.circleData outer).planeCirclePoint z) = _
  exact (D.circleData outer).planarDiskAmbientMap_planeCirclePoint z

/-- The tube-side remainder formula has the required first-coordinate value on the outer
boundary. -/
theorem firstOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (t : ℝ) :
    D.firstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.outerCircleRemainderPoint outer (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (F.circle outer).windingLoop.curve t).1)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (F.circle outer).windingLoop.curve t
  change transportedTubeLongitudeCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.outerCircleRemainderPoint outer (Circle.exp t)), hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.outerCircleRemainderPoint outer (Circle.exp t)), hside _⟩ :
      transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_outerCircleRemainderPoint outer
      (Circle.exp t)).trans <| ((F.circle outer).parametrization t).trans <|
        windingLoop_curve_eq_transportedTorusMap_coordinates (F.circle outer) t]
  exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2

/-- The exterior-side remainder formula has the required second-coordinate value on the outer
boundary. -/
theorem secondOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (t : ℝ) :
    D.secondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.outerCircleRemainderPoint outer (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (F.circle outer).windingLoop.curve t).2)⁻¹ ^ 2 := by
  let zw := transportedLoopCoordinates Phi (F.circle outer).windingLoop.curve t
  change transportedExteriorMeridianCoordinate Phi
    ⟨D.outerDiskRemainderAmbientMap outer
      (D.outerCircleRemainderPoint outer (Circle.exp t)), hside _⟩ = _
  rw [show (⟨D.outerDiskRemainderAmbientMap outer
      (D.outerCircleRemainderPoint outer (Circle.exp t)), hside _⟩ :
      transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
    apply Subtype.ext
    exact (D.outerDiskRemainderAmbientMap_outerCircleRemainderPoint outer
      (Circle.exp t)).trans <| ((F.circle outer).parametrization t).trans <|
        windingLoop_curve_eq_transportedTorusMap_coordinates (F.circle outer) t]
  exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2

theorem firstAxisFillingMap_outerCirclePoint
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (z : Circle) :
    D.firstAxisFillingMap hpairwise outer hzero hside
        ((D.circleData outer).planeCirclePoint z) =
      D.firstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.outerCircleRemainderPoint outer z) := by
  let P := D.firstAxisFillingPastingData hpairwise outer hzero hside
  have hpiece : (D.circleData outer).planeCirclePoint z ∈ D.axisFillingPiece outer none :=
    (D.outerCircleRemainderPoint outer z).2
  change P.glued ((D.circleData outer).planeCirclePoint z) = _
  rw [P.glued_eq none _ hpiece]
  rfl

theorem secondAxisFillingMap_outerCirclePoint
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (z : Circle) :
    D.secondAxisFillingMap hpairwise outer hzero hside
        ((D.circleData outer).planeCirclePoint z) =
      D.secondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.outerCircleRemainderPoint outer z) := by
  let P := D.secondAxisFillingPastingData hpairwise outer hzero hside
  have hpiece : (D.circleData outer).planeCirclePoint z ∈ D.axisFillingPiece outer none :=
    (D.outerCircleRemainderPoint outer z).2
  change P.glued ((D.circleData outer).planeCirclePoint z) = _
  rw [P.glued_eq none _ hpiece]
  rfl

/-- The pasted tube-side map gives a doubled first-coordinate filling of the outer circle. -/
def firstDoubledCoordinateFillingOfOuterDisk
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    SphereCircleDoubledCoordinateFilling (F.circle outer) := by
  let filling : ClosedUnitDisk → Circle :=
    D.firstAxisFillingMap hpairwise outer hzero hside ∘
      (D.circleData outer).planeDiskHomeomorph
  refine .first filling
    ((D.continuous_firstAxisFillingMap hpairwise outer hzero hside).comp
      (D.circleData outer).planeDiskHomeomorph.continuous) ?_
  intro t
  change D.firstAxisFillingMap hpairwise outer hzero hside
      ((D.circleData outer).planeDiskHomeomorph (unitDiskBoundary t)) = _
  rw [← (D.circleData outer).planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary t]
  rw [D.firstAxisFillingMap_outerCirclePoint hpairwise outer hzero hside]
  exact D.firstOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    outer hside t

/-- The pasted exterior-side map gives a doubled second-coordinate filling of the outer circle. -/
def secondDoubledCoordinateFillingOfOuterDisk
    (hzero : F.AllInessential)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    SphereCircleDoubledCoordinateFilling (F.circle outer) := by
  let filling : ClosedUnitDisk → Circle :=
    D.secondAxisFillingMap hpairwise outer hzero hside ∘
      (D.circleData outer).planeDiskHomeomorph
  refine .second filling
    ((D.continuous_secondAxisFillingMap hpairwise outer hzero hside).comp
      (D.circleData outer).planeDiskHomeomorph.continuous) ?_
  intro t
  change D.secondAxisFillingMap hpairwise outer hzero hside
      ((D.circleData outer).planeDiskHomeomorph (unitDiskBoundary t)) = _
  rw [← (D.circleData outer).planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary t]
  rw [D.secondAxisFillingMap_outerCirclePoint hpairwise outer hzero hside]
  exact D.secondOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    outer hside t

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
