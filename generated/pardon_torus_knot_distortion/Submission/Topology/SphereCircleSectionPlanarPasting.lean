import Submission.Topology.SphereCircleSectionPlanarCoordinate

/-!
# Component-local planar cap pasting

The punctured remainder and the inclusion-maximal inner Jordan disks form a finite closed cover
of an outer planar disk.  Zero winding only on those selected inner circles supplies cap maps,
and the component-local remainder coordinate agrees with every cap along the overlap circle.
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

/-- The remainder together with one piece for every selected maximal inner disk. -/
def sectionAxisFillingPiece :
    Option (D.maximalInnerDiskIndex outer) → Set (D.closedPlaneDisk outer)
  | none => Subtype.val ⁻¹' D.outerDiskRemainder outer
  | some i => Subtype.val ⁻¹' D.closedPlaneDisk i.1

theorem isClosed_sectionAxisFillingPiece
    (k : Option (D.maximalInnerDiskIndex outer)) :
    IsClosed (D.sectionAxisFillingPiece outer k) := by
  cases k with
  | none => exact (D.isClosed_outerDiskRemainder outer).preimage continuous_subtype_val
  | some i => exact isClosed_closure.preimage continuous_subtype_val

/-- The exact pointwise inessentiality needed on the selected maximal inner circles. -/
def SectionMaximalInnerAllInessential : Prop :=
  ∀ i : D.maximalInnerDiskIndex outer,
    (circleSection.circle i.1).windingLoop.windingPair = (0, 0)

/-- The component-local remainder and maximal inner disks cover the outer closed disk. -/
theorem sectionAxisFillingPiece_cover :
    ⋃ k, D.sectionAxisFillingPiece outer k = Set.univ := by
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

/-- On a remainder/inner-disk overlap, the first component-local formulas agree. -/
theorem sectionFirstRemainderCapOfZero_compatible
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (x : JordanCurve.Arcs.Plane) (hxRemainder : x ∈ D.outerDiskRemainder outer)
    (hxDisk : x ∈ D.closedPlaneDisk i) :
    D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, hxRemainder⟩ =
      (circleSection.circle i).firstPlanarizedZeroWindingDoubledCapMap
        (hinner ⟨i, hi⟩) (D.circleData i) ⟨x, hxDisk⟩ := by
  have hxCarrier : x ∈ (D.circleData i).planeJordanCircle.carrier := by
    rw [← D.outerDiskRemainder_inter_maximalInnerClosedPlaneDisk
      circleSection.pairwise_disjoint outer hi]
    exact ⟨hxRemainder, hxDisk⟩
  obtain ⟨t, ht⟩ :=
    (D.circleData i).exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier hxCarrier
  have hplane : (D.circleData i).planeCircle (Circle.exp t) = x := by
    rw [← (D.circleData i).planeDisk_boundary t]
    exact ht
  rw [show (⟨x, hxRemainder⟩ : D.outerDiskRemainder outer) =
      D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi
        (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  rw [D.sectionFirstOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    outer hside hi t]
  change _ = (circleSection.circle i).firstPlanarizedZeroWindingDoubledCapMap
    (hinner ⟨i, hi⟩) (D.circleData i)
    ⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩
  rw [show
    (⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩ :
      closure (D.circleData i).planeJordanCircle.inside) =
      (D.circleData i).planeCirclePoint (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  exact ((circleSection.circle i).firstPlanarizedZeroWindingDoubledCapMap_planeCirclePoint_exp
      (hinner ⟨i, hi⟩) (D.circleData i) t).symm

/-- On a remainder/inner-disk overlap, the second component-local formulas agree. -/
theorem sectionSecondRemainderCapOfZero_compatible
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    {i : iota} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer)
    (x : JordanCurve.Arcs.Plane) (hxRemainder : x ∈ D.outerDiskRemainder outer)
    (hxDisk : x ∈ D.closedPlaneDisk i) :
    D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, hxRemainder⟩ =
      (circleSection.circle i).secondPlanarizedZeroWindingDoubledCapMap
        (hinner ⟨i, hi⟩) (D.circleData i) ⟨x, hxDisk⟩ := by
  have hxCarrier : x ∈ (D.circleData i).planeJordanCircle.carrier := by
    rw [← D.outerDiskRemainder_inter_maximalInnerClosedPlaneDisk
      circleSection.pairwise_disjoint outer hi]
    exact ⟨hxRemainder, hxDisk⟩
  obtain ⟨t, ht⟩ :=
    (D.circleData i).exists_planeDisk_unitDiskBoundary_eq_of_mem_carrier hxCarrier
  have hplane : (D.circleData i).planeCircle (Circle.exp t) = x := by
    rw [← (D.circleData i).planeDisk_boundary t]
    exact ht
  rw [show (⟨x, hxRemainder⟩ : D.outerDiskRemainder outer) =
      D.innerCircleRemainderPoint circleSection.pairwise_disjoint outer hi
        (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  rw [D.sectionSecondOuterDiskRemainderDoubledCoordinateMap_innerCircleRemainderPoint
    outer hside hi t]
  change _ = (circleSection.circle i).secondPlanarizedZeroWindingDoubledCapMap
    (hinner ⟨i, hi⟩) (D.circleData i)
    ⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩
  rw [show
    (⟨x, (show x ∈ closure (D.circleData i).planeJordanCircle.inside from hxDisk)⟩ :
      closure (D.circleData i).planeJordanCircle.inside) =
      (D.circleData i).planeCirclePoint (Circle.exp t) by
    apply Subtype.ext
    exact hplane.symm]
  exact ((circleSection.circle i).secondPlanarizedZeroWindingDoubledCapMap_planeCirclePoint_exp
      (hinner ⟨i, hi⟩) (D.circleData i) t).symm

/-! ## Finite closed-cover pasting -/

/-- Piecewise first-coordinate values on the component-local finite closed cover. -/
def sectionFirstAxisFillingPieceValue
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    ∀ k, D.sectionAxisFillingPiece outer k → Circle
  | none, x =>
      D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, x.2⟩
  | some i, x =>
      (circleSection.circle i.1).firstPlanarizedZeroWindingDoubledCapMap
        (hinner i) (D.circleData i.1)
        ⟨x, (show (x : JordanCurve.Arcs.Plane) ∈
          closure (D.circleData i.1).planeJordanCircle.inside from x.2)⟩

theorem continuous_sectionFirstAxisFillingPieceValue
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (k : Option (D.maximalInnerDiskIndex outer)) :
    Continuous (D.sectionFirstAxisFillingPieceValue outer hinner hside k) := by
  cases k with
  | none =>
      exact (D.continuous_sectionFirstOuterDiskRemainderDoubledCoordinateMap
        outer hside).comp <|
          Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  | some i =>
      exact ((circleSection.circle i.1).continuous_firstPlanarizedZeroWindingDoubledCapMap
          (hinner i) (D.circleData i.1)).comp <|
            Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The first-coordinate piece values agree on every pairwise overlap. -/
theorem sectionFirstAxisFillingPieceValue_compatible
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (a b : Option (D.maximalInnerDiskIndex outer))
    (x : D.closedPlaneDisk outer) (hxa : x ∈ D.sectionAxisFillingPiece outer a)
    (hxb : x ∈ D.sectionAxisFillingPiece outer b) :
    D.sectionFirstAxisFillingPieceValue outer hinner hside a ⟨x, hxa⟩ =
      D.sectionFirstAxisFillingPieceValue outer hinner hside b ⟨x, hxb⟩ := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j =>
          exact D.sectionFirstRemainderCapOfZero_compatible outer hinner hside
            j.2 x hxa hxb
  | some i =>
      cases b with
      | none =>
          exact (D.sectionFirstRemainderCapOfZero_compatible outer hinner hside
            i.2 x hxb hxa).symm
      | some j =>
          by_cases hij : i = j
          · subst j
            rfl
          · exfalso
            have hijVal : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
            exact Set.disjoint_left.mp
              (D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
                circleSection.pairwise_disjoint outer i.2 j.2 hijVal) hxa hxb

/-- The component-local first-coordinate finite closed-cover pasting package. -/
def sectionFirstAxisFillingPastingData
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    FiniteClosedCoverPastingData (Option (D.maximalInnerDiskIndex outer))
      (D.closedPlaneDisk outer) Circle where
  piece := D.sectionAxisFillingPiece outer
  isClosed_piece := D.isClosed_sectionAxisFillingPiece outer
  cover := D.sectionAxisFillingPiece_cover outer
  value := D.sectionFirstAxisFillingPieceValue outer hinner hside
  continuous_value := D.continuous_sectionFirstAxisFillingPieceValue outer hinner hside
  compatible := D.sectionFirstAxisFillingPieceValue_compatible outer hinner hside

/-- The glued first-coordinate map on the whole outer planar disk. -/
def sectionFirstAxisFillingMap
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    D.closedPlaneDisk outer → Circle :=
  (D.sectionFirstAxisFillingPastingData outer hinner hside).glued

theorem continuous_sectionFirstAxisFillingMap
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    Continuous (D.sectionFirstAxisFillingMap outer hinner hside) :=
  (D.sectionFirstAxisFillingPastingData outer hinner hside).continuous_glued

/-- Piecewise second-coordinate values on the component-local finite closed cover. -/
def sectionSecondAxisFillingPieceValue
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    ∀ k, D.sectionAxisFillingPiece outer k → Circle
  | none, x =>
      D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside ⟨x, x.2⟩
  | some i, x =>
      (circleSection.circle i.1).secondPlanarizedZeroWindingDoubledCapMap
        (hinner i) (D.circleData i.1)
        ⟨x, (show (x : JordanCurve.Arcs.Plane) ∈
          closure (D.circleData i.1).planeJordanCircle.inside from x.2)⟩

theorem continuous_sectionSecondAxisFillingPieceValue
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (k : Option (D.maximalInnerDiskIndex outer)) :
    Continuous (D.sectionSecondAxisFillingPieceValue outer hinner hside k) := by
  cases k with
  | none =>
      exact (D.continuous_sectionSecondOuterDiskRemainderDoubledCoordinateMap
        outer hside).comp <|
          Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  | some i =>
      exact ((circleSection.circle i.1).continuous_secondPlanarizedZeroWindingDoubledCapMap
          (hinner i) (D.circleData i.1)).comp <|
            Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The second-coordinate piece values agree on every pairwise overlap. -/
theorem sectionSecondAxisFillingPieceValue_compatible
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (a b : Option (D.maximalInnerDiskIndex outer))
    (x : D.closedPlaneDisk outer) (hxa : x ∈ D.sectionAxisFillingPiece outer a)
    (hxb : x ∈ D.sectionAxisFillingPiece outer b) :
    D.sectionSecondAxisFillingPieceValue outer hinner hside a ⟨x, hxa⟩ =
      D.sectionSecondAxisFillingPieceValue outer hinner hside b ⟨x, hxb⟩ := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j =>
          exact D.sectionSecondRemainderCapOfZero_compatible outer hinner hside
            j.2 x hxa hxb
  | some i =>
      cases b with
      | none =>
          exact (D.sectionSecondRemainderCapOfZero_compatible outer hinner hside
            i.2 x hxb hxa).symm
      | some j =>
          by_cases hij : i = j
          · subst j
            rfl
          · exfalso
            have hijVal : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
            exact Set.disjoint_left.mp
              (D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
                circleSection.pairwise_disjoint outer i.2 j.2 hijVal) hxa hxb

/-- The component-local second-coordinate finite closed-cover pasting package. -/
def sectionSecondAxisFillingPastingData
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    FiniteClosedCoverPastingData (Option (D.maximalInnerDiskIndex outer))
      (D.closedPlaneDisk outer) Circle where
  piece := D.sectionAxisFillingPiece outer
  isClosed_piece := D.isClosed_sectionAxisFillingPiece outer
  cover := D.sectionAxisFillingPiece_cover outer
  value := D.sectionSecondAxisFillingPieceValue outer hinner hside
  continuous_value := D.continuous_sectionSecondAxisFillingPieceValue outer hinner hside
  compatible := D.sectionSecondAxisFillingPieceValue_compatible outer hinner hside

/-- The glued second-coordinate map on the whole outer planar disk. -/
def sectionSecondAxisFillingMap
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    D.closedPlaneDisk outer → Circle :=
  (D.sectionSecondAxisFillingPastingData outer hinner hside).glued

theorem continuous_sectionSecondAxisFillingMap
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    Continuous (D.sectionSecondAxisFillingMap outer hinner hside) :=
  (D.sectionSecondAxisFillingPastingData outer hinner hside).continuous_glued

/-! ## Outer-boundary evaluation and essential filling -/

theorem sectionFirstAxisFillingMap_outerCirclePoint
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi)
    (z : Circle) :
    D.sectionFirstAxisFillingMap outer hinner hside
        ((D.circleData outer).planeCirclePoint z) =
      D.sectionFirstOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.sectionOuterCircleRemainderPoint outer z) := by
  let P := D.sectionFirstAxisFillingPastingData outer hinner hside
  have hpiece :
      (D.circleData outer).planeCirclePoint z ∈ D.sectionAxisFillingPiece outer none :=
    (D.sectionOuterCircleRemainderPoint outer z).2
  change P.glued ((D.circleData outer).planeCirclePoint z) = _
  rw [P.glued_eq none _ hpiece]
  rfl

theorem sectionSecondAxisFillingMap_outerCirclePoint
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi)
    (z : Circle) :
    D.sectionSecondAxisFillingMap outer hinner hside
        ((D.circleData outer).planeCirclePoint z) =
      D.sectionSecondOuterDiskRemainderDoubledCoordinateMap outer hside
        (D.sectionOuterCircleRemainderPoint outer z) := by
  let P := D.sectionSecondAxisFillingPastingData outer hinner hside
  have hpiece :
      (D.circleData outer).planeCirclePoint z ∈ D.sectionAxisFillingPiece outer none :=
    (D.sectionOuterCircleRemainderPoint outer z).2
  change P.glued ((D.circleData outer).planeCirclePoint z) = _
  rw [P.glued_eq none _ hpiece]
  rfl

/-- A tube-side component remainder gives a doubled first-coordinate filling. -/
def sectionFirstDoubledCoordinateFillingOfOuterDisk
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) :
    SphereCircleDoubledCoordinateFilling (circleSection.circle outer) := by
  let filling : ClosedUnitDisk → Circle :=
    D.sectionFirstAxisFillingMap outer hinner hside ∘
      (D.circleData outer).planeDiskHomeomorph
  refine .first filling
    ((D.continuous_sectionFirstAxisFillingMap outer hinner hside).comp
      (D.circleData outer).planeDiskHomeomorph.continuous) ?_
  intro t
  change D.sectionFirstAxisFillingMap outer hinner hside
      ((D.circleData outer).planeDiskHomeomorph (unitDiskBoundary t)) = _
  rw [← (D.circleData outer).planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary t]
  rw [D.sectionFirstAxisFillingMap_outerCirclePoint outer hinner hside]
  exact D.sectionFirstOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    outer hside t

/-- An exterior-side component remainder gives a doubled second-coordinate filling. -/
def sectionSecondDoubledCoordinateFillingOfOuterDisk
    (hinner : D.SectionMaximalInnerAllInessential outer)
    (hside : ∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :
    SphereCircleDoubledCoordinateFilling (circleSection.circle outer) := by
  let filling : ClosedUnitDisk → Circle :=
    D.sectionSecondAxisFillingMap outer hinner hside ∘
      (D.circleData outer).planeDiskHomeomorph
  refine .second filling
    ((D.continuous_sectionSecondAxisFillingMap outer hinner hside).comp
      (D.circleData outer).planeDiskHomeomorph.continuous) ?_
  intro t
  change D.sectionSecondAxisFillingMap outer hinner hside
      ((D.circleData outer).planeDiskHomeomorph (unitDiskBoundary t)) = _
  rw [← (D.circleData outer).planeCirclePoint_exp_eq_planeDiskHomeomorph_boundary t]
  rw [D.sectionSecondAxisFillingMap_outerCirclePoint outer hinner hside]
  exact D.sectionSecondOuterDiskRemainderDoubledCoordinateMap_outerCircleRemainderPoint
    outer hside t

/-- Choose an inclusion-minimal essential planar circle; every maximal inner circle is then
zero-winding. -/
theorem exists_essential_sectionMaximalInnerAllInessential
  (hessential : ∃ i, (circleSection.circle i).Essential) :
    ∃ outer, (circleSection.circle outer).Essential ∧
      D.SectionMaximalInnerAllInessential outer := by
  let essentialIndices : Set iota := {i | (circleSection.circle i).Essential}
  have hnonempty : essentialIndices.Nonempty := by
    obtain ⟨i, hi⟩ := hessential
    exact ⟨i, hi⟩
  obtain ⟨outer, houter, hminimal⟩ :=
    Set.Finite.exists_minimalFor D.closedPlaneDisk essentialIndices
      (Set.toFinite essentialIndices) hnonempty
  refine ⟨outer, houter, ?_⟩
  intro i
  by_contra hi
  have hiEssential : (circleSection.circle i.1).Essential := hi
  have hiStrict : D.closedPlaneDisk i.1 ⊆
      (D.circleData outer).planeJordanCircle.inside :=
    D.inclusionMaximalInnerClosedPlaneDisk_inside outer i.2
  have hiSubset : D.closedPlaneDisk i.1 ⊆ D.closedPlaneDisk outer :=
    hiStrict.trans subset_closure
  have houterSubset : D.closedPlaneDisk outer ⊆ D.closedPlaneDisk i.1 :=
    hminimal hiEssential hiSubset
  let x := (D.circleData outer).planeCirclePoint (Circle.exp 0)
  have hxInside : (x : JordanCurve.Arcs.Plane) ∈
      (D.circleData outer).planeJordanCircle.inside :=
    hiStrict (houterSubset x.2)
  have hxCarrier : (x : JordanCurve.Arcs.Plane) ∈
      (D.circleData outer).planeJordanCircle.carrier := by
    rw [(D.circleData outer).carrier_planeJordanCircle]
    exact ⟨Circle.exp 0, (D.circleData outer).coe_planeCirclePoint _ |>.symm⟩
  exact (D.circleData outer).planeJordanCircle.inside_subset_compl hxInside hxCarrier

include D in
/-- Every essential exact circle section on one sphere contains an essential circle with a
doubled-coordinate filling. -/
theorem exists_essential_doubledCoordinateFilling_of_section
    (hessential : ∃ i, (circleSection.circle i).Essential) :
    ∃ i, (circleSection.circle i).Essential ∧
      Nonempty (SphereCircleDoubledCoordinateFilling (circleSection.circle i)) := by
  obtain ⟨outer, houter, hinner⟩ :=
    exists_essential_sectionMaximalInnerAllInessential (D := D) hessential
  rcases D.canonicalSectionOuterDiskRemainder_liesOnOneTorusSide outer with
    hTube | hExterior
  · exact ⟨outer, houter,
      ⟨D.sectionFirstDoubledCoordinateFillingOfOuterDisk outer hinner hTube⟩⟩
  · exact ⟨outer, houter,
      ⟨D.sectionSecondDoubledCoordinateFillingOfOuterDisk outer hinner hExterior⟩⟩

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
