import Submission.Topology.FourPortSixEdgeRawPresentation
import Submission.Topology.FourPortSixEdgeRectangle

/-!
# Locating the six-edge outside arcs relative to the four-port band

The vertical endpoint is the complete pre-stage intersection with the local four-port band.
Consequently, the private portions of the two global outside arcs cannot re-enter that band:
each belongs to the pre-stage boundary, while the honest six-edge incidence says it meets the
vertical patch only at its two ports.

This module proves that unconditional fact.  It also isolates the exact remaining chart input
needed to orient the lifted local rectangle: its closed bounded disk must project into the band.
Under that input the private lifted outside arcs lie on the unbounded side, so the rectangle
rotation data follows from the carrier incidence already proved in
`FourPortSixEdgeRectangle`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

namespace FourPortRawSixEdgeBandPresentation

variable (P : FourPortRawSixEdgeBandPresentation R)

private theorem centralCarrier_eq_range :
    torusCircleCarrier P.graph.centralEmbeddedCircle =
      Set.range P.graph.centralCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩

private theorem bottomCarrier_eq_range :
    torusCircleCarrier P.graph.bottomEmbeddedCircle =
      Set.range P.graph.bottomCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩

private theorem topCarrier_eq_range :
    torusCircleCarrier P.graph.topEmbeddedCircle =
      Set.range P.graph.topCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, Subtype.ext rfl⟩

private theorem range_bottomOutside_subset_preAffected :
    Set.range P.graph.bottomOutside ⊆ raw.preAffectedBoundary := by
  rw [← R.pre_range]
  intro x hx
  cases R.direction with
  | split =>
      change x ∈ torusCircleCarrier (R.circle 0)
      rw [← P.centralCarrier_eq, P.centralCarrier_eq_range,
        P.graph.range_centralCircle]
      exact Or.inr hx
  | merge =>
      change x ∈ torusCircleCarrier (R.circle 1) ∪
        torusCircleCarrier (R.circle 2)
      left
      rw [← P.bottomCarrier_eq, P.bottomCarrier_eq_range,
        P.graph.range_bottomCircle]
      exact Or.inr hx

private theorem range_topOutside_subset_preAffected :
    Set.range P.graph.topOutside ⊆ raw.preAffectedBoundary := by
  rw [← R.pre_range]
  intro x hx
  cases R.direction with
  | split =>
      change x ∈ torusCircleCarrier (R.circle 0)
      rw [← P.centralCarrier_eq, P.centralCarrier_eq_range,
        P.graph.range_centralCircle]
      left
      rw [fourPortCentralUpperPath, Path.trans_range, Path.symm_range,
        Path.trans_range, Path.symm_range]
      exact Or.inl (Or.inr hx)
  | merge =>
      change x ∈ torusCircleCarrier (R.circle 1) ∪
        torusCircleCarrier (R.circle 2)
      right
      rw [← P.topCarrier_eq, P.topCarrier_eq_range,
        P.graph.range_topCircle]
      exact Or.inr hx

/-- The private lower outside arc is disjoint from the four-port band. -/
theorem bottomOutside_private_disjoint_band :
    Disjoint
      (Set.range P.graph.bottomOutside \
        {P.graph.leftBottom, P.graph.rightBottom})
      (fourPortBandPart B) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxOutside, hxEnds⟩ hxBand
  have hxParallel : x ∈ fourPortParallelPart B := by
    rw [← raw.pre_local_patch_exact]
    exact ⟨P.range_bottomOutside_subset_preAffected hxOutside, hxBand⟩
  rw [← P.parallelCarrier_eq] at hxParallel
  have hxRectangle : x ∈ P.graph.localRectangleCarrier := by
    rw [P.graph.localRectangleCarrier_eq]
    rcases hxParallel with hxLeft | hxRight
    · exact Or.inl (Or.inl (Or.inl hxLeft))
    · exact Or.inl (Or.inr hxRight)
  apply hxEnds
  rw [← P.graph.bottomOutside_inter_localRectangleCarrier]
  exact ⟨hxOutside, hxRectangle⟩

/-- The private upper outside arc is disjoint from the four-port band. -/
theorem topOutside_private_disjoint_band :
    Disjoint
      (Set.range P.graph.topOutside \
        {P.graph.leftTop, P.graph.rightTop})
      (fourPortBandPart B) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxOutside, hxEnds⟩ hxBand
  have hxParallel : x ∈ fourPortParallelPart B := by
    rw [← raw.pre_local_patch_exact]
    exact ⟨P.range_topOutside_subset_preAffected hxOutside, hxBand⟩
  rw [← P.parallelCarrier_eq] at hxParallel
  have hxRectangle : x ∈ P.graph.localRectangleCarrier := by
    rw [P.graph.localRectangleCarrier_eq]
    rcases hxParallel with hxLeft | hxRight
    · exact Or.inl (Or.inl (Or.inl hxLeft))
    · exact Or.inl (Or.inr hxRight)
  apply hxEnds
  rw [← P.graph.topOutside_inter_localRectangleCarrier]
  exact ⟨hxOutside, hxRectangle⟩

/-- The local chart fact which remains after the endpoint carrier equations are used.

It says that the closed bounded face of the coherently lifted local rectangle projects into the
chosen four-port band.  This is a chart-containment statement, not a planar orientation or
disk-side conclusion. -/
structure RectangleBandContainmentData where
  projection_rectangleClosed_subset_band :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure
          (P.planePathSystem.localRectangleJordanCircle
            P.planePathSystem.localRectangleData).inside ⊆
      fourPortBandPart B

theorem projection_bottomOutside_private_not_mem_band
    (x : TorusCoveringPlane)
    (hx : x ∈ Set.range P.planePathSystem.bottomOutside \
      {P.planePathSystem.leftBottom, P.planePathSystem.rightBottom}) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x ∉
      fourPortBandPart B := by
  obtain ⟨t, rfl⟩ := hx.1
  have hprojection :=
    FourPortSixEdgeZeroWindingData.projection_bottomOutsidePlanePath
      P.toFourPortRawSixEdgePresentation.zeroWindingData t
  apply Set.disjoint_left.mp P.bottomOutside_private_disjoint_band
  refine ⟨⟨t, ?_⟩, ?_⟩
  · exact hprojection.symm
  rintro (hleft | hright)
  · apply hx.2
    left
    have ht : t = 1 := P.graph.bottomOutside_injective <|
      hprojection.symm.trans <| hleft.trans P.graph.bottomOutside.target.symm
    subst t
    exact P.planePathSystem.bottomOutside.target
  · apply hx.2
    right
    have ht : t = 0 := P.graph.bottomOutside_injective <|
      hprojection.symm.trans <| hright.trans P.graph.bottomOutside.source.symm
    subst t
    exact P.planePathSystem.bottomOutside.source

theorem projection_topOutside_private_not_mem_band
    (x : TorusCoveringPlane)
    (hx : x ∈ Set.range P.planePathSystem.topOutside \
      {P.planePathSystem.leftTop, P.planePathSystem.rightTop}) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x ∉
      fourPortBandPart B := by
  obtain ⟨t, rfl⟩ := hx.1
  have hprojection :=
    FourPortSixEdgeZeroWindingData.projection_topOutsidePlanePath
      P.toFourPortRawSixEdgePresentation.zeroWindingData t
  apply Set.disjoint_left.mp P.topOutside_private_disjoint_band
  refine ⟨⟨t, ?_⟩, ?_⟩
  · exact hprojection.symm
  rintro (hleft | hright)
  · apply hx.2
    left
    have ht : t = 1 := P.graph.topOutside_injective <|
      hprojection.symm.trans <| hleft.trans P.graph.topOutside.target.symm
    subst t
    exact P.planePathSystem.topOutside.target
  · apply hx.2
    right
    have ht : t = 0 := P.graph.topOutside_injective <|
      hprojection.symm.trans <| hright.trans P.graph.topOutside.source.symm
    subst t
    exact P.planePathSystem.topOutside.source

private theorem privatePathRange_nonempty
    {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (hp : Function.Injective p) :
    (Set.range p \ {a, b}).Nonempty := by
  let middle : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  refine ⟨p middle, ⟨middle, rfl⟩, ?_⟩
  rintro (hsource | htarget)
  · have hm : middle = 0 := hp <| hsource.trans p.source.symm
    have := congrArg Subtype.val hm
    norm_num [middle] at this
  · have hm : middle = 1 := hp <| htarget.trans p.target.symm
    have := congrArg Subtype.val hm
    norm_num [middle] at this

namespace RectangleBandContainmentData

variable {P : FourPortRawSixEdgeBandPresentation R}

/-- Every private point of the lifted lower outside arc is on the unbounded side of the local
rectangle. -/
theorem bottomOutside_private_subset_rectangleOutside
    (D : P.RectangleBandContainmentData) :
    Set.range P.planePathSystem.bottomOutside \
        {P.planePathSystem.leftBottom, P.planePathSystem.rightBottom} ⊆
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).outside := by
  intro x hx
  have hnotInside : x ∉
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).inside := by
    intro hxInside
    apply P.projection_bottomOutside_private_not_mem_band x hx
    apply D.projection_rectangleClosed_subset_band
    exact ⟨x, subset_closure hxInside, rfl⟩
  have hnotCarrier : x ∉
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).carrier := by
    intro hxCarrier
    apply hx.2
    have hxInter : x ∈ Set.range P.planePathSystem.bottomOutside ∩
        P.planePathSystem.localRectangleCarrier := by
      refine ⟨hx.1, ?_⟩
      rwa [P.planePathSystem.carrier_localRectangleJordanCircle] at hxCarrier
    rw [P.planePathSystem.bottomOutside_inter_localRectangleCarrier] at hxInter
    simpa only [Set.pair_comm] using hxInter
  have hcomplement : x ∈
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).carrierᶜ := hnotCarrier
  rw [← (P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData).inside_union_outside] at hcomplement
  exact hcomplement.resolve_left hnotInside

/-- Every private point of the lifted upper outside arc is on the unbounded side of the local
rectangle. -/
theorem topOutside_private_subset_rectangleOutside
    (D : P.RectangleBandContainmentData) :
    Set.range P.planePathSystem.topOutside \
        {P.planePathSystem.leftTop, P.planePathSystem.rightTop} ⊆
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).outside := by
  intro x hx
  have hnotInside : x ∉
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).inside := by
    intro hxInside
    apply P.projection_topOutside_private_not_mem_band x hx
    apply D.projection_rectangleClosed_subset_band
    exact ⟨x, subset_closure hxInside, rfl⟩
  have hnotCarrier : x ∉
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).carrier := by
    intro hxCarrier
    apply hx.2
    have hxInter : x ∈ Set.range P.planePathSystem.topOutside ∩
        P.planePathSystem.localRectangleCarrier := by
      refine ⟨hx.1, ?_⟩
      rwa [P.planePathSystem.carrier_localRectangleJordanCircle] at hxCarrier
    rw [P.planePathSystem.topOutside_inter_localRectangleCarrier] at hxInter
    simpa only [Set.pair_comm] using hxInter
  have hcomplement : x ∈
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).carrierᶜ := hnotCarrier
  rw [← (P.planePathSystem.localRectangleJordanCircle
    P.planePathSystem.localRectangleData).inside_union_outside] at hcomplement
  exact hcomplement.resolve_left hnotInside

theorem bottomOutside_private_outside_nonempty
    (D : P.RectangleBandContainmentData) :
    ((Set.range P.planePathSystem.bottomOutside \
        {P.planePathSystem.leftBottom, P.planePathSystem.rightBottom}) ∩
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).outside).Nonempty := by
  obtain ⟨x, hx⟩ := privatePathRange_nonempty
    P.planePathSystem.bottomOutside P.planePathSystem.bottomOutside_injective
  have hx' : x ∈ Set.range P.planePathSystem.bottomOutside \
      {P.planePathSystem.leftBottom, P.planePathSystem.rightBottom} := by
    simpa only [Set.pair_comm] using hx
  exact ⟨x, hx', D.bottomOutside_private_subset_rectangleOutside hx'⟩

theorem topOutside_private_outside_nonempty
    (D : P.RectangleBandContainmentData) :
    ((Set.range P.planePathSystem.topOutside \
        {P.planePathSystem.leftTop, P.planePathSystem.rightTop}) ∩
      (P.planePathSystem.localRectangleJordanCircle
        P.planePathSystem.localRectangleData).outside).Nonempty := by
  obtain ⟨x, hx⟩ := privatePathRange_nonempty
    P.planePathSystem.topOutside P.planePathSystem.topOutside_injective
  have hx' : x ∈ Set.range P.planePathSystem.topOutside \
      {P.planePathSystem.leftTop, P.planePathSystem.rightTop} := by
    simpa only [Set.pair_comm] using hx
  exact ⟨x, hx', D.topOutside_private_subset_rectangleOutside hx'⟩

/-- A chart-contained lifted rectangle has the exact rotation required by the six-edge face
theorem. -/
theorem rectangleRotationData (D : P.RectangleBandContainmentData) :
    P.planePathSystem.RectangleRotationData :=
  P.planePathSystem.rectangleRotationData_of_private_outside
    D.bottomOutside_private_outside_nonempty D.topOutside_private_outside_nonempty

end RectangleBandContainmentData
end FourPortRawSixEdgeBandPresentation
end Submission.Topology
