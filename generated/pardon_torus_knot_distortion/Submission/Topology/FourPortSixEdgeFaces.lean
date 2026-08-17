import Submission.Topology.FourPortSixEdgePlanePaths

/-!
# The four candidate faces of the six-edge four-port graph

The honest graph has four facial cycles: the central raw circle, the two child circles, and the
local rectangle made from the four band edges.  This file packages the fourth cycle and proves
the exact carrier bookkeeping.  It deliberately does not designate an outer face.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X]
  (G : FourPortSixEdgePathSystem X)

namespace FourPortSixEdgePathSystem

/-- The upper route of the local rectangle, from lower-left to lower-right. -/
def localRectangleUpperPath : Path G.leftBottom G.rightBottom :=
  (G.left.trans G.top).trans G.right.symm

/-- The carrier of the local four-edge rectangle. -/
def localRectangleCarrier : Set X :=
  Set.range G.localRectangleUpperPath ∪ Set.range G.bottom

theorem localRectangleCarrier_eq : G.localRectangleCarrier =
    (Set.range G.left ∪ Set.range G.top ∪ Set.range G.right) ∪
      Set.range G.bottom := by
  rw [localRectangleCarrier, localRectangleUpperPath,
    Path.trans_range, Path.trans_range, Path.symm_range]

/-- The exact extra embeddedness input for the local rectangle.

For a graph arising from a four-port band chart, this follows from injectivity of the chart and
the four standard rectangle sides. -/
structure LocalRectangleData : Prop where
  twoArcData : TwoArcCircle.Data G.localRectangleUpperPath G.bottom.symm

namespace LocalRectangleData

theorem upper_injective (D : G.LocalRectangleData) :
    Function.Injective G.localRectangleUpperPath :=
  D.1.first_injective

theorem bottom_symm_injective (D : G.LocalRectangleData) :
    Function.Injective G.bottom.symm :=
  D.1.second_injective

theorem upper_inter_bottom (D : G.LocalRectangleData) :
    Set.range G.localRectangleUpperPath ∩ Set.range G.bottom =
      {G.leftBottom, G.rightBottom} := by
  simpa only [Path.symm_range] using D.1.range_inter

end LocalRectangleData

/-- The local rectangle as an embedded standard circle. -/
def localRectangleCircle (_D : G.LocalRectangleData) : Circle → X :=
  TwoArcCircle.circleMap G.localRectangleUpperPath G.bottom.symm

theorem continuous_localRectangleCircle (D : G.LocalRectangleData) :
    Continuous (G.localRectangleCircle D) :=
  TwoArcCircle.continuous_circleMap _ _

theorem localRectangleCircle_injective (D : G.LocalRectangleData) :
    Function.Injective (G.localRectangleCircle D) :=
  D.twoArcData.injective

@[simp] theorem range_localRectangleCircle (D : G.LocalRectangleData) :
    Set.range (G.localRectangleCircle D) = G.localRectangleCarrier := by
  rw [localRectangleCircle, TwoArcCircle.range_circleMap,
    localRectangleCarrier, Path.symm_range]

end FourPortSixEdgePathSystem

/-! ## Planar Jordan-circle package -/

namespace FourPortSixEdgePathSystem

variable (P : FourPortSixEdgePathSystem Schoenflies.Plane)

/-- The four facial-cycle candidates of the embedded six-edge graph. -/
inductive CandidateFace where
  | central
  | bottom
  | top
  | rectangle
  deriving DecidableEq

/-- The local rectangle as a planar Jordan circle. -/
def localRectangleJordanCircle (D : P.LocalRectangleData) : Schoenflies.JordanCircle :=
  twoArcJordanCircle P.localRectangleUpperPath P.bottom.symm
    D.1.first_injective D.1.second_injective D.1.range_inter

@[simp] theorem carrier_localRectangleJordanCircle (D : P.LocalRectangleData) :
    (P.localRectangleJordanCircle D).carrier = P.localRectangleCarrier := by
  rw [localRectangleJordanCircle, carrier_twoArcJordanCircle,
    localRectangleCarrier, Path.symm_range]

/-- The Jordan circle attached to a named candidate face. -/
def candidateFaceCircle (D : P.LocalRectangleData) : CandidateFace →
    Schoenflies.JordanCircle
  | .central => P.centralJordanCircle
  | .bottom => P.bottomJordanCircle
  | .top => P.topJordanCircle
  | .rectangle => P.localRectangleJordanCircle D

@[simp] theorem candidateFaceCircle_central (D : P.LocalRectangleData) :
    P.candidateFaceCircle D .central = P.centralJordanCircle :=
  rfl

@[simp] theorem candidateFaceCircle_bottom (D : P.LocalRectangleData) :
    P.candidateFaceCircle D .bottom = P.bottomJordanCircle :=
  rfl

@[simp] theorem candidateFaceCircle_top (D : P.LocalRectangleData) :
    P.candidateFaceCircle D .top = P.topJordanCircle :=
  rfl

@[simp] theorem candidateFaceCircle_rectangle (D : P.LocalRectangleData) :
    P.candidateFaceCircle D .rectangle = P.localRectangleJordanCircle D :=
  rfl

/-- Cyclic-order information saying that the two global outside arcs leave the local rectangle
on its exterior side.

Because each private outside arc is connected and avoids the rectangle carrier, it is enough in
applications to check this side at one point near a port.  This is the precise rotation datum;
it does not select which raw cycle is the unbounded face. -/
structure RectangleRotationData : Prop where
  rectangle : P.LocalRectangleData
  bottomOutside_private_subset_outside :
    Set.range P.bottomOutside \ {P.leftBottom, P.rightBottom} ⊆
      (P.localRectangleJordanCircle rectangle).outside
  topOutside_private_subset_outside :
    Set.range P.topOutside \ {P.leftTop, P.rightTop} ⊆
      (P.localRectangleJordanCircle rectangle).outside

private theorem range_diff_endpoints_eq_image_Ioo
    {a b : Schoenflies.Plane} (p : Path a b) (hp : Function.Injective p) :
    Set.range p \ ({a, b} : Set Schoenflies.Plane) =
      p '' Set.Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have ht0 : t ≠ 0 := by
      intro h
      apply ht
      left
      subst t
      exact p.source
    have ht1 : t ≠ 1 := by
      intro h
      apply ht
      right
      subst t
      exact p.target
    exact ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0),
      lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro (ha | hb)
    · exact (ne_of_gt ht.1) (hp <| ha.trans p.source.symm)
    · exact (ne_of_lt ht.2) (hp <| hb.trans p.target.symm)

private theorem path_private_preconnected
    {a b : Schoenflies.Plane} (p : Path a b) (hp : Function.Injective p) :
    IsPreconnected (Set.range p \ ({a, b} : Set Schoenflies.Plane)) := by
  rw [range_diff_endpoints_eq_image_Ioo p hp]
  exact isPreconnected_Ioo.image p p.continuous.continuousOn

private theorem path_private_subset_outside_of_witness
    {a b : Schoenflies.Plane} (J : Schoenflies.JordanCircle)
    (p : Path a b) (hp : Function.Injective p)
    (hinter : Set.range p ∩ J.carrier = {a, b})
    (hwitness : ((Set.range p \ {a, b}) ∩ J.outside).Nonempty) :
    Set.range p \ {a, b} ⊆ J.outside := by
  have hprivate : Set.range p \ {a, b} ⊆ J.carrierᶜ := by
    rintro x ⟨hxp, hxEnds⟩ hxJ
    exact hxEnds (by rw [← hinter]; exact ⟨hxp, hxJ⟩)
  have hcover : Set.range p \ {a, b} ⊆ J.inside ∪ J.outside := by
    rw [J.inside_union_outside]
    exact hprivate
  rcases (path_private_preconnected p hp).subset_or_subset
      J.inside_isOpen J.outside_isOpen J.inside_disjoint_outside hcover with
      hins | hout
  · obtain ⟨x, hxPrivate, hxOutside⟩ := hwitness
    exact False.elim <| Set.disjoint_left.mp J.inside_disjoint_outside
      (hins hxPrivate) hxOutside
  · exact hout

/-- Endpoint incidence plus one local side witness determines the global rotation side of each
outside arc. -/
structure RectangleRotationWitnessData : Prop where
  rectangle : P.LocalRectangleData
  bottomOutside_inter_rectangle :
    Set.range P.bottomOutside ∩
        (P.localRectangleJordanCircle rectangle).carrier =
      {P.leftBottom, P.rightBottom}
  topOutside_inter_rectangle :
    Set.range P.topOutside ∩
        (P.localRectangleJordanCircle rectangle).carrier =
      {P.leftTop, P.rightTop}
  bottomOutside_private_point :
    ((Set.range P.bottomOutside \ {P.leftBottom, P.rightBottom}) ∩
      (P.localRectangleJordanCircle rectangle).outside).Nonempty
  topOutside_private_point :
    ((Set.range P.topOutside \ {P.leftTop, P.rightTop}) ∩
      (P.localRectangleJordanCircle rectangle).outside).Nonempty

namespace RectangleRotationWitnessData

/-- Connectedness promotes the two local exterior witnesses to the full rotation datum. -/
theorem toRectangleRotationData (W : P.RectangleRotationWitnessData) :
    P.RectangleRotationData where
  rectangle := W.rectangle
  bottomOutside_private_subset_outside := by
    have hinter := W.bottomOutside_inter_rectangle
    have hwitness := W.bottomOutside_private_point
    rw [Set.pair_comm] at hinter hwitness
    have h := path_private_subset_outside_of_witness
      (P.localRectangleJordanCircle W.rectangle) P.bottomOutside
      P.bottomOutside_injective hinter hwitness
    simpa only [Set.pair_comm] using h
  topOutside_private_subset_outside := by
    have hinter := W.topOutside_inter_rectangle
    have hwitness := W.topOutside_private_point
    rw [Set.pair_comm] at hinter hwitness
    have h := path_private_subset_outside_of_witness
      (P.localRectangleJordanCircle W.rectangle) P.topOutside
      P.topOutside_injective hinter hwitness
    simpa only [Set.pair_comm] using h

end RectangleRotationWitnessData

namespace RectangleRotationData

variable (D : P.RectangleRotationData)

theorem bottomOutside_subset_closedOutside :
    Set.range P.bottomOutside ⊆
      (P.localRectangleJordanCircle D.rectangle).outside ∪
        (P.localRectangleJordanCircle D.rectangle).carrier := by
  intro x hx
  by_cases hendpoint : x ∈ ({P.leftBottom, P.rightBottom} : Set Schoenflies.Plane)
  · right
    rw [P.carrier_localRectangleJordanCircle, P.localRectangleCarrier_eq]
    rcases hendpoint with rfl | rfl
    · exact Or.inr ⟨0, P.bottom.source⟩
    · exact Or.inr ⟨1, P.bottom.target⟩
  · exact Or.inl (D.bottomOutside_private_subset_outside ⟨hx, hendpoint⟩)

theorem topOutside_subset_closedOutside :
    Set.range P.topOutside ⊆
      (P.localRectangleJordanCircle D.rectangle).outside ∪
        (P.localRectangleJordanCircle D.rectangle).carrier := by
  intro x hx
  by_cases hendpoint : x ∈ ({P.leftTop, P.rightTop} : Set Schoenflies.Plane)
  · right
    rw [P.carrier_localRectangleJordanCircle, P.localRectangleCarrier_eq]
    rcases hendpoint with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨1, P.left.target⟩))
    · exact Or.inl (Or.inr ⟨1, P.right.target⟩)
  · exact Or.inl (D.topOutside_private_subset_outside ⟨hx, hendpoint⟩)

end RectangleRotationData

/-- The union of the three raw face carriers is the whole six-edge graph. -/
theorem rawFaceCarrierUnion_eq :
    P.centralJordanCircle.carrier ∪
        (P.bottomJordanCircle.carrier ∪ P.topJordanCircle.carrier) =
      (Set.range P.left ∪ Set.range P.right) ∪
        (Set.range P.bottom ∪ Set.range P.top) ∪
          (Set.range P.bottomOutside ∪ Set.range P.topOutside) := by
  rw [P.carrier_centralJordanCircle, P.carrier_bottomJordanCircle,
    P.carrier_topJordanCircle, fourPortCentralUpperPath,
    Path.trans_range, Path.trans_range, Path.symm_range]
  ext x
  simp only [Path.symm_range, Set.mem_union]
  tauto

/-- The fourth candidate face adds no new edge to the graph carrier. -/
theorem localRectangleCarrier_subset_rawFaceCarrierUnion
    (D : P.LocalRectangleData) :
    (P.localRectangleJordanCircle D).carrier ⊆
      P.centralJordanCircle.carrier ∪
        (P.bottomJordanCircle.carrier ∪ P.topJordanCircle.carrier) := by
  rw [P.carrier_localRectangleJordanCircle,
    P.localRectangleCarrier_eq,
    P.carrier_centralJordanCircle,
    P.carrier_bottomJordanCircle,
    P.carrier_topJordanCircle,
    fourPortCentralUpperPath,
    Path.trans_range, Path.trans_range, Path.symm_range]
  intro x hx
  simp only [Path.symm_range, Set.mem_union] at hx ⊢
  tauto

end FourPortSixEdgePathSystem
end Submission.Topology
