import Submission.Topology.BooleanFourPortLocalPairing
import Submission.Topology.SuperellipsoidCanonicalEndpointGraphs
import Submission.Topology.SuperellipsoidTruncatedSphereCycleGluing

/-!
# Canonical outside pairing for the central four-port bands

The lower and upper outer gaps each enumerate the central seam once.  Their disjoint union
therefore enumerates the four labelled ports: the cut-gap enumeration supplies the band and side,
while the lower or upper summand supplies the level.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace OuterCircleTransverseHeightCyclicOrderFamily

variable (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
  (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
  [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

/-- The fixed outside edges are the lower and upper outer gaps. -/
abbrev BooleanOutsideEdge :=
  outerOrder.GlobalLowerOuterGap ⊕ outerOrder.GlobalUpperOuterGap

noncomputable instance booleanOutsideEdgeFintype :
    Fintype (BooleanOutsideEdge outerOrder) := by
  dsimp only [BooleanOutsideEdge]
  infer_instance

private def sumProdDistrib {alpha beta gamma : Type*} :
    (alpha ⊕ beta) × gamma ≃ (alpha × gamma) ⊕ (beta × gamma) where
  toFun
    | (Sum.inl a, c) => Sum.inl (a, c)
    | (Sum.inr b, c) => Sum.inr (b, c)
  invFun
    | Sum.inl (a, c) => (Sum.inl a, c)
    | Sum.inr (b, c) => (Sum.inr b, c)
  left_inv x := by rcases x with ⟨a | b, c⟩ <;> rfl
  right_inv x := by rcases x with ⟨a, c⟩ | ⟨b, c⟩ <;> rfl

private def sumSelfFinTwo {alpha : Type*} : alpha ⊕ alpha ≃ alpha × Fin 2 where
  toFun
    | Sum.inl a => (a, 0)
    | Sum.inr a => (a, 1)
  invFun p := Fin.cases (Sum.inl p.1)
    (fun j : Fin 1 => Fin.cases (Sum.inr p.1) (fun k : Fin 0 => Fin.elim0 k) j) p.2
  left_inv x := by rcases x with a | a <;> rfl
  right_inv p := by
    rcases p with ⟨a, j⟩
    fin_cases j <;> rfl

private def reassocFourPort (n : ℕ) :
    ((Fin n × Fin 2) × Fin 2) ≃ FourPortVertex n where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun p := ((p.1, p.2.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical band and side label of one central seam vertex. -/
noncomputable def seamBandSide
    (v : SuperellipsoidSeamVertex Phi frame c R d) :
    Fin cutOrder.toPairedSeamEnumeration.bandCount × Fin 2 :=
  cutOrder.toPairedSeamEnumeration.endpointEquiv.symm v

/-- The endpoints of all central outer gaps enumerate the four labelled band corners exactly. -/
noncomputable def booleanOutsideEndpointEquiv :
    BooleanOutsideEdge outerOrder × Fin 2 ≃
      FourPortVertex cutOrder.toPairedSeamEnumeration.bandCount :=
  sumProdDistrib |>.trans
    ((Equiv.sumCongr outerOrder.globalLowerEndpointEquiv
      outerOrder.globalUpperEndpointEquiv).trans sumSelfFinTwo) |>.trans
    ((Equiv.prodCongr cutOrder.toPairedSeamEnumeration.endpointEquiv.symm
      (Equiv.refl (Fin 2))).trans
        (reassocFourPort cutOrder.toPairedSeamEnumeration.bandCount))

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
@[simp] theorem booleanOutsideEndpointEquiv_lower
    (g : outerOrder.GlobalLowerOuterGap) (e : Fin 2) :
    booleanOutsideEndpointEquiv outerOrder cutOrder (Sum.inl g, e) =
      let bs := seamBandSide cutOrder (outerOrder.globalLowerEndpointEquiv (g, e))
      (bs.1, (bs.2, 0)) := by
  rfl

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
@[simp] theorem booleanOutsideEndpointEquiv_upper
    (g : outerOrder.GlobalUpperOuterGap) (e : Fin 2) :
    booleanOutsideEndpointEquiv outerOrder cutOrder (Sum.inr g, e) =
      let bs := seamBandSide cutOrder (outerOrder.globalUpperEndpointEquiv (g, e))
      (bs.1, (bs.2, 1)) := by
  rfl

/-- The central lower and upper outer gaps form the fixed perfect matching outside the bands. -/
noncomputable def booleanOutsidePairing :
    FiniteEndpointPairing
      (FourPortVertex cutOrder.toPairedSeamEnumeration.bandCount) where
  edge := BooleanOutsideEdge outerOrder
  finite_edge := inferInstance
  endpointEquiv := booleanOutsideEndpointEquiv outerOrder cutOrder

end OuterCircleTransverseHeightCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
