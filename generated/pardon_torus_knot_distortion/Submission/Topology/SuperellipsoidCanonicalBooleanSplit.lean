import Submission.Topology.SuperellipsoidCanonicalBooleanCycleCut

/-!
# The canonical true four-port resolution separates its two local cycles

Every canonical outside gap stays at one lower or upper level.  At a true bit the local matching
also preserves that level, so the two horizontal local edges lie in distinct quotient cycles.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph
namespace OuterCircleTransverseHeightCyclicOrderFamily

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
  (cutOrder : G.CutCircleTransverseCyclicOrderFamily)

/-- A canonical outside edge has the same lower or upper label at both endpoints. -/
theorem booleanOutsidePairing_endpointMate_level
    (v : FourPortVertex cutOrder.toPairedSeamEnumeration.bandCount) :
    ((booleanOutsidePairing outerOrder cutOrder).endpointMate v).2.2 = v.2.2 := by
  obtain ⟨p, rfl⟩ :=
    (booleanOutsideEndpointEquiv outerOrder cutOrder).surjective v
  rcases p with ⟨e, j⟩
  rcases e with g | g <;> fin_cases j <;> rfl

end OuterCircleTransverseHeightCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph

namespace BooleanFourPortOutsidePathData

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}
  (D : BooleanFourPortOutsidePathData Phi F)

/-- At a true bit the local endpoint mate preserves the lower or upper label. -/
theorem localEndpointMate_level_of_true
    (choice : Fin n → Bool) (htrue : ∀ b, choice b = true)
    (v : FourPortVertex n) :
    ((fourPortLocalPairing choice).endpointMate v).2.2 = v.2.2 := by
  rcases v with ⟨b, side, level⟩
  have hv := fourPortLocalEndpointEquiv_true (htrue b) level side
  rw [← hv, (fourPortLocalPairing choice).endpointMate_endpointEquiv]
  rw [fourPortLocalEndpointEquiv_true (htrue b)]
  rw [hv]

/-- Any function preserved by both endpoint matchings is constant on quotient cycles. -/
theorem invariant_of_cycleOfVertex_eq
    {alpha : Type*} (value : FourPortVertex n → alpha)
    (choice : Fin n → Bool)
    (hlocal : ∀ v, value ((fourPortLocalPairing choice).endpointMate v) = value v)
    (houtside : ∀ v, value (D.outside.endpointMate v) = value v)
    {v w : FourPortVertex n}
    (hcycle : (D.localFirstSystem choice).cycleOfVertex v =
      (D.localFirstSystem choice).cycleOfVertex w) :
    value v = value w := by
  have heqv : Relation.EqvGen (D.localFirstSystem choice).Incident v w :=
    Quotient.exact hcycle
  clear hcycle
  induction heqv with
  | rel x y hxy =>
      rcases hxy with hfirst | hsecond
      · subst y
        change value x = value ((fourPortLocalPairing choice).endpointMate x)
        exact (hlocal x).symm
      · subst y
        change value x = value (D.outside.endpointMate x)
        exact (houtside x).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

end BooleanFourPortOutsidePathData

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  (D : CanonicalEndpointRegularityData S)

/-- In the all-true resolution the two local edges of any band belong to distinct cycles. -/
theorem true_localEdge_cycleOfVertex_ne
    (choice : D.CanonicalCycleCutBandIndex → Bool)
    (htrue : ∀ b, choice b = true) (b : D.CanonicalCycleCutBandIndex) :
    (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
        (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0)) ≠
      (D.canonicalBooleanOutsidePathData.localFirstSystem choice).cycleOfVertex
        (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1)) := by
  intro hcycle
  have hlevel := D.canonicalBooleanOutsidePathData.invariant_of_cycleOfVertex_eq
    (fun v : FourPortVertex D.centralCutOrder.toPairedSeamEnumeration.bandCount ↦ v.2.2)
    choice
    (BooleanFourPortOutsidePathData.localEndpointMate_level_of_true choice htrue)
    (D.centralOuterOrder.booleanOutsidePairing_endpointMate_level D.centralCutOrder)
    hcycle
  have hb := htrue b
  simp [BooleanFourPortOutsidePathData.localEdgeStart,
    fourPortLocalEndpointEquiv_true hb] at hlevel

/-- The two specified local-edge circles of the all-true resolution are disjoint. -/
theorem true_localEdgeCircle_disjoint
    (choice : D.CanonicalCycleCutBandIndex → Bool)
    (htrue : ∀ b, choice b = true) (b : D.CanonicalCycleCutBandIndex) :
    Disjoint
      (Set.range (D.canonicalBooleanOutsidePathData.localEdgeCircle choice (b, 0)))
      (Set.range (D.canonicalBooleanOutsidePathData.localEdgeCircle choice (b, 1))) := by
  let paths := D.canonicalBooleanOutsidePathData
  let q := (paths.localFirstSystem choice).cycleOfVertex
    (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 0))
  let r := (paths.localFirstSystem choice).cycleOfVertex
    (BooleanFourPortOutsidePathData.localEdgeStart choice (b, 1))
  have hqr : q ≠ r := D.true_localEdge_cycleOfVertex_ne choice htrue b
  have hcarrier := (paths.localFirstIncidence choice).cycleEdgeCarrier_disjoint hqr
  exact hcarrier.mono
    (paths.range_localEdgeCircle_subset_cycleEdgeCarrier choice (b, 0))
    (paths.range_localEdgeCircle_subset_cycleEdgeCarrier choice (b, 1))

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
