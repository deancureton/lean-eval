import Submission.Topology.SuperellipsoidActiveCycleConcatenation

/-!
# Cutting a finite alternating cycle at a specified edge

The canonical quotient-cycle parametrization chooses an arbitrary representative.  A local
four-port move instead needs to cut a component at one prescribed edge.  This file supplies the
same embedded complementary path construction based at an arbitrary vertex.
-/

open Set

noncomputable section

namespace Submission.Topology
namespace FiniteAlternatingEndpointSystem

universe u v

variable {vertex : Type u} [Fintype vertex]
  {X : Type v} [TopologicalSpace X]
  {A : FiniteAlternatingEndpointSystem vertex} {point : vertex → X}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- Exchange the two colours of a finite alternating endpoint system. -/
def swap (A : FiniteAlternatingEndpointSystem vertex) :
    FiniteAlternatingEndpointSystem vertex where
  first := A.second
  second := A.first

/-- Swapping the two edge colours does not change the unoriented cycle index. -/
noncomputable def swapCycleEquiv
    (A : FiniteAlternatingEndpointSystem vertex) : A.swap.CycleIndex ≃ A.CycleIndex where
  toFun := Quotient.map' id fun x y h ↦ by
    unfold cycleSetoid at h ⊢
    change Relation.EqvGen A.swap.Incident _ _ at h
    change Relation.EqvGen A.Incident _ _
    have hrel : A.swap.Incident ≤ A.Incident := by
      intro _ _ hxy
      exact hxy.elim Or.inr Or.inl
    exact (Relation.EqvGen.mono hrel) x y h
  invFun := Quotient.map' id fun x y h ↦ by
    unfold cycleSetoid at h ⊢
    change Relation.EqvGen A.Incident _ _ at h
    change Relation.EqvGen A.swap.Incident _ _
    have hrel : A.Incident ≤ A.swap.Incident := by
      intro _ _ hxy
      exact hxy.elim Or.inr Or.inl
    exact (Relation.EqvGen.mono hrel) x y h
  left_inv q := Quotient.inductionOn q fun _ ↦ rfl
  right_inv q := Quotient.inductionOn q fun _ ↦ rfl

@[simp] theorem swapCycleEquiv_cycleOfVertex
    (A : FiniteAlternatingEndpointSystem vertex) (v : vertex) :
    A.swapCycleEquiv (A.swap.cycleOfVertex v) = A.cycleOfVertex v :=
  rfl

namespace OrientedAlternatingArcFamily

/-- The complementary arc based at a prescribed first-colour edge. -/
def complementPathAt (D : OrientedAlternatingArcFamily A point) (v : vertex) :
    Path (point (A.first.endpointMate v)) (point v) := by
  let L := A.cycleLengthAt v
  by_cases hL : L = 1
  · have hsuccessor : A.successor v = v := by
      have hreturn := A.successor_pow_cycleLengthAt v
      simpa only [L, hL, pow_one] using hreturn
    exact (D.second v).cast rfl (congrArg point hsuccessor.symm)
  · have htwo : 2 ≤ L := by
      have hpos : 0 < L := A.cycleLengthAt_pos v
      omega
    let tail := (D.second v).trans
      (D.successorStepsNE (A.successor v) (L - 2))
    have hcount : (L - 2) + 1 + 1 = L := by omega
    have hpow : (A.successor ^ ((L - 2) + 1)) (A.successor v) =
        (A.successor ^ L) v := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, hcount]
    exact tail.cast rfl (congrArg point
      (hpow.trans (A.successor_pow_cycleLengthAt v)).symm)

/-- The prescribed first-colour edge and the rest of its alternating component. -/
def firstPathAt (D : OrientedAlternatingArcFamily A point) (v : vertex) :
    Path (point v) (point (A.first.endpointMate v)) :=
  D.first v

end OrientedAlternatingArcFamily

namespace ClosedArcIncidenceData

variable {vertex : Type u} [Fintype vertex]
  {X : Type v} [TopologicalSpace X]
  {A : FiniteAlternatingEndpointSystem vertex} {point : vertex → X}
  {firstPaths : FiniteAlternatingEndpointSystem.EndpointPathFamily A.first point}
  {secondPaths : FiniteAlternatingEndpointSystem.EndpointPathFamily A.second point}

/-- The exact edge carrier is unchanged when the two alternating colours are exchanged. -/
theorem cycleEdgeCarrier_swap
    (_H : ClosedArcIncidenceData A point firstPaths secondPaths) (q : A.swap.CycleIndex) :
    cycleEdgeCarrier A.swap point secondPaths firstPaths q =
      cycleEdgeCarrier A point firstPaths secondPaths (A.swapCycleEquiv q) := by
  classical
  have hcycle (v : vertex) :
      A.swap.cycleOfVertex v = q ↔
        A.cycleOfVertex v = A.swapCycleEquiv q := by
    rw [← A.swapCycleEquiv.injective.eq_iff, A.swapCycleEquiv_cycleOfVertex]
  unfold cycleEdgeCarrier
  change
    ((⋃ e : A.second.edge,
        if A.swap.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q then
          Set.range (secondPaths.path e) else ∅) ∪
      (⋃ e : A.first.edge,
        if A.swap.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q then
          Set.range (firstPaths.path e) else ∅)) = _
  simp_rw [hcycle]
  rw [Set.union_comm]

/-- Exact constituent incidence is symmetric in the two edge colours. -/
theorem swap
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) :
    ClosedArcIncidenceData A.swap point secondPaths firstPaths where
  point_injective := H.point_injective
  first_injective := H.second_injective
  second_injective := H.first_injective
  first_pairwise := H.second_pairwise
  second_pairwise := H.first_pairwise
  cross_intersection := by
    intro e f
    change Set.range (secondPaths.path e) ∩ Set.range (firstPaths.path f) =
      point '' (A.second.endpointSet e ∩ A.first.endpointSet f)
    rw [Set.inter_comm, H.cross_intersection f e, Set.inter_comm]

/-- The complementary path based at an arbitrary vertex is embedded. -/
theorem complementPathAt_injective
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    Function.Injective
      ((orientedFamily firstPaths secondPaths).complementPathAt v) := by
  let D := orientedFamily firstPaths secondPaths
  let L := A.cycleLengthAt v
  by_cases hL : L = 1
  · have hL' : A.cycleLengthAt v = 1 := by simpa only [L] using hL
    have hsecond : Function.Injective (D.second v) := by
      change Function.Injective
        ((secondPaths.orientedPath (A.first.endpointMate v)).cast rfl
          (congrArg point (by rw [successor_apply])))
      simpa only [Path.cast_coe] using
        ClosedArcIncidenceData.second_oriented_injective H
          (A.first.endpointMate v)
    simpa only [D, OrientedAlternatingArcFamily.complementPathAt,
      dif_pos hL', Path.cast_coe] using hsecond
  · have hL' : A.cycleLengthAt v ≠ 1 := by simpa only [L] using hL
    have htwo : 2 ≤ L := by
      have hpos : 0 < L := A.cycleLengthAt_pos v
      omega
    have htail : Function.Injective
        (D.successorStepsNE (A.successor v) (L - 2)) := by
      apply ClosedArcIncidenceData.successorStepsNE_injective H
      rw [A.cycleLengthAt_successor]
      change L - 2 + 1 < L
      omega
    have hsecond : Function.Injective (D.second v) := by
      change Function.Injective
        ((secondPaths.orientedPath (A.first.endpointMate v)).cast rfl
          (congrArg point (by rw [successor_apply])))
      simpa only [Path.cast_coe] using
        ClosedArcIncidenceData.second_oriented_injective H
          (A.first.endpointMate v)
    have hinter : Set.range (D.second v) ∩
        Set.range (D.successorStepsNE (A.successor v) (L - 2)) =
        {point (A.successor v)} := by
      have hcarrier :=
        ClosedArcIncidenceData.second_inter_full_successorStepsCarrier H v (by
          simpa only [L] using htwo)
      rw [← ClosedArcIncidenceData.range_successorStepsNE] at hcarrier
      simpa only [D] using hcarrier
    simpa only [D, OrientedAlternatingArcFamily.complementPathAt,
      dif_neg hL', Path.cast_coe] using
      LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
        (D.second v)
        (D.successorStepsNE (A.successor v) (L - 2))
        hsecond htail hinter

/-- The prescribed edge meets its complementary path exactly at their two endpoints. -/
theorem firstPathAt_inter_complementPathAt
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    Set.range ((orientedFamily firstPaths secondPaths).firstPathAt v) ∩
      Set.range ((orientedFamily firstPaths secondPaths).complementPathAt v) =
      {point v, point (A.first.endpointMate v)} := by
  let D := orientedFamily firstPaths secondPaths
  let L := A.cycleLengthAt v
  by_cases hL : L = 1
  · have hreturn : A.successor v = v := by
      have hpow := A.successor_pow_cycleLengthAt v
      simpa only [L, hL, pow_one] using hpow
    have hL' : A.cycleLengthAt v = 1 := by simpa only [L] using hL
    have hcross := ClosedArcIncidenceData.first_inter_second_eq H v v
    have hset :
        ({v, A.first.endpointMate v} : Set vertex) ∩
            {A.first.endpointMate v, A.successor v} =
          {v, A.first.endpointMate v} := by
      rw [hreturn, Set.pair_comm, Set.inter_self]
    have hcross' : Set.range (D.first v) ∩ Set.range (D.second v) =
        {point v, point (A.first.endpointMate v)} := by
      calc
        _ = point '' (({v, A.first.endpointMate v} : Set vertex) ∩
            {A.first.endpointMate v, A.successor v}) := hcross
        _ = _ := by rw [hset, Set.image_pair]
    simpa only [D, OrientedAlternatingArcFamily.firstPathAt,
      OrientedAlternatingArcFamily.complementPathAt, dif_pos hL',
      Path.cast_coe] using hcross'
  · have hL' : A.cycleLengthAt v ≠ 1 := by simpa only [L] using hL
    have htwo : 2 ≤ L := by
      have hpos : 0 < L := A.cycleLengthAt_pos v
      omega
    have hfirstSecond :=
      ClosedArcIncidenceData.first_inter_second_same_successor_pow H v 0 (by
        simpa only [L] using (show 1 < L by omega))
    have hzero : (A.successor ^ 0) v = v := rfl
    have hfirstZero := congrArg
      (fun w ↦ Set.range (D.first w)) hzero
    have hsecondZero := congrArg
      (fun w ↦ Set.range (D.second w)) hzero
    have hfirstSecond' : Set.range (D.first v) ∩ Set.range (D.second v) =
        {point (A.first.endpointMate v)} := by
      calc
        _ = Set.range (D.first ((A.successor ^ 0) v)) ∩
            Set.range (D.second ((A.successor ^ 0) v)) := by
              rw [hfirstZero, hsecondZero]
        _ = {point (A.first.endpointMate ((A.successor ^ 0) v))} := hfirstSecond
        _ = _ := by rw [hzero]
    have hfirstTail :=
      ClosedArcIncidenceData.first_inter_full_successorStepsCarrier H v (by
        simpa only [L] using htwo)
    rw [← ClosedArcIncidenceData.range_successorStepsNE] at hfirstTail
    simp only [OrientedAlternatingArcFamily.firstPathAt,
      OrientedAlternatingArcFamily.complementPathAt, dif_neg hL',
      Path.cast_coe, Path.trans_range, Set.inter_union_distrib_left]
    rw [hfirstSecond', hfirstTail]
    simp [Set.pair_comm]

/-- Constituent incidence gives a two-arc circle cut at any prescribed first-colour edge. -/
theorem twoArcDataAt
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    TwoArcCircle.Data
      ((orientedFamily firstPaths secondPaths).firstPathAt v)
      ((orientedFamily firstPaths secondPaths).complementPathAt v) where
  first_injective := ClosedArcIncidenceData.first_oriented_injective H v
  second_injective := complementPathAt_injective H v
  range_inter := firstPathAt_inter_complementPathAt H v

private theorem cycleOf_firstEndpoint_zero_eq
    (e : A.first.edge) (j : Fin 2) :
    A.cycleOfVertex (A.first.endpointEquiv (e, 0)) =
      A.cycleOfVertex (A.first.endpointEquiv (e, j)) := by
  fin_cases j
  · rfl
  · exact (A.first_edge_endpoints_same_cycle e).symm

private theorem cycleOf_secondEndpoint_zero_eq
    (e : A.second.edge) (j : Fin 2) :
    A.cycleOfVertex (A.second.endpointEquiv (e, 0)) =
      A.cycleOfVertex (A.second.endpointEquiv (e, j)) := by
  fin_cases j
  · rfl
  · exact (A.second_edge_endpoints_same_cycle e).symm

private theorem first_range_subset_cycleEdgeCarrier
    (_H : ClosedArcIncidenceData A point firstPaths secondPaths)
    {q : A.CycleIndex} {v : vertex} (hv : A.cycleOfVertex v = q) :
    Set.range ((orientedFamily firstPaths secondPaths).first v) ⊆
      cycleEdgeCarrier A point firstPaths secondPaths q := by
  intro x hx
  let p := A.first.endpointEquiv.symm v
  have hp : A.first.endpointEquiv p = v := A.first.endpointEquiv.apply_symm_apply v
  have hcycle : A.cycleOfVertex (A.first.endpointEquiv (p.1, 0)) = q := by
    exact (cycleOf_firstEndpoint_zero_eq p.1 p.2).trans (congrArg A.cycleOfVertex hp) |>.trans hv
  rw [cycleEdgeCarrier]
  left
  refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
  rw [if_pos hcycle]
  change x ∈ Set.range (firstPaths.orientedPath v) at hx
  rw [firstPaths.range_orientedPath] at hx
  simpa only [p] using hx

private theorem second_range_subset_cycleEdgeCarrier
    (_H : ClosedArcIncidenceData A point firstPaths secondPaths)
    {q : A.CycleIndex} {v : vertex} (hv : A.cycleOfVertex v = q) :
    Set.range ((orientedFamily firstPaths secondPaths).second v) ⊆
      cycleEdgeCarrier A point firstPaths secondPaths q := by
  intro x hx
  let w := A.first.endpointMate v
  let p := A.second.endpointEquiv.symm w
  have hp : A.second.endpointEquiv p = w := A.second.endpointEquiv.apply_symm_apply w
  have hcycle : A.cycleOfVertex (A.second.endpointEquiv (p.1, 0)) = q := by
    refine (cycleOf_secondEndpoint_zero_eq p.1 p.2).trans ?_
    rw [hp, A.first_mate_same_cycle]
    exact hv
  rw [cycleEdgeCarrier]
  right
  refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
  rw [if_pos hcycle]
  have hx' : x ∈ Set.range (secondPaths.orientedPath w) := by
    simpa only [orientedFamily,
      OrientedAlternatingArcFamily.ofEndpointPathFamilies, Path.cast_coe] using hx
  rw [secondPaths.range_orientedPath] at hx'
  simpa only [p] using hx'

private theorem successorStepsCarrier_subset_cycleEdgeCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (v : vertex) (n : ℕ) :
    successorStepsCarrier firstPaths secondPaths v n ⊆
      cycleEdgeCarrier A point firstPaths secondPaths (A.cycleOfVertex v) := by
  induction n with
  | zero =>
      rw [successorStepsCarrier, range_stepPath]
      exact Set.union_subset
        (H.first_range_subset_cycleEdgeCarrier rfl)
        (H.second_range_subset_cycleEdgeCarrier rfl)
  | succ n ih =>
      rw [successorStepsCarrier]
      apply Set.union_subset ih
      rw [range_stepPath]
      have hcycle : A.cycleOfVertex ((A.successor ^ (n + 1)) v) =
          A.cycleOfVertex v := by
        induction n + 1 with
        | zero => rfl
        | succ k ih =>
            rw [pow_succ', Equiv.Perm.mul_apply, A.successor_same_cycle]
            exact ih
      exact Set.union_subset
        (H.first_range_subset_cycleEdgeCarrier hcycle)
        (H.second_range_subset_cycleEdgeCarrier hcycle)

/-- Cutting at a specified edge never leaves its quotient-cycle carrier. -/
theorem range_firstPathAt_union_complementPathAt_subset_cycleEdgeCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    Set.range ((orientedFamily firstPaths secondPaths).firstPathAt v) ∪
        Set.range ((orientedFamily firstPaths secondPaths).complementPathAt v) ⊆
      cycleEdgeCarrier A point firstPaths secondPaths (A.cycleOfVertex v) := by
  let D := orientedFamily firstPaths secondPaths
  apply Set.union_subset
  · exact H.first_range_subset_cycleEdgeCarrier rfl
  · let L := A.cycleLengthAt v
    by_cases hL : L = 1
    · have hL' : A.cycleLengthAt v = 1 := by simpa only [L] using hL
      simpa only [D, OrientedAlternatingArcFamily.complementPathAt,
        dif_pos hL', Path.cast_coe] using H.second_range_subset_cycleEdgeCarrier (q :=
          A.cycleOfVertex v) (v := v) rfl
    · have hL' : A.cycleLengthAt v ≠ 1 := by simpa only [L] using hL
      simp only [OrientedAlternatingArcFamily.complementPathAt,
        dif_neg hL', Path.cast_coe, Path.trans_range]
      apply Set.union_subset
      · exact H.second_range_subset_cycleEdgeCarrier rfl
      · rw [range_successorStepsNE]
        have hsubset := H.successorStepsCarrier_subset_cycleEdgeCarrier
          (A.successor v) (L - 2)
        rwa [A.successor_same_cycle] at hsubset

/-- Distinct quotient-cycle edge carriers are disjoint. -/
theorem cycleEdgeCarrier_disjoint
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    {q r : A.CycleIndex} (hqr : q ≠ r) :
    Disjoint (cycleEdgeCarrier A point firstPaths secondPaths q)
      (cycleEdgeCarrier A point firstPaths secondPaths r) := by
  rw [← H.range_circleMap_eq_cycleEdgeCarrier,
    ← H.range_circleMap_eq_cycleEdgeCarrier]
  exact H.circleMap_ranges_disjoint hqr

end ClosedArcIncidenceData
end FiniteAlternatingEndpointSystem
end Submission.Topology
