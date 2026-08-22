import Submission.Topology.EmbeddedPathSubarc
import Submission.Topology.FiniteAlternatingArcCycleCut

/-!
# Cutting an alternating component at a second specified edge

If two distinct first-colour edges lie in the same alternating component, the second edge lies in
the embedded complementary path obtained by cutting at the first.  Consequently it determines an
ordered subpath of that complement.
-/

open Set

noncomputable section

namespace Submission.Topology
namespace FiniteAlternatingEndpointSystem

universe u v

variable {vertex : Type u} [Fintype vertex]
  {X : Type v} [TopologicalSpace X] [T2Space X]
  {A : FiniteAlternatingEndpointSystem vertex} {point : vertex → X}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- Quotient equality gives one of the two successor-orbit parities relative to any chosen
vertex. -/
theorem exists_twoParityAt_of_cycleOfVertex_eq {v w : vertex}
    (hvw : A.cycleOfVertex w = A.cycleOfVertex v) :
    (∃ i : Fin (A.cycleLengthAt v), w = (A.successor ^ (i : ℕ)) v) ∨
      (∃ i : Fin (A.cycleLengthAt v),
        w = A.first.endpointMate ((A.successor ^ (i : ℕ)) v)) := by
  let L := A.cycleLengthAt v
  have hL : 0 < L := A.cycleLengthAt_pos v
  have hperiod : Function.IsPeriodicPt (A.successor : vertex → vertex) L v := by
    rw [Function.IsPeriodicPt, A.successor.iterate_eq_pow]
    exact A.successor_pow_cycleLengthAt v
  have heqv : Relation.EqvGen A.Incident v w := by
    apply Quotient.exact (s := A.cycleSetoid)
    change A.cycleOfVertex v = A.cycleOfVertex w
    exact hvw.symm
  rcases A.eqvGen_incident_twoParity heqv with hsame | hsame
  · obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
    let i : Fin L := ⟨n % L, Nat.mod_lt n hL⟩
    left
    refine ⟨i, ?_⟩
    change w = (A.successor ^ (n % L)) v
    have hmod := hperiod.iterate_mod_apply n
    rw [A.successor.iterate_eq_pow, A.successor.iterate_eq_pow] at hmod
    rw [hmod]
    exact hn.symm
  · have hmate := A.sameCycle_first_endpointMate hsame
    obtain ⟨n, hn⟩ := hmate.exists_nat_pow_eq
    let i : Fin L := ⟨n % L, Nat.mod_lt n hL⟩
    right
    refine ⟨i, ?_⟩
    have hmod : (A.successor ^ (n % L)) v = A.first.endpointMate w := by
      have hperiodMod := hperiod.iterate_mod_apply n
      rw [A.successor.iterate_eq_pow, A.successor.iterate_eq_pow] at hperiodMod
      rw [hperiodMod]
      simpa only [A.first.endpointMate_endpointMate] using hn
    have hmate' := congrArg A.first.endpointMate hmod
    simpa only [A.first.endpointMate_endpointMate] using hmate'.symm

namespace ClosedArcIncidenceData

variable (H : ClosedArcIncidenceData A point firstPaths secondPaths)

omit [T2Space X] in
private theorem range_first_endpointMate (w : vertex) :
    Set.range ((orientedFamily firstPaths secondPaths).first
        (A.first.endpointMate w)) =
      Set.range ((orientedFamily firstPaths secondPaths).first w) := by
  change Set.range (firstPaths.orientedPath (A.first.endpointMate w)) =
    Set.range (firstPaths.orientedPath w)
  have hedge : (A.first.endpointEquiv.symm (A.first.endpointMate w)).1 =
      (A.first.endpointEquiv.symm w).1 := by
    have hw := A.first.endpointEquiv.apply_symm_apply w
    rw [← hw, A.first.endpointMate_endpointEquiv,
      A.first.endpointEquiv.symm_apply_apply, A.first.endpointEquiv.symm_apply_apply]
  rw [firstPaths.range_orientedPath, firstPaths.range_orientedPath]
  exact congrArg (fun e ↦ Set.range (firstPaths.path e)) hedge

omit [T2Space X] in
private theorem range_stepPath_pow_subset_successorStepsCarrier (w : vertex) {k n : ℕ}
    (hkn : k ≤ n) :
    Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ k) w)) ⊆
      successorStepsCarrier firstPaths secondPaths w n := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      rw [successorStepsCarrier]
      by_cases hkle : k ≤ n
      · exact Set.Subset.trans (ih hkle) Set.subset_union_left
      · have hk : k = n + 1 := by omega
        subst k
        exact Set.subset_union_right

omit [T2Space X] in
/-- Every positive successor-position first edge lies in the complementary path based at the
cut vertex. -/
private theorem range_first_pow_subset_complementPathAt (w : vertex)
    (i : Fin (A.cycleLengthAt w)) (hi : 0 < (i : ℕ)) :
    Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ (i : ℕ)) w)) ⊆
      Set.range ((orientedFamily firstPaths secondPaths).complementPathAt w) := by
  let L := A.cycleLengthAt w
  have htwo : 2 ≤ L := by
    have hiLt : (i : ℕ) < L := i.isLt
    omega
  have hL : A.cycleLengthAt w ≠ 1 := by
    simpa only [L] using (show L ≠ 1 by omega)
  obtain ⟨k, hik⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
  have hk : k ≤ L - 2 := by
    have hiLt : (i : ℕ) < L := i.isLt
    omega
  have hpow : (A.successor ^ (i : ℕ)) w =
      (A.successor ^ k) (A.successor w) := by
    rw [hik, ← Equiv.Perm.mul_apply, ← pow_succ]
  rw [OrientedAlternatingArcFamily.complementPathAt, dif_neg hL,
    Path.cast_coe, Path.trans_range]
  apply Set.Subset.trans ?_ Set.subset_union_right
  rw [range_successorStepsNE]
  apply Set.Subset.trans ?_
    (range_stepPath_pow_subset_successorStepsCarrier (A.successor w) hk)
  rw [← hpow, range_stepPath]
  exact Set.subset_union_left

private theorem edge_eq_of_start_eq {e f : A.first.edge}
    (h : A.first.endpointEquiv (e, 0) = A.first.endpointEquiv (f, 0)) : e = f := by
  exact congrArg Prod.fst (A.first.endpointEquiv.injective h)

private theorem edge_eq_of_start_eq_mate {e f : A.first.edge}
    (h : A.first.endpointEquiv (e, 0) =
      A.first.endpointMate (A.first.endpointEquiv (f, 0))) : e = f := by
  rw [A.first.endpointMate_endpointEquiv] at h
  have hpairs := A.first.endpointEquiv.injective h
  exact congrArg Prod.fst hpairs

omit [T2Space X] H in
/-- A distinct first-colour edge in the same quotient component lies in the complementary path
obtained by cutting at the selected first edge. -/
theorem range_firstPath_subset_complementPathAt_of_cycle_eq {e f : A.first.edge}
    (hef : e ≠ f)
    (hcycle : A.cycleOfVertex (A.first.endpointEquiv (f, 0)) =
      A.cycleOfVertex (A.first.endpointEquiv (e, 0))) :
    Set.range (firstPaths.path f) ⊆
      Set.range ((orientedFamily firstPaths secondPaths).complementPathAt
        (A.first.endpointEquiv (e, 0))) := by
  let w := A.first.endpointEquiv (e, 0)
  let z := A.first.endpointEquiv (f, 0)
  have hpath : Set.range (firstPaths.path f) =
      Set.range ((orientedFamily firstPaths secondPaths).first z) := by
    change Set.range (firstPaths.path f) = Set.range (firstPaths.orientedPath z)
    exact (congrArg Set.range (funext fun t ↦
      firstPaths.orientedPath_endpointEquiv_zero_apply f t)).symm
  rcases A.exists_twoParityAt_of_cycleOfVertex_eq hcycle with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hiPos : 0 < (i : ℕ) := by
      by_contra hnot
      have hiZero : (i : ℕ) = 0 := by omega
      have hpowZero : (A.successor ^ (i : ℕ)) w = w := by
        rw [hiZero, pow_zero]
        rfl
      have hzw : z = w := by
        exact (show z = (A.successor ^ (i : ℕ)) w by simpa only [z, w] using hi).trans
          hpowZero
      exact hef (edge_eq_of_start_eq hzw.symm)
    rw [hpath]
    change Set.range ((orientedFamily firstPaths secondPaths).first
        (A.first.endpointEquiv (f, 0))) ⊆ _
    rw [hi]
    exact range_first_pow_subset_complementPathAt w i hiPos
  · have hiPos : 0 < (i : ℕ) := by
      by_contra hnot
      have hiZero : (i : ℕ) = 0 := by omega
      have hpowZero : (A.successor ^ (i : ℕ)) w = w := by
        rw [hiZero, pow_zero]
        rfl
      have hzw : z = A.first.endpointMate w := by
        exact (show z = A.first.endpointMate ((A.successor ^ (i : ℕ)) w) by
          simpa only [z, w] using hi).trans (congrArg A.first.endpointMate hpowZero)
      have hwz : w = A.first.endpointMate z := by
        simpa only [A.first.endpointMate_endpointMate] using
          (congrArg A.first.endpointMate hzw).symm
      exact hef (edge_eq_of_start_eq_mate hwz)
    rw [hpath]
    change Set.range ((orientedFamily firstPaths secondPaths).first
        (A.first.endpointEquiv (f, 0))) ⊆ _
    rw [hi, range_first_endpointMate]
    exact range_first_pow_subset_complementPathAt w i hiPos

include H in
/-- The second specified edge therefore determines ordered parameters in the complementary
path, with either endpoint orientation. -/
theorem exists_ordered_complement_parameters_of_cycle_eq {e f : A.first.edge}
    (hef : e ≠ f)
    (hcycle : A.cycleOfVertex (A.first.endpointEquiv (f, 0)) =
      A.cycleOfVertex (A.first.endpointEquiv (e, 0))) :
    ∃ s t : unitInterval, s < t ∧
      Set.range (firstPaths.path f) =
        Set.range (((orientedFamily firstPaths secondPaths).complementPathAt
          (A.first.endpointEquiv (e, 0))).subpath s t) ∧
      ((point (A.first.endpointEquiv (f, 0)) =
          (orientedFamily firstPaths secondPaths).complementPathAt
            (A.first.endpointEquiv (e, 0)) s ∧
        point (A.first.endpointEquiv (f, 1)) =
          (orientedFamily firstPaths secondPaths).complementPathAt
            (A.first.endpointEquiv (e, 0)) t) ∨
       (point (A.first.endpointEquiv (f, 0)) =
          (orientedFamily firstPaths secondPaths).complementPathAt
            (A.first.endpointEquiv (e, 0)) t ∧
        point (A.first.endpointEquiv (f, 1)) =
          (orientedFamily firstPaths secondPaths).complementPathAt
            (A.first.endpointEquiv (e, 0)) s)) := by
  apply EmbeddedPathSubarc.exists_ordered_parameters_of_range_subset
  · exact ClosedArcIncidenceData.complementPathAt_injective H _
  · exact ClosedArcIncidenceData.first_injective H f
  · exact range_firstPath_subset_complementPathAt_of_cycle_eq hef hcycle

end ClosedArcIncidenceData
end FiniteAlternatingEndpointSystem
end Submission.Topology
