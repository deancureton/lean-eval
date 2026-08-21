import Submission.Topology.SuperellipsoidOuterClosedGapPackage
import Submission.PlaneSchoenflies.ClassificationOfSurfaces.Moise.GraphPolygonalization

/-!
# Constituent incidence for active superellipsoid cycles

This file supplies the set-theoretic input to the finite alternating-path concatenation theorem.
The closed outer arcs of either child are pairwise disjoint, as are the closed inward cutting
arcs.  An outer arc and a cutting arc meet exactly at the seam vertices which label endpoints of
both arcs.  Thus every intersection in the finite degree-two graph is prescribed by its abstract
endpoint pairings.

The ambient local `V`-germ is deliberately not asserted here.  It remains the separate
`ActiveCycleLocalGermData` input to the final realization constructor.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {vertex X : Type*} [Fintype vertex] [TopologicalSpace X]

/-- The endpoint vertices belonging to one edge of a finite endpoint pairing. -/
def FiniteEndpointPairing.endpointSet (P : FiniteEndpointPairing vertex)
    (e : P.edge) : Set vertex :=
  Set.range fun j : Fin 2 ↦ P.endpointEquiv (e, j)

/-- The endpoint set of the edge incident to a vertex consists of that vertex and its mate. -/
theorem FiniteEndpointPairing.endpointSet_edgeOf
    (P : FiniteEndpointPairing vertex) (v : vertex) :
    P.endpointSet (P.endpointEquiv.symm v).1 = {v, P.endpointMate v} := by
  generalize hp : P.endpointEquiv.symm v = p
  rcases p with ⟨e, j⟩
  have hv : P.endpointEquiv (e, j) = v := by
    rw [← hp, P.endpointEquiv.apply_symm_apply]
  rw [← hv]
  fin_cases j <;>
    ext w <;>
    simp [FiniteEndpointPairing.endpointSet, Fin.rev, eq_comm, or_comm]

/-- Two vertices select the same underlying pairing edge exactly when they are equal or are the
two mates on that edge. -/
theorem FiniteEndpointPairing.edgeOf_eq_iff
    (P : FiniteEndpointPairing vertex) (v w : vertex) :
    (P.endpointEquiv.symm v).1 = (P.endpointEquiv.symm w).1 ↔
      v = w ∨ v = P.endpointMate w := by
  constructor
  · intro h
    have hv : v ∈ P.endpointSet (P.endpointEquiv.symm w).1 := by
      rw [← h, P.endpointSet_edgeOf]
      exact Set.mem_insert v _
    simpa only [P.endpointSet_edgeOf, Set.mem_insert_iff, Set.mem_singleton_iff] using hv
  · rintro (rfl | rfl)
    · rfl
    · rw [P.endpointMate_apply]
      simp

namespace FiniteAlternatingEndpointSystem

/-- The two endpoint parities of an alternating component are disjoint.  If the first mate of a
vertex belonged to the same successor orbit, parity of the corresponding integral power would
give a fixed point of one of the two fixed-point-free endpoint involutions. -/
theorem not_sameCycle_first_endpointMate (A : FiniteAlternatingEndpointSystem vertex)
    (v : vertex) :
    ¬A.successor.SameCycle v (A.first.endpointMate v) := by
  let f := A.first.endpointMate
  let g := A.second.endpointMate
  let s := A.successor
  have hs : s = g * f := by
    ext x
    rfl
  have hf : f * f = 1 := A.first.endpointMate_self_comp
  have hg : g * g = 1 := A.second.endpointMate_self_comp
  have hfinv : f⁻¹ = f := inv_eq_iff_mul_eq_one.mpr hf
  have hginv : g⁻¹ = g := inv_eq_iff_mul_eq_one.mpr hg
  have hsemi : SemiconjBy f s s⁻¹ := by
    rw [SemiconjBy]
    rw [hs, mul_inv_rev, hfinv, hginv]
    group
  rintro ⟨n, hn⟩
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · apply A.first.endpointMate_ne ((s ^ k) v)
    change f ((s ^ k) v) = (s ^ k) v
    have hcomm : f * s ^ k = (s⁻¹) ^ k * f := hsemi.zpow_right k
    have hpow : (s⁻¹) ^ k * s ^ (2 * k) = s ^ k := by
      group
    calc
      f ((s ^ k) v) = (f * s ^ k) v := rfl
      _ = ((s⁻¹) ^ k * f) v :=
        congrArg (fun q : Equiv.Perm vertex ↦ q v) hcomm
      _ = ((s⁻¹) ^ k) (f v) := rfl
      _ = ((s⁻¹) ^ k) ((s ^ (2 * k)) v) := congrArg _ hn.symm
      _ = (((s⁻¹) ^ k * s ^ (2 * k)) v) := rfl
      _ = (s ^ k) v := congrArg (fun q : Equiv.Perm vertex ↦ q v) hpow
  · apply A.second.endpointMate_ne ((s ^ (k + 1)) v)
    change g ((s ^ (k + 1)) v) = (s ^ (k + 1)) v
    have hgFromS : g = s * f := by
      rw [hs, mul_assoc, hf, mul_one]
    have hcomm : f * s ^ (k + 1) = (s⁻¹) ^ (k + 1) * f :=
      hsemi.zpow_right (k + 1)
    have hpow : s * (s⁻¹) ^ (k + 1) * s ^ (2 * k + 1) =
        s ^ (k + 1) := by
      group
    calc
      g ((s ^ (k + 1)) v) = (s * f) ((s ^ (k + 1)) v) := by rw [hgFromS]
      _ = (s * (f * s ^ (k + 1))) v := by rfl
      _ = (s * ((s⁻¹) ^ (k + 1) * f)) v := by rw [hcomm]
      _ = (s * (s⁻¹) ^ (k + 1)) (f v) := rfl
      _ = (s * (s⁻¹) ^ (k + 1)) ((s ^ (2 * k + 1)) v) :=
        congrArg _ hn.symm
      _ = (s * (s⁻¹) ^ (k + 1) * s ^ (2 * k + 1)) v := rfl
      _ = (s ^ (k + 1)) v :=
        congrArg (fun q : Equiv.Perm vertex ↦ q v) hpow

/-- Successor powers before the chosen first return time do not repeat. -/
theorem successor_pow_injective_before_cycleLengthAt
    (A : FiniteAlternatingEndpointSystem vertex) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v) (hj : j < A.cycleLengthAt v)
    (hij : (A.successor ^ i) v = (A.successor ^ j) v) : i = j := by
  wlog hijOrder : i ≤ j generalizing i j
  · exact (this hj hi hij.symm (le_of_not_ge hijOrder)).symm
  by_contra hne
  have hijLt : i < j := lt_of_le_of_ne hijOrder hne
  let k := j - i
  have hkPos : 0 < k := Nat.sub_pos_of_lt hijLt
  have hkLt : k < A.cycleLengthAt v := lt_of_le_of_lt (Nat.sub_le j i) hj
  have hkReturn : (A.successor ^ k) v = v := by
    apply (A.successor ^ i).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    rw [show i + k = j by dsimp [k]; omega]
    exact hij.symm
  classical
  have hminimal : A.cycleLengthAt v ≤ k :=
    @Nat.find_min' _ _ (A.exists_pos_successor_pow_eq v) k ⟨hkPos, hkReturn⟩
  exact (not_le_of_gt hkLt) hminimal

/-- The first-return length is invariant under moving the basepoint once around the successor
orbit. -/
theorem cycleLengthAt_successor (A : FiniteAlternatingEndpointSystem vertex) (v : vertex) :
    A.cycleLengthAt (A.successor v) = A.cycleLengthAt v := by
  classical
  unfold cycleLengthAt
  apply Nat.find_congr'
  intro n
  refine and_congr_right fun _ ↦ ?_
  have hcomm : (A.successor ^ n) * A.successor =
      A.successor * (A.successor ^ n) := by group
  constructor
  · intro h
    apply A.successor.injective
    change (A.successor * A.successor ^ n) v = A.successor v
    rw [← hcomm]
    exact h
  · intro h
    change (A.successor ^ n * A.successor) v = A.successor v
    rw [hcomm]
    exact congrArg A.successor h

/-- No successor-orbit vertex can equal a first-mate-parity vertex in the same component. -/
theorem successor_pow_ne_firstMate_successor_pow
    (A : FiniteAlternatingEndpointSystem vertex) (v : vertex) (i j : ℕ) :
    (A.successor ^ i) v ≠ A.first.endpointMate ((A.successor ^ j) v) := by
  intro hij
  apply A.not_sameCycle_first_endpointMate ((A.successor ^ j) v)
  have hvj : A.successor.SameCycle ((A.successor ^ j) v) v :=
    (Equiv.Perm.SameCycle.refl A.successor v).pow_left
  have hvi : A.successor.SameCycle v ((A.successor ^ i) v) :=
    (Equiv.Perm.SameCycle.refl A.successor v).pow_right
  exact (hvj.trans hvi).trans (hij.sameCycle A.successor)

/-- Distinct pre-return successor vertices use distinct first-colour edges. -/
theorem first_edgeOf_successor_pow_ne
    (A : FiniteAlternatingEndpointSystem vertex) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v) (hj : j < A.cycleLengthAt v)
    (hij : i ≠ j) :
    (A.first.endpointEquiv.symm ((A.successor ^ i) v)).1 ≠
      (A.first.endpointEquiv.symm ((A.successor ^ j) v)).1 := by
  intro hedge
  rw [A.first.edgeOf_eq_iff] at hedge
  rcases hedge with hvertices | hparity
  · exact hij (A.successor_pow_injective_before_cycleLengthAt v hi hj hvertices)
  · exact A.successor_pow_ne_firstMate_successor_pow v i j hparity

/-- Distinct pre-return successor vertices also use distinct second-colour edges after applying
the first mate. -/
theorem second_edgeOf_firstMate_successor_pow_ne
    (A : FiniteAlternatingEndpointSystem vertex) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v) (hj : j < A.cycleLengthAt v)
    (hij : i ≠ j) :
    (A.second.endpointEquiv.symm
        (A.first.endpointMate ((A.successor ^ i) v))).1 ≠
      (A.second.endpointEquiv.symm
        (A.first.endpointMate ((A.successor ^ j) v))).1 := by
  intro hedge
  rw [A.second.edgeOf_eq_iff] at hedge
  rcases hedge with hvertices | hparity
  · apply hij
    apply A.successor_pow_injective_before_cycleLengthAt v hi hj
    exact A.first.endpointMate.injective hvertices
  · have hnext : (A.successor ^ (j + 1)) v =
        A.first.endpointMate ((A.successor ^ i) v) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hparity.symm
    exact A.successor_pow_ne_firstMate_successor_pow v (j + 1) i hnext

/-- Pure constituent-arc hypotheses for realizing a finite alternating degree-two graph.

The cross-colour equation is phrased in the vertex type, rather than as a list of exceptional
cases.  In particular it also covers a two-edge component, where the two arcs share both
endpoints. -/
structure ClosedArcIncidenceData (A : FiniteAlternatingEndpointSystem vertex)
    (point : vertex → X)
    (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) : Prop where
  point_injective : Function.Injective point
  first_injective : ∀ e, Function.Injective (firstPaths.path e)
  second_injective : ∀ e, Function.Injective (secondPaths.path e)
  first_pairwise : Pairwise fun e f ↦
    Disjoint (Set.range (firstPaths.path e)) (Set.range (firstPaths.path f))
  second_pairwise : Pairwise fun e f ↦
    Disjoint (Set.range (secondPaths.path e)) (Set.range (secondPaths.path f))
  cross_intersection : ∀ e f,
    Set.range (firstPaths.path e) ∩ Set.range (secondPaths.path f) =
      point '' (A.first.endpointSet e ∩ A.second.endpointSet f)

namespace ClosedArcIncidenceData

variable {A : FiniteAlternatingEndpointSystem vertex} {point : vertex → X}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- Every oriented first-colour constituent is embedded. -/
theorem first_oriented_injective
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    Function.Injective (firstPaths.orientedPath v) :=
  firstPaths.injective_orientedPath H.first_injective v

/-- Every oriented second-colour constituent is embedded. -/
theorem second_oriented_injective
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    Function.Injective (secondPaths.orientedPath v) :=
  secondPaths.injective_orientedPath H.second_injective v

/-- Distinct underlying first-colour edges have disjoint oriented ranges. -/
theorem first_oriented_disjoint_of_edge_ne
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) {v w : vertex}
    (hvw : (A.first.endpointEquiv.symm v).1 ≠
      (A.first.endpointEquiv.symm w).1) :
    Disjoint (Set.range (firstPaths.orientedPath v))
      (Set.range (firstPaths.orientedPath w)) := by
  rw [firstPaths.range_orientedPath, firstPaths.range_orientedPath]
  exact H.first_pairwise hvw

/-- Distinct underlying second-colour edges have disjoint oriented ranges. -/
theorem second_oriented_disjoint_of_edge_ne
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) {v w : vertex}
    (hvw : (A.second.endpointEquiv.symm v).1 ≠
      (A.second.endpointEquiv.symm w).1) :
    Disjoint (Set.range (secondPaths.orientedPath v))
      (Set.range (secondPaths.orientedPath w)) := by
  rw [secondPaths.range_orientedPath, secondPaths.range_orientedPath]
  exact H.second_pairwise hvw

/-- Cross-colour intersections of oriented constituents are still exactly their common abstract
endpoints. -/
theorem oriented_cross_intersection
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v w : vertex) :
    Set.range (firstPaths.orientedPath v) ∩
        Set.range (secondPaths.orientedPath w) =
      point ''
        (A.first.endpointSet (A.first.endpointEquiv.symm v).1 ∩
          A.second.endpointSet (A.second.endpointEquiv.symm w).1) := by
  rw [firstPaths.range_orientedPath, secondPaths.range_orientedPath]
  exact H.cross_intersection _ _

/-- Canonically orient both endpoint path families along the alternating successor. -/
noncomputable def orientedFamily
    (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) :
    OrientedAlternatingArcFamily A point :=
  OrientedAlternatingArcFamily.ofEndpointPathFamilies firstPaths secondPaths

/-- Cross-colour incidence in the orientation used by an alternating step. -/
theorem first_inter_second_eq
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v w : vertex) :
    Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
        Set.range ((orientedFamily firstPaths secondPaths).second w) =
      point '' ({v, A.first.endpointMate v} ∩
        {A.first.endpointMate w, A.successor w}) := by
  change Set.range (firstPaths.orientedPath v) ∩
    Set.range ((secondPaths.orientedPath (A.first.endpointMate w)).cast rfl
      (congrArg point (by rw [successor_apply]))) = _
  simp only [Path.cast_coe]
  rw [H.oriented_cross_intersection]
  rw [A.first.endpointSet_edgeOf, A.second.endpointSet_edgeOf]
  rfl

/-- Distinct successor positions before first return have disjoint first-colour arc ranges. -/
theorem first_ranges_disjoint_of_successor_pow_ne
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v) (hj : j < A.cycleLengthAt v)
    (hij : i ≠ j) :
    Disjoint
      (Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ i) v)))
      (Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ j) v))) := by
  exact H.first_oriented_disjoint_of_edge_ne
    (A.first_edgeOf_successor_pow_ne v hi hj hij)

/-- Distinct successor positions before first return have disjoint second-colour arc ranges. -/
theorem second_ranges_disjoint_of_successor_pow_ne
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v) (hj : j < A.cycleLengthAt v)
    (hij : i ≠ j) :
    Disjoint
      (Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ i) v)))
      (Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ j) v))) := by
  change Disjoint
    (Set.range ((secondPaths.orientedPath
      (A.first.endpointMate ((A.successor ^ i) v))).cast rfl
        (congrArg point (by rw [successor_apply]))))
    (Set.range ((secondPaths.orientedPath
      (A.first.endpointMate ((A.successor ^ j) v))).cast rfl
        (congrArg point (by rw [successor_apply]))))
  simpa only [Path.cast_coe] using H.second_oriented_disjoint_of_edge_ne
    (A.second_edgeOf_firstMate_successor_pow_ne v hi hj hij)

/-- At one successor position the first and second constituents meet only at their joining
vertex, provided the step does not close the whole component. -/
theorem first_inter_second_same_successor_pow
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (i : ℕ) (hiNext : i + 1 < A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ i) v)) ∩
      Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ i) v)) =
      {point (A.first.endpointMate ((A.successor ^ i) v))} := by
  rw [H.first_inter_second_eq]
  have hstep : (A.successor ^ i) v ≠
      A.successor ((A.successor ^ i) v) := by
    intro h
    have hp : (A.successor ^ i) v = (A.successor ^ (i + 1)) v := by
      simpa only [pow_succ', Equiv.Perm.mul_apply] using h
    exact (Nat.ne_of_lt (Nat.lt_succ_self i))
      (A.successor_pow_injective_before_cycleLengthAt v (by omega) hiNext hp)
  have hfirst := A.first.endpointMate_ne ((A.successor ^ i) v)
  have hsecond := A.second.endpointMate_ne
    (A.first.endpointMate ((A.successor ^ i) v))
  have hset :
      ({(A.successor ^ i) v, A.first.endpointMate ((A.successor ^ i) v)} : Set vertex) ∩
          {A.first.endpointMate ((A.successor ^ i) v),
            A.successor ((A.successor ^ i) v)} =
        {A.first.endpointMate ((A.successor ^ i) v)} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx | hm, hm' | hs⟩
      · exact (hfirst (hm'.symm.trans hx)).elim
      · exact (hstep (hx.symm.trans hs)).elim
      · exact hm
      · exact (hsecond (hs.symm.trans hm)).elim
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  rw [hset, Set.image_singleton]

/-- Nonadjacent first/second constituents in one pre-return orbit are disjoint. -/
theorem first_inter_second_successor_pow_eq_empty
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    {i j : ℕ} (hi : i < A.cycleLengthAt v)
    (hj : j < A.cycleLengthAt v) (hjNext : j + 1 < A.cycleLengthAt v)
    (hij : i ≠ j) (hijNext : i ≠ j + 1) :
    Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ i) v)) ∩
      Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ j) v)) = ∅ := by
  rw [H.first_inter_second_eq]
  have hvv : (A.successor ^ i) v ≠ (A.successor ^ j) v := fun h ↦
    hij (A.successor_pow_injective_before_cycleLengthAt v hi hj h)
  have hvnext : (A.successor ^ i) v ≠
      A.successor ((A.successor ^ j) v) := by
    intro h
    apply hijNext
    apply A.successor_pow_injective_before_cycleLengthAt v hi hjNext
    simpa only [pow_succ', Equiv.Perm.mul_apply] using h
  have hmateMate : A.first.endpointMate ((A.successor ^ i) v) ≠
      A.first.endpointMate ((A.successor ^ j) v) := fun h ↦
    hvv (A.first.endpointMate.injective h)
  have hleftParity := A.successor_pow_ne_firstMate_successor_pow v i j
  have hrightParity := A.successor_pow_ne_firstMate_successor_pow v (j + 1) i
  have hmateNext : A.first.endpointMate ((A.successor ^ i) v) ≠
      A.successor ((A.successor ^ j) v) := by
    intro h
    apply hrightParity
    simpa only [pow_succ', Equiv.Perm.mul_apply] using h.symm
  have hset :
      ({(A.successor ^ i) v, A.first.endpointMate ((A.successor ^ i) v)} : Set vertex) ∩
          {A.first.endpointMate ((A.successor ^ j) v),
            A.successor ((A.successor ^ j) v)} = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx | hm, hm' | hs⟩
    · exact hleftParity (hx.symm.trans hm')
    · exact hvnext (hx.symm.trans hs)
    · exact hmateMate (hm.symm.trans hm')
    · exact hmateNext (hm.symm.trans hs)
  rw [hset, Set.image_empty]

/-- Consecutive second/first constituents meet exactly at their shared successor vertex. -/
theorem second_inter_first_next_successor_pow
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (i : ℕ) (hiNext : i + 1 < A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ i) v)) ∩
      Set.range ((orientedFamily firstPaths secondPaths).first
        ((A.successor ^ (i + 1)) v)) =
      {point ((A.successor ^ (i + 1)) v)} := by
  rw [Set.inter_comm]
  rw [H.first_inter_second_eq]
  have hstep : (A.successor ^ i) v ≠ (A.successor ^ (i + 1)) v := fun h ↦
    (Nat.ne_of_lt (Nat.lt_succ_self i))
      (A.successor_pow_injective_before_cycleLengthAt v (by omega) hiNext h)
  have hparity := A.successor_pow_ne_firstMate_successor_pow v (i + 1) i
  have hfirst := A.first.endpointMate_ne ((A.successor ^ (i + 1)) v)
  have hmateMate : A.first.endpointMate ((A.successor ^ (i + 1)) v) ≠
      A.first.endpointMate ((A.successor ^ i) v) := fun h ↦
    hstep.symm (A.first.endpointMate.injective h)
  have hsucc : A.successor ((A.successor ^ i) v) =
      (A.successor ^ (i + 1)) v := by
    simp only [pow_succ', Equiv.Perm.mul_apply]
  have hset :
      ({(A.successor ^ (i + 1)) v,
          A.first.endpointMate ((A.successor ^ (i + 1)) v)} : Set vertex) ∩
          {A.first.endpointMate ((A.successor ^ i) v),
            A.successor ((A.successor ^ i) v)} =
        {(A.successor ^ (i + 1)) v} := by
    rw [hsucc]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [hset, Set.image_singleton]

/-- The carrier of one alternating step is the union of its two constituent colours. -/
theorem range_stepPath (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) (v : vertex) :
    Set.range ((orientedFamily firstPaths secondPaths).stepPath v) =
      Set.range ((orientedFamily firstPaths secondPaths).first v) ∪
        Set.range ((orientedFamily firstPaths secondPaths).second v) := by
  exact Path.trans_range _ _

/-- Nonadjacent steps in one pre-return successor chain are disjoint. -/
theorem step_ranges_disjoint_of_lt
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    {i j : ℕ} (hgap : i + 1 < j) (hjNext : j + 1 < A.cycleLengthAt v) :
    Disjoint
      (Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ i) v)))
      (Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ j) v))) := by
  have hi : i < A.cycleLengthAt v := by omega
  have hiNext : i + 1 < A.cycleLengthAt v := by omega
  have hj : j < A.cycleLengthAt v := by omega
  have hij : i ≠ j := by omega
  have hijNext : i ≠ j + 1 := by omega
  have hjiNext : j ≠ i + 1 := by omega
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [range_stepPath, range_stepPath, Set.union_inter_distrib_right,
    Set.inter_union_distrib_left]
  have hff := Set.disjoint_iff_inter_eq_empty.mp
    (H.first_ranges_disjoint_of_successor_pow_ne v hi hj hij)
  have hss := Set.disjoint_iff_inter_eq_empty.mp
    (H.second_ranges_disjoint_of_successor_pow_ne v hi hj hij)
  have hfs := H.first_inter_second_successor_pow_eq_empty v
    hi hj hjNext hij hijNext
  have hsf := H.first_inter_second_successor_pow_eq_empty v
    hj hi hiNext hij.symm hjiNext
  have hsf' :
      Set.range ((orientedFamily firstPaths secondPaths).second
          ((A.successor ^ i) v)) ∩
        Set.range ((orientedFamily firstPaths secondPaths).first
          ((A.successor ^ j) v)) = ∅ := by
    simpa only [Set.inter_comm] using hsf
  rw [Set.inter_union_distrib_left, hff, hfs, hsf', hss]
  simp

/-- Consecutive steps meet exactly at their common successor vertex. -/
theorem step_inter_next_step
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (i : ℕ) (hiNextNext : i + 2 < A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ i) v)) ∩
      Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ (i + 1)) v)) =
      {point ((A.successor ^ (i + 1)) v)} := by
  have hi : i < A.cycleLengthAt v := by omega
  have hiNext : i + 1 < A.cycleLengthAt v := by omega
  have hij : i ≠ i + 1 := by omega
  rw [range_stepPath, range_stepPath, Set.union_inter_distrib_right,
    Set.inter_union_distrib_left]
  have hff := Set.disjoint_iff_inter_eq_empty.mp
    (H.first_ranges_disjoint_of_successor_pow_ne v hi hiNext hij)
  have hss := Set.disjoint_iff_inter_eq_empty.mp
    (H.second_ranges_disjoint_of_successor_pow_ne v hi hiNext hij)
  have hfs := H.first_inter_second_successor_pow_eq_empty v
    hi hiNext hiNextNext hij (by omega)
  have hsf := H.second_inter_first_next_successor_pow v i hiNext
  rw [Set.inter_union_distrib_left, hff, hfs, hsf, hss]
  simp

/-- The second constituent at one position meets the next whole step only at their shared
successor vertex. -/
theorem second_inter_next_step
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (i : ℕ) (hiNext : i + 1 < A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ i) v)) ∩
      Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ (i + 1)) v)) =
      {point ((A.successor ^ (i + 1)) v)} := by
  have hi : i < A.cycleLengthAt v := by omega
  rw [range_stepPath, Set.inter_union_distrib_left]
  have hsf := H.second_inter_first_next_successor_pow v i hiNext
  have hss := Set.disjoint_iff_inter_eq_empty.mp
    (H.second_ranges_disjoint_of_successor_pow_ne v
      hi hiNext (by omega))
  rw [hsf, hss, union_empty]

/-- The second constituent at position `i` is disjoint from every step more than one position
later. -/
theorem second_disjoint_step_of_lt
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    {i j : ℕ} (hgap : i + 1 < j) (hjNext : j + 1 < A.cycleLengthAt v) :
    Disjoint
      (Set.range ((orientedFamily firstPaths secondPaths).second
        ((A.successor ^ i) v)))
      (Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ j) v))) := by
  have hi : i < A.cycleLengthAt v := by omega
  have hj : j < A.cycleLengthAt v := by omega
  have hij : i ≠ j := by omega
  rw [Set.disjoint_iff_inter_eq_empty, range_stepPath,
    Set.inter_union_distrib_left]
  have hsf := H.first_inter_second_successor_pow_eq_empty v
    hj hi (by omega) hij.symm (by omega)
  rw [Set.inter_comm] at hsf
  have hss := Set.disjoint_iff_inter_eq_empty.mp
    (H.second_ranges_disjoint_of_successor_pow_ne v hi hj hij)
  rw [hsf, hss, empty_union]

/-- A first constituent is disjoint from every genuinely later, nonclosing step. -/
theorem first_disjoint_step_middle
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (j : ℕ) (hj : 0 < j) (hjNext : j + 1 < A.cycleLengthAt v) :
    Disjoint
      (Set.range ((orientedFamily firstPaths secondPaths).first v))
      (Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ j) v))) := by
  have hzero : 0 < A.cycleLengthAt v := A.cycleLengthAt_pos v
  have hj' : j < A.cycleLengthAt v := by omega
  rw [Set.disjoint_iff_inter_eq_empty, range_stepPath,
    Set.inter_union_distrib_left]
  have hff := Set.disjoint_iff_inter_eq_empty.mp
    (H.first_ranges_disjoint_of_successor_pow_ne v hzero hj' (by omega))
  have hfs := H.first_inter_second_successor_pow_eq_empty v
    hzero hj' hjNext (by omega) (by omega)
  have hpowZero : (A.successor ^ 0) v = v := rfl
  have hfirstZero :
      Set.range ((orientedFamily firstPaths secondPaths).first
          ((A.successor ^ 0) v)) =
        Set.range ((orientedFamily firstPaths secondPaths).first v) :=
    congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).first w)) hpowZero
  have hff' :
      Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
        Set.range ((orientedFamily firstPaths secondPaths).first
          ((A.successor ^ j) v)) = ∅ := by
    rw [← hfirstZero]
    exact hff
  have hfs' :
      Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
        Set.range ((orientedFamily firstPaths secondPaths).second
          ((A.successor ^ j) v)) = ∅ := by
    rw [← hfirstZero]
    exact hfs
  rw [hff', hfs', empty_union]

/-- The initial first constituent meets the final closing step exactly at the base vertex. -/
theorem first_inter_closing_step
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (htwo : 2 ≤ A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
      Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ (A.cycleLengthAt v - 1)) v)) =
      {point v} := by
  let L := A.cycleLengthAt v
  have hLPos : 0 < L := A.cycleLengthAt_pos v
  have hlastLt : L - 1 < L := by omega
  have hlastNe : L - 1 ≠ 0 := by omega
  rw [range_stepPath, Set.inter_union_distrib_left]
  have hff := Set.disjoint_iff_inter_eq_empty.mp
    (H.first_ranges_disjoint_of_successor_pow_ne v hLPos hlastLt hlastNe.symm)
  have hcross := H.first_inter_second_eq v ((A.successor ^ (L - 1)) v)
  have hlastVertex : (A.successor ^ (L - 1)) v ≠ v := fun h ↦
    hlastNe (A.successor_pow_injective_before_cycleLengthAt v
      hlastLt hLPos h)
  have hmateLast : A.first.endpointMate v ≠
      A.first.endpointMate ((A.successor ^ (L - 1)) v) := fun h ↦
    hlastVertex.symm (A.first.endpointMate.injective h)
  have hreturn : A.successor ((A.successor ^ (L - 1)) v) = v := by
    calc
      A.successor ((A.successor ^ (L - 1)) v) =
          (A.successor ^ ((L - 1) + 1)) v := by
            rw [pow_succ', Equiv.Perm.mul_apply]
      _ = (A.successor ^ L) v := by congr 2; omega
      _ = v := A.successor_pow_cycleLengthAt v
  have hpowZero : (A.successor ^ 0) v = v := rfl
  have hfirstZero :
      Set.range ((orientedFamily firstPaths secondPaths).first
          ((A.successor ^ 0) v)) =
        Set.range ((orientedFamily firstPaths secondPaths).first v) :=
    congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).first w)) hpowZero
  have hff' :
      Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
        Set.range ((orientedFamily firstPaths secondPaths).first
          ((A.successor ^ (L - 1)) v)) = ∅ := by
    rw [← hfirstZero]
    exact hff
  have hset :
      ({v, A.first.endpointMate v} : Set vertex) ∩
          {A.first.endpointMate ((A.successor ^ (L - 1)) v),
            A.successor ((A.successor ^ (L - 1)) v)} = {v} := by
    rw [hreturn]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hy⟩
      rcases hx with rfl | hx
      · rfl
      rcases hy with hy | hy
      · exact False.elim (hmateLast (hx.symm.trans hy))
      · exact hy
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hcross' :
      Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
        Set.range ((orientedFamily firstPaths secondPaths).second
          ((A.successor ^ (L - 1)) v)) = {point v} := by
    calc
      _ = point '' ({v, A.first.endpointMate v} ∩
          {A.first.endpointMate ((A.successor ^ (L - 1)) v),
            A.successor ((A.successor ^ (L - 1)) v)}) := hcross
      _ = {point v} := by
        rw [hset, Set.image_singleton]
  rw [hff', hcross', empty_union]

/-- Recursive carrier of a nonempty successor-step concatenation. -/
def successorStepsCarrier (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) (v : vertex) : ℕ → Set X
  | 0 => Set.range ((orientedFamily firstPaths secondPaths).stepPath v)
  | n + 1 =>
      successorStepsCarrier firstPaths secondPaths v n ∪
        Set.range ((orientedFamily firstPaths secondPaths).stepPath
          ((A.successor ^ (n + 1)) v))

/-- The recursive carrier is exactly the range of the nonempty path concatenator. -/
theorem range_successorStepsNE (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) (v : vertex) (n : ℕ) :
    Set.range ((orientedFamily firstPaths secondPaths).successorStepsNE v n) =
      successorStepsCarrier firstPaths secondPaths v n := by
  induction n with
  | zero =>
      change Set.range (((orientedFamily firstPaths secondPaths).stepPath v).cast _ _) = _
      rw [Path.cast_coe]
      rfl
  | succ n ih =>
      change Set.range ((((orientedFamily firstPaths secondPaths).successorStepsNE v n).trans
        ((orientedFamily firstPaths secondPaths).stepPath
          ((A.successor ^ (n + 1)) v))).cast _ _) = _
      rw [Path.cast_coe, Path.trans_range, ih]
      rfl

/-- A completed initial block of steps is disjoint from any later nonadjacent step. -/
theorem successorStepsCarrier_disjoint_step_of_lt
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (n j : ℕ) (hnj : n + 1 < j) (hjNext : j + 1 < A.cycleLengthAt v) :
    Disjoint (successorStepsCarrier firstPaths secondPaths v n)
      (Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ j) v))) := by
  induction n with
  | zero =>
      exact H.step_ranges_disjoint_of_lt v (i := 0) (j := j) hnj hjNext
  | succ n ih =>
      rw [successorStepsCarrier]
      exact Set.disjoint_union_left.mpr ⟨
        ih (by omega),
        H.step_ranges_disjoint_of_lt v (i := n + 1) (j := j) hnj hjNext⟩

/-- An initial nonempty successor block meets the next step only at their joining vertex. -/
theorem successorStepsCarrier_inter_next_step
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (n : ℕ) (hnNextNext : n + 2 < A.cycleLengthAt v) :
    successorStepsCarrier firstPaths secondPaths v n ∩
      Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ (n + 1)) v)) =
      {point ((A.successor ^ (n + 1)) v)} := by
  cases n with
  | zero =>
      exact H.step_inter_next_step v 0 hnNextNext
  | succ n =>
      rw [successorStepsCarrier, Set.union_inter_distrib_right]
      have hfar := Set.disjoint_iff_inter_eq_empty.mp
        (H.successorStepsCarrier_disjoint_step_of_lt v n (n + 2)
          (by omega) (by omega))
      have hadj := H.step_inter_next_step v (n + 1) (by omega)
      rw [hfar, hadj, empty_union]

/-- One alternating step is an embedded path whenever it is not already the entire two-edge
cycle. -/
theorem stepPath_injective_of_successor_ne
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (hv : A.successor v ≠ v) :
    Function.Injective
      ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
        firstPaths secondPaths).stepPath v) := by
  let D := OrientedAlternatingArcFamily.ofEndpointPathFamilies firstPaths secondPaths
  have hfirst : Function.Injective (D.first v) := by
    exact H.first_oriented_injective v
  have hsecond : Function.Injective (D.second v) := by
    change Function.Injective
      ((secondPaths.orientedPath (A.first.endpointMate v)).cast rfl
        (congrArg point (by rw [successor_apply])))
    simpa only [Path.cast_coe] using
      H.second_oriented_injective (A.first.endpointMate v)
  have hinter : Set.range (D.first v) ∩ Set.range (D.second v) =
      {point (A.first.endpointMate v)} := by
    change Set.range (firstPaths.orientedPath v) ∩
      Set.range ((secondPaths.orientedPath (A.first.endpointMate v)).cast rfl
        (congrArg point (by rw [successor_apply]))) = _
    simp only [Path.cast_coe]
    rw [H.oriented_cross_intersection]
    rw [A.first.endpointSet_edgeOf, A.second.endpointSet_edgeOf]
    have hvm : v ≠ A.first.endpointMate v :=
      (A.first.endpointMate_ne v).symm
    have hvs : v ≠ A.successor v := hv.symm
    have hset :
        ({v, A.first.endpointMate v} : Set vertex) ∩
            {A.first.endpointMate v, A.successor v} =
          {A.first.endpointMate v} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx, hy⟩
        rcases hx with rfl | rfl
        · rcases hy with hy | hy
          · exact False.elim (hvm hy)
          · exact False.elim (hvs hy)
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, Or.inl rfl⟩
    rw [← A.successor_apply]
    rw [hset, Set.image_singleton]
  exact LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    (D.first v) (D.second v) hfirst hsecond hinter

/-- The initial second-colour arc meets the remaining nonempty successor chain exactly at the
first join. -/
theorem second_inter_successorStepsCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (n : ℕ) (hn : n + 2 < A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
      successorStepsCarrier firstPaths secondPaths (A.successor v) n =
      {point (A.successor v)} := by
  induction n with
  | zero =>
      rw [successorStepsCarrier]
      have hbase := H.second_inter_next_step v 0 (by omega)
      have hzero : (A.successor ^ 0) v = v := rfl
      have hone : (A.successor ^ 1) v = A.successor v := by rw [pow_one]
      have hsecondZero :
          Set.range ((orientedFamily firstPaths secondPaths).second
              ((A.successor ^ 0) v)) =
            Set.range ((orientedFamily firstPaths secondPaths).second v) :=
        congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
      have hstepOne :
          Set.range ((orientedFamily firstPaths secondPaths).stepPath
              ((A.successor ^ 1) v)) =
            Set.range ((orientedFamily firstPaths secondPaths).stepPath
              (A.successor v)) :=
        congrArg (fun w ↦ Set.range
          ((orientedFamily firstPaths secondPaths).stepPath w)) hone
      calc
        _ = Set.range ((orientedFamily firstPaths secondPaths).second
              ((A.successor ^ 0) v)) ∩
            Set.range ((orientedFamily firstPaths secondPaths).stepPath
              ((A.successor ^ 1) v)) := by rw [hsecondZero, hstepOne]
        _ = {point ((A.successor ^ 1) v)} := hbase
        _ = {point (A.successor v)} := by rw [hone]
  | succ n ih =>
      rw [successorStepsCarrier, Set.inter_union_distrib_left]
      have hprefix := ih (by omega)
      have hfar := Set.disjoint_iff_inter_eq_empty.mp
        (H.second_disjoint_step_of_lt v (i := 0) (j := n + 2)
          (by omega) (by omega))
      have hzero : (A.successor ^ 0) v = v := rfl
      have hsecondZero :
          Set.range ((orientedFamily firstPaths secondPaths).second
              ((A.successor ^ 0) v)) =
            Set.range ((orientedFamily firstPaths secondPaths).second v) :=
        congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
      have hfar' :
          Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
            Set.range ((orientedFamily firstPaths secondPaths).stepPath
              ((A.successor ^ (n + 2)) v)) = ∅ := by
        rw [← hsecondZero]
        exact hfar
      have hshift : (A.successor ^ (n + 1)) (A.successor v) =
          (A.successor ^ (n + 2)) v := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
      rw [hshift, hprefix, hfar', union_empty]

/-- Before the closing step, the successor carrier based at `successor v` is disjoint from the
initial first-colour constituent. -/
theorem first_disjoint_successorStepsCarrier_middle
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (n : ℕ) (hn : n + 2 < A.cycleLengthAt v) :
    Disjoint (Set.range ((orientedFamily firstPaths secondPaths).first v))
      (successorStepsCarrier firstPaths secondPaths (A.successor v) n) := by
  induction n with
  | zero =>
      rw [successorStepsCarrier]
      have hmiddle := H.first_disjoint_step_middle v 1 (by omega) hn
      have hone : (A.successor ^ 1) v = A.successor v := by rw [pow_one]
      have hstepOne :
          Set.range ((orientedFamily firstPaths secondPaths).stepPath
              ((A.successor ^ 1) v)) =
            Set.range ((orientedFamily firstPaths secondPaths).stepPath
              (A.successor v)) :=
        congrArg (fun w ↦ Set.range
          ((orientedFamily firstPaths secondPaths).stepPath w)) hone
      rw [← hstepOne]
      exact hmiddle
  | succ n ih =>
      rw [successorStepsCarrier]
      refine Set.disjoint_union_right.mpr ⟨ih (by omega), ?_⟩
      have hmiddle := H.first_disjoint_step_middle v (n + 2) (by omega) hn
      have hshift : (A.successor ^ (n + 1)) (A.successor v) =
          (A.successor ^ (n + 2)) v := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
      rwa [hshift]

/-- The initial first-colour arc meets the whole complementary successor carrier only at the
closing base vertex. -/
theorem first_inter_full_successorStepsCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (htwo : 2 ≤ A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
      successorStepsCarrier firstPaths secondPaths (A.successor v)
        (A.cycleLengthAt v - 2) = {point v} := by
  let L := A.cycleLengthAt v
  by_cases hLtwo : L = 2
  · have hclose := H.first_inter_closing_step v htwo
    have hindex :
        (A.successor ^ (A.cycleLengthAt v - 1)) v = A.successor v := by
      rw [show A.cycleLengthAt v = L by rfl, hLtwo]
      simp
    rw [show A.cycleLengthAt v = L by rfl, hLtwo]
    change Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
      successorStepsCarrier firstPaths secondPaths (A.successor v) 0 = {point v}
    rw [successorStepsCarrier]
    rw [← hindex]
    exact hclose
  · have hthree : 3 ≤ L := by omega
    rw [show L - 2 = (L - 3) + 1 by omega, successorStepsCarrier,
      Set.inter_union_distrib_left]
    have hprefix := Set.disjoint_iff_inter_eq_empty.mp
      (H.first_disjoint_successorStepsCarrier_middle v (L - 3) (by omega))
    have hclose := H.first_inter_closing_step v htwo
    change Set.range ((orientedFamily firstPaths secondPaths).first v) ∩
      Set.range ((orientedFamily firstPaths secondPaths).stepPath
        ((A.successor ^ (L - 1)) v)) = {point v} at hclose
    have hshift : (A.successor ^ (L - 3 + 1)) (A.successor v) =
        (A.successor ^ (L - 1)) v := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
      congr 2
      omega
    rw [hshift, hprefix, hclose, empty_union]

/-- Every nonempty successor block strictly shorter than one successor period is an embedded
path. -/
theorem successorStepsNE_injective
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (n : ℕ) (hn : n + 1 < A.cycleLengthAt v) :
    Function.Injective
      ((orientedFamily firstPaths secondPaths).successorStepsNE v n) := by
  induction n with
  | zero =>
      have hv : A.successor v ≠ v := by
        intro hv
        exact Nat.zero_ne_one (A.successor_pow_injective_before_cycleLengthAt v
          (Nat.zero_lt_of_lt hn) hn (by simpa using hv.symm))
      simpa only [orientedFamily, OrientedAlternatingArcFamily.successorStepsNE,
        Path.cast_coe] using
        H.stepPath_injective_of_successor_ne v hv
  | succ n ih =>
      have hprefix : Function.Injective
          ((orientedFamily firstPaths secondPaths).successorStepsNE v n) :=
        ih (by omega)
      have hstepNe : A.successor ((A.successor ^ (n + 1)) v) ≠
          (A.successor ^ (n + 1)) v := by
        intro h
        exact Nat.succ_ne_self (n + 1)
          (A.successor_pow_injective_before_cycleLengthAt v
            (by omega) (by omega) (by
              rw [pow_succ', Equiv.Perm.mul_apply]
              exact h))
      have hstep := H.stepPath_injective_of_successor_ne
        ((A.successor ^ (n + 1)) v) hstepNe
      have hinter := H.successorStepsCarrier_inter_next_step v n (by omega)
      rw [← range_successorStepsNE] at hinter
      simpa only [OrientedAlternatingArcFamily.successorStepsNE, Path.cast_coe] using
        LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
          ((orientedFamily firstPaths secondPaths).successorStepsNE v n)
          ((orientedFamily firstPaths secondPaths).stepPath
            ((A.successor ^ (n + 1)) v)) hprefix hstep hinter

/-- The initial second-colour arc meets the complete complementary successor carrier only at its
first joining vertex. -/
theorem second_inter_full_successorStepsCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex)
    (htwo : 2 ≤ A.cycleLengthAt v) :
    Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
        successorStepsCarrier firstPaths secondPaths (A.successor v)
          (A.cycleLengthAt v - 2) =
      {point (A.successor v)} := by
  let L := A.cycleLengthAt v
  by_cases hLtwo : L = 2
  · have hbase := H.second_inter_next_step v 0 (by
      simpa only [L, hLtwo] using (show 1 < L by omega))
    rw [show A.cycleLengthAt v = L by rfl, hLtwo]
    change Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
      successorStepsCarrier firstPaths secondPaths (A.successor v) 0 = _
    rw [successorStepsCarrier]
    have hzero : (A.successor ^ 0) v = v := rfl
    have hone : (A.successor ^ 1) v = A.successor v := by rw [pow_one]
    have hsecondZero := congrArg
      (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
    have hstepOne := congrArg
      (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).stepPath w)) hone
    calc
      _ = Set.range ((orientedFamily firstPaths secondPaths).second
            ((A.successor ^ 0) v)) ∩
          Set.range ((orientedFamily firstPaths secondPaths).stepPath
            ((A.successor ^ 1) v)) := by rw [hsecondZero, hstepOne]
      _ = {point ((A.successor ^ 1) v)} := hbase
      _ = _ := by rw [hone]
  · have hthree : 3 ≤ L := by
      have hpos := A.cycleLengthAt_pos v
      omega
    rw [show A.cycleLengthAt v = L by rfl,
      show L - 2 = (L - 3) + 1 by omega, successorStepsCarrier,
      Set.inter_union_distrib_left]
    have hprefix := H.second_inter_successorStepsCarrier v (L - 3) (by
      change L - 3 + 2 < L
      omega)
    have hzero : (A.successor ^ 0) v = v := rfl
    have hlastLt : L - 1 < L := by omega
    have hzeroLt : 0 < L := by omega
    have hfirstSecond := H.first_inter_second_successor_pow_eq_empty v
      hlastLt hzeroLt (by omega) (by omega) (by omega)
    have hfirstSecond' :
        Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
            Set.range ((orientedFamily firstPaths secondPaths).first
              ((A.successor ^ (L - 1)) v)) = ∅ := by
      have hsecondZero := congrArg
        (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
      rw [← hsecondZero, Set.inter_comm]
      exact hfirstSecond
    have hsecondSecond := Set.disjoint_iff_inter_eq_empty.mp
      (H.second_ranges_disjoint_of_successor_pow_ne v hzeroLt hlastLt (by omega))
    have hsecondSecond' :
        Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
            Set.range ((orientedFamily firstPaths secondPaths).second
              ((A.successor ^ (L - 1)) v)) = ∅ := by
      have hsecondZero := congrArg
        (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
      rw [← hsecondZero]
      exact hsecondSecond
    have hclosing :
        Set.range ((orientedFamily firstPaths secondPaths).second v) ∩
            Set.range ((orientedFamily firstPaths secondPaths).stepPath
              ((A.successor ^ (L - 1)) v)) = ∅ := by
      rw [range_stepPath, Set.inter_union_distrib_left,
        hfirstSecond', hsecondSecond', empty_union]
    have hshift : (A.successor ^ (L - 3 + 1)) (A.successor v) =
        (A.successor ^ (L - 1)) v := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
      congr 2
      omega
    rw [hprefix, hshift, hclosing, union_empty]

/-- The canonical complementary path around one alternating component is embedded. -/
theorem complementPath_injective
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (q : A.CycleIndex) :
    Function.Injective
      ((orientedFamily firstPaths secondPaths).complementPath q) := by
  let D := orientedFamily firstPaths secondPaths
  let b := A.baseVertex q
  let L := A.cycleLengthAt b
  by_cases hL : L = 1
  · have hL' : A.cycleLengthAt b = 1 := by simpa only [L] using hL
    have hsecond : Function.Injective
        ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
          firstPaths secondPaths).second b) := by
      change Function.Injective
        ((secondPaths.orientedPath (A.first.endpointMate b)).cast rfl
          (congrArg point (by rw [successor_apply])))
      simpa only [Path.cast_coe] using
        H.second_oriented_injective (A.first.endpointMate b)
    simpa only [D, orientedFamily, OrientedAlternatingArcFamily.complementPath,
      b, dif_pos hL', Path.cast_coe] using hsecond
  · have hL' : A.cycleLengthAt b ≠ 1 := by simpa only [L] using hL
    have htwo : 2 ≤ L := by
      have hpos := A.cycleLengthAt_pos b
      omega
    have htail : Function.Injective
        (D.successorStepsNE (A.successor b) (L - 2)) := by
      apply H.successorStepsNE_injective
      rw [A.cycleLengthAt_successor]
      change L - 2 + 1 < L
      omega
    have hsecond : Function.Injective (D.second b) := by
      change Function.Injective
        ((secondPaths.orientedPath (A.first.endpointMate b)).cast rfl
          (congrArg point (by rw [successor_apply])))
      simpa only [Path.cast_coe] using
        H.second_oriented_injective (A.first.endpointMate b)
    have hinter : Set.range (D.second b) ∩
        Set.range (D.successorStepsNE (A.successor b) (L - 2)) =
        {point (A.successor b)} := by
      rw [range_successorStepsNE]
      exact H.second_inter_full_successorStepsCarrier b (by
        simpa only [L] using htwo)
    simpa only [D, orientedFamily, OrientedAlternatingArcFamily.complementPath,
      b, dif_neg hL', Path.cast_coe] using
      LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
        (D.second b)
        (D.successorStepsNE (A.successor b) (L - 2))
        hsecond htail hinter

/-- The canonical first arc and its complementary concatenation meet exactly at their two common
endpoints. -/
theorem firstPath_inter_complementPath
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (q : A.CycleIndex) :
    Set.range ((orientedFamily firstPaths secondPaths).firstPath q) ∩
      Set.range ((orientedFamily firstPaths secondPaths).complementPath q) =
      {point (A.baseVertex q), point (A.first.endpointMate (A.baseVertex q))} := by
  let D := orientedFamily firstPaths secondPaths
  let b := A.baseVertex q
  let L := A.cycleLengthAt b
  by_cases hL : L = 1
  · have hreturn : A.successor b = b := by
      have := A.successor_pow_cycleLengthAt b
      simpa only [L, hL, pow_one] using this
    have hL' : A.cycleLengthAt b = 1 := by simpa only [L] using hL
    have hcross := H.first_inter_second_eq b b
    have hset :
        ({b, A.first.endpointMate b} : Set vertex) ∩
            {A.first.endpointMate b, A.successor b} =
          {b, A.first.endpointMate b} := by
      rw [hreturn, Set.pair_comm, Set.inter_self]
    have hcross' :
        Set.range ((orientedFamily firstPaths secondPaths).first b) ∩
            Set.range ((orientedFamily firstPaths secondPaths).second b) =
          {point b, point (A.first.endpointMate b)} := by
      calc
        _ = point '' (({b, A.first.endpointMate b} : Set vertex) ∩
            {A.first.endpointMate b, A.successor b}) := hcross
        _ = _ := by rw [hset, Set.image_pair]
    simpa only [D, b, orientedFamily, OrientedAlternatingArcFamily.firstPath,
      OrientedAlternatingArcFamily.complementPath, dif_pos hL', Path.cast_coe] using hcross'
  · have hL' : A.cycleLengthAt b ≠ 1 := by simpa only [L] using hL
    have htwo : 2 ≤ L := by
      have hpos := A.cycleLengthAt_pos b
      omega
    have hfirstSecond := H.first_inter_second_same_successor_pow b 0 (by
      simpa only [L] using (show 1 < L by omega))
    have hzero : (A.successor ^ 0) b = b := rfl
    have hfirstZero :
        Set.range ((orientedFamily firstPaths secondPaths).first
            ((A.successor ^ 0) b)) =
          Set.range ((orientedFamily firstPaths secondPaths).first b) :=
      congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).first w)) hzero
    have hsecondZero :
        Set.range ((orientedFamily firstPaths secondPaths).second
            ((A.successor ^ 0) b)) =
          Set.range ((orientedFamily firstPaths secondPaths).second b) :=
      congrArg (fun w ↦ Set.range ((orientedFamily firstPaths secondPaths).second w)) hzero
    have hfirstSecond' :
        Set.range ((orientedFamily firstPaths secondPaths).first b) ∩
            Set.range ((orientedFamily firstPaths secondPaths).second b) =
          {point (A.first.endpointMate b)} := by
      calc
        _ = Set.range ((orientedFamily firstPaths secondPaths).first
              ((A.successor ^ 0) b)) ∩
            Set.range ((orientedFamily firstPaths secondPaths).second
              ((A.successor ^ 0) b)) := by rw [hfirstZero, hsecondZero]
        _ = {point (A.first.endpointMate ((A.successor ^ 0) b))} := hfirstSecond
        _ = _ := by rw [hzero]
    have hfirstTail := H.first_inter_full_successorStepsCarrier b (by
      simpa only [L] using htwo)
    rw [← range_successorStepsNE] at hfirstTail
    simp only [b, orientedFamily, OrientedAlternatingArcFamily.firstPath,
      OrientedAlternatingArcFamily.complementPath, dif_neg hL', Path.cast_coe,
      Path.trans_range, Set.inter_union_distrib_left]
    have hfirstSecond'' :
        Set.range ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
            firstPaths secondPaths).first (A.baseVertex q)) ∩
          Set.range ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
            firstPaths secondPaths).second (A.baseVertex q)) =
          {point (A.first.endpointMate (A.baseVertex q))} := by
      simpa only [b, orientedFamily] using hfirstSecond'
    have hfirstTail' :
        Set.range ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
            firstPaths secondPaths).first (A.baseVertex q)) ∩
          Set.range ((OrientedAlternatingArcFamily.ofEndpointPathFamilies
            firstPaths secondPaths).successorStepsNE
              (A.successor (A.baseVertex q))
              (A.cycleLengthAt (A.baseVertex q) - 2)) =
          {point (A.baseVertex q)} := by
      simpa only [b, orientedFamily] using hfirstTail
    rw [hfirstSecond'', hfirstTail']
    simp [Set.pair_comm]

/-- Constituent incidence produces the canonical two-arc Jordan data for every alternating
component. -/
theorem twoArcData
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (q : A.CycleIndex) :
    (orientedFamily firstPaths secondPaths).TwoArcData q where
  data := {
    first_injective := H.first_oriented_injective (A.baseVertex q)
    second_injective := H.complementPath_injective q
    range_inter := H.firstPath_inter_complementPath q
  }

/-- The carrier obtained by retaining exactly the two-colour edges in one quotient cycle. -/
noncomputable def cycleEdgeCarrier
    (A : FiniteAlternatingEndpointSystem vertex) (point : vertex → X)
    (firstPaths : EndpointPathFamily A.first point)
    (secondPaths : EndpointPathFamily A.second point) (q : A.CycleIndex) : Set X := by
  classical
  exact
    (⋃ e : A.first.edge,
      if A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q then
        Set.range (firstPaths.path e)
      else ∅) ∪
    (⋃ e : A.second.edge,
      if A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q then
        Set.range (secondPaths.path e)
      else ∅)

private theorem mem_successorStepsCarrier_iff
    (v : vertex) (n : ℕ) (x : X) :
    x ∈ successorStepsCarrier firstPaths secondPaths v n ↔
      ∃ k ≤ n,
        x ∈ Set.range ((orientedFamily firstPaths secondPaths).stepPath
          ((A.successor ^ k) v)) := by
  induction n with
  | zero =>
      simp only [successorStepsCarrier, Nat.le_zero, exists_eq_left]
      rw [pow_zero]
      rfl
  | succ n ih =>
      rw [successorStepsCarrier, Set.mem_union, ih]
      constructor
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, Nat.le_succ_of_le hk, hx⟩
        · exact ⟨n + 1, le_rfl, hx⟩
      · rintro ⟨k, hk, hx⟩
        by_cases hkn : k ≤ n
        · exact Or.inl ⟨k, hkn, hx⟩
        · have hk' : k = n + 1 := by omega
          subst k
          exact Or.inr hx

/-- The canonical circle contains exactly the first- and second-colour constituents at all
successor positions in its quotient cycle. -/
theorem range_circleMap_eq_orientedCycleUnion
    (_H : ClosedArcIncidenceData A point firstPaths secondPaths) (q : A.CycleIndex) :
    Set.range ((orientedFamily firstPaths secondPaths).circleMap q) =
      ⋃ i : Fin (A.cycleLengthAt (A.baseVertex q)),
        (Set.range ((orientedFamily firstPaths secondPaths).first
            (A.orientedVertex q i)) ∪
          Set.range ((orientedFamily firstPaths secondPaths).second
            (A.orientedVertex q i))) := by
  let D := orientedFamily firstPaths secondPaths
  let b := A.baseVertex q
  let L := A.cycleLengthAt b
  have hLpos : 0 < L := A.cycleLengthAt_pos b
  rw [OrientedAlternatingArcFamily.range_circleMap]
  change Set.range (D.firstPath q) ∪ Set.range (D.complementPath q) = _
  change Set.range (D.first b) ∪ Set.range (D.complementPath q) = _
  by_cases hL : L = 1
  · have hsuccessor : A.successor b = b := by
      have hreturn := A.successor_pow_cycleLengthAt b
      simpa only [L, hL, pow_one] using hreturn
    have hcompRange : Set.range (D.complementPath q) = Set.range (D.second b) := by
      unfold OrientedAlternatingArcFamily.complementPath
      simp only [D, b, L, hL, dif_pos, Path.cast_coe]
    rw [hcompRange]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨⟨0, by simpa only [L, hL]⟩, ?_⟩
      change x ∈ Set.range (D.first ((A.successor ^ 0) b)) ∪
        Set.range (D.second ((A.successor ^ 0) b))
      rw [pow_zero]
      exact hx
    · rintro ⟨i, hx⟩
      have hiLt : i.1 < L := i.isLt
      have hi : i.1 = 0 := by omega
      change x ∈ Set.range (D.first ((A.successor ^ i.1) b)) ∪
        Set.range (D.second ((A.successor ^ i.1) b)) at hx
      rw [hi, pow_zero] at hx
      exact hx
  · have htwo : 2 ≤ L := by omega
    have htail := range_successorStepsNE firstPaths secondPaths
      (A.successor b) (L - 2)
    have hcompRange : Set.range (D.complementPath q) =
        Set.range (D.second b) ∪
          Set.range (D.successorStepsNE (A.successor b) (L - 2)) := by
      have hLraw : ¬A.cycleLengthAt (A.baseVertex q) = 1 := by
        simpa only [L, b] using hL
      unfold OrientedAlternatingArcFamily.complementPath
      dsimp only
      rw [dif_neg hLraw]
      simp only [Path.cast_coe, Path.trans_range]
      rfl
    rw [hcompRange]
    rw [htail]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hfirst | hsecond | htailMem)
      · refine ⟨⟨0, hLpos⟩, Or.inl ?_⟩
        change x ∈ Set.range (D.first ((A.successor ^ 0) b))
        rw [pow_zero]
        exact hfirst
      · refine ⟨⟨0, hLpos⟩, Or.inr ?_⟩
        change x ∈ Set.range (D.second ((A.successor ^ 0) b))
        rw [pow_zero]
        exact hsecond
      · rw [mem_successorStepsCarrier_iff] at htailMem
        obtain ⟨k, hk, hkx⟩ := htailMem
        have hkL : k + 1 < L := by omega
        refine ⟨⟨k + 1, hkL⟩, ?_⟩
        rw [range_stepPath] at hkx
        have hpow : (A.successor ^ k) (A.successor b) =
            (A.successor ^ (k + 1)) b := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ]
        rw [hpow] at hkx
        exact hkx
    · rintro ⟨i, hi⟩
      by_cases hi0 : i.1 = 0
      · change x ∈ Set.range (D.first ((A.successor ^ i.1) b)) ∪
          Set.range (D.second ((A.successor ^ i.1) b)) at hi
        rw [hi0, pow_zero] at hi
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
      · obtain ⟨k, hik⟩ : ∃ k, i.1 = k + 1 := by
          exact ⟨i.1 - 1, by omega⟩
        have hiLt : i.1 < L := i.isLt
        have hk : k ≤ L - 2 := by omega
        right
        right
        rw [mem_successorStepsCarrier_iff]
        refine ⟨k, hk, ?_⟩
        rw [range_stepPath]
        change x ∈ Set.range (D.first ((A.successor ^ i.1) b)) ∪
          Set.range (D.second ((A.successor ^ i.1) b)) at hi
        have hpow : (A.successor ^ i.1) b =
            (A.successor ^ k) (A.successor b) := by
          rw [hik, ← Equiv.Perm.mul_apply, ← pow_succ]
        rw [hpow] at hi
        exact hi

private theorem cycleOfVertex_eq_of_mem_first_endpointSet
    {e : A.first.edge} {v : vertex} (hv : v ∈ A.first.endpointSet e) :
    A.cycleOfVertex v = A.cycleOfVertex (A.first.endpointEquiv (e, 0)) := by
  rcases hv with ⟨j, rfl⟩
  fin_cases j
  · rfl
  · exact A.first_edge_endpoints_same_cycle e

private theorem cycleOfVertex_eq_of_mem_second_endpointSet
    {e : A.second.edge} {v : vertex} (hv : v ∈ A.second.endpointSet e) :
    A.cycleOfVertex v = A.cycleOfVertex (A.second.endpointEquiv (e, 0)) := by
  rcases hv with ⟨j, rfl⟩
  fin_cases j
  · rfl
  · exact A.second_edge_endpoints_same_cycle e

/-- The predecessor of an oriented successor-list vertex is again represented in that list. -/
private theorem exists_orientedVertex_eq_successor_inv (q : A.CycleIndex)
    (i : Fin (A.cycleLengthAt (A.baseVertex q))) :
    ∃ j : Fin (A.cycleLengthAt (A.baseVertex q)),
      A.orientedVertex q j = A.successor⁻¹ (A.orientedVertex q i) := by
  let b := A.baseVertex q
  let L := A.cycleLengthAt b
  have hL : 0 < L := A.cycleLengthAt_pos b
  by_cases hi : i.1 = 0
  · let j : Fin L := ⟨L - 1, Nat.sub_lt hL (by omega)⟩
    refine ⟨j, ?_⟩
    apply A.successor.injective
    change A.successor (A.orientedVertex q j) =
      A.successor (A.successor.symm (A.orientedVertex q i))
    rw [A.successor.apply_symm_apply]
    change A.successor ((A.successor ^ (L - 1)) b) =
      (A.successor ^ i.1) b
    rw [hi, pow_zero]
    rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hL]
    exact A.successor_pow_cycleLengthAt b
  · obtain ⟨k, hik⟩ : ∃ k, i.1 = k + 1 := ⟨i.1 - 1, by omega⟩
    have hkL : k < L := by
      have hiLt : i.1 < L := i.isLt
      omega
    refine ⟨⟨k, hkL⟩, ?_⟩
    apply A.successor.injective
    change A.successor (A.orientedVertex q ⟨k, hkL⟩) =
      A.successor (A.successor.symm (A.orientedVertex q i))
    rw [A.successor.apply_symm_apply]
    change A.successor ((A.successor ^ k) b) = (A.successor ^ i.1) b
    rw [hik, ← Equiv.Perm.mul_apply, ← pow_succ']

/-- A second-colour edge viewed from a vertex is the second edge of the predecessor successor
step. -/
private theorem range_second_oriented_eq_second_predecessor (v : vertex) :
    Set.range (secondPaths.orientedPath v) =
      Set.range ((orientedFamily firstPaths secondPaths).second (A.successor⁻¹ v)) := by
  have hsecond :
      Set.range ((orientedFamily firstPaths secondPaths).second (A.successor⁻¹ v)) =
        Set.range (secondPaths.orientedPath
          (A.first.endpointMate (A.successor⁻¹ v))) := by
    simp only [orientedFamily, OrientedAlternatingArcFamily.ofEndpointPathFamilies,
      Path.cast_coe]
  rw [hsecond, secondPaths.range_orientedPath, secondPaths.range_orientedPath]
  have hedge :=
    (A.second.edgeOf_eq_iff v (A.first.endpointMate (A.successor⁻¹ v))).mpr
    (Or.inr (by
      change v = A.successor (A.successor⁻¹ v)
      exact (EquivLike.apply_inv_apply A.successor v).symm))
  rw [hedge]

/-- Exact quotient bookkeeping: the canonical circle range is the union of precisely the
constituent edges whose endpoint quotient is the selected cycle. -/
theorem range_circleMap_eq_cycleEdgeCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (q : A.CycleIndex) :
    Set.range ((orientedFamily firstPaths secondPaths).circleMap q) =
      cycleEdgeCarrier A point firstPaths secondPaths q := by
  classical
  rw [H.range_circleMap_eq_orientedCycleUnion]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, cycleEdgeCarrier]
  constructor
  · rintro ⟨i, hfirst | hsecond⟩
    · left
      let v := A.orientedVertex q i
      let e := (A.first.endpointEquiv.symm v).1
      refine ⟨e, ?_⟩
      have hcycle : A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q := by
        rw [← cycleOfVertex_eq_of_mem_first_endpointSet
          (show v ∈ A.first.endpointSet e by
            exact ⟨(A.first.endpointEquiv.symm v).2,
              A.first.endpointEquiv.apply_symm_apply v⟩)]
        exact A.cycleOf_orientedVertex q i
      simp only [hcycle, if_pos]
      rw [← firstPaths.range_orientedPath]
      exact hfirst
    · right
      let v := A.orientedVertex q i
      let e := (A.second.endpointEquiv.symm (A.first.endpointMate v)).1
      refine ⟨e, ?_⟩
      have hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q := by
        rw [← cycleOfVertex_eq_of_mem_second_endpointSet
          (show A.first.endpointMate v ∈ A.second.endpointSet e by
            exact ⟨(A.second.endpointEquiv.symm (A.first.endpointMate v)).2,
              A.second.endpointEquiv.apply_symm_apply _⟩)]
        rw [A.first_mate_same_cycle]
        exact A.cycleOf_orientedVertex q i
      simp only [hcycle, if_pos]
      simpa only [orientedFamily,
        OrientedAlternatingArcFamily.ofEndpointPathFamilies, Path.cast_coe,
        secondPaths.range_orientedPath] using hsecond
  · rintro (⟨e, he⟩ | ⟨e, he⟩)
    · by_cases hcycle : A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q
      · rw [if_pos hcycle] at he
        have he' : x ∈ Set.range
            (firstPaths.orientedPath (A.first.endpointEquiv (e, 0))) := by
          rw [firstPaths.range_orientedPath]
          have hedge :
              (A.first.endpointEquiv.symm (A.first.endpointEquiv (e, 0))).1 = e :=
            congrArg Prod.fst (A.first.endpointEquiv.symm_apply_apply (e, 0))
          rw [hedge]
          exact he
        rcases (A.cycleOfVertex_eq_iff_twoParity q
          (A.first.endpointEquiv (e, 0))).mp hcycle with ⟨i, hi⟩ | ⟨i, hi⟩
        · refine ⟨i, Or.inl ?_⟩
          change x ∈ Set.range (firstPaths.orientedPath (A.orientedVertex q i))
          rw [← hi]
          exact he'
        · refine ⟨i, Or.inl ?_⟩
          change x ∈ Set.range (firstPaths.orientedPath (A.orientedVertex q i))
          have hedge :
              (A.first.endpointEquiv.symm (A.first.endpointEquiv (e, 0))).1 =
                (A.first.endpointEquiv.symm (A.orientedVertex q i)).1 :=
            (A.first.edgeOf_eq_iff _ _).mpr (Or.inr hi)
          rw [firstPaths.range_orientedPath] at he' ⊢
          rw [← hedge]
          exact he'
      · rw [if_neg hcycle] at he
        exact he.elim
    · by_cases hcycle : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
      · rw [if_pos hcycle] at he
        let v := A.second.endpointEquiv (e, 0)
        have he' : x ∈ Set.range (secondPaths.orientedPath v) := by
          rw [secondPaths.range_orientedPath]
          have hedge : (A.second.endpointEquiv.symm v).1 = e := by
            exact congrArg Prod.fst (A.second.endpointEquiv.symm_apply_apply (e, 0))
          rw [hedge]
          exact he
        rcases (A.cycleOfVertex_eq_iff_twoParity q v).mp hcycle with ⟨i, hi⟩ | ⟨i, hi⟩
        · obtain ⟨j, hj⟩ := exists_orientedVertex_eq_successor_inv q i
          refine ⟨j, Or.inr ?_⟩
          have hrange := range_second_oriented_eq_second_predecessor
            (firstPaths := firstPaths) (secondPaths := secondPaths) (v := v)
          rw [hi] at he' hrange
          rw [hrange] at he'
          rw [← hj] at he'
          exact he'
        · refine ⟨i, Or.inr ?_⟩
          have hsecond :
              Set.range ((orientedFamily firstPaths secondPaths).second
                  (A.orientedVertex q i)) =
                Set.range (secondPaths.orientedPath
                  (A.first.endpointMate (A.orientedVertex q i))) := by
            simp only [orientedFamily,
              OrientedAlternatingArcFamily.ofEndpointPathFamilies, Path.cast_coe]
          rw [hsecond]
          rw [← hi]
          exact he'
      · rw [if_neg hcycle] at he
        exact he.elim

/-- Different quotient cycles have disjoint canonical circle ranges. -/
theorem circleMap_ranges_disjoint
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) {q r : A.CycleIndex}
    (hqr : q ≠ r) :
    Disjoint (Set.range ((orientedFamily firstPaths secondPaths).circleMap q))
      (Set.range ((orientedFamily firstPaths secondPaths).circleMap r)) := by
  rw [H.range_circleMap_eq_cycleEdgeCarrier, H.range_circleMap_eq_cycleEdgeCarrier]
  refine Set.disjoint_left.mpr ?_
  intro x hxq hxr
  simp only [cycleEdgeCarrier, Set.mem_union, Set.mem_iUnion] at hxq hxr
  rcases hxq with ⟨e, he⟩ | ⟨e, he⟩ <;>
    rcases hxr with ⟨f, hf⟩ | ⟨f, hf⟩
  · by_cases heq : A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q
    · rw [if_pos heq] at he
      by_cases hfr : A.cycleOfVertex (A.first.endpointEquiv (f, 0)) = r
      · rw [if_pos hfr] at hf
        by_cases hef : e = f
        · subst f
          exact hqr (heq.symm.trans hfr)
        · exact Set.disjoint_left.mp (H.first_pairwise hef) he hf
      · rw [if_neg hfr] at hf
        exact hf.elim
    · rw [if_neg heq] at he
      exact he.elim
  · by_cases heq : A.cycleOfVertex (A.first.endpointEquiv (e, 0)) = q
    · rw [if_pos heq] at he
      by_cases hfr : A.cycleOfVertex (A.second.endpointEquiv (f, 0)) = r
      · rw [if_pos hfr] at hf
        have hx := Set.mem_inter he hf
        rw [H.cross_intersection] at hx
        obtain ⟨v, ⟨hve, hvf⟩, -⟩ := hx
        have hqv := cycleOfVertex_eq_of_mem_first_endpointSet hve
        have hrv := cycleOfVertex_eq_of_mem_second_endpointSet hvf
        exact hqr (heq.symm.trans (hqv.symm.trans (hrv.trans hfr)))
      · rw [if_neg hfr] at hf
        exact hf.elim
    · rw [if_neg heq] at he
      exact he.elim
  · by_cases heq : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
    · rw [if_pos heq] at he
      by_cases hfr : A.cycleOfVertex (A.first.endpointEquiv (f, 0)) = r
      · rw [if_pos hfr] at hf
        have hx := Set.mem_inter hf he
        rw [H.cross_intersection] at hx
        obtain ⟨v, ⟨hvf, hve⟩, -⟩ := hx
        have hqv := cycleOfVertex_eq_of_mem_second_endpointSet hve
        have hrv := cycleOfVertex_eq_of_mem_first_endpointSet hvf
        exact hqr (heq.symm.trans (hqv.symm.trans (hrv.trans hfr)))
      · rw [if_neg hfr] at hf
        exact hf.elim
    · rw [if_neg heq] at he
      exact he.elim
  · by_cases heq : A.cycleOfVertex (A.second.endpointEquiv (e, 0)) = q
    · rw [if_pos heq] at he
      by_cases hfr : A.cycleOfVertex (A.second.endpointEquiv (f, 0)) = r
      · rw [if_pos hfr] at hf
        by_cases hef : e = f
        · subst f
          exact hqr (heq.symm.trans hfr)
        · exact Set.disjoint_left.mp (H.second_pairwise hef) he hf
      · rw [if_neg hfr] at hf
        exact hf.elim
    · rw [if_neg heq] at he
      exact he.elim

end ClosedArcIncidenceData

end FiniteAlternatingEndpointSystem

namespace FiniteSuperellipsoidBarrierGraph

universe idx

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type idx} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace TruncatedSphereAlternatingCycles

variable
  (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
  (cutOrder : CutCircleTransverseCyclicOrderFamily G)

variable [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem seam_of_mem_outer_and_cut
    {x : R3} {g : outerOrder.GlobalLowerOuterGap} {h : cutOrder.GlobalInwardGap}
    (hxOuter : x ∈ Set.range fun u ↦
      ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3))
    (hxCut : x ∈ Set.range fun u ↦
      ((cutOrder.globalInwardExcursionPath h u : transportedTorus Phi) : R3)) :
    x ∈ superellipsoidTorusSeam Phi frame c R d := by
  obtain ⟨u, rfl⟩ := hxOuter
  obtain ⟨v, hxv⟩ := hxCut
  have houterCircle := outerOrder.gapPath_mem_outerCircle
    (outerOrder.lowerGapAsGlobalOuterGap g) u
  have houterSection := G.outer.circle_mem_section g.1.1 houterCircle
  have houterSection' :
      ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) ∈
        superellipsoidOuterTorusSection Phi frame c R := by
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.globalLowerOuterPath] using
      houterSection
  have hcutCircle := cutOrder.globalInwardExcursionPath_mem_cutCircle h v
  have hcutSection := G.cut.circle_mem_section h.1.1 hcutCircle
  have hcutSection' :
      ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) ∈
        superellipsoidCutTorusSection Phi frame d := by
    change (fun w ↦ ((outerOrder.globalLowerOuterPath g w : transportedTorus Phi) : R3)) u ∈ _
    rw [← hxv]
    exact hcutSection
  exact ⟨houterSection', hcutSection'.2⟩

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem seam_of_mem_upper_outer_and_cut
    {x : R3} {g : outerOrder.GlobalUpperOuterGap} {h : cutOrder.GlobalInwardGap}
    (hxOuter : x ∈ Set.range fun u ↦
      ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3))
    (hxCut : x ∈ Set.range fun u ↦
      ((cutOrder.globalInwardExcursionPath h u : transportedTorus Phi) : R3)) :
    x ∈ superellipsoidTorusSeam Phi frame c R d := by
  obtain ⟨u, rfl⟩ := hxOuter
  obtain ⟨v, hxv⟩ := hxCut
  have houterCircle := outerOrder.gapPath_mem_outerCircle
    (outerOrder.upperGapAsGlobalOuterGap g) u
  have houterSection := G.outer.circle_mem_section g.1.1 houterCircle
  have houterSection' :
      ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) ∈
        superellipsoidOuterTorusSection Phi frame c R := by
    simpa only [OuterCircleTransverseHeightCyclicOrderFamily.globalUpperOuterPath] using
      houterSection
  have hcutCircle := cutOrder.globalInwardExcursionPath_mem_cutCircle h v
  have hcutSection := G.cut.circle_mem_section h.1.1 hcutCircle
  have hcutSection' :
      ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) ∈
        superellipsoidCutTorusSection Phi frame d := by
    change (fun w ↦ ((outerOrder.globalUpperOuterPath g w : transportedTorus Phi) : R3)) u ∈ _
    rw [← hxv]
    exact hcutSection
  exact ⟨houterSection', hcutSection'.2⟩

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem lower_mem_endpointSet_of_mem_seam
    (g : outerOrder.GlobalLowerOuterGap) {x : R3}
    (hxGap : x ∈ Set.range fun u ↦
      ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3))
    (hxSeam : x ∈ superellipsoidTorusSeam Phi frame c R d) :
    ∃ e : Fin 2, x = (outerOrder.globalLowerEndpointEquiv (g, e) : R3) := by
  let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
  let ge := outerOrder.globalLowerEndpointEquiv.symm p
  have hp : outerOrder.globalLowerEndpointEquiv ge = p :=
    outerOrder.globalLowerEndpointEquiv.apply_symm_apply p
  have hxOther : x ∈ Set.range fun u ↦
      ((outerOrder.globalLowerOuterPath ge.1 u : transportedTorus Phi) : R3) := by
    refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval ge.2, ?_⟩
    exact (outerOrder.globalLowerEndpointEquiv_val_eq_path_endpoint ge.1 ge.2).symm.trans
      (congrArg Subtype.val hp)
  have hge : ge.1 = g := by
    by_contra hne
    exact Set.disjoint_left.mp
      (outerOrder.globalLowerOuterPath_ranges_pairwise_disjoint hne)
      hxOther hxGap
  refine ⟨ge.2, ?_⟩
  rw [← hge]
  exact (congrArg Subtype.val hp).symm

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem upper_mem_endpointSet_of_mem_seam
    (g : outerOrder.GlobalUpperOuterGap) {x : R3}
    (hxGap : x ∈ Set.range fun u ↦
      ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3))
    (hxSeam : x ∈ superellipsoidTorusSeam Phi frame c R d) :
    ∃ e : Fin 2, x = (outerOrder.globalUpperEndpointEquiv (g, e) : R3) := by
  let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
  let ge := outerOrder.globalUpperEndpointEquiv.symm p
  have hp : outerOrder.globalUpperEndpointEquiv ge = p :=
    outerOrder.globalUpperEndpointEquiv.apply_symm_apply p
  have hxOther : x ∈ Set.range fun u ↦
      ((outerOrder.globalUpperOuterPath ge.1 u : transportedTorus Phi) : R3) := by
    refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval ge.2, ?_⟩
    exact (outerOrder.globalUpperEndpointEquiv_val_eq_path_endpoint ge.1 ge.2).symm.trans
      (congrArg Subtype.val hp)
  have hge : ge.1 = g := by
    by_contra hne
    exact Set.disjoint_left.mp
      (outerOrder.globalUpperOuterPath_ranges_pairwise_disjoint hne)
      hxOther hxGap
  refine ⟨ge.2, ?_⟩
  rw [← hge]
  exact (congrArg Subtype.val hp).symm

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem cut_mem_endpointSet_of_mem_seam
    (g : cutOrder.GlobalInwardGap) {x : R3}
    (hxGap : x ∈ Set.range fun u ↦
      ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3))
    (hxSeam : x ∈ superellipsoidTorusSeam Phi frame c R d) :
    ∃ e : Fin 2, x = (cutOrder.globalEndpointEquiv (g, e) : R3) := by
  let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
  let ge := cutOrder.globalEndpointEquiv.symm p
  have hp : cutOrder.globalEndpointEquiv ge = p :=
    cutOrder.globalEndpointEquiv.apply_symm_apply p
  have hxOther : x ∈ Set.range fun u ↦
      ((cutOrder.globalInwardExcursionPath ge.1 u : transportedTorus Phi) : R3) := by
    refine ⟨CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval ge.2, ?_⟩
    exact (cutOrder.globalEndpointEquiv_val_eq_path_endpoint ge.1 ge.2).symm.trans
      (congrArg Subtype.val hp)
  have hge : ge.1 = g := by
    by_contra hne
    exact Set.disjoint_left.mp
      (cutOrder.globalInwardExcursionPath_ranges_pairwise_disjoint hne)
      hxOther hxGap
  refine ⟨ge.2, ?_⟩
  rw [← hge]
  exact (congrArg Subtype.val hp).symm

/-- A selected lower outer arc and a selected inward cutting arc meet exactly at their common
abstract seam endpoints. -/
theorem lowerOuterPath_inter_cutPath (g : outerOrder.GlobalLowerOuterGap)
    (h : cutOrder.GlobalInwardGap) :
    (Set.range fun u ↦
        ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3)) ∩
      (Set.range fun u ↦
        ((cutOrder.globalInwardExcursionPath h u : transportedTorus Phi) : R3)) =
      ((fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3)) ''
        ((lowerOuterPairing outerOrder).endpointSet g ∩
          (inwardCutPairing cutOrder).endpointSet h)) := by
  ext x
  constructor
  · rintro ⟨hxOuter, hxCut⟩
    have hxSeam := seam_of_mem_outer_and_cut outerOrder cutOrder hxOuter hxCut
    obtain ⟨e, he⟩ := lower_mem_endpointSet_of_mem_seam outerOrder g hxOuter hxSeam
    obtain ⟨f, hf⟩ := cut_mem_endpointSet_of_mem_seam cutOrder h hxCut hxSeam
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
    refine ⟨p, ⟨⟨e, ?_⟩, ⟨f, ?_⟩⟩, rfl⟩
    · apply Subtype.ext
      exact he.symm
    · apply Subtype.ext
      exact hf.symm
  · rintro ⟨p, ⟨⟨e, he⟩, ⟨f, hf⟩⟩, rfl⟩
    subst p
    have hp := congrArg Subtype.val hf
    constructor
    · refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e, ?_⟩
      exact (outerOrder.globalLowerEndpointEquiv_val_eq_path_endpoint g e).symm
    · refine ⟨CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval f, ?_⟩
      exact (cutOrder.globalEndpointEquiv_val_eq_path_endpoint h f).symm.trans hp

/-- A selected upper outer arc and a selected inward cutting arc meet exactly at their common
abstract seam endpoints. -/
theorem upperOuterPath_inter_cutPath (g : outerOrder.GlobalUpperOuterGap)
    (h : cutOrder.GlobalInwardGap) :
    (Set.range fun u ↦
        ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3)) ∩
      (Set.range fun u ↦
        ((cutOrder.globalInwardExcursionPath h u : transportedTorus Phi) : R3)) =
      ((fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3)) ''
        ((upperOuterPairing outerOrder).endpointSet g ∩
          (inwardCutPairing cutOrder).endpointSet h)) := by
  ext x
  constructor
  · rintro ⟨hxOuter, hxCut⟩
    have hxSeam := seam_of_mem_upper_outer_and_cut outerOrder cutOrder hxOuter hxCut
    obtain ⟨e, he⟩ := upper_mem_endpointSet_of_mem_seam outerOrder g hxOuter hxSeam
    obtain ⟨f, hf⟩ := cut_mem_endpointSet_of_mem_seam cutOrder h hxCut hxSeam
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hxSeam⟩
    refine ⟨p, ⟨⟨e, ?_⟩, ⟨f, ?_⟩⟩, rfl⟩
    · apply Subtype.ext
      exact he.symm
    · apply Subtype.ext
      exact hf.symm
  · rintro ⟨p, ⟨⟨e, he⟩, ⟨f, hf⟩⟩, rfl⟩
    subst p
    have hp := congrArg Subtype.val hf
    constructor
    · refine ⟨OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval e, ?_⟩
      exact (outerOrder.globalUpperEndpointEquiv_val_eq_path_endpoint g e).symm
    · refine ⟨CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval f, ?_⟩
      exact (cutOrder.globalEndpointEquiv_val_eq_path_endpoint h f).symm.trans hp

/-- The lower child's original endpoint-indexed paths satisfy the complete constituent-incidence
package. -/
theorem lowerClosedArcIncidenceData :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData (lowerSystem outerOrder cutOrder)
      (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3))
      (lowerOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder) where
  point_injective := fun _ _ h ↦ Subtype.ext h
  first_injective := by
    intro g
    change (lowerOuterPairing outerOrder).edge at g
    change Function.Injective ((lowerOuterEndpointPaths outerOrder).path g)
    rw [show ((lowerOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
      fun u ↦ (outerOrder.globalLowerOuterPath g u : R3) by
        funext u; exact lowerOuterEndpointPaths_path_apply outerOrder g u]
    exact outerOrder.globalLowerOuterPath_injective g
  second_injective := by
    intro g
    change (inwardCutPairing cutOrder).edge at g
    change Function.Injective ((inwardCutEndpointPaths cutOrder).path g)
    rw [show ((inwardCutEndpointPaths cutOrder).path g : unitInterval → R3) =
      fun u ↦ (cutOrder.globalInwardExcursionPath g u : R3) by
        funext u; exact inwardCutEndpointPaths_path_apply cutOrder g u]
    exact cutOrder.globalInwardExcursionPath_injective g
  first_pairwise := by
    intro g h hgh
    change (lowerOuterPairing outerOrder).edge at g h
    change Disjoint (Set.range ((lowerOuterEndpointPaths outerOrder).path g))
      (Set.range ((lowerOuterEndpointPaths outerOrder).path h))
    rw [show ((lowerOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
        fun u ↦ (outerOrder.globalLowerOuterPath g u : R3) by
          funext u; exact lowerOuterEndpointPaths_path_apply outerOrder g u,
      show ((lowerOuterEndpointPaths outerOrder).path h : unitInterval → R3) =
        fun u ↦ (outerOrder.globalLowerOuterPath h u : R3) by
          funext u; exact lowerOuterEndpointPaths_path_apply outerOrder h u]
    exact outerOrder.globalLowerOuterPath_ranges_pairwise_disjoint hgh
  second_pairwise := by
    intro g h hgh
    change (inwardCutPairing cutOrder).edge at g h
    change Disjoint (Set.range ((inwardCutEndpointPaths cutOrder).path g))
      (Set.range ((inwardCutEndpointPaths cutOrder).path h))
    rw [show ((inwardCutEndpointPaths cutOrder).path g : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath g u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder g u,
      show ((inwardCutEndpointPaths cutOrder).path h : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath h u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder h u]
    exact cutOrder.globalInwardExcursionPath_ranges_pairwise_disjoint hgh
  cross_intersection := by
    intro g h
    change (lowerOuterPairing outerOrder).edge at g
    change (inwardCutPairing cutOrder).edge at h
    change Set.range ((lowerOuterEndpointPaths outerOrder).path g) ∩
      Set.range ((inwardCutEndpointPaths cutOrder).path h) =
        (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3)) ''
          ((lowerOuterPairing outerOrder).endpointSet g ∩
            (inwardCutPairing cutOrder).endpointSet h)
    rw [show ((lowerOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
        fun u ↦ (outerOrder.globalLowerOuterPath g u : R3) by
          funext u; exact lowerOuterEndpointPaths_path_apply outerOrder g u,
      show ((inwardCutEndpointPaths cutOrder).path h : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath h u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder h u]
    exact lowerOuterPath_inter_cutPath outerOrder cutOrder g h

/-- The upper child's original endpoint-indexed paths satisfy the complete constituent-incidence
package. -/
theorem upperClosedArcIncidenceData :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData (upperSystem outerOrder cutOrder)
      (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3))
      (upperOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder) where
  point_injective := fun _ _ h ↦ Subtype.ext h
  first_injective := by
    intro g
    change (upperOuterPairing outerOrder).edge at g
    change Function.Injective ((upperOuterEndpointPaths outerOrder).path g)
    rw [show ((upperOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
      fun u ↦ (outerOrder.globalUpperOuterPath g u : R3) by
        funext u; exact upperOuterEndpointPaths_path_apply outerOrder g u]
    exact outerOrder.globalUpperOuterPath_injective g
  second_injective := by
    intro g
    change (inwardCutPairing cutOrder).edge at g
    change Function.Injective ((inwardCutEndpointPaths cutOrder).path g)
    rw [show ((inwardCutEndpointPaths cutOrder).path g : unitInterval → R3) =
      fun u ↦ (cutOrder.globalInwardExcursionPath g u : R3) by
        funext u; exact inwardCutEndpointPaths_path_apply cutOrder g u]
    exact cutOrder.globalInwardExcursionPath_injective g
  first_pairwise := by
    intro g h hgh
    change (upperOuterPairing outerOrder).edge at g h
    change Disjoint (Set.range ((upperOuterEndpointPaths outerOrder).path g))
      (Set.range ((upperOuterEndpointPaths outerOrder).path h))
    rw [show ((upperOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
        fun u ↦ (outerOrder.globalUpperOuterPath g u : R3) by
          funext u; exact upperOuterEndpointPaths_path_apply outerOrder g u,
      show ((upperOuterEndpointPaths outerOrder).path h : unitInterval → R3) =
        fun u ↦ (outerOrder.globalUpperOuterPath h u : R3) by
          funext u; exact upperOuterEndpointPaths_path_apply outerOrder h u]
    exact outerOrder.globalUpperOuterPath_ranges_pairwise_disjoint hgh
  second_pairwise := by
    intro g h hgh
    change (inwardCutPairing cutOrder).edge at g h
    change Disjoint (Set.range ((inwardCutEndpointPaths cutOrder).path g))
      (Set.range ((inwardCutEndpointPaths cutOrder).path h))
    rw [show ((inwardCutEndpointPaths cutOrder).path g : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath g u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder g u,
      show ((inwardCutEndpointPaths cutOrder).path h : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath h u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder h u]
    exact cutOrder.globalInwardExcursionPath_ranges_pairwise_disjoint hgh
  cross_intersection := by
    intro g h
    change (upperOuterPairing outerOrder).edge at g
    change (inwardCutPairing cutOrder).edge at h
    change Set.range ((upperOuterEndpointPaths outerOrder).path g) ∩
      Set.range ((inwardCutEndpointPaths cutOrder).path h) =
        (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3)) ''
          ((upperOuterPairing outerOrder).endpointSet g ∩
            (inwardCutPairing cutOrder).endpointSet h)
    rw [show ((upperOuterEndpointPaths outerOrder).path g : unitInterval → R3) =
        fun u ↦ (outerOrder.globalUpperOuterPath g u : R3) by
          funext u; exact upperOuterEndpointPaths_path_apply outerOrder g u,
      show ((inwardCutEndpointPaths cutOrder).path h : unitInterval → R3) =
        fun u ↦ (cutOrder.globalInwardExcursionPath h u : R3) by
          funext u; exact inwardCutEndpointPaths_path_apply cutOrder h u]
    exact upperOuterPath_inter_cutPath outerOrder cutOrder g h

private theorem lower_cycleEdgeCarrier_eq (q : LowerCycleIndex outerOrder cutOrder) :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
      (lowerSystem outerOrder cutOrder)
      (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3))
      (lowerOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder) q =
      lowerCycleCarrier outerOrder cutOrder q := by
  classical
  unfold FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
    lowerCycleCarrier
  apply congrArg₂ (· ∪ ·)
  · apply iUnion_congr
    intro g
    change (if lowerCycleOfOuterGap outerOrder cutOrder g = q then
        Set.range ((lowerOuterEndpointPaths outerOrder).path g) else ∅) = _
    by_cases hg : lowerCycleOfOuterGap outerOrder cutOrder g = q
    · rw [if_pos hg, if_pos hg]
      apply congrArg (fun f : unitInterval → R3 ↦ Set.range f)
      funext u
      exact lowerOuterEndpointPaths_path_apply outerOrder g u
    · rw [if_neg hg, if_neg hg]
  · apply iUnion_congr
    intro g
    change (if lowerCycleOfCutGap outerOrder cutOrder g = q then
        Set.range ((inwardCutEndpointPaths cutOrder).path g) else ∅) = _
    by_cases hg : lowerCycleOfCutGap outerOrder cutOrder g = q
    · rw [if_pos hg, if_pos hg]
      apply congrArg (fun f : unitInterval → R3 ↦ Set.range f)
      funext u
      exact inwardCutEndpointPaths_path_apply cutOrder g u
    · rw [if_neg hg, if_neg hg]

private theorem upper_cycleEdgeCarrier_eq (q : UpperCycleIndex outerOrder cutOrder) :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
      (upperSystem outerOrder cutOrder)
      (fun p : SuperellipsoidSeamVertex Phi frame c R d ↦ (p : R3))
      (upperOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder) q =
      upperCycleCarrier outerOrder cutOrder q := by
  classical
  unfold FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
    upperCycleCarrier
  apply congrArg₂ (· ∪ ·)
  · apply iUnion_congr
    intro g
    change (if upperCycleOfOuterGap outerOrder cutOrder g = q then
        Set.range ((upperOuterEndpointPaths outerOrder).path g) else ∅) = _
    by_cases hg : upperCycleOfOuterGap outerOrder cutOrder g = q
    · rw [if_pos hg, if_pos hg]
      apply congrArg (fun f : unitInterval → R3 ↦ Set.range f)
      funext u
      exact upperOuterEndpointPaths_path_apply outerOrder g u
    · rw [if_neg hg, if_neg hg]
  · apply iUnion_congr
    intro g
    change (if upperCycleOfCutGap outerOrder cutOrder g = q then
        Set.range ((inwardCutEndpointPaths cutOrder).path g) else ∅) = _
    by_cases hg : upperCycleOfCutGap outerOrder cutOrder g = q
    · rw [if_pos hg, if_pos hg]
      apply congrArg (fun f : unitInterval → R3 ↦ Set.range f)
      funext u
      exact inwardCutEndpointPaths_path_apply cutOrder g u
    · rw [if_neg hg, if_neg hg]

/-- Exact carrier of each canonical lower quotient-cycle circle. -/
theorem lower_circleMap_range (q : LowerCycleIndex outerOrder cutOrder) :
    Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) =
      lowerCycleCarrier outerOrder cutOrder q := by
  change Set.range
    ((FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (lowerOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder)).circleMap q) = _
  rw [(lowerClosedArcIncidenceData outerOrder cutOrder).range_circleMap_eq_cycleEdgeCarrier,
    lower_cycleEdgeCarrier_eq outerOrder cutOrder]

/-- Exact carrier of each canonical upper quotient-cycle circle. -/
theorem upper_circleMap_range (q : UpperCycleIndex outerOrder cutOrder) :
    Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) =
      upperCycleCarrier outerOrder cutOrder q := by
  change Set.range
    ((FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (upperOuterEndpointPaths outerOrder) (inwardCutEndpointPaths cutOrder)).circleMap q) = _
  rw [(upperClosedArcIncidenceData outerOrder cutOrder).range_circleMap_eq_cycleEdgeCarrier,
    upper_cycleEdgeCarrier_eq outerOrder cutOrder]

/-- All global concatenation fields follow from the exact closed-arc incidence packages. -/
theorem canonicalActiveCycleConcatenationData :
    ActiveCycleConcatenationData outerOrder cutOrder where
  lower_twoArc := (lowerClosedArcIncidenceData outerOrder cutOrder).twoArcData
  lower_pairwise := by
    intro q r hqr
    exact (lowerClosedArcIncidenceData outerOrder cutOrder).circleMap_ranges_disjoint hqr
  lower_range := lower_circleMap_range outerOrder cutOrder
  upper_twoArc := (upperClosedArcIncidenceData outerOrder cutOrder).twoArcData
  upper_pairwise := by
    intro q r hqr
    exact (upperClosedArcIncidenceData outerOrder cutOrder).circleMap_ranges_disjoint hqr
  upper_range := upper_circleMap_range outerOrder cutOrder

/-- The only additional input needed to promote the canonical quotient cycles to active child
intersection circles is the explicit ambient seam germ. -/
noncomputable def canonicalActiveCycleRealizationData
    (localGerm : ActiveCycleLocalGermData outerOrder cutOrder) :
    ActiveCycleRealizationData outerOrder cutOrder :=
  ActiveCycleRealizationData.ofCanonicalConcatenations
    outerOrder cutOrder (canonicalActiveCycleConcatenationData outerOrder cutOrder) localGerm

end TruncatedSphereAlternatingCycles

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
