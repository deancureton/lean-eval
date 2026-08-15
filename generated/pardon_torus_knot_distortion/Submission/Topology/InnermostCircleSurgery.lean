import Submission.Topology.GeneralCompression

/-!
# Abstract innermost-circle surgery

This module records the exact geometry required by the innermost-circle argument used in
Pardon's Lemma 2.5.  It deliberately does not assert that cutting and regluing disks preserves
embeddedness: every surgery result, its embedding, and the decrease of the finite intersection
system are fields of an explicit contract.

Once that contract is supplied, termination is purely finite.  Repeated replacement of an
inessential intersection circle strictly decreases the number of remaining circles, so after a
finite sequence one obtains an embedded essential-boundary disk whose open interior misses the
transported torus.  The final disk converts directly to `GeneralCompressingDiskWitness`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-! ## Geometric input data -/

/-- An embedded disk in `R3` with a fixed real-periodic parametrization of its boundary. -/
structure BoundaryParametrizedEmbeddedDiskInR3 where
  disk : ClosedUnitDisk → R3
  isEmbedding : IsEmbedding disk
  boundaryCurve : ℝ → R3
  continuous_boundaryCurve : Continuous boundaryCurve
  periodic_boundaryCurve : Function.Periodic boundaryCurve (2 * Real.pi)
  boundary : ∀ t, disk (unitDiskBoundary t) = boundaryCurve t

namespace BoundaryParametrizedEmbeddedDiskInR3

theorem continuous (D : BoundaryParametrizedEmbeddedDiskInR3) : Continuous D.disk :=
  D.isEmbedding.continuous

end BoundaryParametrizedEmbeddedDiskInR3

/-- A parametrized embedded intersection circle on the transported torus, with its winding data
kept on the real-periodic parametrization. -/
structure EmbeddedTorusIntersectionCircle (Phi : AmbientIsotopy) where
  circle : Circle → R3
  isEmbedding : IsEmbedding circle
  windingLoop : TransportedWindingLoop Phi Set.univ
  parametrization : ∀ t, circle (Circle.exp t) = windingLoop.curve t

namespace EmbeddedTorusIntersectionCircle

variable {Phi : AmbientIsotopy}

def Essential (C : EmbeddedTorusIntersectionCircle Phi) : Prop :=
  C.windingLoop.windingPair ≠ (0, 0)

theorem range_subset_transportedTorus (C : EmbeddedTorusIntersectionCircle Phi) :
    Set.range C.circle ⊆ transportedTorus Phi := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  rw [← ht, C.parametrization]
  exact (C.windingLoop.curve t).property

end EmbeddedTorusIntersectionCircle

/-- A finite, pairwise-disjoint circle description of the intersection of a plane disk with the
transported torus.  Exactness and all embedding assertions are geometric input, not conclusions
of the finite argument below. -/
structure FinitePlaneDiskTorusCircleSystem
    (Phi : AmbientIsotopy) (ι : Type*) [DecidableEq ι] where
  plane : Set R3
  planeDisk : BoundaryParametrizedEmbeddedDiskInR3
  disk_mem_plane : Set.range planeDisk.disk ⊆ plane
  circles : Finset ι
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  circle_mem_disk : ∀ i ∈ circles, Set.range (circle i).circle ⊆ Set.range planeDisk.disk
  pairwise_disjoint : ∀ {i}, i ∈ circles → ∀ {j}, j ∈ circles → i ≠ j →
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  intersection_exact : Set.range planeDisk.disk ∩ transportedTorus Phi =
    ⋃ i ∈ circles, Set.range (circle i).circle
  has_essential : ∃ i ∈ circles, (circle i).Essential
  inside : ι → ι → Prop
  depth : ι → ℕ
  inside_depth_lt : ∀ {i j}, i ∈ circles → j ∈ circles → inside i j → depth i < depth j

namespace FinitePlaneDiskTorusCircleSystem

variable {Phi : AmbientIsotopy} {ι : Type*} [DecidableEq ι]

noncomputable def essentialCircles (S : FinitePlaneDiskTorusCircleSystem Phi ι) : Finset ι := by
  classical
  exact S.circles.filter fun i ↦ (S.circle i).Essential

def InnermostEssential (S : FinitePlaneDiskTorusCircleSystem Phi ι) (i : ι) : Prop :=
  i ∈ S.circles ∧ (S.circle i).Essential ∧
    ∀ j ∈ S.circles, S.inside j i → ¬ (S.circle j).Essential

/-- A finite nesting system with an essential circle has an innermost essential circle. -/
theorem exists_innermostEssential (S : FinitePlaneDiskTorusCircleSystem Phi ι) :
    ∃ i, S.InnermostEssential i := by
  classical
  have hnonempty : S.essentialCircles.Nonempty := by
    obtain ⟨i, hi, he⟩ := S.has_essential
    exact ⟨i, by simp [essentialCircles, hi, he]⟩
  obtain ⟨i, hi, hmin⟩ := S.essentialCircles.exists_min_image S.depth hnonempty
  have hi' : i ∈ S.circles ∧ (S.circle i).Essential := by
    simpa only [essentialCircles, Finset.mem_filter] using hi
  refine ⟨i, hi'.1, hi'.2, ?_⟩
  intro j hj hji hej
  have hjEssential : j ∈ S.essentialCircles := by
    simp only [essentialCircles, Finset.mem_filter]
    exact ⟨hj, hej⟩
  exact (not_lt_of_ge (hmin j hjEssential)) (S.inside_depth_lt hj hi'.1 hji)

end FinitePlaneDiskTorusCircleSystem

/-! ## Essential-boundary disks and compression -/

/-- An embedded disk whose boundary is an essential loop on the transported torus.  Its interior
may still meet the torus. -/
structure EssentialBoundaryEmbeddedDisk (Phi : AmbientIsotopy) where
  boundaryLoop : TransportedWindingLoop Phi Set.univ
  disk : ClosedUnitDisk → R3
  isEmbedding : IsEmbedding disk
  boundary : ∀ t, disk (unitDiskBoundary t) = boundaryLoop.curve t
  essential : boundaryLoop.windingPair ≠ (0, 0)

namespace EssentialBoundaryEmbeddedDisk

variable {Phi : AmbientIsotopy}

def InteriorDisjoint (D : EssentialBoundaryEmbeddedDisk Phi) : Prop :=
  ∀ z : ClosedUnitDisk, ‖(z : ℂ)‖ < 1 → D.disk z ∉ transportedTorus Phi

theorem continuous (D : EssentialBoundaryEmbeddedDisk Phi) : Continuous D.disk :=
  D.isEmbedding.continuous

/-- An essential-boundary disk with disjoint open interior is exactly the general compression
witness consumed by the later distortion argument. -/
def toGeneralCompressingDiskWitness (D : EssentialBoundaryEmbeddedDisk Phi)
    (hdisjoint : D.InteriorDisjoint) : GeneralCompressingDiskWitness Phi where
  boundaryLoop := D.boundaryLoop
  disk := D.disk
  isEmbedding := D.isEmbedding
  boundary := D.boundary
  interior_disjoint := hdisjoint
  essential := D.essential

end EssentialBoundaryEmbeddedDisk

/-! ## The surgery contract -/

/-- Honest finite innermost-circle surgery data.

`State` contains the explicitly constructed embedded disks.  A `Step` is an explicitly supplied
replacement surgery.  Its fields say that it removes an inessential remaining circle, introduces
no circle outside the previous finite system, and strictly lowers cardinality.  The crucial
geometric existence assertion `surgery_of_not_disjoint` is a field rather than a theorem. -/
structure FiniteInnermostCircleSurgeryContract
    (Phi : AmbientIsotopy) (ι : Type*) [DecidableEq ι]
    (system : FinitePlaneDiskTorusCircleSystem Phi ι) where
  State : Type
  stateDisk : State → EssentialBoundaryEmbeddedDisk Phi
  remaining : State → Finset ι
  initial : ∀ i, system.InnermostEssential i → State
  initial_boundary : ∀ i hi,
    (stateDisk (initial i hi)).boundaryLoop = (system.circle i).windingLoop
  initial_remaining_subset : ∀ i hi, remaining (initial i hi) ⊆ system.circles
  initial_remaining_inside : ∀ i hi j, j ∈ remaining (initial i hi) → system.inside j i
  Step : State → State → Prop
  step_removes_inessential : ∀ {s t}, Step s t →
    ∃ i ∈ remaining s, ¬ (system.circle i).Essential ∧ i ∉ remaining t
  step_remaining_subset : ∀ {s t}, Step s t → remaining t ⊆ remaining s
  step_card_lt : ∀ {s t}, Step s t → (remaining t).card < (remaining s).card
  surgery_of_not_disjoint : ∀ s, ¬ (stateDisk s).InteriorDisjoint →
    ∃ t, Step s t

namespace FiniteInnermostCircleSurgeryContract

variable {Phi : AmbientIsotopy} {ι : Type*} [DecidableEq ι]
  {system : FinitePlaneDiskTorusCircleSystem Phi ι}

def Reachable (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    (s t : C.State) : Prop :=
  Relation.ReflTransGen C.Step s t

theorem reachable_refl (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    (s : C.State) : C.Reachable s s :=
  Relation.ReflTransGen.refl

theorem reachable_tail (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    {s t u : C.State} (hst : C.Reachable s t) (htu : C.Step t u) : C.Reachable s u :=
  Relation.ReflTransGen.tail hst htu

/-- Remaining intersection labels can only decrease along a finite surgery sequence. -/
theorem remaining_subset_of_reachable
    (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    {s t : C.State} (hst : C.Reachable s t) : C.remaining t ⊆ C.remaining s := by
  induction hst with
  | refl => exact Finset.Subset.rfl
  | tail hreach hstep ih => exact (C.step_remaining_subset hstep).trans ih

/-- In particular, no surgery introduces a label outside the initial finite circle system. -/
theorem remaining_subset_system_of_initial_reachable
    (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    {i : ι} {hi : system.InnermostEssential i}
    {t : C.State} (ht : C.Reachable (C.initial i hi) t) :
    C.remaining t ⊆ system.circles :=
  (C.remaining_subset_of_reachable ht).trans (C.initial_remaining_subset i hi)

/-- Every circle remaining below the selected innermost essential circle is inessential, and
this remains true throughout the nested surgery sequence. -/
theorem remaining_inessential_of_initial_reachable
    (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    {i : ι} {hi : system.InnermostEssential i}
    {t : C.State} (ht : C.Reachable (C.initial i hi) t)
    {j : ι} (hj : j ∈ C.remaining t) : ¬ (system.circle j).Essential := by
  have hjInitial : j ∈ C.remaining (C.initial i hi) :=
    C.remaining_subset_of_reachable ht hj
  exact hi.2.2 j (C.initial_remaining_subset i hi hjInitial)
    (C.initial_remaining_inside i hi j hjInitial)

/-- Strict decrease makes the supplied surgery relation terminate at an interior-disjoint disk. -/
theorem exists_reachable_interiorDisjoint
    (C : FiniteInnermostCircleSurgeryContract Phi ι system) (s : C.State) :
    ∃ t, C.Reachable s t ∧ (C.stateDisk t).InteriorDisjoint := by
  induction hcard : (C.remaining s).card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hfinal : (C.stateDisk s).InteriorDisjoint
      · exact ⟨s, C.reachable_refl s, hfinal⟩
      · obtain ⟨t, hstep⟩ := C.surgery_of_not_disjoint s hfinal
        obtain ⟨u, htu, hfinalu⟩ := ih (C.remaining t).card (by
          calc
            (C.remaining t).card < (C.remaining s).card := C.step_card_lt hstep
            _ = n := hcard) t rfl
        exact ⟨u, Relation.ReflTransGen.head hstep htu, hfinalu⟩

/-- Starting from a chosen essential intersection circle, either its disk is already a
compressing disk or at least one supplied surgery followed by a finite sequence produces one. -/
theorem already_or_nonempty_surgery_sequence
    (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    (i : ι) (hi : system.InnermostEssential i) :
    (C.stateDisk (C.initial i hi)).InteriorDisjoint ∨
      ∃ s t, C.Step (C.initial i hi) s ∧ C.Reachable s t ∧
        (C.stateDisk t).InteriorDisjoint := by
  by_cases hfinal : (C.stateDisk (C.initial i hi)).InteriorDisjoint
  · exact Or.inl hfinal
  · obtain ⟨s, hstep⟩ := C.surgery_of_not_disjoint _ hfinal
    obtain ⟨t, hreach, htfinal⟩ := C.exists_reachable_interiorDisjoint s
    exact Or.inr ⟨s, t, hstep, hreach, htfinal⟩

/-- System-level formulation of the innermost-circle alternative. -/
theorem exists_innermost_already_or_surgery_sequence
    (C : FiniteInnermostCircleSurgeryContract Phi ι system) :
    ∃ i, ∃ hi : system.InnermostEssential i,
      (C.stateDisk (C.initial i hi)).InteriorDisjoint ∨
        ∃ s t, C.Step (C.initial i hi) s ∧ C.Reachable s t ∧
          (C.stateDisk t).InteriorDisjoint := by
  obtain ⟨i, hi⟩ := system.exists_innermostEssential
  exact ⟨i, hi, C.already_or_nonempty_surgery_sequence i hi⟩

/-- The finite circle system and surgery contract produce a general compressing disk. -/
theorem exists_generalCompressingDiskWitness
    (C : FiniteInnermostCircleSurgeryContract Phi ι system) :
    Nonempty (GeneralCompressingDiskWitness Phi) := by
  obtain ⟨i, hi⟩ := system.exists_innermostEssential
  obtain ⟨t, _hreach, hdisjoint⟩ :=
    C.exists_reachable_interiorDisjoint (C.initial i hi)
  exact ⟨(C.stateDisk t).toGeneralCompressingDiskWitness hdisjoint⟩

end FiniteInnermostCircleSurgeryContract

end Submission.Topology
