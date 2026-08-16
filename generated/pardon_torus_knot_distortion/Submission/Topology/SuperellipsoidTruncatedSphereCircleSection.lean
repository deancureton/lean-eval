import Submission.Topology.SuperellipsoidConvexSpheres
import Submission.Topology.SuperellipsoidAnalyticSphere
import Submission.Topology.SuperellipsoidOuterCircleSection

/-!
# Circle sections of the two truncated superellipsoid spheres

The frontier of a closed lower or upper truncation has two pages: the corresponding half of the
outer superellipsoid and the closed cutting disk.  Intersecting with the transported torus gives
two finite families of regular circle branches meeting at the finite transverse seam.  At each
seam point the selected outer and cutting half-branches form a `V`, so they must be glued into one
local one-manifold branch.

This file proves the frontier and branch-carrier equalities and isolates the exact remaining
gluing contract.  The contract supplies continuous injective cyclic gluings and verifies the two
branch types separately.  It does not assume a `FiniteEmbeddedTorusCircleSection` or its final
section equality.  Those are derived below, including the winding-loop data.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {R d : ℝ}

/-! ## The two analytic endpoint sections -/

/-- Torus intersection of the lower truncated convex sphere. -/
def lowerTruncatedSuperellipsoidTorusSection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d : ℝ) : Set R3 :=
  transportedTorus Phi ∩
    frontier (closedLowerSuperellipsoidTruncation frame c R d)

/-- Torus intersection of the upper truncated convex sphere. -/
def upperTruncatedSuperellipsoidTorusSection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d : ℝ) : Set R3 :=
  transportedTorus Phi ∩
    frontier (closedUpperSuperellipsoidTruncation frame c R d)

/-- For two closed sets, the usual frontier-of-intersection inclusion is an equality. -/
theorem frontier_inter_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) :
    frontier (s ∩ t) = frontier s ∩ t ∪ s ∩ frontier t := by
  apply Set.Subset.antisymm
  · simpa only [hs.closure_eq, ht.closure_eq] using frontier_inter_subset s t
  · rintro x (hx | hx)
    · have hxs : x ∈ s := hs.frontier_subset hx.1
      have hxst : x ∈ s ∩ t := ⟨hxs, hx.2⟩
      apply (mem_frontier_iff_notMem_interior hxst).2
      intro hxInterior
      exact ((mem_frontier_iff_notMem_interior hxs).1 hx.1)
        (interior_mono inter_subset_left hxInterior)
    · have hxt : x ∈ t := ht.frontier_subset hx.2
      have hxst : x ∈ s ∩ t := ⟨hx.1, hxt⟩
      apply (mem_frontier_iff_notMem_interior hxst).2
      intro hxInterior
      exact ((mem_frontier_iff_notMem_interior hxt).1 hx.2)
        (interior_mono inter_subset_right hxInterior)

/-- A coordinate projection from `R3` onto the line is surjective. -/
theorem coordinateCLM_surjective (i : Fin 3) :
    Function.Surjective (coordinateCLM i) := by
  intro y
  refine ⟨PiLp.single 2 i y, ?_⟩
  simp [coordinateCLM_apply]

/-- The frontier of the lower closed halfspace is the cutting plane. -/
theorem frontier_lowerClosedHalfspace_eq_coordinateCuttingPlane
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    frontier (lowerClosedHalfspace frame d) = coordinateCuttingPlane frame d := by
  change frontier ((coordinateCLM (frame 2)) ⁻¹' Set.Iic d) =
    (coordinateCLM (frame 2)) ⁻¹' {d}
  rw [(coordinateCLM (frame 2)).frontier_preimage
    (coordinateCLM_surjective (frame 2)), frontier_Iic]

/-- The frontier of the upper closed halfspace is the cutting plane. -/
theorem frontier_upperClosedHalfspace_eq_coordinateCuttingPlane
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    frontier (upperClosedHalfspace frame d) = coordinateCuttingPlane frame d := by
  change frontier ((coordinateCLM (frame 2)) ⁻¹' Set.Ici d) =
    (coordinateCLM (frame 2)) ⁻¹' {d}
  rw [(coordinateCLM (frame 2)).frontier_preimage
    (coordinateCLM_surjective (frame 2)), frontier_Ici]

/-- The lower truncated frontier is exactly its outer page together with its cutting page. -/
theorem frontier_closedLowerSuperellipsoidTruncation_eq
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) (d : ℝ) :
    frontier (closedLowerSuperellipsoidTruncation frame c R d) =
      superellipsoidBoundary frame c R ∩ lowerClosedHalfspace frame d ∪
        closedSuperellipsoidBody frame c R ∩ coordinateCuttingPlane frame d := by
  change frontier
      (closedSuperellipsoidBody frame c R ∩ lowerClosedHalfspace frame d) = _
  rw [frontier_inter_eq_of_isClosed
      (isClosed_closedSuperellipsoidBody_convexSphere frame c R)
      (isClosed_lowerClosedHalfspace frame d),
    frontier_closedSuperellipsoidBody_eq_boundary frame c hR,
    frontier_lowerClosedHalfspace_eq_coordinateCuttingPlane]

/-- The upper truncated frontier is exactly its outer page together with its cutting page. -/
theorem frontier_closedUpperSuperellipsoidTruncation_eq
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) (d : ℝ) :
    frontier (closedUpperSuperellipsoidTruncation frame c R d) =
      superellipsoidBoundary frame c R ∩ upperClosedHalfspace frame d ∪
        closedSuperellipsoidBody frame c R ∩ coordinateCuttingPlane frame d := by
  change frontier
      (closedSuperellipsoidBody frame c R ∩ upperClosedHalfspace frame d) = _
  rw [frontier_inter_eq_of_isClosed
      (isClosed_closedSuperellipsoidBody_convexSphere frame c R)
      (isClosed_upperClosedHalfspace frame d),
    frontier_closedSuperellipsoidBody_eq_boundary frame c hR,
    frontier_upperClosedHalfspace_eq_coordinateCuttingPlane]

/-- Analytic `V`-carrier of the lower truncated endpoint. -/
def lowerTruncatedSeamVCarrier
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d : ℝ) : Set R3 :=
  (superellipsoidOuterTorusSection Phi frame c R ∩ lowerClosedHalfspace frame d) ∪
    (superellipsoidCutTorusSection Phi frame d ∩
      closedSuperellipsoidBody frame c R)

/-- Analytic `V`-carrier of the upper truncated endpoint. -/
def upperTruncatedSeamVCarrier
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d : ℝ) : Set R3 :=
  (superellipsoidOuterTorusSection Phi frame c R ∩ upperClosedHalfspace frame d) ∪
    (superellipsoidCutTorusSection Phi frame d ∩
      closedSuperellipsoidBody frame c R)

/-- The lower endpoint section is its outer/cut `V`-carrier. -/
theorem lowerTruncatedSuperellipsoidTorusSection_eq_seamVCarrier
    (hR : 0 < R) :
    lowerTruncatedSuperellipsoidTorusSection Phi frame c R d =
      lowerTruncatedSeamVCarrier Phi frame c R d := by
  rw [lowerTruncatedSuperellipsoidTorusSection,
    frontier_closedLowerSuperellipsoidTruncation_eq frame c hR d]
  ext x
  simp only [lowerTruncatedSeamVCarrier, superellipsoidOuterTorusSection,
    superellipsoidCutTorusSection, Set.mem_inter_iff, Set.mem_union]
  tauto

/-- The upper endpoint section is its outer/cut `V`-carrier. -/
theorem upperTruncatedSuperellipsoidTorusSection_eq_seamVCarrier
    (hR : 0 < R) :
    upperTruncatedSuperellipsoidTorusSection Phi frame c R d =
      upperTruncatedSeamVCarrier Phi frame c R d := by
  rw [upperTruncatedSuperellipsoidTorusSection,
    frontier_closedUpperSuperellipsoidTruncation_eq frame c hR d]
  ext x
  simp only [upperTruncatedSeamVCarrier, superellipsoidOuterTorusSection,
    superellipsoidCutTorusSection, Set.mem_inter_iff, Set.mem_union]
  tauto

/-! ## The exact finite `V`-gluing boundary -/

/-- Explicit cyclic gluing of the outer and cutting half-branches at the endpoint seams.

The regular section families already supply every complete outer and cut circle.  These fields
ask only for the result of cutting those circles at the seam and pairing the two selected local
ports into continuous injective cyclic maps.  Coverage is stated separately on outer and cut
branches, while `lower_mem` and `upper_mem` rule out adding unrelated arcs. -/
structure TruncatedSphereSeamVGluingData
    {outerIndex cutIndex lowerIndex upperIndex : Type*}
    [Fintype outerIndex] [Fintype cutIndex]
    [Fintype lowerIndex] [Fintype upperIndex]
    (outer : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R) outerIndex)
    (cut : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame d) cutIndex) where
  lowerCurve : lowerIndex → Circle → R3
  lower_continuous : ∀ k, Continuous (lowerCurve k)
  lower_injective : ∀ k, Function.Injective (lowerCurve k)
  lower_mem_torus : ∀ k z, lowerCurve k z ∈ transportedTorus Phi
  lower_pairwise : Pairwise fun k l ↦
    Disjoint (Set.range (lowerCurve k)) (Set.range (lowerCurve l))
  lower_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ k z i j U, IsOpen U ∧ p ∈ U ∧ lowerCurve k z = p ∧
      Set.range (lowerCurve k) ∩ U =
        ((Set.range (outer.circle i).circle ∩ lowerClosedHalfspace frame d) ∪
          (Set.range (cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U
  lower_mem : ∀ k, Set.range (lowerCurve k) ⊆
    lowerTruncatedSeamVCarrier Phi frame c R d
  lower_outer_covered : ∀ i,
    Set.range (outer.circle i).circle ∩ lowerClosedHalfspace frame d ⊆
      ⋃ k, Set.range (lowerCurve k)
  lower_cut_covered : ∀ j,
    Set.range (cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (lowerCurve k)
  upperCurve : upperIndex → Circle → R3
  upper_continuous : ∀ k, Continuous (upperCurve k)
  upper_injective : ∀ k, Function.Injective (upperCurve k)
  upper_mem_torus : ∀ k z, upperCurve k z ∈ transportedTorus Phi
  upper_pairwise : Pairwise fun k l ↦
    Disjoint (Set.range (upperCurve k)) (Set.range (upperCurve l))
  upper_local_v : ∀ p ∈ superellipsoidTorusSeam Phi frame c R d,
    ∃ k z i j U, IsOpen U ∧ p ∈ U ∧ upperCurve k z = p ∧
      Set.range (upperCurve k) ∩ U =
        ((Set.range (outer.circle i).circle ∩ upperClosedHalfspace frame d) ∪
          (Set.range (cut.circle j).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U
  upper_mem : ∀ k, Set.range (upperCurve k) ⊆
    upperTruncatedSeamVCarrier Phi frame c R d
  upper_outer_covered : ∀ i,
    Set.range (outer.circle i).circle ∩ upperClosedHalfspace frame d ⊆
      ⋃ k, Set.range (upperCurve k)
  upper_cut_covered : ∀ j,
    Set.range (cut.circle j).circle ∩ closedSuperellipsoidBody frame c R ⊆
      ⋃ k, Set.range (upperCurve k)

namespace TruncatedSphereSeamVGluingData

variable {outerIndex cutIndex lowerIndex upperIndex : Type*}
  [Fintype outerIndex] [Fintype cutIndex]
  [Fintype lowerIndex] [Fintype upperIndex]
  {outer : FiniteEmbeddedTorusCircleSection Phi
    (superellipsoidOuterTorusSection Phi frame c R) outerIndex}
  {cut : FiniteEmbeddedTorusCircleSection Phi
    (superellipsoidCutTorusSection Phi frame d) cutIndex}

/-- A continuous injective cyclic ambient gluing, bundled with its torus winding loop. -/
def embeddedCircleOfCurve (curve : Circle → R3)
    (hcontinuous : Continuous curve) (hinjective : Function.Injective curve)
    (hmem : ∀ z, curve z ∈ transportedTorus Phi) :
    EmbeddedTorusIntersectionCircle Phi := by
  let torusCurve : Circle → transportedTorus Phi := fun z ↦ ⟨curve z, hmem z⟩
  let beta : Circle → Circle × Circle := fun z ↦
    (transportedTorusHomeomorph Phi).symm (torusCurve z)
  have htorusCurve : Continuous torusCurve := hcontinuous.subtype_mk hmem
  have hbeta : Continuous beta :=
    (transportedTorusHomeomorph Phi).symm.continuous.comp htorusCurve
  let loop := FiniteCoordinatePlaneTorusCircleFamily.windingLoopOfCircle
    (Phi := Phi) beta hbeta
  exact {
    circle := curve
    isEmbedding := (hcontinuous.isClosedEmbedding hinjective).isEmbedding
    windingLoop := loop
    parametrization := fun t ↦ by
      change curve (Circle.exp t) =
        ((transportedTorusHomeomorph Phi
          ((transportedTorusHomeomorph Phi).symm
            (torusCurve (Circle.exp t)))) : transportedTorus Phi)
      exact congrArg Subtype.val
        ((transportedTorusHomeomorph Phi).apply_symm_apply
          (torusCurve (Circle.exp t))) |>.symm
  }

/-- The cyclic gluing maps cover the entire lower analytic `V`-carrier. -/
theorem lower_carrier_subset_curveUnion
    (V : TruncatedSphereSeamVGluingData
      (lowerIndex := lowerIndex) (upperIndex := upperIndex) outer cut) :
    lowerTruncatedSeamVCarrier Phi frame c R d ⊆
      ⋃ k, Set.range (V.lowerCurve k) := by
  intro x hx
  rcases hx with hxOuter | hxCut
  · rw [outer.section_exact] at hxOuter
    obtain ⟨hxFamily, hxHalf⟩ := hxOuter
    simp only [Set.mem_iUnion] at hxFamily
    obtain ⟨i, hi⟩ := hxFamily
    exact V.lower_outer_covered i ⟨hi, hxHalf⟩
  · rw [cut.section_exact] at hxCut
    obtain ⟨hxFamily, hxBody⟩ := hxCut
    simp only [Set.mem_iUnion] at hxFamily
    obtain ⟨j, hj⟩ := hxFamily
    exact V.lower_cut_covered j ⟨hj, hxBody⟩

/-- The cyclic gluing maps cover the entire upper analytic `V`-carrier. -/
theorem upper_carrier_subset_curveUnion
    (V : TruncatedSphereSeamVGluingData
      (lowerIndex := lowerIndex) (upperIndex := upperIndex) outer cut) :
    upperTruncatedSeamVCarrier Phi frame c R d ⊆
      ⋃ k, Set.range (V.upperCurve k) := by
  intro x hx
  rcases hx with hxOuter | hxCut
  · rw [outer.section_exact] at hxOuter
    obtain ⟨hxFamily, hxHalf⟩ := hxOuter
    simp only [Set.mem_iUnion] at hxFamily
    obtain ⟨i, hi⟩ := hxFamily
    exact V.upper_outer_covered i ⟨hi, hxHalf⟩
  · rw [cut.section_exact] at hxCut
    obtain ⟨hxFamily, hxBody⟩ := hxCut
    simp only [Set.mem_iUnion] at hxFamily
    obtain ⟨j, hj⟩ := hxFamily
    exact V.upper_cut_covered j ⟨hj, hxBody⟩

/-- The local `V`-gluing contract produces the finite lower child section. -/
def lowerFiniteSection
    (hR : 0 < R)
    (V : TruncatedSphereSeamVGluingData
      (lowerIndex := lowerIndex) (upperIndex := upperIndex) outer cut) :
    FiniteEmbeddedTorusCircleSection Phi
      (lowerTruncatedSuperellipsoidTorusSection Phi frame c R d) lowerIndex where
  circle := fun k ↦ embeddedCircleOfCurve (V.lowerCurve k)
    (V.lower_continuous k) (V.lower_injective k) (V.lower_mem_torus k)
  circle_mem_section := by
    intro k x hx
    rw [lowerTruncatedSuperellipsoidTorusSection_eq_seamVCarrier hR]
    exact V.lower_mem k hx
  pairwise_disjoint := V.lower_pairwise
  section_exact := by
    rw [lowerTruncatedSuperellipsoidTorusSection_eq_seamVCarrier hR]
    apply Set.Subset.antisymm
    · exact V.lower_carrier_subset_curveUnion
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk⟩ := hx
      exact V.lower_mem k hk

/-- The local `V`-gluing contract produces the finite upper child section. -/
def upperFiniteSection
    (hR : 0 < R)
    (V : TruncatedSphereSeamVGluingData
      (lowerIndex := lowerIndex) (upperIndex := upperIndex) outer cut) :
    FiniteEmbeddedTorusCircleSection Phi
      (upperTruncatedSuperellipsoidTorusSection Phi frame c R d) upperIndex where
  circle := fun k ↦ embeddedCircleOfCurve (V.upperCurve k)
    (V.upper_continuous k) (V.upper_injective k) (V.upper_mem_torus k)
  circle_mem_section := by
    intro k x hx
    rw [upperTruncatedSuperellipsoidTorusSection_eq_seamVCarrier hR]
    exact V.upper_mem k hx
  pairwise_disjoint := V.upper_pairwise
  section_exact := by
    rw [upperTruncatedSuperellipsoidTorusSection_eq_seamVCarrier hR]
    apply Set.Subset.antisymm
    · exact V.upper_carrier_subset_curveUnion
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk⟩ := hx
      exact V.upper_mem k hk

end TruncatedSphereSeamVGluingData

end Submission.Topology
