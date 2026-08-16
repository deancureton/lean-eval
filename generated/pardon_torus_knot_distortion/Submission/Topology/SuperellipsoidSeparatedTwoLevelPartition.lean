import Submission.Topology.SuperellipsoidGlobalNeckPinchRounding
import Submission.Topology.TwoLevelSphereDichotomy

/-!
# A separated three-sphere four-cell partition

The two convex truncation spheres at radius `R` are enclosed by a third superellipsoid sphere at
radius `R + η`.  For `η > 0` the enclosing sphere is disjoint from both child spheres, while the
two children are disjoint because their cutting levels are separated by `2 * ε`.  Their
complement has the four honest open cells needed by `TwoLevelSpherePartition`: the two child
interiors, the region inside the enclosing sphere and outside both children, and the exterior of
the enclosing closed body.

This construction deliberately makes no claim that the middle cell is contained in a regular
coordinate-height band.  That is separate geometric input for the cyclic-winding argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy}

private theorem outerParallelFrontier_disjoint_lowerTruncationFrontier
    {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε η : ℝ}
    (hR : 0 < R) (hη : 0 < η) :
    Disjoint (frontier (closedSuperellipsoidBody frame c (R + η)))
      (frontier (separatedLowerSuperellipsoidTruncation frame c R d ε)) := by
  rw [Set.disjoint_left]
  intro x hxOuter hxLower
  have hxOuterEq : superellipsoidGauge frame c x = R + η := by
    rw [frontier_closedSuperellipsoidBody_eq_boundary frame c (add_pos hR hη)] at hxOuter
    change superellipsoidGauge frame c x = R + η at hxOuter
    exact hxOuter
  have hxLowerClosed : x ∈ closedSuperellipsoidBody frame c R ∩
      {y | y.ofLp (frame 2) ≤ d - ε} :=
    isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset hxLower
  have hxLowerLe : superellipsoidGauge frame c x ≤ R := hxLowerClosed.1
  linarith

private theorem outerParallelFrontier_disjoint_upperTruncationFrontier
    {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε η : ℝ}
    (hR : 0 < R) (hη : 0 < η) :
    Disjoint (frontier (closedSuperellipsoidBody frame c (R + η)))
      (frontier (separatedUpperSuperellipsoidTruncation frame c R d ε)) := by
  rw [Set.disjoint_left]
  intro x hxOuter hxUpper
  have hxOuterEq : superellipsoidGauge frame c x = R + η := by
    rw [frontier_closedSuperellipsoidBody_eq_boundary frame c (add_pos hR hη)] at hxOuter
    change superellipsoidGauge frame c x = R + η at hxOuter
    exact hxOuter
  have hxUpperClosed : x ∈ closedSuperellipsoidBody frame c R ∩
      {y | d + ε ≤ y.ofLp (frame 2)} :=
    isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset hxUpper
  have hxUpperLe : superellipsoidGauge frame c x ≤ R := hxUpperClosed.1
  linarith

/-- The enclosing parallel outer sphere followed by the lower and upper separated child
spheres. -/
def separatedTruncationWithOuterSphereFamily
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d ε η : ℝ}
    (hR : 0 < R) (hη : 0 < η)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2))
    (hε : 0 < ε) : FiniteEmbeddedTopologicalSphereFamilyInR3 where
  count := 3
  sphere
    | ⟨0, _⟩ => (outerSuperellipsoidSphereData frame c (add_pos hR hη)).sphere
    | ⟨1, _⟩ => (lowerTruncatedSuperellipsoidSphereData frame c hR hlower).sphere
    | ⟨2, _⟩ => (upperTruncatedSuperellipsoidSphereData frame c hR hupper).sphere
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedLowerSuperellipsoidTruncation] using
        outerParallelFrontier_disjoint_lowerTruncationFrontier hR hη
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedUpperSuperellipsoidTruncation] using
        outerParallelFrontier_disjoint_upperTruncationFrontier hR hη
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedLowerSuperellipsoidTruncation] using
        (outerParallelFrontier_disjoint_lowerTruncationFrontier hR hη).symm
    · exact False.elim (hij rfl)
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedLowerSuperellipsoidTruncation,
        separatedUpperSuperellipsoidTruncation] using
        (separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
          (d := d) hε).mono
            isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset
            isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedUpperSuperellipsoidTruncation] using
        (outerParallelFrontier_disjoint_upperTruncationFrontier hR hη).symm
    · simpa [ConvexBodySphereData.sphere_carrier_eq_frontier,
        separatedLowerSuperellipsoidTruncation,
        separatedUpperSuperellipsoidTruncation] using
        ((separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
          (d := d) hε).mono
            isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset
            isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset).symm
    · exact False.elim (hij rfl)

@[simp] theorem separatedTruncationWithOuterSphereFamily_count
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d ε η : ℝ}
    (hR : 0 < R) (hη : 0 < η)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2))
    (hε : 0 < ε) :
    (separatedTruncationWithOuterSphereFamily frame c hR hη
      hlower hupper hε).count = 3 := rfl

/-- Exact carrier of the honest three-sphere family. -/
theorem separatedTruncationWithOuterSphereFamily_carrier
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d ε η : ℝ}
    (hR : 0 < R) (hη : 0 < η)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2))
    (hε : 0 < ε) :
    (separatedTruncationWithOuterSphereFamily frame c hR hη
      hlower hupper hε).carrier =
      frontier (closedSuperellipsoidBody frame c (R + η)) ∪
        frontier (separatedLowerSuperellipsoidTruncation frame c R d ε) ∪
          frontier (separatedUpperSuperellipsoidTruncation frame c R d ε) := by
  change (⋃ i : Fin 3,
    ((separatedTruncationWithOuterSphereFamily frame c hR hη
      hlower hupper hε).sphere i).carrier) = _
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [separatedTruncationWithOuterSphereFamily,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hi))
    · exact Or.inl (Or.inr (by simpa [separatedTruncationWithOuterSphereFamily,
        separatedLowerSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hi))
    · exact Or.inr (by simpa [separatedTruncationWithOuterSphereFamily,
        separatedUpperSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hi)
  · rintro ((hxOuter | hxLower) | hxUpper)
    · refine ⟨0, ?_⟩
      simpa [separatedTruncationWithOuterSphereFamily,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hxOuter
    · refine ⟨1, ?_⟩
      simpa [separatedTruncationWithOuterSphereFamily,
        separatedLowerSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hxLower
    · refine ⟨2, ?_⟩
      simpa [separatedTruncationWithOuterSphereFamily,
        separatedUpperSuperellipsoidTruncation,
        ConvexBodySphereData.sphere_carrier_eq_frontier] using hxUpper

/-- The lower open surface cell. -/
def separatedThreeSphereLowerPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d ε : ℝ) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi (separatedLowerSuperellipsoidInside frame c R d ε)

/-- The middle open cell inside the enclosing sphere and outside both closed children. -/
def separatedThreeSphereMiddlePart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d ε η : ℝ) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi
    (interior (closedSuperellipsoidBody frame c (R + η)) \
      (separatedLowerSuperellipsoidTruncation frame c R d ε ∪
        separatedUpperSuperellipsoidTruncation frame c R d ε))

/-- The upper open surface cell. -/
def separatedThreeSphereUpperPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d ε : ℝ) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi (separatedUpperSuperellipsoidInside frame c R d ε)

/-- The open exterior of the enclosing parallel sphere. -/
def separatedThreeSphereExteriorPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R η : ℝ) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi (closedSuperellipsoidBody frame c (R + η))ᶜ

/-- The parent part is the transported-torus part inside the enclosing parallel sphere. -/
def separatedThreeSphereParentPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R η : ℝ) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi (interior (closedSuperellipsoidBody frame c (R + η)))

/-- The original parent body lies in the parent part bounded by the parallel outer sphere. -/
theorem originalParentPart_subset_separatedThreeSphereParentPart
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    transportedTorusPart Phi (interior (closedSuperellipsoidBody frame c R)) ⊆
      separatedThreeSphereParentPart Phi frame c R η := by
  apply preimage_mono
  apply interior_mono
  intro x hx
  change superellipsoidGauge frame c x ≤ R at hx
  change superellipsoidGauge frame c x ≤ R + η
  linarith

/-- The usual strict-gauge parent used by the quantitative box step also lies in the enlarged
parent cell. -/
theorem superellipsoidBodyPart_subset_separatedThreeSphereParentPart
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    transportedTorusPart Phi (superellipsoidBody frame c R) ⊆
      separatedThreeSphereParentPart Phi frame c R η :=
  preimage_mono <| (superellipsoidBody_subset_interior_closedSuperellipsoidBody
    frame c R).trans <| by
      apply interior_mono
      intro x hx
      change superellipsoidGauge frame c x ≤ R at hx
      change superellipsoidGauge frame c x ≤ R + η
      linarith

private theorem windingCurveUnion_mem_of_sphereCarrier_mem
    {iota : Type*} [Fintype iota]
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    {x : transportedTorus Phi} (hx : (x : R3) ∈ S.sphereFamily.carrier) :
    x ∈ ⋃ i, Set.range (fun t ↦ (S.circle i).windingLoop.curve t) := by
  have hxIntersection : (x : R3) ∈
      S.sphereFamily.carrier ∩ transportedTorus Phi := ⟨hx, x.property⟩
  rw [S.intersection_exact] at hxIntersection
  simp only [Set.mem_iUnion] at hxIntersection ⊢
  obtain ⟨i, z, hz⟩ := hxIntersection
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  refine ⟨i, t, ?_⟩
  apply Subtype.ext
  rw [← (S.circle i).parametrization t, ht]
  exact hz

/-- An exact regular intersection system for the explicit three-sphere family. -/
structure SeparatedThreeSphereSystemGeometry
    {iota : Type*} [Fintype iota]
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d ε η : ℝ)
    (hR : 0 < R) (hη : 0 < η)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2))
    (hε : 0 < ε) where
  sphereFamily_carrier_eq :
    S.sphereFamily.carrier =
      (separatedTruncationWithOuterSphereFamily frame c hR hη
        hlower hupper hε).carrier

namespace SeparatedThreeSphereSystemGeometry

variable {iota : Type*} [Fintype iota]
  {S : FiniteSphereSurgeryIntersectionSystem Phi iota}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε η : ℝ}
  {hR : 0 < R} {hη : 0 < η}
  {hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
    x.ofLp (frame 2) < d - ε}
  {hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
    d + ε < x.ofLp (frame 2)}
  {hε : 0 < ε}

private theorem sphereCarrier_mem_of_outerFrontier
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε)
    {x : transportedTorus Phi}
    (hx : (x : R3) ∈ frontier
      (closedSuperellipsoidBody frame c (R + η))) :
    (x : R3) ∈ S.sphereFamily.carrier := by
  rw [G.sphereFamily_carrier_eq,
    separatedTruncationWithOuterSphereFamily_carrier]
  exact Or.inl (Or.inl hx)

private theorem sphereCarrier_mem_of_lowerFrontier
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε)
    {x : transportedTorus Phi}
    (hx : (x : R3) ∈ frontier
      (separatedLowerSuperellipsoidTruncation frame c R d ε)) :
    (x : R3) ∈ S.sphereFamily.carrier := by
  rw [G.sphereFamily_carrier_eq,
    separatedTruncationWithOuterSphereFamily_carrier]
  exact Or.inl (Or.inr hx)

private theorem sphereCarrier_mem_of_upperFrontier
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε)
    {x : transportedTorus Phi}
    (hx : (x : R3) ∈ frontier
      (separatedUpperSuperellipsoidTruncation frame c R d ε)) :
    (x : R3) ∈ S.sphereFamily.carrier := by
  rw [G.sphereFamily_carrier_eq,
    separatedTruncationWithOuterSphereFamily_carrier]
  exact Or.inr hx

variable [DecidableEq iota]

/-- The exact four-cell partition of the transported torus by the honest three-sphere family. -/
def toTwoLevelSpherePartition
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) : TwoLevelSpherePartition S where
  parentPart := separatedThreeSphereParentPart Phi frame c R η
  lowerPart := separatedThreeSphereLowerPart Phi frame c R d ε
  middlePart := separatedThreeSphereMiddlePart Phi frame c R d ε η
  upperPart := separatedThreeSphereUpperPart Phi frame c R d ε
  exteriorPart := separatedThreeSphereExteriorPart Phi frame c R η
  isOpen_lowerPart := isOpen_interior.preimage continuous_subtype_val
  isOpen_middlePart := (isOpen_interior.sdiff
    (isClosed_separatedLowerSuperellipsoidTruncation.union
      isClosed_separatedUpperSuperellipsoidTruncation)).preimage continuous_subtype_val
  isOpen_upperPart := isOpen_interior.preimage continuous_subtype_val
  isOpen_exteriorPart :=
    (isClosed_closedSuperellipsoidBody_convexSphere frame c (R + η)).isOpen_compl.preimage
      continuous_subtype_val
  lower_disjoint_middle := by
    rw [Set.disjoint_left]
    intro x hxLower hxMiddle
    exact hxMiddle.2 (Or.inl (interior_subset hxLower))
  lower_disjoint_upper := by
    rw [Set.disjoint_left]
    intro x hxLower hxUpper
    exact Set.disjoint_left.mp (separatedInsides_disjoint hε) hxLower hxUpper
  lower_disjoint_exterior := by
    rw [Set.disjoint_left]
    intro x hxLower hxExterior
    have hxClosed : (x : R3) ∈ closedSuperellipsoidBody frame c R ∩
        {y | y.ofLp (frame 2) ≤ d - ε} := interior_subset hxLower
    have hxGauge : superellipsoidGauge frame c x ≤ R := hxClosed.1
    apply hxExterior
    change superellipsoidGauge frame c x ≤ R + η
    linarith
  middle_disjoint_upper := by
    rw [Set.disjoint_left]
    intro x hxMiddle hxUpper
    exact hxMiddle.2 (Or.inr (interior_subset hxUpper))
  middle_disjoint_exterior := by
    rw [Set.disjoint_left]
    intro x hxMiddle hxExterior
    exact hxExterior (interior_subset hxMiddle.1)
  upper_disjoint_exterior := by
    rw [Set.disjoint_left]
    intro x hxUpper hxExterior
    have hxClosed : (x : R3) ∈ closedSuperellipsoidBody frame c R ∩
        {y | d + ε ≤ y.ofLp (frame 2)} := interior_subset hxUpper
    have hxGauge : superellipsoidGauge frame c x ≤ R := hxClosed.1
    apply hxExterior
    change superellipsoidGauge frame c x ≤ R + η
    linarith
  lower_subset_parent := by
    intro x hxLower
    apply interior_mono _ hxLower
    intro y hy
    have hyGauge : superellipsoidGauge frame c y ≤ R := hy.1
    change superellipsoidGauge frame c y ≤ R + η
    linarith
  middle_subset_parent := fun _ hx ↦ hx.1
  upper_subset_parent := by
    intro x hxUpper
    apply interior_mono _ hxUpper
    intro y hy
    have hyGauge : superellipsoidGauge frame c y ≤ R := hy.1
    change superellipsoidGauge frame c y ≤ R + η
    linarith
  parent_disjoint_exterior := by
    rw [Set.disjoint_left]
    intro x hxParent hxExterior
    exact hxExterior (interior_subset hxParent)
  surface_partition := by
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_union]
    by_cases hxOuterInterior :
        (x : R3) ∈ interior (closedSuperellipsoidBody frame c (R + η))
    · by_cases hxLowerClosed : (x : R3) ∈
          separatedLowerSuperellipsoidTruncation frame c R d ε
      · by_cases hxLowerInterior : (x : R3) ∈
            interior (separatedLowerSuperellipsoidTruncation frame c R d ε)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hxLowerInterior)))
        · apply Or.inr
          apply windingCurveUnion_mem_of_sphereCarrier_mem S
          apply G.sphereCarrier_mem_of_lowerFrontier
          rw [isClosed_separatedLowerSuperellipsoidTruncation.frontier_eq]
          exact ⟨hxLowerClosed, hxLowerInterior⟩
      · by_cases hxUpperClosed : (x : R3) ∈
            separatedUpperSuperellipsoidTruncation frame c R d ε
        · by_cases hxUpperInterior : (x : R3) ∈
              interior (separatedUpperSuperellipsoidTruncation frame c R d ε)
          · exact Or.inl (Or.inl (Or.inr hxUpperInterior))
          · apply Or.inr
            apply windingCurveUnion_mem_of_sphereCarrier_mem S
            apply G.sphereCarrier_mem_of_upperFrontier
            rw [isClosed_separatedUpperSuperellipsoidTruncation.frontier_eq]
            exact ⟨hxUpperClosed, hxUpperInterior⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inr
            ⟨hxOuterInterior, by simpa using ⟨hxLowerClosed, hxUpperClosed⟩⟩)))
    · by_cases hxOuterClosed :
          (x : R3) ∈ closedSuperellipsoidBody frame c (R + η)
      · apply Or.inr
        apply windingCurveUnion_mem_of_sphereCarrier_mem S
        apply G.sphereCarrier_mem_of_outerFrontier
        rw [(isClosed_closedSuperellipsoidBody_convexSphere frame c
          (R + η)).frontier_eq]
        exact ⟨hxOuterClosed, hxOuterInterior⟩
      · exact Or.inl (Or.inr hxOuterClosed)

@[simp] theorem toTwoLevelSpherePartition_parentPart
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) :
    G.toTwoLevelSpherePartition.parentPart =
      separatedThreeSphereParentPart Phi frame c R η := rfl

@[simp] theorem toTwoLevelSpherePartition_middlePart
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) :
    G.toTwoLevelSpherePartition.middlePart =
      separatedThreeSphereMiddlePart Phi frame c R d ε η := rfl

@[simp] theorem toTwoLevelSpherePartition_lowerPart
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) :
    G.toTwoLevelSpherePartition.lowerPart =
      separatedThreeSphereLowerPart Phi frame c R d ε := rfl

@[simp] theorem toTwoLevelSpherePartition_upperPart
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) :
    G.toTwoLevelSpherePartition.upperPart =
      separatedThreeSphereUpperPart Phi frame c R d ε := rfl

@[simp] theorem toTwoLevelSpherePartition_exteriorPart
    (G : SeparatedThreeSphereSystemGeometry S frame c R d ε η
      hR hη hlower hupper hε) :
    G.toTwoLevelSpherePartition.exteriorPart =
      separatedThreeSphereExteriorPart Phi frame c R η := rfl

end SeparatedThreeSphereSystemGeometry

end Submission.Topology
