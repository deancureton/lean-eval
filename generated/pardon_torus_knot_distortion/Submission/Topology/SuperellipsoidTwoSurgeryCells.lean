import Submission.SuperellipsoidGeometry
import Submission.Topology.HalfSphereSurgeryDichotomy

/-!
# Analytic cells for the superellipsoid two-surgery

The open lower, upper, and exterior surface cells are defined by strict inequalities.  The
remaining barrier is exactly the outer superellipsoid boundary together with the cutting disk.
This gives an exhaustive, disjoint three-cell partition with no artificial rounded gap.  Once a
finite circle family is identified with the barrier, these sets instantiate the abstract
elementary half-sphere surgery event.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped ENNReal

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- Strict lower cell inside the selected open superellipsoid. -/
def superellipsoidStrictLowerPart (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Set (transportedTorus Phi) :=
  transportedTorusPart Phi
    (superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) < d})

/-- Strict upper cell inside the selected open superellipsoid. -/
def superellipsoidStrictUpperPart (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Set (transportedTorus Phi) :=
  transportedTorusPart Phi
    (superellipsoidBody frame c R ∩ {x | d < x.ofLp (frame 2)})

/-- Strict exterior of the selected outer superellipsoid. -/
def superellipsoidStrictExteriorPart (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    Set (transportedTorus Phi) :=
  transportedTorusPart Phi {x | R < superellipsoidGauge frame c x}

/-- The complete barrier: outer boundary plus the portion of the cutting plane in the open
body. -/
def superellipsoidOuterCutBarrierPart (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Set (transportedTorus Phi) :=
  transportedTorusPart Phi
    (superellipsoidBoundary frame c R ∪
      (superellipsoidBody frame c R ∩ coordinateCuttingPlane frame d))

private theorem continuous_superellipsoidGauge'
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    Continuous (superellipsoidGauge frame c) := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hcoordinates : Continuous (superellipsoidCoordinates frame c) := by
    change Continuous (fun x ↦ WithLp.toLp 256 (normalizedOrientedBoxCoordinates frame c x))
    apply (PiLp.continuous_toLp 256 (fun _ : Fin 3 ↦ ℝ)).comp
    exact continuous_pi fun i ↦
      (((coordinateCLM (frame i)).continuous.comp
        (continuous_id.sub continuous_const)).div_const (axisWeight i))
  exact (continuous_norm.comp hcoordinates).congr fun _ ↦ rfl

theorem isOpen_superellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsOpen (superellipsoidBody frame c R) :=
  isOpen_Iio.preimage (continuous_superellipsoidGauge' frame c)

theorem isOpen_superellipsoidStrictLowerPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsOpen (superellipsoidStrictLowerPart Phi frame c R d) := by
  exact ((isOpen_superellipsoidBody frame c R).inter <|
    isOpen_Iio.preimage (coordinateCLM (frame 2)).continuous).preimage continuous_subtype_val

theorem isOpen_superellipsoidStrictUpperPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsOpen (superellipsoidStrictUpperPart Phi frame c R d) := by
  exact ((isOpen_superellipsoidBody frame c R).inter <|
    isOpen_Ioi.preimage (coordinateCLM (frame 2)).continuous).preimage continuous_subtype_val

theorem isOpen_superellipsoidStrictExteriorPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsOpen (superellipsoidStrictExteriorPart Phi frame c R) := by
  exact (isOpen_Ioi.preimage (continuous_superellipsoidGauge' frame c)).preimage
    continuous_subtype_val

theorem superellipsoidStrictLowerPart_disjoint_upperPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Disjoint (superellipsoidStrictLowerPart Phi frame c R d)
      (superellipsoidStrictUpperPart Phi frame c R d) := by
  rw [Set.disjoint_left]
  intro x hxLower hxUpper
  change superellipsoidGauge frame c x < R ∧ x.1.ofLp (frame 2) < d at hxLower
  change superellipsoidGauge frame c x < R ∧ d < x.1.ofLp (frame 2) at hxUpper
  exact (not_lt_of_ge hxUpper.2.le) hxLower.2

theorem superellipsoidStrictLowerPart_disjoint_exteriorPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Disjoint (superellipsoidStrictLowerPart Phi frame c R d)
      (superellipsoidStrictExteriorPart Phi frame c R) := by
  rw [Set.disjoint_left]
  intro x hxLower hxExterior
  change superellipsoidGauge frame c x < R ∧ x.1.ofLp (frame 2) < d at hxLower
  change R < superellipsoidGauge frame c x at hxExterior
  exact (not_lt_of_ge hxExterior.le) hxLower.1

theorem superellipsoidStrictUpperPart_disjoint_exteriorPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Disjoint (superellipsoidStrictUpperPart Phi frame c R d)
      (superellipsoidStrictExteriorPart Phi frame c R) := by
  rw [Set.disjoint_left]
  intro x hxUpper hxExterior
  change superellipsoidGauge frame c x < R ∧ d < x.1.ofLp (frame 2) at hxUpper
  change R < superellipsoidGauge frame c x at hxExterior
  exact (not_lt_of_ge hxExterior.le) hxUpper.1

theorem superellipsoidStrictLowerPart_subset_parent
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    superellipsoidStrictLowerPart Phi frame c R d ⊆
      transportedTorusPart Phi (superellipsoidBody frame c R) :=
  fun _ hx ↦ hx.1

theorem superellipsoidStrictUpperPart_subset_parent
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    superellipsoidStrictUpperPart Phi frame c R d ⊆
      transportedTorusPart Phi (superellipsoidBody frame c R) :=
  fun _ hx ↦ hx.1

theorem superellipsoidParentPart_disjoint_exteriorPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    Disjoint (transportedTorusPart Phi (superellipsoidBody frame c R))
      (superellipsoidStrictExteriorPart Phi frame c R) := by
  rw [Set.disjoint_left]
  intro x hxParent hxExterior
  change superellipsoidGauge frame c x < R at hxParent
  change R < superellipsoidGauge frame c x at hxExterior
  exact (not_lt_of_ge hxExterior.le) hxParent

/-- Every transported-torus point lies in one strict cell or on the complete outer/cut
barrier. -/
theorem superellipsoid_surface_partition
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Set.univ = superellipsoidStrictLowerPart Phi frame c R d ∪
      superellipsoidStrictUpperPart Phi frame c R d ∪
      superellipsoidStrictExteriorPart Phi frame c R ∪
      superellipsoidOuterCutBarrierPart Phi frame c R d := by
  ext x
  simp only [Set.mem_univ, true_iff, Set.mem_union, transportedTorusPart,
    Set.mem_preimage, superellipsoidStrictLowerPart,
    superellipsoidStrictUpperPart, superellipsoidStrictExteriorPart,
    superellipsoidOuterCutBarrierPart, superellipsoidBody,
    superellipsoidBoundary, coordinateCuttingPlane, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  rcases lt_trichotomy (superellipsoidGauge frame c x) R with hinside | hboundary | hexterior
  · rcases lt_trichotomy (x.1.ofLp (frame 2)) d with hlower | hcut | hupper
    · exact Or.inl (Or.inl (Or.inl ⟨hinside, hlower⟩))
    · exact Or.inr (Or.inr ⟨hinside, hcut⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨hinside, hupper⟩))
  · exact Or.inr (Or.inl hboundary)
  · exact Or.inl (Or.inr hexterior)

/-- A finite circle family whose ranges equal the analytic outer/cut barrier instantiates the
exact elementary half-sphere surgery event. -/
def elementaryHalfSphereSurgeryEvent_of_superellipsoidBarrier
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hbarrier : ⋃ i, Set.range (fun t ↦ (S.circle i).windingLoop.curve t) =
      superellipsoidOuterCutBarrierPart Phi frame c R d) :
    ElementaryHalfSphereSurgeryEvent S where
  parentPart := transportedTorusPart Phi (superellipsoidBody frame c R)
  lowerPart := superellipsoidStrictLowerPart Phi frame c R d
  upperPart := superellipsoidStrictUpperPart Phi frame c R d
  exteriorPart := superellipsoidStrictExteriorPart Phi frame c R
  isOpen_lowerPart := isOpen_superellipsoidStrictLowerPart Phi frame c R d
  isOpen_upperPart := isOpen_superellipsoidStrictUpperPart Phi frame c R d
  isOpen_exteriorPart := isOpen_superellipsoidStrictExteriorPart Phi frame c R
  lower_disjoint_upper :=
    superellipsoidStrictLowerPart_disjoint_upperPart Phi frame c R d
  lower_disjoint_exterior :=
    superellipsoidStrictLowerPart_disjoint_exteriorPart Phi frame c R d
  upper_disjoint_exterior :=
    superellipsoidStrictUpperPart_disjoint_exteriorPart Phi frame c R d
  lower_subset_parent := superellipsoidStrictLowerPart_subset_parent Phi frame c R d
  upper_subset_parent := superellipsoidStrictUpperPart_subset_parent Phi frame c R d
  parent_disjoint_exterior :=
    superellipsoidParentPart_disjoint_exteriorPart Phi frame c R
  surface_partition := by
    rw [hbarrier]
    exact superellipsoid_surface_partition Phi frame c R d

/-- Strict lower cells lie in the closed lower half-body used by the successor-box theorem. -/
theorem superellipsoidStrictLowerPart_subset_closedLowerBody
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    superellipsoidStrictLowerPart Phi frame c R d ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d}) := by
  intro x hx
  change superellipsoidGauge frame c x < R ∧ x.1.ofLp (frame 2) < d at hx
  change superellipsoidGauge frame c x < R ∧ x.1.ofLp (frame 2) ≤ d
  exact ⟨hx.1, hx.2.le⟩

/-- Strict upper cells lie in the closed upper half-body used by the successor-box theorem. -/
theorem superellipsoidStrictUpperPart_subset_closedUpperBody
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    superellipsoidStrictUpperPart Phi frame c R d ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)}) := by
  intro x hx
  change superellipsoidGauge frame c x < R ∧ d < x.1.ofLp (frame 2) at hx
  change superellipsoidGauge frame c x < R ∧ d ≤ x.1.ofLp (frame 2)
  exact ⟨hx.1, hx.2.le⟩

end Submission.Topology
