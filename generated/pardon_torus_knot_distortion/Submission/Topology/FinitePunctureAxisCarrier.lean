import Submission.Topology.BasedLoopCarrier
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Interval.Set.Infinite

/-!
# An explicit based carrier avoiding finitely many torus points

For finitely many points of `Circle × Circle`, choose a first coordinate absent from all of
their first coordinates and a second coordinate absent from all of their second coordinates.
The longitude and meridian through the resulting product point miss every puncture, share their
basepoint, and have winding pairs `(1, 0)` and `(0, 1)`.  Transporting through the ambient torus
homeomorphism gives a based carrier of the finite-point complement.

This direct construction is the finite-puncture input for radial disk-pushout arguments; no
global connectivity theorem for a punctured surface is needed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- A product-torus point whose two coordinates avoid the corresponding coordinates of every
member of a finite family. -/
structure AvoidingAxisBase {ι : Type*} (centers : ι → Circle × Circle) where
  first : Circle
  second : Circle
  first_ne : ∀ i, first ≠ (centers i).1
  second_ne : ∀ i, second ≠ (centers i).2

/-- A circle has points outside every specified finite family. -/
private theorem exists_circle_not_mem_finite_range
    {ι : Type*} [Fintype ι] (f : ι → Circle) :
    ∃ z, ∀ i, z ≠ f i := by
  let arc : Set.Ioo (0 : ℝ) 1 → Circle := fun x ↦ Circle.exp x
  have harc : Function.Injective arc := by
    intro x y hxy
    apply Subtype.ext
    exact Circle.exp_injOn_Ico (a := 0) (b := 1)
      (by nlinarith [Real.pi_gt_three])
      (Set.Ioo_subset_Ico_self x.2) (Set.Ioo_subset_Ico_self y.2) hxy
  let hInfiniteCircle : Infinite Circle :=
    @Infinite.of_injective Circle (Set.Ioo (0 : ℝ) 1)
      (Set.Ioo.infinite zero_lt_one) arc harc
  have hproper : Set.range f ≠ (Set.univ : Set Circle) := by
    intro h
    have hfiniteCircle : Finite Circle :=
      Set.finite_univ_iff.mp (h ▸ Set.finite_range f)
    exact hInfiniteCircle.not_finite hfiniteCircle
  obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hproper
  refine ⟨z, ?_⟩
  intro i hzi
  exact hz ⟨i, hzi.symm⟩

/-- Every finite family of product-torus points admits an avoiding axis base. -/
theorem exists_avoidingAxisBase {ι : Type*} [Fintype ι]
    (centers : ι → Circle × Circle) :
    Nonempty (AvoidingAxisBase centers) := by
  obtain ⟨b, hb⟩ := exists_circle_not_mem_finite_range (fun i ↦ (centers i).1)
  obtain ⟨a, ha⟩ := exists_circle_not_mem_finite_range (fun i ↦ (centers i).2)
  exact ⟨{
    first := b
    second := a
    first_ne := hb
    second_ne := ha
  }⟩

/-- The finite-point complement after transporting the chosen product points to the embedded
torus. -/
def transportedFinitePointComplement {ι : Type*} (Phi : AmbientIsotopy)
    (centers : ι → Circle × Circle) : Set (transportedTorus Phi) :=
  {x | ∀ i, x ≠ transportedTorusHomeomorph Phi (centers i)}

/-- The pointwise definition is exactly the complement of the finite transported range. -/
theorem transportedFinitePointComplement_eq_compl_range
    {ι : Type*} (Phi : AmbientIsotopy) (centers : ι → Circle × Circle) :
    transportedFinitePointComplement Phi centers =
      (Set.range (fun i ↦ transportedTorusHomeomorph Phi (centers i)))ᶜ := by
  ext x
  constructor
  · intro hx hmem
    obtain ⟨i, hi⟩ := hmem
    exact hx i hi.symm
  · intro hx i hi
    exact hx ⟨i, hi.symm⟩

namespace AvoidingAxisBase

variable {ι : Type*} {centers : ι → Circle × Circle}

/-- Longitude through the avoiding product point. -/
def longitudeProductCurve (B : AvoidingAxisBase centers) (t : ℝ) :
    Circle × Circle :=
  (Circle.exp (t + (B.first : ℂ).arg), B.second)

/-- Meridian through the avoiding product point. -/
def meridianProductCurve (B : AvoidingAxisBase centers) (t : ℝ) :
    Circle × Circle :=
  (B.first, Circle.exp (t + (B.second : ℂ).arg))

theorem continuous_longitudeProductCurve (B : AvoidingAxisBase centers) :
    Continuous B.longitudeProductCurve := by
  exact (Circle.exp.continuous.comp
    (continuous_id.add continuous_const)).prodMk continuous_const

theorem continuous_meridianProductCurve (B : AvoidingAxisBase centers) :
    Continuous B.meridianProductCurve := by
  exact continuous_const.prodMk (Circle.exp.continuous.comp
    (continuous_id.add continuous_const))

theorem periodic_longitudeProductCurve (B : AvoidingAxisBase centers) :
    Function.Periodic B.longitudeProductCurve (2 * Real.pi) := by
  intro t
  apply Prod.ext
  · change Circle.exp (t + 2 * Real.pi + (B.first : ℂ).arg) =
      Circle.exp (t + (B.first : ℂ).arg)
    rw [show t + 2 * Real.pi + (B.first : ℂ).arg =
        (t + (B.first : ℂ).arg) + 2 * Real.pi by ring,
      Circle.exp_add_two_pi]
  · rfl

theorem periodic_meridianProductCurve (B : AvoidingAxisBase centers) :
    Function.Periodic B.meridianProductCurve (2 * Real.pi) := by
  intro t
  apply Prod.ext
  · rfl
  · change Circle.exp (t + 2 * Real.pi + (B.second : ℂ).arg) =
      Circle.exp (t + (B.second : ℂ).arg)
    rw [show t + 2 * Real.pi + (B.second : ℂ).arg =
        (t + (B.second : ℂ).arg) + 2 * Real.pi by ring,
      Circle.exp_add_two_pi]

@[simp]
theorem longitudeProductCurve_zero (B : AvoidingAxisBase centers) :
    B.longitudeProductCurve 0 = (B.first, B.second) := by
  simp [longitudeProductCurve, Circle.exp_arg]

@[simp]
theorem meridianProductCurve_zero (B : AvoidingAxisBase centers) :
    B.meridianProductCurve 0 = (B.first, B.second) := by
  simp [meridianProductCurve, Circle.exp_arg]

theorem longitudeProductCurve_ne_center (B : AvoidingAxisBase centers)
    (t : ℝ) (i : ι) : B.longitudeProductCurve t ≠ centers i := by
  intro h
  exact B.second_ne i (congrArg Prod.snd h)

theorem meridianProductCurve_ne_center (B : AvoidingAxisBase centers)
    (t : ℝ) (i : ι) : B.meridianProductCurve t ≠ centers i := by
  intro h
  exact B.first_ne i (congrArg Prod.fst h)

/-- Transported longitude through the avoiding basepoint. -/
def longitudeCurve (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) (t : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi (B.longitudeProductCurve t)

/-- Transported meridian through the avoiding basepoint. -/
def meridianCurve (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) (t : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi (B.meridianProductCurve t)

/-- Explicit lift with winding pair `(1, 0)` for the avoiding longitude. -/
def longitudeLift (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) :
    TorusLoopLift (transportedLoopCoordinates Phi (B.longitudeCurve Phi)) where
  first := {
    angle := fun t ↦ t + (B.first : ℂ).arg
    continuous_angle := continuous_id.add continuous_const
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, longitudeCurve, longitudeProductCurve]
    winding := 1
    angle_add_period := fun t ↦ by ring
  }
  second := {
    angle := fun _ ↦ (B.second : ℂ).arg
    continuous_angle := continuous_const
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, longitudeCurve, longitudeProductCurve,
        Circle.exp_arg]
    winding := 0
    angle_add_period := fun t ↦ by ring
  }

/-- Explicit lift with winding pair `(0, 1)` for the avoiding meridian. -/
def meridianLift (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) :
    TorusLoopLift (transportedLoopCoordinates Phi (B.meridianCurve Phi)) where
  first := {
    angle := fun _ ↦ (B.first : ℂ).arg
    continuous_angle := continuous_const
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, meridianCurve, meridianProductCurve,
        Circle.exp_arg]
    winding := 0
    angle_add_period := fun t ↦ by ring
  }
  second := {
    angle := fun t ↦ t + (B.second : ℂ).arg
    continuous_angle := continuous_id.add continuous_const
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, meridianCurve, meridianProductCurve]
    winding := 1
    angle_add_period := fun t ↦ by ring
  }

/-- The avoiding longitude as a winding loop in the finite-point complement. -/
def longitudeWindingLoop (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) :
    TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers) where
  curve := B.longitudeCurve Phi
  continuous_curve :=
    (transportedTorusHomeomorph Phi).continuous.comp B.continuous_longitudeProductCurve
  periodic_curve := fun t ↦ congrArg (transportedTorusHomeomorph Phi)
    (B.periodic_longitudeProductCurve t)
  curve_mem := by
    intro t i h
    exact B.longitudeProductCurve_ne_center t i <|
      (transportedTorusHomeomorph Phi).injective h
  lift := B.longitudeLift Phi

/-- The avoiding meridian as a winding loop in the finite-point complement. -/
def meridianWindingLoop (Phi : AmbientIsotopy) (B : AvoidingAxisBase centers) :
    TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers) where
  curve := B.meridianCurve Phi
  continuous_curve :=
    (transportedTorusHomeomorph Phi).continuous.comp B.continuous_meridianProductCurve
  periodic_curve := fun t ↦ congrArg (transportedTorusHomeomorph Phi)
    (B.periodic_meridianProductCurve t)
  curve_mem := by
    intro t i h
    exact B.meridianProductCurve_ne_center t i <|
      (transportedTorusHomeomorph Phi).injective h
  lift := B.meridianLift Phi

@[simp]
theorem windingPair_longitudeWindingLoop (Phi : AmbientIsotopy)
    (B : AvoidingAxisBase centers) :
    (B.longitudeWindingLoop Phi).windingPair = (1, 0) :=
  rfl

@[simp]
theorem windingPair_meridianWindingLoop (Phi : AmbientIsotopy)
    (B : AvoidingAxisBase centers) :
    (B.meridianWindingLoop Phi).windingPair = (0, 1) :=
  rfl

/-- The two avoiding axes give an explicit based carrier of the finite-point complement. -/
def toBasedLoopCarrierWitness (Phi : AmbientIsotopy)
    (B : AvoidingAxisBase centers) :
    BasedLoopCarrierWitness Phi (transportedFinitePointComplement Phi centers) where
  basepoint := transportedTorusHomeomorph Phi (B.first, B.second)
  first := B.longitudeWindingLoop Phi
  second := B.meridianWindingLoop Phi
  first_zero := congrArg (transportedTorusHomeomorph Phi) B.longitudeProductCurve_zero
  second_zero := congrArg (transportedTorusHomeomorph Phi) B.meridianProductCurve_zero
  independent := by
    norm_num [windingPair_longitudeWindingLoop, windingPair_meridianWindingLoop, windingDet]

end AvoidingAxisBase

/-- The complement of any finite family of transported torus points carries based loop genus. -/
theorem finitePointComplement_carriesBasedLoopTorusGenus
    {ι : Type*} [Fintype ι] (Phi : AmbientIsotopy)
    (centers : ι → Circle × Circle) :
    CarriesBasedLoopTorusGenus Phi (transportedFinitePointComplement Phi centers) := by
  obtain ⟨B⟩ := exists_avoidingAxisBase centers
  exact ⟨B.toBasedLoopCarrierWitness Phi⟩

end Submission.Topology
