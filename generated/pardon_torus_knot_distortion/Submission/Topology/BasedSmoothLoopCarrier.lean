import Submission.Topology.BasedLoopCarrier
import Submission.Topology.FourierSmoothApproximation
import Submission.Topology.SmoothLoopCarrier

/-!
# Basepoint-preserving smooth loop carriers

Fourier smoothing does not automatically fix a prescribed parameter value.  For a covering
lift, its periodic error is zero at parameter zero.  We approximate that error at half the
desired tolerance and subtract the approximant's value at zero.  The corrected approximant is
still smooth and periodic, is exactly zero at zero, and remains within the full tolerance.

Applying this correction to both circle coordinates preserves the transported loop's point at
parameter zero exactly, as well as its winding pair and containment in an open set.  Smoothing
the two members of a based carrier separately therefore preserves their common basepoint.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology Metric
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-! ## Constant-corrected periodic approximation -/

/-- Subtracting the value at zero from a half-tolerance approximant gives a full-tolerance
approximant which is exactly zero at zero, provided the target function is zero there. -/
def zeroCorrectedPeriodicSmoothApproximant {f : ℝ → ℝ} {period tolerance : ℝ}
    (A : PeriodicSmoothApproximant f period (tolerance / 2))
    (hfzero : f 0 = 0) : PeriodicSmoothApproximant f period tolerance where
  toFun := fun t ↦ A.toFun t - A.toFun 0
  contDiff_toFun := A.contDiff_toFun.sub contDiff_const
  periodic_toFun := by
    intro t
    change A.toFun (t + period) - A.toFun 0 = A.toFun t - A.toFun 0
    rw [A.periodic_toFun]
  dist_lt := by
    intro t
    have ht : |A.toFun t - f t| < tolerance / 2 := by
      simpa only [Real.dist_eq] using A.dist_lt t
    have hzero : |A.toFun 0| < tolerance / 2 := by
      simpa only [Real.dist_eq, hfzero, sub_zero] using A.dist_lt 0
    rw [Real.dist_eq]
    calc
      |(A.toFun t - A.toFun 0) - f t| = |(A.toFun t - f t) - A.toFun 0| := by
        congr 1
        ring
      _ ≤ |A.toFun t - f t| + |A.toFun 0| := abs_sub _ _
      _ < tolerance / 2 + tolerance / 2 := add_lt_add ht hzero
      _ = tolerance := by ring

@[simp] lemma zeroCorrectedPeriodicSmoothApproximant_zero
    {f : ℝ → ℝ} {period tolerance : ℝ}
    (A : PeriodicSmoothApproximant f period (tolerance / 2))
    (hfzero : f 0 = 0) :
    (zeroCorrectedPeriodicSmoothApproximant A hfzero).toFun 0 = 0 := by
  change A.toFun 0 - A.toFun 0 = 0
  ring

lemma circleLoopLift_error_zero {gamma : ℝ → Circle} (L : CircleLoopLift gamma) :
    L.error 0 = 0 := by
  simp [CircleLoopLift.error]

/-! ## One based loop -/

/-- A smooth approximation which preserves both the exact winding pair and parameter-zero
basepoint of the original transported winding loop. -/
structure BasedSmoothWindingApproximation {Phi : AmbientIsotopy}
    {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s)
    (U : Set (transportedTorus Phi)) (ambientTolerance : ℝ)
    extends SmoothWindingApproximation L U ambientTolerance where
  curve_zero_eq : loop.curve 0 = L.curve 0

/-- Every winding loop in an open set has a smooth, uniformly close representative with the same
winding pair and exactly the same point at parameter zero. -/
theorem exists_basedSmoothWindingApproximation_unconditional
    {Phi : AmbientIsotopy} {U : Set (transportedTorus Phi)}
    (hU : IsOpen U) (L : TransportedWindingLoop Phi U)
    {ambientTolerance : ℝ} (hambientTolerance : 0 < ambientTolerance) :
    Nonempty (BasedSmoothWindingApproximation L U ambientTolerance) := by
  have hperiod : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcompact : IsCompact (range L.curve) :=
    L.periodic_curve.compact_of_continuous hperiod L.continuous_curve
  have hrange : range L.curve ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact L.curve_mem t
  obtain ⟨clearance, hclearance, hthickening⟩ :=
    hcompact.exists_thickening_subset_open hU hrange
  let outputTolerance := min clearance ambientTolerance
  have houtput : 0 < outputTolerance := lt_min hclearance hambientTolerance
  obtain ⟨inputTolerance, hinput, hcontrol⟩ :=
    exists_transport_coordinate_tolerance Phi houtput
  have herror₁ : Continuous L.lift.first.error := by
    exact L.lift.first.continuous_angle.sub
      ((continuous_const.mul continuous_id).add continuous_const)
  have herror₂ : Continuous L.lift.second.error := by
    exact L.lift.second.continuous_angle.sub
      ((continuous_const.mul continuous_id).add continuous_const)
  obtain ⟨raw₁⟩ := hasPeriodicSmoothApproximation_fourier L.lift.first.error herror₁
    L.lift.first.error_periodic (inputTolerance / 2) (half_pos hinput)
  obtain ⟨raw₂⟩ := hasPeriodicSmoothApproximation_fourier L.lift.second.error herror₂
    L.lift.second.error_periodic (inputTolerance / 2) (half_pos hinput)
  let A₁ := zeroCorrectedPeriodicSmoothApproximant raw₁
    (circleLoopLift_error_zero L.lift.first)
  let A₂ := zeroCorrectedPeriodicSmoothApproximant raw₂
    (circleLoopLift_error_zero L.lift.second)
  let curve := smoothedTransportedCurve (Phi := Phi) L.lift A₁ A₂
  have hclose (t : ℝ) : dist (curve t) (L.curve t) < outputTolerance :=
    dist_smoothedTransportedCurve_lt L hcontrol A₁ A₂ t
  have hmem (t : ℝ) : curve t ∈ U := by
    apply hthickening
    rw [mem_thickening_iff]
    exact ⟨L.curve t, ⟨t, rfl⟩, (hclose t).trans_le (min_le_left _ _)⟩
  have hcurvezero : curve 0 = L.curve 0 := by
    rw [← transported_curve_eq_exp_lifts L 0]
    apply congrArg (transportedTorusHomeomorph Phi)
    apply Prod.ext
    · simp [smoothedTorusCoordinates, smoothedLiftAngle, A₁]
    · simp [smoothedTorusCoordinates, smoothedLiftAngle, A₂]
  let newLoop : TransportedWindingLoop Phi U := {
    curve := curve
    continuous_curve := continuous_smoothedTransportedCurve L.lift A₁ A₂
    periodic_curve := periodic_smoothedTransportedCurve L.lift A₁ A₂
    curve_mem := hmem
    lift := smoothedTransportedLoopLift L.lift A₁ A₂
  }
  refine ⟨{
    loop := newLoop
    first_angle_contDiff := contDiff_smoothedLiftAngle L.lift.first A₁
    second_angle_contDiff := contDiff_smoothedLiftAngle L.lift.second A₂
    ambient_curve_contDiff := contDiff_coe_smoothedTransportedCurve L.lift A₁ A₂
    windingPair_eq := rfl
    dist_lt := ?_
    curve_zero_eq := hcurvezero
  }⟩
  intro t
  exact (hclose t).trans_le (min_le_right _ _)

/-! ## Smooth based carrier pairs -/

/-- Two ambient-smooth independent winding loops which pass through one exact common basepoint. -/
structure SmoothBasedLoopCarrierWitness (Phi : AmbientIsotopy) (a : Set R3) where
  basepoint : transportedTorus Phi
  first : TransportedWindingLoop Phi (transportedTorusPart Phi a)
  second : TransportedWindingLoop Phi (transportedTorusPart Phi a)
  first_zero : first.curve 0 = basepoint
  second_zero : second.curve 0 = basepoint
  first_firstAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) first.lift.first.angle
  first_secondAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) first.lift.second.angle
  second_firstAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) second.lift.first.angle
  second_secondAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) second.lift.second.angle
  first_ambientCurve_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (first.curve t : R3))
  second_ambientCurve_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (second.curve t : R3))
  independent : windingDet first.windingPair.1 first.windingPair.2
    second.windingPair.1 second.windingPair.2 ≠ 0

namespace SmoothBasedLoopCarrierWitness

variable {Phi : AmbientIsotopy} {a : Set R3}

/-- Forgetting smoothness gives a based carrier witness. -/
def toBasedLoopCarrierWitness (W : SmoothBasedLoopCarrierWitness Phi a) :
    BasedLoopCarrierWitness Phi (transportedTorusPart Phi a) where
  basepoint := W.basepoint
  first := W.first
  second := W.second
  first_zero := W.first_zero
  second_zero := W.second_zero
  independent := W.independent

/-- Forgetting the basepoint gives the previously defined smooth carrier witness. -/
def toSmoothLoopCarrierWitness (W : SmoothBasedLoopCarrierWitness Phi a) :
    SmoothLoopCarrierWitness Phi a where
  first := W.first
  second := W.second
  first_firstAngle_contDiff := W.first_firstAngle_contDiff
  first_secondAngle_contDiff := W.first_secondAngle_contDiff
  second_firstAngle_contDiff := W.second_firstAngle_contDiff
  second_secondAngle_contDiff := W.second_secondAngle_contDiff
  first_ambientCurve_contDiff := W.first_ambientCurve_contDiff
  second_ambientCurve_contDiff := W.second_ambientCurve_contDiff
  independent := W.independent

end SmoothBasedLoopCarrierWitness

/-- Every based carrier in an open ambient set has an ambient-smooth witness through the exact
same common basepoint, with both winding pairs unchanged. -/
theorem exists_smoothBasedLoopCarrierWitness_of_isOpen
    {Phi : AmbientIsotopy} {a : Set R3} (ha : IsOpen a)
    (hcarrier : CarriesTransportedBasedLoopGenus Phi a) :
    Nonempty (SmoothBasedLoopCarrierWitness Phi a) := by
  obtain ⟨W⟩ := hcarrier
  have hopen : IsOpen (transportedTorusPart Phi a) :=
    ha.preimage continuous_subtype_val
  obtain ⟨A₁⟩ := exists_basedSmoothWindingApproximation_unconditional
    hopen W.first (ambientTolerance := 1) zero_lt_one
  obtain ⟨A₂⟩ := exists_basedSmoothWindingApproximation_unconditional
    hopen W.second (ambientTolerance := 1) zero_lt_one
  refine ⟨{
    basepoint := W.basepoint
    first := A₁.loop
    second := A₂.loop
    first_zero := A₁.curve_zero_eq.trans W.first_zero
    second_zero := A₂.curve_zero_eq.trans W.second_zero
    first_firstAngle_contDiff := A₁.first_angle_contDiff
    first_secondAngle_contDiff := A₁.second_angle_contDiff
    second_firstAngle_contDiff := A₂.first_angle_contDiff
    second_secondAngle_contDiff := A₂.second_angle_contDiff
    first_ambientCurve_contDiff := A₁.ambient_curve_contDiff
    second_ambientCurve_contDiff := A₂.ambient_curve_contDiff
    independent := ?_
  }⟩
  rw [A₁.windingPair_eq, A₂.windingPair_eq]
  exact W.independent

/-- Every positive based-loop-carrying oriented box contains a smooth based witness. -/
theorem exists_smoothBasedLoopCarrierWitness_of_orientedBasedLoopCarrier
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : OrientedBasedLoopCarrier Phi frame c r) :
    Nonempty (SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)) :=
  exists_smoothBasedLoopCarrierWitness_of_isOpen
    (isOpen_orientedBox frame c hr) hcarrier

end Submission.Topology
