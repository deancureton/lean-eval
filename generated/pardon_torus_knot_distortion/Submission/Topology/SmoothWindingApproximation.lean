import Submission.Topology.LoopCarrier
import Submission.Topology.SurfaceRegularValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth approximation of winding loops

The two real covering lifts of a `TransportedWindingLoop` split canonically into an affine
winding term and a continuous `2π`-periodic error.  This file isolates the remaining analytic
input as uniform smooth approximation of such real-valued periodic functions.  From that input
we construct a smooth real-angle parametrization of the transported loop, prove that its winding
pair is exactly unchanged, and use compact-range clearance to keep the new loop in any prescribed
open neighbourhood of the old loop.

The ambient curve is smooth because it is expressed through `transportedTorusPlaneMap`, whose
smoothness includes the smooth inverse time-one slice of the ambient isotopy.  Thus no smooth
structure on the subtype `transportedTorus Phi` is needed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology Metric
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus
open Submission.SurfaceRegularValue

/-! ## The isolated analytic approximation input -/

/-- A smooth periodic function uniformly approximating a prescribed function. -/
structure PeriodicSmoothApproximant (f : ℝ → ℝ) (period tolerance : ℝ) where
  toFun : ℝ → ℝ
  contDiff_toFun : ContDiff ℝ (⊤ : ℕ∞) toFun
  periodic_toFun : Function.Periodic toFun period
  dist_lt : ∀ t, dist (toFun t) (f t) < tolerance

/-- The exact analytic statement needed below.  Fourier/Stone--Weierstrass density in Mathlib
supplies the main approximation ingredient, but the pinned API does not package the resulting
real trigonometric polynomial as this periodic `ContDiff` approximation theorem. -/
def HasPeriodicSmoothApproximation : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f → Function.Periodic f (2 * Real.pi) →
    ∀ tolerance, 0 < tolerance →
      Nonempty (PeriodicSmoothApproximant f (2 * Real.pi) tolerance)

/-! ## Smooth angles and their exact winding -/

/-- Replace the periodic error of a covering lift by a chosen smooth periodic approximant. -/
def smoothedLiftAngle {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    {tolerance : ℝ}
    (A : PeriodicSmoothApproximant L.error (2 * Real.pi) tolerance) (t : ℝ) : ℝ :=
  (L.winding : ℝ) * t + L.angle 0 + A.toFun t

lemma contDiff_smoothedLiftAngle {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    {tolerance : ℝ}
    (A : PeriodicSmoothApproximant L.error (2 * Real.pi) tolerance) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothedLiftAngle L A) := by
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).add A.contDiff_toFun

lemma smoothedLiftAngle_add_period {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    {tolerance : ℝ}
    (A : PeriodicSmoothApproximant L.error (2 * Real.pi) tolerance) (t : ℝ) :
    smoothedLiftAngle L A (t + 2 * Real.pi) =
      smoothedLiftAngle L A t + (L.winding : ℝ) * (2 * Real.pi) := by
  rw [smoothedLiftAngle, smoothedLiftAngle, A.periodic_toFun]
  ring

lemma dist_smoothedLiftAngle_lt {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    {tolerance : ℝ}
    (A : PeriodicSmoothApproximant L.error (2 * Real.pi) tolerance) (t : ℝ) :
    dist (smoothedLiftAngle L A t) (L.angle t) < tolerance := by
  rw [Real.dist_eq]
  convert A.dist_lt t using 1
  rw [Real.dist_eq]
  congr 1
  unfold smoothedLiftAngle CircleLoopLift.error
  ring

/-! ## The smoothed transported curve -/

/-- Product-circle coordinates obtained from the two smoothed covering angles. -/
def smoothedTorusCoordinates {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance)
    (t : ℝ) : Circle × Circle :=
  (Circle.exp (smoothedLiftAngle L.first A₁ t),
    Circle.exp (smoothedLiftAngle L.second A₂ t))

lemma periodic_smoothedTorusCoordinates {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) :
    Function.Periodic (smoothedTorusCoordinates L A₁ A₂) (2 * Real.pi) := by
  intro t
  apply Prod.ext
  · apply Circle.exp_eq_exp.mpr
    exact ⟨L.first.winding, smoothedLiftAngle_add_period L.first A₁ t⟩
  · apply Circle.exp_eq_exp.mpr
    exact ⟨L.second.winding, smoothedLiftAngle_add_period L.second A₂ t⟩

/-- The smoothed coordinate curve mapped into the transported torus. -/
def smoothedTransportedCurve {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance)
    (t : ℝ) : transportedTorus Phi :=
  transportedTorusHomeomorph Phi (smoothedTorusCoordinates L A₁ A₂ t)

lemma continuous_smoothedTransportedCurve {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) :
    Continuous (smoothedTransportedCurve (Phi := Phi) L A₁ A₂) := by
  exact (transportedTorusHomeomorph Phi).continuous.comp
    ((Circle.exp.continuous.comp (contDiff_smoothedLiftAngle L.first A₁).continuous).prodMk
      (Circle.exp.continuous.comp (contDiff_smoothedLiftAngle L.second A₂).continuous))

lemma periodic_smoothedTransportedCurve {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) :
    Function.Periodic (smoothedTransportedCurve (Phi := Phi) L A₁ A₂)
      (2 * Real.pi) := by
  intro t
  exact congrArg (transportedTorusHomeomorph Phi)
    (periodic_smoothedTorusCoordinates L A₁ A₂ t)

lemma coe_smoothedTransportedCurve {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) (t : ℝ) :
    (smoothedTransportedCurve (Phi := Phi) L A₁ A₂ t : R3) =
      transportedTorusPlaneMap Phi
        (smoothedLiftAngle L.first A₁ t, smoothedLiftAngle L.second A₂ t) := by
  change transportedTorusMap Phi
      (Circle.exp (smoothedLiftAngle L.first A₁ t),
        Circle.exp (smoothedLiftAngle L.second A₂ t)) = _
  rw [
    transportedTorusMap, transportedTorusPlaneMap, Function.uncurry_apply_pair,
    circleTorusMap_exp_exp, ambientHomeomorph_symm_apply]

lemma contDiff_coe_smoothedTransportedCurve {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun t ↦ (smoothedTransportedCurve (Phi := Phi) L A₁ A₂ t : R3)) := by
  rw [show (fun t ↦ (smoothedTransportedCurve (Phi := Phi) L A₁ A₂ t : R3)) =
      fun t ↦ transportedTorusPlaneMap Phi
        (smoothedLiftAngle L.first A₁ t, smoothedLiftAngle L.second A₂ t) by
    funext t
    exact coe_smoothedTransportedCurve L A₁ A₂ t]
  exact (transportedTorusPlaneMap_contDiff Phi).comp
    ((contDiff_smoothedLiftAngle L.first A₁).prodMk
      (contDiff_smoothedLiftAngle L.second A₂))

/-! ## Metric control and compact-range clearance -/

/-- Passing from real angles to the unit circle does not increase distance. -/
lemma dist_circleExp_le (x y : ℝ) :
    dist (Circle.exp x) (Circle.exp y) ≤ dist x y := by
  rw [show dist (Circle.exp x) (Circle.exp y) =
      dist (Circle.exp x : ℂ) (Circle.exp y : ℂ) from
    (isometry_subtype_coe.dist_eq _ _).symm, Complex.dist_eq, Real.dist_eq]
  change ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤ |x - y|
  calc
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ =
        ‖Complex.exp (y * Complex.I) *
          (Complex.exp ((x - y) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((x - y) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ ‖x - y‖ := by
      simpa only [Complex.ofReal_sub, mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))
    _ = |x - y| := Real.norm_eq_abs _

lemma dist_smoothedTorusCoordinates_lt {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance)
    (t : ℝ) :
    dist (smoothedTorusCoordinates L A₁ A₂ t) (gamma t) < tolerance := by
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · calc
      dist (Circle.exp (smoothedLiftAngle L.first A₁ t)) (gamma t).1 =
          dist (Circle.exp (smoothedLiftAngle L.first A₁ t))
            (Circle.exp (L.first.angle t)) := by rw [L.first.exp_angle]
      _ ≤ dist (smoothedLiftAngle L.first A₁ t) (L.first.angle t) :=
        dist_circleExp_le _ _
      _ < tolerance := dist_smoothedLiftAngle_lt L.first A₁ t
  · calc
      dist (Circle.exp (smoothedLiftAngle L.second A₂ t)) (gamma t).2 =
          dist (Circle.exp (smoothedLiftAngle L.second A₂ t))
            (Circle.exp (L.second.angle t)) := by rw [L.second.exp_angle]
      _ ≤ dist (smoothedLiftAngle L.second A₂ t) (L.second.angle t) :=
        dist_circleExp_le _ _
      _ < tolerance := dist_smoothedLiftAngle_lt L.second A₂ t

/-- A continuous map from the compact product of circles has a uniform input tolerance for every
positive output tolerance. -/
lemma exists_transport_coordinate_tolerance (Phi : AmbientIsotopy)
    {outputTolerance : ℝ} (houtput : 0 < outputTolerance) :
    ∃ inputTolerance > 0,
      ∀ ⦃z w : Circle × Circle⦄, dist z w < inputTolerance →
        dist (transportedTorusHomeomorph Phi z)
          (transportedTorusHomeomorph Phi w) < outputTolerance := by
  exact Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous
      (transportedTorusHomeomorph Phi).continuous) outputTolerance houtput

lemma transported_curve_eq_exp_lifts {Phi : AmbientIsotopy}
    {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s) (t : ℝ) :
    transportedTorusHomeomorph Phi
        (Circle.exp (L.lift.first.angle t), Circle.exp (L.lift.second.angle t)) =
      L.curve t := by
  apply (transportedTorusHomeomorph Phi).symm.injective
  rw [(transportedTorusHomeomorph Phi).symm_apply_apply]
  exact Prod.ext (L.lift.first.exp_angle t) (L.lift.second.exp_angle t)

lemma dist_smoothedTransportedCurve_lt {Phi : AmbientIsotopy}
    {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s)
    {outputTolerance inputTolerance : ℝ}
    (hcontrol : ∀ ⦃z w : Circle × Circle⦄, dist z w < inputTolerance →
      dist (transportedTorusHomeomorph Phi z)
        (transportedTorusHomeomorph Phi w) < outputTolerance)
    (A₁ : PeriodicSmoothApproximant L.lift.first.error
      (2 * Real.pi) inputTolerance)
    (A₂ : PeriodicSmoothApproximant L.lift.second.error
      (2 * Real.pi) inputTolerance) (t : ℝ) :
    dist (smoothedTransportedCurve (Phi := Phi) L.lift A₁ A₂ t)
      (L.curve t) < outputTolerance := by
  rw [← transported_curve_eq_exp_lifts L t]
  apply hcontrol
  have h := dist_smoothedTorusCoordinates_lt L.lift A₁ A₂ t
  have hcoordinates : transportedLoopCoordinates Phi L.curve t =
      (Circle.exp (L.lift.first.angle t), Circle.exp (L.lift.second.angle t)) :=
    Prod.ext (L.lift.first.exp_angle t).symm (L.lift.second.exp_angle t).symm
  rw [hcoordinates] at h
  exact h

/-! ## Packaging the result as a winding loop -/

/-- The covering lift naturally carried by the smoothed transported curve. -/
def smoothedTransportedLoopLift {Phi : AmbientIsotopy}
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    {tolerance : ℝ}
    (A₁ : PeriodicSmoothApproximant L.first.error (2 * Real.pi) tolerance)
    (A₂ : PeriodicSmoothApproximant L.second.error (2 * Real.pi) tolerance) :
    TorusLoopLift (transportedLoopCoordinates Phi
      (smoothedTransportedCurve (Phi := Phi) L A₁ A₂)) where
  first := {
    angle := smoothedLiftAngle L.first A₁
    continuous_angle := (contDiff_smoothedLiftAngle L.first A₁).continuous
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, smoothedTransportedCurve,
        smoothedTorusCoordinates]
    winding := L.first.winding
    angle_add_period := smoothedLiftAngle_add_period L.first A₁
  }
  second := {
    angle := smoothedLiftAngle L.second A₂
    continuous_angle := (contDiff_smoothedLiftAngle L.second A₂).continuous
    exp_angle := fun t ↦ by
      simp [transportedLoopCoordinates, smoothedTransportedCurve,
        smoothedTorusCoordinates]
    winding := L.second.winding
    angle_add_period := smoothedLiftAngle_add_period L.second A₂
  }

/-- A smooth-angle approximation, together with its ambient smoothness, exact winding pair, and
uniform closeness to the original curve. -/
structure SmoothWindingApproximation {Phi : AmbientIsotopy}
    {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s)
    (U : Set (transportedTorus Phi)) (ambientTolerance : ℝ) where
  loop : TransportedWindingLoop Phi U
  first_angle_contDiff : ContDiff ℝ (⊤ : ℕ∞) loop.lift.first.angle
  second_angle_contDiff : ContDiff ℝ (⊤ : ℕ∞) loop.lift.second.angle
  ambient_curve_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (loop.curve t : R3))
  windingPair_eq : loop.windingPair = L.windingPair
  dist_lt : ∀ t, dist (loop.curve t) (L.curve t) < ambientTolerance

/-- Assuming only the isolated periodic approximation principle, every transported winding loop
whose range lies in an open set has an arbitrarily close smooth-angle representative in that same
open set.  Its ambient `R3` parametrization is smooth and its winding pair is definitionally
unchanged. -/
theorem exists_smoothWindingApproximation
    (happrox : HasPeriodicSmoothApproximation)
    {Phi : AmbientIsotopy} {U : Set (transportedTorus Phi)}
    (hU : IsOpen U) (L : TransportedWindingLoop Phi U)
    {ambientTolerance : ℝ} (hambientTolerance : 0 < ambientTolerance) :
    Nonempty (SmoothWindingApproximation L U ambientTolerance) := by
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
  obtain ⟨A₁⟩ := happrox L.lift.first.error herror₁
    L.lift.first.error_periodic inputTolerance hinput
  obtain ⟨A₂⟩ := happrox L.lift.second.error herror₂
    L.lift.second.error_periodic inputTolerance hinput
  let curve := smoothedTransportedCurve (Phi := Phi) L.lift A₁ A₂
  have hclose (t : ℝ) : dist (curve t) (L.curve t) < outputTolerance :=
    dist_smoothedTransportedCurve_lt L hcontrol A₁ A₂ t
  have hmem (t : ℝ) : curve t ∈ U := by
    apply hthickening
    rw [mem_thickening_iff]
    exact ⟨L.curve t, ⟨t, rfl⟩, (hclose t).trans_le (min_le_left _ _)⟩
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
    windingPair_eq := ?_
    dist_lt := ?_
  }⟩
  · rfl
  · intro t
    exact (hclose t).trans_le (min_le_right _ _)

end Submission.Topology
