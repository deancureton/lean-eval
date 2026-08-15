import Submission.Topology.FourierSmoothApproximation
import Submission.LoopNested

/-!
# Smooth witnesses for arbitrary-loop carriers

An open ambient carrier containing two independent continuous winding loops also contains two
independent winding loops whose real covering angles and ambient `R3` curves are `C∞`.  The
winding pairs are preserved exactly by Fourier smoothing, so independence is unchanged.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- Two smooth winding loops with independent winding pairs in the transported-torus part of an
ambient set. -/
structure SmoothLoopCarrierWitness (Phi : AmbientIsotopy) (a : Set R3) where
  first : TransportedWindingLoop Phi (transportedTorusPart Phi a)
  second : TransportedWindingLoop Phi (transportedTorusPart Phi a)
  first_firstAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) first.lift.first.angle
  first_secondAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) first.lift.second.angle
  second_firstAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) second.lift.first.angle
  second_secondAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) second.lift.second.angle
  first_ambientCurve_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (first.curve t : R3))
  second_ambientCurve_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ (second.curve t : R3))
  independent : windingDet first.windingPair.1 first.windingPair.2
    second.windingPair.1 second.windingPair.2 ≠ 0

/-- Every arbitrary-loop carrier in an open ambient set has a smooth witness with exactly the
same two winding pairs. -/
theorem exists_smoothLoopCarrierWitness_of_isOpen
    {Phi : AmbientIsotopy} {a : Set R3} (ha : IsOpen a)
    (hcarrier : CarriesTransportedLoopGenus Phi a) :
    Nonempty (SmoothLoopCarrierWitness Phi a) := by
  obtain ⟨W⟩ := hcarrier
  have hopen : IsOpen (transportedTorusPart Phi a) :=
    ha.preimage continuous_subtype_val
  obtain ⟨A₁⟩ := exists_smoothWindingApproximation_unconditional
    hopen W.first (ambientTolerance := 1) zero_lt_one
  obtain ⟨A₂⟩ := exists_smoothWindingApproximation_unconditional
    hopen W.second (ambientTolerance := 1) zero_lt_one
  refine ⟨{
    first := A₁.loop
    second := A₂.loop
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

/-- A positive-scale oriented box is open. -/
lemma isOpen_orientedBox (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) :
    IsOpen (orientedBox frame c r) := by
  have heq : orientedBox frame c r =
      orientedBoxGauge frame c ⁻¹' Iio r := by
    ext x
    exact mem_orientedBox_iff_gauge_lt hr
  rw [heq]
  exact isOpen_Iio.preimage (continuous_orientedBoxGauge frame c)

/-- Every oriented-loop carrier at positive scale admits two ambient-smooth winding loops in the
same open box, with the same independent winding pairs. -/
theorem exists_smoothLoopCarrierWitness_of_orientedLoopCarrier
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : OrientedLoopCarrier Phi frame c r) :
    Nonempty (SmoothLoopCarrierWitness Phi (orientedBox frame c r)) :=
  exists_smoothLoopCarrierWitness_of_isOpen
    (isOpen_orientedBox frame c hr) hcarrier

end Submission.Topology
