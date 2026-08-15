import Submission.Topology.InnermostCircleSurgery

/-!
# Loops contained in an inessential embedded torus circle

An embedded circle on the transported torus has a homeomorphic inverse on its range.  Hence a
continuous periodic loop whose ambient range lies in that circle factors continuously through
the circle parameter.  If the embedded circle has winding pair `(0, 0)`, its two real covering
lifts are genuinely periodic.  Composing them with a covering lift of the factor loop gives
periodic real lifts of the contained loop, so both of its winding coordinates vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy} {s : Set (transportedTorus Phi)}

namespace EmbeddedTorusIntersectionCircle

/-- The ambient curve of a loop, bundled in the range of an embedded circle containing it. -/
def rangeCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    ℝ → Set.range C.circle :=
  fun t ↦ ⟨L.curve t, hsub ⟨t, rfl⟩⟩

theorem continuous_rangeCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    Continuous (C.rangeCurve L hsub) := by
  exact (continuous_subtype_val.comp L.continuous_curve).subtype_mk _

theorem periodic_rangeCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    Function.Periodic (C.rangeCurve L hsub) (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  change (L.curve (t + 2 * Real.pi) : R3) = L.curve t
  exact congrArg Subtype.val (L.periodic_curve t)

/-- The unique circle parameter of a loop contained in the range of an embedded circle. -/
def factorCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) : ℝ → Circle :=
  fun t ↦ C.isEmbedding.toHomeomorph.symm (C.rangeCurve L hsub t)

theorem continuous_factorCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    Continuous (C.factorCurve L hsub) :=
  C.isEmbedding.toHomeomorph.symm.continuous.comp (C.continuous_rangeCurve L hsub)

theorem periodic_factorCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    Function.Periodic (C.factorCurve L hsub) (2 * Real.pi) := by
  intro t
  exact congrArg C.isEmbedding.toHomeomorph.symm (C.periodic_rangeCurve L hsub t)

theorem circle_factorCurve (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) (t : ℝ) :
    C.circle (C.factorCurve L hsub t) = L.curve t := by
  exact congrArg Subtype.val
    (C.isEmbedding.toHomeomorph.apply_symm_apply (C.rangeCurve L hsub t))

/-- A covering lift of the factor through the embedded circle. -/
def factorCurveLift (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) :
    CircleLoopLift (C.factorCurve L hsub) :=
  Classical.choice <| exists_circleLoopLift _
    (C.continuous_factorCurve L hsub) (C.periodic_factorCurve L hsub)

theorem transportedLoopCoordinates_eq_at_factorCurveLift
    (C : EmbeddedTorusIntersectionCircle Phi) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle) (t : ℝ) :
    transportedLoopCoordinates Phi L.curve t =
      transportedLoopCoordinates Phi C.windingLoop.curve
        ((C.factorCurveLift L hsub).angle t) := by
  apply congrArg (transportedTorusHomeomorph Phi).symm
  apply Subtype.ext
  calc
    (L.curve t : R3) = C.circle (C.factorCurve L hsub t) :=
      (C.circle_factorCurve L hsub t).symm
    _ = C.circle (Circle.exp ((C.factorCurveLift L hsub).angle t)) := by
      rw [(C.factorCurveLift L hsub).exp_angle]
    _ = C.windingLoop.curve ((C.factorCurveLift L hsub).angle t) :=
      C.parametrization _

/-- The lift of a contained loop obtained by composing the embedded circle's lift with a lift of
the factor parameter.  When the embedded circle has zero winding, both composed angles are
periodic, so this lift has winding pair `(0, 0)`. -/
def zeroWindingLiftOfContainedLoop (C : EmbeddedTorusIntersectionCircle Phi)
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    TorusLoopLift (transportedLoopCoordinates Phi L.curve) := by
  have hfirst : C.windingLoop.lift.first.winding = 0 := by
    simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair] using
      congrArg Prod.fst hzero
  have hsecond : C.windingLoop.lift.second.winding = 0 := by
    simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair] using
      congrArg Prod.snd hzero
  have hfirstPeriodic : Function.Periodic C.windingLoop.lift.first.angle (2 * Real.pi) := by
    intro u
    simpa [hfirst] using C.windingLoop.lift.first.angle_add_period u
  have hsecondPeriodic : Function.Periodic C.windingLoop.lift.second.angle (2 * Real.pi) := by
    intro u
    simpa [hsecond] using C.windingLoop.lift.second.angle_add_period u
  let A := C.factorCurveLift L hsub
  exact {
    first := {
      angle := fun t ↦ C.windingLoop.lift.first.angle (A.angle t)
      continuous_angle := C.windingLoop.lift.first.continuous_angle.comp A.continuous_angle
      exp_angle := fun t ↦ by
        rw [C.windingLoop.lift.first.exp_angle]
        exact congrArg Prod.fst (C.transportedLoopCoordinates_eq_at_factorCurveLift L hsub t).symm
      winding := 0
      angle_add_period := fun t ↦ by
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [A.angle_add_period]
        exact hfirstPeriodic.int_mul A.winding (A.angle t)
    }
    second := {
      angle := fun t ↦ C.windingLoop.lift.second.angle (A.angle t)
      continuous_angle := C.windingLoop.lift.second.continuous_angle.comp A.continuous_angle
      exp_angle := fun t ↦ by
        rw [C.windingLoop.lift.second.exp_angle]
        exact congrArg Prod.snd (C.transportedLoopCoordinates_eq_at_factorCurveLift L hsub t).symm
      winding := 0
      angle_add_period := fun t ↦ by
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [A.angle_add_period]
        exact hsecondPeriodic.int_mul A.winding (A.angle t)
    }
  }

/-- Every winding loop ambiently contained in an inessential embedded torus circle has zero
winding pair.  No connectedness or separately supplied factor map is needed: embedding produces
the continuous factor map from the range inclusion. -/
theorem windingPair_eq_zero_of_range_subset_of_windingPair_eq_zero
    (C : EmbeddedTorusIntersectionCircle Phi) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range (fun t ↦ (L.curve t : R3)) ⊆ Set.range C.circle)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    L.windingPair = (0, 0) := by
  have heq := L.lift.windingPair_eq (C.zeroWindingLiftOfContainedLoop L hsub hzero)
  change L.lift.windingPair = (0, 0)
  calc
    L.lift.windingPair =
        (C.zeroWindingLiftOfContainedLoop L hsub hzero).windingPair := heq
    _ = (0, 0) := by
      rw [TorusLoopLift.windingPair]
      rfl

end EmbeddedTorusIntersectionCircle

end Submission.Topology
