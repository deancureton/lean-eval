import Submission.Topology.BasedLoopCarrier
import Submission.Topology.ThreeBoundaryOuterDiskRegularCarrier

/-!
# Genus vanishes in a covering-injective plane neighborhood

If a subset of the transported torus is contained in the projection of an open set on which the
torus covering projection is injective, every periodic loop in that subset has a periodic lift to
the covering plane.  Coordinatewise uniqueness of circle lifts then forces both winding numbers
to vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

namespace TransportedWindingLoop

/-- A loop contained in the projection of one covering-injective open plane set has zero winding.

The openness assumption turns the restricted covering projection into an open embedding.  Its
inverse gives a continuous periodic plane lift; no fundamental-group classification is used. -/
theorem windingPair_eq_zero_of_subset_coveringProjection_image
    {s : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi s)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (hs : s ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    L.windingPair = (0, 0) := by
  let projection := EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
  let projectionOn : U → transportedTorus Phi := fun x ↦ projection x
  have hprojectionOn : IsOpenEmbedding projectionOn := by
    apply IsLocalHomeomorph.isOpenEmbedding_of_injective
    · exact
        (EmbeddedTorusIntersectionCircle.isLocalHomeomorph_torusCoveringProjectionToTorus Phi).comp
          hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    · intro x y hxy
      exact Subtype.ext (hinj x.2 y.2 hxy)
  let e := hprojectionOn.isEmbedding.toHomeomorph
  have hcurveRange (t : ℝ) : L.curve t ∈ Set.range projectionOn := by
    obtain ⟨x, hxU, hx⟩ := hs (L.curve_mem t)
    exact ⟨⟨x, hxU⟩, hx⟩
  let curveInRange (t : ℝ) : Set.range projectionOn :=
    ⟨L.curve t, hcurveRange t⟩
  have hcurveInRange : Continuous curveInRange :=
    L.continuous_curve.subtype_mk _
  let planeLift (t : ℝ) : U := e.symm (curveInRange t)
  have hplaneLift : Continuous planeLift := e.symm.continuous.comp hcurveInRange
  have hplaneLiftPeriodic : Function.Periodic planeLift (2 * Real.pi) := by
    intro t
    apply e.injective
    rw [show e (planeLift (t + 2 * Real.pi)) = curveInRange (t + 2 * Real.pi) by
      exact e.apply_symm_apply _,
      show e (planeLift t) = curveInRange t by exact e.apply_symm_apply _]
    exact Subtype.ext (L.periodic_curve t)
  have hprojection (t : ℝ) : projection (planeLift t) = L.curve t := by
    have he := e.apply_symm_apply (curveInRange t)
    exact congrArg Subtype.val he
  have hcoordinates (t : ℝ) :
      (Circle.exp ((planeLift t : TorusCoveringPlane) 0),
        Circle.exp ((planeLift t : TorusCoveringPlane) 1)) =
        transportedLoopCoordinates Phi L.curve t := by
    have h := congrArg (transportedTorusHomeomorph Phi).symm (hprojection t)
    simpa [projection, EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus,
      transportedLoopCoordinates] using h
  let periodicLift : TorusLoopLift (transportedLoopCoordinates Phi L.curve) := {
    first := {
      angle := fun t ↦ (planeLift t : TorusCoveringPlane) 0
      continuous_angle :=
        (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 0).comp
          (continuous_subtype_val.comp hplaneLift)
      exp_angle := fun t ↦ congrArg Prod.fst (hcoordinates t)
      winding := 0
      angle_add_period := fun t ↦ by
        rw [hplaneLiftPeriodic]
        simp
    }
    second := {
      angle := fun t ↦ (planeLift t : TorusCoveringPlane) 1
      continuous_angle :=
        (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 1).comp
          (continuous_subtype_val.comp hplaneLift)
      exp_angle := fun t ↦ congrArg Prod.snd (hcoordinates t)
      winding := 0
      angle_add_period := fun t ↦ by
        rw [hplaneLiftPeriodic]
        simp
    }
  }
  change L.lift.windingPair = (0, 0)
  rw [L.lift.windingPair_eq periodicLift]
  rfl

end TransportedWindingLoop

/-- The projection of one covering-injective open plane set cannot carry arbitrary loop genus. -/
theorem not_carriesLoopTorusGenus_of_subset_coveringProjection_image
    (s : Set (transportedTorus Phi))
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (hs : s ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ¬ CarriesLoopTorusGenus Phi s := by
  rintro ⟨W⟩
  have hfirst := W.first.windingPair_eq_zero_of_subset_coveringProjection_image U hU hinj hs
  have hsecond := W.second.windingPair_eq_zero_of_subset_coveringProjection_image U hU hinj hs
  apply W.independent
  simp [windingDet, hfirst, hsecond]

/-- The same covering-injective obstruction rules out the stronger based carrier predicate. -/
theorem not_carriesBasedLoopTorusGenus_of_subset_coveringProjection_image
    (s : Set (transportedTorus Phi))
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (hs : s ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ¬ CarriesBasedLoopTorusGenus Phi s :=
  fun hcarrier ↦
    not_carriesLoopTorusGenus_of_subset_coveringProjection_image s U hU hinj hs
      hcarrier.toCarriesLoopTorusGenus

namespace ThreeBoundaryRegularClosedCarrierData

variable {Q : ThreeBoundaryPairOfPantsCarrier Phi}

/-- Covering-injectivity replaces the pair-of-pants boundary-generation premise in the regular
closed-carrier constructor. -/
theorem toThreeBoundaryPairOfPantsTopology_of_subset_coveringProjection_image
    (R : ThreeBoundaryRegularClosedCarrierData Q)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (hQ : Q.carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ThreeBoundaryPairOfPantsTopology Q := by
  apply R.toThreeBoundaryPairOfPantsTopology
  intro L
  refine ⟨0, ?_⟩
  rw [L.windingPair_eq_zero_of_subset_coveringProjection_image U hU hinj hQ]
  apply Prod.ext <;> simp [Q.zeroWinding]

/-- A regular closed three-boundary trace contained in one covering-injective plane image lies
in one of its three canonical zero-winding disks. -/
theorem exists_canonicalDisk_contains_carrier_of_subset_coveringProjection_image
    (R : ThreeBoundaryRegularClosedCarrierData Q)
    (U : Set TorusCoveringPlane) (hU : IsOpen U)
    (hinj : Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U)
    (hQ : Q.carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U) :
    ∃ i, Q.carrier ⊆ Q.disk i :=
  (R.toThreeBoundaryPairOfPantsTopology_of_subset_coveringProjection_image U hU hinj hQ)
    |>.exists_canonicalDisk_contains_carrier

end ThreeBoundaryRegularClosedCarrierData

end Submission.Topology
