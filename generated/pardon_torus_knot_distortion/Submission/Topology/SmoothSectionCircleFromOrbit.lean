import Submission.Topology.RegularLevelTangentODE
import Submission.Topology.SmoothEssentialSectionCircle
import Submission.Topology.InessentialSliceCircle
import Submission.Coarea.PlaneSlice
import Submission.Torus.AmbientTransfer
import Submission.Coarea.SurfaceRegularBasedDoubleBubbleSelection

/-!
# Smooth section circles from complete rotated-gradient orbits

The topological circle homeomorphism obtained from a cyclic orbit forgets the real covering path
which produced it. This module retains that path and derives its deck monodromy by covering-lift
uniqueness. Smoothness, embeddedness, exact component range, the explicit torus lift, and root
transversality at a regular cutting level are then derived rather than assumed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

end Submission.Topology

namespace Submission.SurfaceRegularValue.RegularComponentCompleteOrbit

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open Submission.PardonDistortion
open Submission.Topology
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)}

/-- The affine rescaling which turns the orbit's chosen cyclic period into `2π`. -/
def standardTime (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) : ℝ :=
  t * ((2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period)

/-- The original lifted rotated-gradient orbit, with standard `2π` parameter. -/
def standardLift (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) : Plane :=
  O.liftedIntegral.curve (O.standardTime t)

/-- The corresponding component-valued orbit with standard `2π` parameter. -/
def standardComponentCurve (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) : componentPiece c :=
  O.curve (O.standardTime t)

/-- Product-circle coordinates of the standard-period lifted orbit. -/
def standardCoordinates (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) : Circle × Circle :=
  planeExpPair (O.standardLift t)

theorem standardCoordinates_eq_componentCurve
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) :
    O.standardCoordinates t =
      (O.standardComponentCurve t : coordinateTorusLevelSet Phi frame d).1 := by
  exact (O.curve_eq_expPair (O.standardTime t)).symm

/-- The real lifted integral curve is `C¹`.  Its derivative is the continuous rotated-gradient
field evaluated along the curve. -/
theorem contDiff_liftedIntegral_curve
    (O : RegularComponentCompleteOrbit Phi frame d c) :
    ContDiff ℝ 1 O.liftedIntegral.curve := by
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun t ↦ (O.liftedIntegral.integral t).differentiableAt
  · have hderiv : deriv O.liftedIntegral.curve = fun t ↦
        rotatedDerivativeField (orientedCoordinateLift Phi frame 2)
          (O.liftedIntegral.curve t) := by
      funext t
      exact (O.liftedIntegral.integral t).deriv
    rw [hderiv]
    exact (contDiff_rotatedDerivativeField
      ((orientedCoordinateLift_contDiff Phi frame 2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous.comp
        O.liftedIntegral.integral.continuous

/-- Consequently the standard-period real lift is `C¹`. -/
theorem contDiff_standardLift
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] :
    ContDiff ℝ 1 O.standardLift := by
  exact O.contDiff_liftedIntegral_curve.comp
    (contDiff_id.mul contDiff_const)

/-- Derivative of the standard-period lift. -/
theorem deriv_standardLift
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) :
    deriv O.standardLift t =
      ((2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period) •
        rotatedDerivativeField (orientedCoordinateLift Phi frame 2)
          (O.standardLift t) := by
  let scale := (2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period
  have htime : HasDerivAt O.standardTime scale t := by
    change HasDerivAt (fun u : ℝ ↦ u * scale) scale t
    simpa using (hasDerivAt_id t).mul_const scale
  have hcomp := (O.liftedIntegral.integral (O.standardTime t)).scomp t htime
  change deriv (O.liftedIntegral.curve ∘ O.standardTime) t =
    scale • rotatedDerivativeField (orientedCoordinateLift Phi frame 2)
      (O.liftedIntegral.curve (O.standardTime t))
  exact hcomp.deriv

/-- The standard-period lifted orbit remains in the selected planar level. -/
theorem standardLift_stays_in_level
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] (t : ℝ) :
    orientedCoordinateLift Phi frame 2 (O.standardLift t) = d :=
  O.liftedIntegral.stays_in_level (O.standardTime t)

/-- The standard coordinates are genuinely `2π`-periodic. -/
theorem periodic_standardCoordinates
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] :
    Function.Periodic O.standardCoordinates (2 * Real.pi) := by
  intro t
  rw [O.standardCoordinates_eq_componentCurve,
    O.standardCoordinates_eq_componentCurve]
  apply congrArg (fun z : componentPiece c ↦
    (z : coordinateTorusLevelSet Phi frame d).1)
  change O.curve (O.standardTime (t + 2 * Real.pi)) =
    O.curve (O.standardTime t)
  rw [show O.standardTime (t + 2 * Real.pi) =
      O.standardTime t + O.cyclicLineParametrization.period by
    unfold standardTime
    field_simp [Real.pi_ne_zero]]
  exact O.cyclicLineParametrization.periodic_curve (O.standardTime t)

end Submission.SurfaceRegularValue.RegularComponentCompleteOrbit

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)}

/-- A continuous real lift of a `2π`-periodic circle loop has one fixed integral deck increment.
This is the covering-uniqueness argument used internally by `exists_circleLoopLift`, stated so an
already explicit ODE angle can be retained. -/
theorem exists_winding_angle_add_two_pi
    {gamma : ℝ → Circle} (theta : ℝ → ℝ)
    (htheta : Continuous theta)
    (hexp : ∀ t, Circle.exp (theta t) = gamma t)
    (hperiodic : Function.Periodic gamma (2 * Real.pi)) :
    ∃ winding : ℤ, ∀ t,
      theta (t + 2 * Real.pi) =
        theta t + (winding : ℝ) * (2 * Real.pi) := by
  let gc : C(ℝ, Circle) := ⟨gamma,
    (Circle.exp.continuous.comp htheta).congr hexp⟩
  have hExpPeriod : Circle.exp (theta (2 * Real.pi)) = Circle.exp (theta 0) := by
    rw [hexp, hexp]
    simpa only [zero_add] using hperiodic 0
  obtain ⟨winding, hwinding⟩ := Circle.exp_eq_exp.mp hExpPeriod
  have hbaseShift : Circle.exp (theta (2 * Real.pi)) = gc 0 := by
    change Circle.exp (theta (2 * Real.pi)) = gamma 0
    rw [hexp]
    simpa only [zero_add] using hperiodic 0
  have hunique := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    gc (0 : ℝ) (theta (2 * Real.pi)) hbaseShift
  let shifted : C(ℝ, ℝ) :=
    ⟨fun t ↦ theta (t + 2 * Real.pi),
      htheta.comp (continuous_id.add continuous_const)⟩
  let translated : C(ℝ, ℝ) :=
    ⟨fun t ↦ theta t + (winding : ℝ) * (2 * Real.pi),
      htheta.add continuous_const⟩
  have hshifted : shifted 0 = theta (2 * Real.pi) ∧ Circle.exp ∘ shifted = gc := by
    constructor
    · change theta (0 + 2 * Real.pi) = theta (2 * Real.pi)
      rw [zero_add]
    · funext t
      change Circle.exp (theta (t + 2 * Real.pi)) = gamma t
      exact (hexp (t + 2 * Real.pi)).trans (hperiodic t)
  have htranslated : translated 0 = theta (2 * Real.pi) ∧
      Circle.exp ∘ translated = gc := by
    constructor
    · exact hwinding.symm
    · funext t
      change Circle.exp (theta t + (winding : ℝ) * (2 * Real.pi)) = gamma t
      calc
        Circle.exp (theta t + (winding : ℝ) * (2 * Real.pi)) =
            Circle.exp (theta t) := by
          apply Circle.exp_eq_exp.mpr
          exact ⟨winding, rfl⟩
        _ = gamma t := hexp t
  have heq : shifted = translated := hunique.unique hshifted htranslated
  exact ⟨winding, fun t ↦ congrArg (fun F : C(ℝ, ℝ) ↦ F t) heq⟩

/-- The abstract circle homeomorphism built from a cyclic parametrization agrees with its
explicit real curve after the canonical period rescaling. -/
theorem CyclicLineParametrization.circleHomeomorph_exp
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (P : CyclicLineParametrization X) (t : ℝ) :
    P.circleHomeomorph (Circle.exp t) =
      P.curve (t * ((2 * Real.pi)⁻¹ * P.period)) := by
  change P.periodic_curve.lift
      ((AddCircle.homeomorphCircle P.period_ne_zero).symm (Circle.exp t)) =
    P.curve (t * ((2 * Real.pi)⁻¹ * P.period))
  rw [← P.periodic_curve.lift_coe]
  congr 1
  apply (AddCircle.homeomorphCircle P.period_ne_zero).injective
  rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  field_simp [P.period_ne_zero, Real.pi_ne_zero]
  ring

/-- Exact deck data retained from the lifted cyclic ODE orbit.

`circle_exp` is the rescaling compatibility lost when the cyclic parametrization is converted to
an abstract circle homeomorphism.  `lift_add_period` is its lift-level monodromy.  Both statements
concern the already constructed orbit; neither assumes smoothness, embeddedness, essentiality, or
transversality of the desired section circle. -/
structure RegularOrbitStandardPeriodData
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] where
  firstWinding : ℤ
  secondWinding : ℤ
  circle_exp : ∀ t,
    O.cyclicLineParametrization.circleHomeomorph (Circle.exp t) =
      O.standardComponentCurve t
  lift_add_period : ∀ t,
    O.standardLift (t + 2 * Real.pi) =
      O.standardLift t +
        ((firstWinding : ℝ) * (2 * Real.pi),
          (secondWinding : ℝ) * (2 * Real.pi))

/-- Covering-lift uniqueness supplies the period/deck data for every complete regular component
orbit.  Thus `RegularOrbitStandardPeriodData` is an internal package, not an additional geometric
hypothesis. -/
noncomputable def regularOrbitStandardPeriodData
    (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] : RegularOrbitStandardPeriodData O := by
  let firstExistence := exists_winding_angle_add_two_pi
    (fun t ↦ (O.standardLift t).1)
    (continuous_fst.comp O.contDiff_standardLift.continuous)
    (fun _ ↦ rfl)
    (fun t ↦ congrArg Prod.fst (O.periodic_standardCoordinates t))
  let m := Classical.choose firstExistence
  have hm := Classical.choose_spec firstExistence
  let secondExistence := exists_winding_angle_add_two_pi
    (fun t ↦ (O.standardLift t).2)
    (continuous_snd.comp O.contDiff_standardLift.continuous)
    (fun _ ↦ rfl)
    (fun t ↦ congrArg Prod.snd (O.periodic_standardCoordinates t))
  let n := Classical.choose secondExistence
  have hn := Classical.choose_spec secondExistence
  exact {
    firstWinding := m
    secondWinding := n
    circle_exp := by
      intro t
      simpa only [RegularComponentCompleteOrbit.cyclicLineParametrization,
        RegularComponentCompleteOrbit.toHomogeneousLocalOrbit,
        HomogeneousLocalOrbit.cyclicLineParametrization,
        RegularComponentCompleteOrbit.standardComponentCurve,
        RegularComponentCompleteOrbit.standardTime] using
          Submission.Topology.CyclicLineParametrization.circleHomeomorph_exp
            O.cyclicLineParametrization t
    lift_add_period := by
      intro t
      ext
      · simpa only [Prod.fst_add] using hm t
      · simpa only [Prod.snd_add] using hn t
  }

namespace RegularOrbitStandardPeriodData

variable {O : RegularComponentCompleteOrbit Phi frame d c}
  [CompactSpace (componentPiece c)]

/-- The product-circle coordinates of the standard-period orbit. -/
def coordinates (_M : RegularOrbitStandardPeriodData O) (t : ℝ) : Circle × Circle :=
  planeExpPair (O.standardLift t)

theorem coordinates_eq_componentCurve
    (M : RegularOrbitStandardPeriodData O) (t : ℝ) :
    M.coordinates t =
      (O.standardComponentCurve t : coordinateTorusLevelSet Phi frame d).1 := by
  exact (O.curve_eq_expPair (O.standardTime t)).symm

theorem continuous_coordinates (M : RegularOrbitStandardPeriodData O) :
    Continuous M.coordinates := by
  exact planeExpPair_isLocalHomeomorph.continuous.comp O.contDiff_standardLift.continuous

theorem periodic_coordinates (M : RegularOrbitStandardPeriodData O) :
    Function.Periodic M.coordinates (2 * Real.pi) := by
  intro t
  rw [M.coordinates_eq_componentCurve, M.coordinates_eq_componentCurve,
    ← M.circle_exp, ← M.circle_exp, Circle.exp_add_two_pi]

/-- The first explicit real angle lift, with the deck winding supplied by the orbit. -/
def firstLift (M : RegularOrbitStandardPeriodData O) :
    CircleLoopLift (fun t ↦ (M.coordinates t).1) where
  angle t := (O.standardLift t).1
  continuous_angle :=
    (continuous_fst.comp O.contDiff_standardLift.continuous)
  exp_angle t := rfl
  winding := M.firstWinding
  angle_add_period t := by
    have h := congrArg Prod.fst (M.lift_add_period t)
    simpa only [Prod.fst_add] using h

/-- The second explicit real angle lift, with the deck winding supplied by the orbit. -/
def secondLift (M : RegularOrbitStandardPeriodData O) :
    CircleLoopLift (fun t ↦ (M.coordinates t).2) where
  angle t := (O.standardLift t).2
  continuous_angle :=
    (continuous_snd.comp O.contDiff_standardLift.continuous)
  exp_angle t := rfl
  winding := M.secondWinding
  angle_add_period t := by
    have h := congrArg Prod.snd (M.lift_add_period t)
    simpa only [Prod.snd_add] using h

/-- The coordinatewise explicit lift of the standard-period orbit. -/
def torusLoopLift (M : RegularOrbitStandardPeriodData O) :
    TorusLoopLift M.coordinates where
  first := M.firstLift
  second := M.secondLift

/-- The transported real-periodic orbit, retaining the explicit ODE angle lift. -/
def windingLoop (M : RegularOrbitStandardPeriodData O) :
    TransportedWindingLoop Phi Set.univ where
  curve t := transportedTorusHomeomorph Phi (M.coordinates t)
  continuous_curve :=
    (transportedTorusHomeomorph Phi).continuous.comp M.continuous_coordinates
  periodic_curve t := by
    exact congrArg (transportedTorusHomeomorph Phi) (M.periodic_coordinates t)
  curve_mem _ := Set.mem_univ _
  lift := {
    first := {
      angle := fun t ↦ (O.standardLift t).1
      continuous_angle := continuous_fst.comp O.contDiff_standardLift.continuous
      exp_angle := fun t ↦ by
        change Circle.exp (O.standardLift t).1 =
          (transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (M.coordinates u)) t).1
        rw [show transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (M.coordinates u)) t =
              M.coordinates t by
          exact (transportedTorusHomeomorph Phi).symm_apply_apply _]
        rfl
      winding := M.firstWinding
      angle_add_period := fun t ↦ by
        have h := congrArg Prod.fst (M.lift_add_period t)
        simpa only [Prod.fst_add] using h
    }
    second := {
      angle := fun t ↦ (O.standardLift t).2
      continuous_angle := continuous_snd.comp O.contDiff_standardLift.continuous
      exp_angle := fun t ↦ by
        change Circle.exp (O.standardLift t).2 =
          (transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (M.coordinates u)) t).2
        rw [show transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (M.coordinates u)) t =
              M.coordinates t by
          exact (transportedTorusHomeomorph Phi).symm_apply_apply _]
        rfl
      winding := M.secondWinding
      angle_add_period := fun t ↦ by
        have h := congrArg Prod.snd (M.lift_add_period t)
        simpa only [Prod.snd_add] using h
    }
  }

/-- The ambient circle obtained from the cyclic component homeomorphism. -/
def ambientCircle (_M : RegularOrbitStandardPeriodData O) (z : Circle) : R3 :=
  transportedTorusMap Phi
    (((O.cyclicLineParametrization.circleHomeomorph z : componentPiece c) :
      coordinateTorusLevelSet Phi frame d).1)

theorem isEmbedding_ambientCircle (M : RegularOrbitStandardPeriodData O) :
    IsEmbedding M.ambientCircle := by
  apply (transportedTorusMap_isEmbedding Phi).comp
  exact IsEmbedding.subtypeVal.comp <|
    IsEmbedding.subtypeVal.comp O.cyclicLineParametrization.circleHomeomorph.isEmbedding

theorem ambientCircle_parametrization
    (M : RegularOrbitStandardPeriodData O) (t : ℝ) :
    M.ambientCircle (Circle.exp t) = M.windingLoop.curve t := by
  rw [ambientCircle, M.circle_exp]
  change transportedTorusMap Phi
      ((O.standardComponentCurve t : coordinateTorusLevelSet Phi frame d).1) =
    transportedTorusMap Phi (M.coordinates t)
  rw [M.coordinates_eq_componentCurve]

/-- The derived embedded circle before asserting essentiality or knot transversality. -/
def embeddedCircle (M : RegularOrbitStandardPeriodData O) :
    EmbeddedTorusIntersectionCircle Phi where
  circle := M.ambientCircle
  isEmbedding := M.isEmbedding_ambientCircle
  windingLoop := M.windingLoop
  parametrization := M.ambientCircle_parametrization

theorem embeddedCircle_range_eq_component
    (M : RegularOrbitStandardPeriodData O) :
    Set.range M.embeddedCircle.circle =
      (fun z : coordinateTorusLevelSet Phi frame d ↦ transportedTorusMap Phi z) ''
        componentPiece c := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨O.cyclicLineParametrization.circleHomeomorph z,
      (O.cyclicLineParametrization.circleHomeomorph z).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := O.cyclicLineParametrization.circleHomeomorph.surjective ⟨z, hz⟩
    refine ⟨w, ?_⟩
    exact congrArg (fun u : componentPiece c ↦ transportedTorusMap Phi u.1.1) hw

theorem contDiff_first_angle (M : RegularOrbitStandardPeriodData O) :
    ContDiff ℝ 1 M.windingLoop.lift.first.angle := by
  change ContDiff ℝ 1 (fun t ↦ (O.standardLift t).1)
  exact contDiff_fst.comp O.contDiff_standardLift

theorem contDiff_second_angle (M : RegularOrbitStandardPeriodData O) :
    ContDiff ℝ 1 M.windingLoop.lift.second.angle := by
  change ContDiff ℝ 1 (fun t ↦ (O.standardLift t).2)
  exact contDiff_snd.comp O.contDiff_standardLift

theorem coordinates_injOn (M : RegularOrbitStandardPeriodData O) :
    Set.InjOn M.coordinates (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  apply Circle.exp_injOn_Ico (by linarith [Real.pi_pos]) hx hy
  apply O.cyclicLineParametrization.circleHomeomorph.injective
  rw [M.circle_exp, M.circle_exp]
  apply Subtype.ext
  apply Subtype.ext
  rw [← M.coordinates_eq_componentCurve, ← M.coordinates_eq_componentCurve, hxy]

/-- Essentiality transfers from any existing parametrization of the same embedded component.
This uses only range equality, not equality of the two chosen lifts. -/
theorem essential_of_range_eq_of_essential
    (M : RegularOrbitStandardPeriodData O)
    (C : EmbeddedTorusIntersectionCircle Phi) (hC : C.Essential)
    (hrange : Set.range C.circle = Set.range M.embeddedCircle.circle) :
    M.embeddedCircle.Essential := by
  intro hzero
  apply hC
  exact M.embeddedCircle.windingPair_eq_zero_of_range_subset_of_windingPair_eq_zero
    C.windingLoop (by
      rintro _ ⟨t, rfl⟩
      change (C.windingLoop.curve t : R3) ∈ Set.range M.embeddedCircle.circle
      rw [← C.parametrization t]
      rw [← hrange]
      exact ⟨Circle.exp t, rfl⟩) hzero

end RegularOrbitStandardPeriodData

/-! ## Knot-height transversality in covering coordinates -/

/-- Height of the standard `(p,q)` torus-knot lift, expressed on the same real covering plane as
the rotated-gradient orbit. -/
def standardTorusKnotHeight (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (p q : ℕ) (t : ℝ) : ℝ :=
  orientedCoordinateLift Phi frame 2 ((p : ℝ) * t, (q : ℝ) * t)

/-- The class equation identifies standard-knot height with the height of the given knot after
the inverse circle reparametrization. -/
theorem standardTorusKnotHeight_eq_longCoordinate_comp_finv
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t)) :
    standardTorusKnotHeight Phi frame p q =
      fun t ↦ Submission.PardonDistortion.longCoordinate K frame (sigma.finv t) := by
  funext t
  unfold standardTorusKnotHeight orientedCoordinateLift
  rw [transportedTorusPlaneMap_eq_expPair]
  change ambientCoordinate (frame 2)
      (transportedTorusMap Phi (torusKnotLift p q t)) =
    ambientCoordinate (frame 2) (K.curve (sigma.finv t))
  rw [curve_eq_transportedTorusMap p q K Phi sigma hclass, sigma.right_inv]

/-- A smooth reparametrization with a smooth inverse has nonzero inverse derivative everywhere. -/
theorem CircleReparam.deriv_finv_ne_zero (sigma : CircleReparam) (t : ℝ) :
    deriv sigma.finv t ≠ 0 := by
  have hf : DifferentiableAt ℝ sigma.f (sigma.finv t) :=
    sigma.smooth.differentiable (by simp) (sigma.finv t)
  have hfinv : DifferentiableAt ℝ sigma.finv t :=
    sigma.smooth_inv.differentiable (by simp) t
  have hcomp := (hf.hasDerivAt.comp t hfinv.hasDerivAt).deriv
  have hfun : sigma.f ∘ sigma.finv = id := by
    funext u
    exact sigma.right_inv u
  rw [hfun, deriv_id] at hcomp
  intro hzero
  rw [hzero, mul_zero] at hcomp
  norm_num at hcomp

/-- Regularity of the selected height for the given knot transfers through the smooth class
reparametrization to regularity of the standard torus-knot height. -/
theorem standardTorusKnotHeight_regular_of_class
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    {height : ℝ}
    (hregular : Submission.Coarea.IsRegularValue
      (Submission.PardonDistortion.longCoordinate K frame) height) :
    Submission.Coarea.IsRegularValue
      (standardTorusKnotHeight Phi frame p q) height := by
  intro t ht
  let g := Submission.PardonDistortion.longCoordinate K frame
  have heq := standardTorusKnotHeight_eq_longCoordinate_comp_finv
    p q K Phi frame sigma hclass
  have hvalue : g (sigma.finv t) = height := by
    exact (congrFun heq t).symm.trans ht
  have hg : deriv g (sigma.finv t) ≠ 0 := hregular _ hvalue
  have hchain : deriv (fun u ↦ g (sigma.finv u)) t =
      deriv g (sigma.finv t) * deriv sigma.finv t := by
    exact deriv_comp t
      ((contDiff_longCoordinate K frame).differentiable
        (by simp) (sigma.finv t))
      (sigma.smooth_inv.differentiable (by simp) t)
  have hderivEq := congrArg (fun F : ℝ → ℝ ↦ deriv F t) heq
  rw [hderivEq, hchain]
  exact mul_ne_zero hg (CircleReparam.deriv_finv_ne_zero sigma t)

/-- A regular coordinate-torus selection which retains the analytic regular-value proof used to
construct it.  The older `RegularCoordinateTorusLevel` keeps only the descended local-line
structure, from which this differential statement cannot be recovered. -/
structure RegularCoordinateTorusLevelWithRegularValue
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (a b : ℝ) where
  levelData : RegularCoordinateTorusLevel Phi frame a b
  regularValue : Submission.SurfaceRegularValue.IsRegularValue
    (orientedCoordinateLift Phi frame 2) levelData.selection.level

/-- Planar Sard constructs the strengthened selection directly, retaining the regular-value
witness instead of discarding it after quotient-chart descent. -/
theorem nonempty_regularCoordinateTorusLevelWithRegularValue
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    {a b : ℝ} (hab : a < b) :
    Nonempty (RegularCoordinateTorusLevelWithRegularValue Phi frame a b) := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    orientedCoordinateLift_contDiff Phi frame 2
  have hnull : Submission.SurfaceRegularValue.CriticalValuesNull f :=
    criticalValuesNull_of_sardMoreiraConclusion
      (planarSardTheorem f hf)
  obtain ⟨d, hdmem, hdregular⟩ := exists_regularValue_between hnull hab
  let selection : CompactRegularLevelSelection f a b := {
    level := d
    level_mem := hdmem
    isCompact := isCompact_fundamentalLevelSet hf.continuous d
    localCharts := regularValue_has_local_charts hf hdregular
  }
  let levelData : RegularCoordinateTorusLevel Phi frame a b := {
    selection := selection
    quotientLocallyLineModeled :=
      isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hdregular
  }
  exact ⟨⟨levelData, hdregular⟩⟩

/-- Root-level deck matching between an explicit lifted section orbit and the standard knot
angle line.  This is the small covering-space fact still to be extracted from
`exp_transformedSlopeAngle_eq_one_iff_mem_range_torusKnotLift`; it contains no derivative or
regularity conclusion. -/
structure OrbitKnotRootDeckMatch
    {O : RegularComponentCompleteOrbit Phi frame d c}
    [CompactSpace (componentPiece c)]
    (M : RegularOrbitStandardPeriodData O) (p q : ℕ) : Prop where
  match_root : ∀ t,
    Circle.exp (transformedSlopeAngle p q M.windingLoop.lift t) = 1 →
      ∃ u : ℝ, ∃ m n : ℤ,
        O.standardLift t =
          ((p : ℝ) * u, (q : ℝ) * u) + planeDeckVector m n

/-- Coprimality and the slope-character root criterion supply the root deck matching
unconditionally. -/
theorem OrbitKnotRootDeckMatch.ofCoprime
    {O : RegularComponentCompleteOrbit Phi frame d c}
    [CompactSpace (componentPiece c)]
    (M : RegularOrbitStandardPeriodData O) (p q : ℕ) (hc : p.Coprime q) :
    OrbitKnotRootDeckMatch M p q where
  match_root t hroot := by
    have hmem :=
      (exp_transformedSlopeAngle_eq_one_iff_mem_range_torusKnotLift
        p q hc M.windingLoop.lift t).mp hroot
    obtain ⟨u, hu⟩ := hmem
    have hcoordinates :
        transportedLoopCoordinates Phi M.windingLoop.curve t = M.coordinates t := by
      change (transportedTorusHomeomorph Phi).symm
          (transportedTorusHomeomorph Phi (M.coordinates t)) = M.coordinates t
      exact (transportedTorusHomeomorph Phi).symm_apply_apply _
    rw [hcoordinates] at hu
    have hfirst : Circle.exp (O.standardLift t).1 = Circle.exp ((p : ℝ) * u) := by
      simpa only [RegularOrbitStandardPeriodData.windingLoop,
        RegularOrbitStandardPeriodData.coordinates, planeExpPair,
        torusKnotLift] using congrArg Prod.fst hu.symm
    have hsecond : Circle.exp (O.standardLift t).2 = Circle.exp ((q : ℝ) * u) := by
      simpa only [RegularOrbitStandardPeriodData.windingLoop,
        RegularOrbitStandardPeriodData.coordinates, planeExpPair,
        torusKnotLift] using congrArg Prod.snd hu.symm
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hfirst
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hsecond
    refine ⟨u, m, n, ?_⟩
    ext
    · simpa only [planeDeckVector, Prod.fst_add] using hm
    · simpa only [planeDeckVector, Prod.snd_add] using hn

/-- A linear-algebra core: a nonzero vector annihilated by a height differential cannot be
parallel to a knot-slope vector on which that differential is nonzero. -/
theorem slopeDet_ne_zero_of_height_transverse
    (p q : ℕ) (hp : 0 < p) (L : Plane →L[ℝ] ℝ) (v : Plane)
    (hv : v ≠ 0) (hvHeight : L v = 0)
    (hknotHeight : L ((p : ℝ), (q : ℝ)) ≠ 0) :
    (p : ℝ) * v.2 - (q : ℝ) * v.1 ≠ 0 := by
  intro hdet
  let a : ℝ := v.1 / (p : ℝ)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hvEq : v = a • ((p : ℝ), (q : ℝ)) := by
    ext
    · simp only [smul_eq_mul, Prod.smul_fst, a]
      field_simp
    · simp only [smul_eq_mul, Prod.smul_snd, a]
      field_simp
      nlinarith
  have ha : a = 0 := by
    rw [hvEq, map_smul, smul_eq_mul] at hvHeight
    exact (mul_eq_zero.mp hvHeight).resolve_right hknotHeight
  apply hv
  rw [hvEq, ha, zero_smul]

/-- The selected plane is transverse to every root of the explicit section orbit.  The proof is
the geometric tangent argument: the section tangent is nonzero and annihilated by the height
differential, whereas the knot-slope tangent has nonzero height derivative. -/
theorem regular_transformed_roots_of_height_regular
    {O : RegularComponentCompleteOrbit Phi frame d c}
    [CompactSpace (componentPiece c)]
    (M : RegularOrbitStandardPeriodData O) (p q : ℕ) (hp : 0 < p)
    (hlevelRegular : Submission.SurfaceRegularValue.IsRegularValue
      (orientedCoordinateLift Phi frame 2) d)
    (hknotRegular : Submission.Coarea.IsRegularValue
      (standardTorusKnotHeight Phi frame p q) d)
    (hdeck : OrbitKnotRootDeckMatch M p q) :
    ∀ t, Circle.exp (transformedSlopeAngle p q M.windingLoop.lift t) = 1 →
      deriv (transformedSlopeAngle p q M.windingLoop.lift) t ≠ 0 := by
  intro t hroot
  obtain ⟨u, m, n, hmatch⟩ := hdeck.match_root t hroot
  let f := orientedCoordinateLift Phi frame 2
  let theta := O.standardLift
  let v := deriv theta t
  let knotVector : Plane := ((p : ℝ), (q : ℝ))
  have hthetaDeriv := O.deriv_standardLift t
  have hthetaV : HasDerivAt theta v t := by
    exact (O.contDiff_standardLift.differentiable (by simp) t).hasDerivAt
  have hscale : (2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period ≠ 0 := by
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      O.cyclicLineParametrization.period_ne_zero
  have hrot : rotatedDerivativeField f (theta t) ≠ 0 := by
    apply rotatedDerivativeField_ne_zero
    exact hlevelRegular _ (O.standardLift_stays_in_level t)
  have hv : v ≠ 0 := by
    rw [show v = ((2 * Real.pi)⁻¹ *
      O.cyclicLineParametrization.period) •
        rotatedDerivativeField f (theta t) from hthetaDeriv]
    exact smul_ne_zero hscale hrot
  have hheightFunction : f ∘ theta = fun _ ↦ d := by
    funext x
    exact O.standardLift_stays_in_level x
  have hvHeight : fderiv ℝ f (theta t) v = 0 := by
    have hcomp := ((orientedCoordinateLift_contDiff Phi frame 2).differentiable
      (by simp) (theta t)).hasFDerivAt.comp_hasDerivAt t hthetaV
    have hzero : deriv (f ∘ theta) t = 0 := by
      rw [hheightFunction, deriv_const]
    rw [hcomp.deriv] at hzero
    exact hzero
  have hknotValue : standardTorusKnotHeight Phi frame p q u = d := by
    change orientedCoordinateLift Phi frame 2
      (((p : ℝ) * u), ((q : ℝ) * u)) = d
    rw [← orientedCoordinateLift_add_planeDeckVector Phi frame 2 m n,
      ← hmatch]
    exact O.standardLift_stays_in_level t
  have hknotDeriv : deriv (standardTorusKnotHeight Phi frame p q) u ≠ 0 :=
    hknotRegular u hknotValue
  have hknotAngle : HasDerivAt
      (fun x : ℝ ↦ ((p : ℝ) * x, (q : ℝ) * x)) knotVector u := by
    simpa only [knotVector, id_eq, mul_one] using
      ((hasDerivAt_id u).const_mul (p : ℝ)).prodMk
        ((hasDerivAt_id u).const_mul (q : ℝ))
  have hknotHeightAt :
      fderiv ℝ f (((p : ℝ) * u), ((q : ℝ) * u)) knotVector ≠ 0 := by
    have hcomp := ((orientedCoordinateLift_contDiff Phi frame 2).differentiable
      (by simp) (((p : ℝ) * u), ((q : ℝ) * u))).hasFDerivAt.comp_hasDerivAt
        u hknotAngle
    exact hcomp.deriv ▸ hknotDeriv
  have hknotHeightAtTheta : fderiv ℝ f (theta t) knotVector ≠ 0 := by
    change fderiv ℝ (orientedCoordinateLift Phi frame 2)
      (O.standardLift t) knotVector ≠ 0
    rw [hmatch,
      fderiv_orientedCoordinateLift_add_planeDeckVector Phi frame 2 m n]
    exact hknotHeightAt
  have hdet : (p : ℝ) * v.2 - (q : ℝ) * v.1 ≠ 0 :=
    slopeDet_ne_zero_of_height_transverse p q hp (fderiv ℝ f (theta t)) v
      hv hvHeight hknotHeightAtTheta
  have hfirst : HasDerivAt (fun x ↦ (theta x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hthetaV
  have hsecond : HasDerivAt (fun x ↦ (theta x).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hthetaV
  have hslopeFunction : transformedSlopeAngle p q M.windingLoop.lift =
      fun x ↦ (p : ℝ) * (theta x).2 - (q : ℝ) * (theta x).1 := by
    rfl
  have hslopeDeriv : deriv
      (fun x ↦ (p : ℝ) * (theta x).2 - (q : ℝ) * (theta x).1) t =
        (p : ℝ) * v.2 - (q : ℝ) * v.1 :=
    ((hsecond.const_mul (p : ℝ)).sub (hfirst.const_mul (q : ℝ))).deriv
  rw [hslopeFunction, hslopeDeriv]
  exact hdet


variable {a b : ℝ}
  {S : RegularCoordinateTorusLevel Phi frame a b}
  {component : ConnectedComponents
    (coordinateTorusLevelSet Phi frame S.selection.level)}
  [CompactSpace (componentPiece component)]

/-- A complete lifted orbit and its narrow period/deck compatibility produce all fields of the
smooth essential section circle except the transformed-root regularity.  Essentiality is
transported from the existing topological component parametrization by equality of ranges. -/
def smoothEssentialSectionCircleOfOrbit
    (p q : ℕ)
    (O : RegularComponentCompleteOrbit Phi frame S.selection.level component)
    (M : RegularOrbitStandardPeriodData O)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (hessential :
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        S C component).Essential)
    (hregular : ∀ t,
      Circle.exp (transformedSlopeAngle p q M.windingLoop.lift t) = 1 →
        deriv (transformedSlopeAngle p q M.windingLoop.lift) t ≠ 0) :
    SmoothEssentialSectionCircle S component p q where
  embeddedCircle := M.embeddedCircle
  range_eq_component := M.embeddedCircle_range_eq_component
  contDiff_first := M.contDiff_first_angle
  contDiff_second := M.contDiff_second_angle
  coordinates_injOn := by
    have hcoordinates :
        transportedLoopCoordinates Phi M.embeddedCircle.windingLoop.curve =
          M.coordinates := by
      funext t
      change (transportedTorusHomeomorph Phi).symm
          (transportedTorusHomeomorph Phi (M.coordinates t)) = M.coordinates t
      exact (transportedTorusHomeomorph Phi).symm_apply_apply _
    rw [hcoordinates]
    exact M.coordinates_injOn
  regular_transformed_roots := hregular
  essential := M.essential_of_range_eq_of_essential
    (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent S C component)
    hessential (by
      rw [M.embeddedCircle_range_eq_component,
        FiniteCoordinatePlaneTorusCircleFamily.component_circle_range])

/-- Full construction from a complete rotated-gradient orbit, the exact period/deck data, and
the two regular-value statements selected upstream.  Knot-height regularity is transported
through the ambient class equation; the tangent argument then supplies transformed-root
regularity rather than assuming it. -/
def smoothEssentialSectionCircleOfOrbitOfKnotHeightRegular
    (p q : ℕ) (hp : 0 < p) (hc : p.Coprime q)
    (K : Knot) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (hlevelRegular : Submission.SurfaceRegularValue.IsRegularValue
      (orientedCoordinateLift Phi frame 2) S.selection.level)
    (hknotRegular : Submission.Coarea.IsRegularValue
      (Submission.PardonDistortion.longCoordinate K frame) S.selection.level)
    (O : RegularComponentCompleteOrbit Phi frame S.selection.level component)
    (M : RegularOrbitStandardPeriodData O)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (hessential :
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        S C component).Essential) :
    SmoothEssentialSectionCircle S component p q :=
  smoothEssentialSectionCircleOfOrbit p q O M C hessential <|
    regular_transformed_roots_of_height_regular M p q hp hlevelRegular
      (standardTorusKnotHeight_regular_of_class
        p q K Phi frame sigma hclass hknotRegular)
      (OrbitKnotRootDeckMatch.ofCoprime M p q hc)

/-- Canonical version using the retained-regular-value selector and the deck data derived from the
complete orbit itself.  No smoothness, monodromy, root matching, or transformed-root regularity
is left as an input. -/
def smoothEssentialSectionCircleOfCompleteOrbit
    {R : RegularCoordinateTorusLevelWithRegularValue Phi frame a b}
    {component : ConnectedComponents
      (coordinateTorusLevelSet Phi frame R.levelData.selection.level)}
    [CompactSpace (componentPiece component)]
    (p q : ℕ) (hp : 0 < p) (hc : p.Coprime q)
    (K : Knot) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (hknotRegular : Submission.Coarea.IsRegularValue
      (Submission.PardonDistortion.longCoordinate K frame)
        R.levelData.selection.level)
    (O : RegularComponentCompleteOrbit Phi frame
      R.levelData.selection.level component)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame R.levelData.selection.level))
    (hessential :
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        R.levelData C component).Essential) :
    SmoothEssentialSectionCircle R.levelData component p q :=
  smoothEssentialSectionCircleOfOrbitOfKnotHeightRegular p q hp hc K sigma hclass
    R.regularValue hknotRegular O (regularOrbitStandardPeriodData O) C hessential

/-! ## The exact cutting level of a based double-bubble selector -/

/-- The strengthened based selector determines a genuine regular coordinate-torus level at its
exact cutting height.  The auxiliary interval is centered at that height and carries no geometric
content; it only supplies the interval fields of `RegularCoordinateTorusLevel`. -/
def cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection
    {K : Knot} {center : R3} {r : ℝ}
    (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame center r) :
    RegularCoordinateTorusLevel Phi frame (S.cut.height - 1) (S.cut.height + 1) where
  selection := {
    level := S.cut.height
    level_mem := by constructor <;> linarith
    isCompact := isCompact_fundamentalLevelSet
      (orientedCoordinateLift_contDiff Phi frame 2).continuous S.cut.height
    localCharts := regularValue_has_local_charts
      (orientedCoordinateLift_contDiff Phi frame 2) S.cutSurfaceRegular
  }
  quotientLocallyLineModeled :=
    isLocallyLineModeled_coordinateTorusLevel_of_regularValue
      Phi frame S.cutSurfaceRegular

/-- The same exact cutting level with its analytic regular-value witness retained. -/
def cutRegularCoordinateTorusLevelWithRegularValueOfSurfaceRegularBasedSelection
    {K : Knot} {center : R3} {r : ℝ}
    (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame center r) :
    RegularCoordinateTorusLevelWithRegularValue
      Phi frame (S.cut.height - 1) (S.cut.height + 1) where
  levelData := cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S
  regularValue := S.cutSurfaceRegular

/-- At the exact cut chosen by the strengthened based double-bubble selector, a complete orbit of
an essential classified component canonically gives the smooth section circle needed by the
shifted compression certificate.  Knot-height regularity is not a new hypothesis: it is exactly
`S.cut.knotRegular`. -/
def smoothEssentialSectionCircleOfSurfaceRegularBasedSelection
    {K : Knot} {center : R3} {r : ℝ}
    (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame center r)
    (p q : ℕ) (hp : 0 < p) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    {component : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.cut.height)}
    (O : RegularComponentCompleteOrbit Phi frame S.cut.height component)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.cut.height))
    (hessential :
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S) C component).Essential) :
    SmoothEssentialSectionCircle
      (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S) component p q := by
  let _ : CompactSpace (coordinateTorusLevelSet Phi frame S.cut.height) :=
    (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S).compactSpace
  let _ : LocallyConnectedSpace (coordinateTorusLevelSet Phi frame S.cut.height) :=
    (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S).locallyConnectedSpace
  let componentCompact : CompactSpace (componentPiece component) :=
    isCompact_iff_compactSpace.mp
      (isClopen_componentPiece component).isClosed.isCompact
  exact @smoothEssentialSectionCircleOfCompleteOrbit Phi frame
    (S.cut.height - 1) (S.cut.height + 1)
    (cutRegularCoordinateTorusLevelWithRegularValueOfSurfaceRegularBasedSelection S)
    component componentCompact
    p q hp hc K sigma hclass S.cut.knotRegular O C hessential

/-- If the regular quotient family supplies an essential component and complete orbits on all
components, choose that component and return its canonical smooth section circle.  This is the
existential form used by the cutting argument; the only branch assumption is the honest
essential-component side of the existing section dichotomy. -/
theorem exists_smoothEssentialSectionCircleOfSurfaceRegularBasedSelection
    {K : Knot} {center : R3} {r : ℝ}
    (S : SurfaceRegularBasedDoubleBubbleSelection K Phi frame center r)
    (p q : ℕ) (hp : 0 < p) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (O : ∀ component : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.cut.height),
        RegularComponentCompleteOrbit Phi frame S.cut.height component)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.cut.height))
    (hessential : ∃ component : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.cut.height),
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S) C component).Essential) :
    ∃ component : ConnectedComponents
        (coordinateTorusLevelSet Phi frame S.cut.height),
      Nonempty (SmoothEssentialSectionCircle
        (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S) component p q) := by
  let _ : CompactSpace (coordinateTorusLevelSet Phi frame S.cut.height) :=
    (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S).compactSpace
  let _ : LocallyConnectedSpace (coordinateTorusLevelSet Phi frame S.cut.height) :=
    (cutRegularCoordinateTorusLevelOfSurfaceRegularBasedSelection S).locallyConnectedSpace
  obtain ⟨component, hcomponent⟩ := hessential
  let _ : CompactSpace (componentPiece component) :=
    isCompact_iff_compactSpace.mp
      (isClopen_componentPiece component).isClosed.isCompact
  exact ⟨component, ⟨smoothEssentialSectionCircleOfSurfaceRegularBasedSelection
    S p q hp hc sigma hclass (O component) C hcomponent⟩⟩

end Submission.Topology
