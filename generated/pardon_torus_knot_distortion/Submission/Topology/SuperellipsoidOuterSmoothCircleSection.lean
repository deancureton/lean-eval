import Submission.Topology.SmoothSectionCircleFromOrbit
import Submission.Topology.CrossingSignFlip
import Submission.Topology.SuperellipsoidOuterCircleSection
import Submission.Coarea.SuperellipsoidSeamSard

/-!
# Smooth circle parametrizations of regular outer superellipsoid sections

The ordinary outer-section classifier intentionally exposes only embedded topological circles.
For cyclic cutting-height order one must retain the complete rotated-gradient orbit which produced
each component.  This file standardizes those orbits to period `2π`, retains their covering-plane
lifts, and proves the cutting height is a regular one-variable function at every seam crossing.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}

/-- The retained complete orbit on one component of a regular outer polynomial level. -/
abbrev SuperellipsoidOuterComponentOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ)
    (k : ConnectedComponents
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)) :=
  PeriodicRegularComponentCompleteOrbit
    (superellipsoidPolynomialLift Phi frame c)
    (superellipsoidTorusPolynomial Phi frame c) (R ^ 256) k

/-- Regularity of the lifted polynomial constructs a complete smooth orbit on each quotient
component while retaining the exact covering-plane lift. -/
theorem exists_superellipsoidOuterComponentOrbit
    (hregular : IsRegularValue
      (superellipsoidPolynomialLift Phi frame c) (R ^ 256))
    (k : ConnectedComponents
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)) :
    Nonempty (SuperellipsoidOuterComponentOrbit Phi frame c R k) := by
  exact exists_periodicRegularComponentCompleteOrbit
    (contDiff_superellipsoidPolynomialLift Phi frame c)
    (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c)
    hregular k

namespace SuperellipsoidOuterComponentOrbit

variable {k : ConnectedComponents
    (superellipsoidTorusPolynomialLevelSet Phi frame c R)}

/-- The retained cyclic parametrization with the compact-component instance passed explicitly.
This avoids asking typeclass search to unfold the two definitionally equal level-set wrappers. -/
abbrev retainedCyclicLineParametrization
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] :=
  @PeriodicRegularComponentCompleteOrbit.cyclicLineParametrization
    _ _ _ _ O componentCompact

/-- Affine time rescaling from the canonical cyclic period to `2π`. -/
def standardTime (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) : ℝ :=
  t * ((2 * Real.pi)⁻¹ *
    (retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).period)

/-- The retained covering-plane orbit with standard period. -/
def standardLift (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) : Plane :=
  O.liftedIntegral.curve (O.standardTime t)

/-- The component-valued orbit with standard period. -/
def standardComponentCurve (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) : componentPiece k :=
  O.curve (O.standardTime t)

/-- Product-circle coordinates of the standard-period lift. -/
def standardCoordinates (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) : Circle × Circle :=
  planeExpPair (O.standardLift t)

theorem standardCoordinates_eq_componentCurve
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) :
    O.standardCoordinates t =
      (O.standardComponentCurve t :
        superellipsoidTorusPolynomialLevelSet Phi frame c R).1 := by
  exact (O.curve_eq_expPair (O.standardTime t)).symm

/-- The standard-period lift is `C¹`. -/
theorem contDiff_standardLift
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] : ContDiff ℝ 1 O.standardLift := by
  exact (O.liftedIntegral.contDiff
    ((contDiff_superellipsoidPolynomialLift Phi frame c).of_le
      (WithTop.coe_le_coe.mpr le_top))).comp
        (contDiff_id.mul contDiff_const)

/-- The nonzero time-rescaling factor. -/
def standardScale (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] : ℝ :=
  (2 * Real.pi)⁻¹ *
    (retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).period

theorem standardScale_ne_zero
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] : O.standardScale ≠ 0 :=
  mul_ne_zero (inv_ne_zero (ne_of_gt Real.two_pi_pos))
    (retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).period_ne_zero

/-- The standard lift remains an integral curve, with the expected constant time scale. -/
theorem hasDerivAt_standardLift
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) :
    HasDerivAt O.standardLift
      (O.standardScale • rotatedDerivativeField
        (superellipsoidPolynomialLift Phi frame c) (O.standardLift t)) t := by
  have htime : HasDerivAt O.standardTime O.standardScale t := by
    change HasDerivAt (fun u : ℝ ↦ u * O.standardScale) O.standardScale t
    simpa using (hasDerivAt_id t).mul_const O.standardScale
  exact (O.liftedIntegral.integral (O.standardTime t)).scomp t htime

/-- The standard lift remains on the selected outer polynomial level. -/
theorem standardLift_stays_in_level
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) :
    superellipsoidPolynomialLift Phi frame c (O.standardLift t) = R ^ 256 :=
  O.liftedIntegral.stays_in_level (O.standardTime t)

/-- The abstract cyclic circle homeomorphism agrees with the standardized retained orbit. -/
theorem circleHomeomorph_exp
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] (t : ℝ) :
    (retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).circleHomeomorph (Circle.exp t) =
      O.standardComponentCurve t := by
  simpa only [retainedCyclicLineParametrization,
    PeriodicRegularComponentCompleteOrbit.cyclicLineParametrization,
    PeriodicRegularComponentCompleteOrbit.toHomogeneousLocalOrbit,
    HomogeneousLocalOrbit.cyclicLineParametrization,
    standardComponentCurve, standardTime] using
      CyclicLineParametrization.circleHomeomorph_exp
        (retainedCyclicLineParametrization
          (componentCompact := componentCompact) O) t

/-- The standardized product-circle coordinates are genuinely `2π`-periodic. -/
theorem periodic_standardCoordinates
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] :
    Function.Periodic O.standardCoordinates (2 * Real.pi) := by
  intro t
  rw [O.standardCoordinates_eq_componentCurve,
    O.standardCoordinates_eq_componentCurve,
    ← O.circleHomeomorph_exp, ← O.circleHomeomorph_exp,
    Circle.exp_add_two_pi]

end SuperellipsoidOuterComponentOrbit

/-! ## Explicit deck data and the smooth embedded circle -/

/-- A planar lift returns after one standard period up to the indicated deck translation.
Keeping this relation separate prevents the standard-period structure from eagerly expanding the
retained orbit and its compact-component instance while elaborating its dependent fields. -/
def PlaneLiftHasDeckTranslation (lift : ℝ → Plane) (m n : ℤ) : Prop :=
  ∀ t, lift (t + 2 * Real.pi) =
    lift t + ((m : ℝ) * (2 * Real.pi), (n : ℝ) * (2 * Real.pi))

/-- Deck monodromy of a standardized outer component orbit. -/
structure SuperellipsoidOuterStandardPeriodData (lift : ℝ → Plane) where
  firstWinding : ℤ
  secondWinding : ℤ
  lift_add_period : PlaneLiftHasDeckTranslation lift firstWinding secondWinding

/-- Covering-lift uniqueness supplies deck monodromy for every retained outer orbit. -/
noncomputable def superellipsoidOuterStandardPeriodData
    {k : ConnectedComponents
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)}
    (O : SuperellipsoidOuterComponentOrbit Phi frame c R k)
    [componentCompact : CompactSpace (componentPiece k)] :
    SuperellipsoidOuterStandardPeriodData O.standardLift := by
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
    lift_add_period := by
      intro t
      ext
      · simpa only [Prod.fst_add] using hm t
      · simpa only [Prod.snd_add] using hn t }

namespace SuperellipsoidOuterStandardPeriodData

variable {k : ConnectedComponents
    (superellipsoidTorusPolynomialLevelSet Phi frame c R)}
  {O : SuperellipsoidOuterComponentOrbit Phi frame c R k}
  [componentCompact : CompactSpace (componentPiece k)]
  (M : SuperellipsoidOuterStandardPeriodData O.standardLift)

/-- The transported winding loop retaining the explicit smooth covering-plane lift. -/
def windingLoop : TransportedWindingLoop Phi Set.univ where
  curve t := transportedTorusHomeomorph Phi (O.standardCoordinates t)
  continuous_curve :=
    (transportedTorusHomeomorph Phi).continuous.comp
      (planeExpPair_isLocalHomeomorph.continuous.comp
        O.contDiff_standardLift.continuous)
  periodic_curve t :=
    congrArg (transportedTorusHomeomorph Phi) (O.periodic_standardCoordinates t)
  curve_mem _ := Set.mem_univ _
  lift := {
    first := {
      angle := fun t ↦ (O.standardLift t).1
      continuous_angle := continuous_fst.comp O.contDiff_standardLift.continuous
      exp_angle := fun t ↦ by
        change Circle.exp (O.standardLift t).1 =
          (transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (O.standardCoordinates u)) t).1
        rw [show transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (O.standardCoordinates u)) t =
              O.standardCoordinates t by
          exact (transportedTorusHomeomorph Phi).symm_apply_apply _]
        rfl
      winding := M.firstWinding
      angle_add_period := fun t ↦ by
        have h := congrArg Prod.fst (M.lift_add_period t)
        simpa only [Prod.fst_add] using h }
    second := {
      angle := fun t ↦ (O.standardLift t).2
      continuous_angle := continuous_snd.comp O.contDiff_standardLift.continuous
      exp_angle := fun t ↦ by
        change Circle.exp (O.standardLift t).2 =
          (transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (O.standardCoordinates u)) t).2
        rw [show transportedLoopCoordinates Phi
            (fun u ↦ transportedTorusHomeomorph Phi (O.standardCoordinates u)) t =
              O.standardCoordinates t by
          exact (transportedTorusHomeomorph Phi).symm_apply_apply _]
        rfl
      winding := M.secondWinding
      angle_add_period := fun t ↦ by
        have h := congrArg Prod.snd (M.lift_add_period t)
        simpa only [Prod.snd_add] using h } }

/-- Ambient circle induced by the canonical cyclic component homeomorphism. -/
def ambientCircle (_M : SuperellipsoidOuterStandardPeriodData O.standardLift)
    (z : Circle) : R3 :=
  transportedTorusMap Phi
    ((SuperellipsoidOuterComponentOrbit.retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).circleHomeomorph z).1.1

theorem isEmbedding_ambientCircle : IsEmbedding M.ambientCircle := by
  apply (transportedTorusMap_isEmbedding Phi).comp
  exact IsEmbedding.subtypeVal.comp <|
    IsEmbedding.subtypeVal.comp
      (SuperellipsoidOuterComponentOrbit.retainedCyclicLineParametrization
        (componentCompact := componentCompact) O).circleHomeomorph.isEmbedding

theorem ambientCircle_parametrization (t : ℝ) :
    M.ambientCircle (Circle.exp t) = M.windingLoop.curve t := by
  rw [ambientCircle, O.circleHomeomorph_exp]
  change transportedTorusMap Phi
      ((O.standardComponentCurve t :
        superellipsoidTorusPolynomialLevelSet Phi frame c R).1) =
    transportedTorusMap Phi (O.standardCoordinates t)
  rw [O.standardCoordinates_eq_componentCurve]

/-- The smooth orbit gives an embedded ambient torus circle with its explicit winding loop. -/
def embeddedCircle : EmbeddedTorusIntersectionCircle Phi where
  circle := M.ambientCircle
  isEmbedding := M.isEmbedding_ambientCircle
  windingLoop := M.windingLoop
  parametrization := M.ambientCircle_parametrization

theorem embeddedCircle_range_eq_component :
    Set.range M.embeddedCircle.circle =
      (fun z : superellipsoidTorusPolynomialLevelSet Phi frame c R ↦
        transportedTorusMap Phi z) '' componentPiece k := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let q := (SuperellipsoidOuterComponentOrbit.retainedCyclicLineParametrization
      (componentCompact := componentCompact) O).circleHomeomorph z
    exact ⟨q.1, q.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ :=
      (SuperellipsoidOuterComponentOrbit.retainedCyclicLineParametrization
        (componentCompact := componentCompact) O).circleHomeomorph.surjective ⟨z, hz⟩
    exact ⟨w, congrArg (fun u : componentPiece k ↦
      transportedTorusMap Phi u.1.1) hw⟩

/-- The ambient loop is exactly the transported covering-plane orbit. -/
theorem windingLoop_curve_eq_planeMap (t : ℝ) :
    (M.windingLoop.curve t : R3) =
      transportedTorusPlaneMap Phi (O.standardLift t) := by
  change transportedTorusMap Phi (planeExpPair (O.standardLift t)) = _
  exact (transportedTorusPlaneMap_eq_expPair Phi (O.standardLift t)).symm

/-- Cutting height on the ambient loop is the coordinate lift along the retained planar orbit. -/
theorem windingLoopCutHeight_eq :
    windingLoopCutHeight frame d M.windingLoop =
      fun t ↦ orientedCoordinateLift Phi frame 2 (O.standardLift t) - d := by
  funext t
  unfold windingLoopCutHeight orientedCoordinateLift
  rw [M.windingLoop_curve_eq_planeMap]
  simp only [ambientCoordinate_apply]

/-- Derivative of the cutting height along the outer rotated-gradient orbit. -/
theorem hasDerivAt_heightDifference (t : ℝ) :
    HasDerivAt
      (fun u ↦ orientedCoordinateLift Phi frame 2 (O.standardLift u) - d)
      (O.standardScale * planarDifferentialDet
        (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) (O.standardLift t)) t := by
  let f := superellipsoidPolynomialLift Phi frame c
  let g := orientedCoordinateLift Phi frame 2
  have hg : DifferentiableAt ℝ g (O.standardLift t) :=
    (orientedCoordinateLift_contDiff Phi frame 2).differentiable
      (by simp) (O.standardLift t)
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt t (O.hasDerivAt_standardLift t)
  have heval : fderiv ℝ g (O.standardLift t)
      (rotatedDerivativeField f (O.standardLift t)) =
        planarDifferentialDet f g (O.standardLift t) := by
    rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, planarDifferentialDet]
    ring
  rw [map_smul, smul_eq_mul, heval] at hcomp
  exact hcomp.sub_const d

/-- Seam transversality makes height zero a regular value on every smooth outer circle. -/
theorem smoothRegularLoopCutData
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    SmoothRegularLoopCutData frame d M.embeddedCircle.windingLoop where
  contDiff_height := by
    change ContDiff ℝ 1 (windingLoopCutHeight frame d M.windingLoop)
    rw [M.windingLoopCutHeight_eq]
    exact ((orientedCoordinateLift_contDiff Phi frame 2).of_le
      (WithTop.coe_le_coe.mpr le_top)).comp O.contDiff_standardLift |>.sub contDiff_const
  regular_zero := by
    intro t ht
    change windingLoopCutHeight frame d M.windingLoop t = 0 at ht
    change deriv (windingLoopCutHeight frame d M.windingLoop) t ≠ 0
    have hheight : orientedCoordinateLift Phi frame 2 (O.standardLift t) = d := by
      rw [M.windingLoopCutHeight_eq] at ht
      exact sub_eq_zero.mp ht
    have hdet : planarDifferentialDet
        (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) (O.standardLift t) ≠ 0 :=
      hseam (O.standardLift t) (O.standardLift_stays_in_level t) hheight
    have hderiv :=
      (SuperellipsoidOuterStandardPeriodData.hasDerivAt_heightDifference
        (O := O) (d := d) t).deriv
    rw [M.windingLoopCutHeight_eq, hderiv]
    exact mul_ne_zero O.standardScale_ne_zero hdet

end SuperellipsoidOuterStandardPeriodData

/-! ## Finite smooth outer family -/

/-- A regular outer finite-circle family together with the smooth height data on each retained
orbit parametrization. -/
structure FiniteSuperellipsoidOuterTorusSmoothCircleFamily
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (R d : ℝ) where
  index : Type*
  finite_index : Finite index
  circle : index → EmbeddedTorusIntersectionCircle Phi
  circle_mem_outer : ∀ i, Set.range (circle i).circle ⊆
    superellipsoidOuterTorusSection Phi frame c R
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  outer_exact : superellipsoidOuterTorusSection Phi frame c R =
    ⋃ i, Set.range (circle i).circle
  smoothHeight : ∀ i, SmoothRegularLoopCutData frame d (circle i).windingLoop

namespace FiniteSuperellipsoidOuterTorusSmoothCircleFamily

/-- The regular outer value and seam transversality construct the smooth finite outer family. -/
noncomputable def ofRegularValue
    (hR : 0 ≤ R)
    (hregular : IsRegularValue
      (superellipsoidPolynomialLift Phi frame c) (R ^ 256))
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    FiniteSuperellipsoidOuterTorusSmoothCircleFamily Phi frame c R d := by
  let Level := superellipsoidTorusPolynomialLevelSet Phi frame c R
  let _ : CompactSpace Level := isCompact_iff_compactSpace.mp
    (isCompact_superellipsoidTorusPolynomialLevelSet Phi frame c R)
  have hlocal : IsLocallyLineModeled Level := by
    change IsLocallyLineModeled
      (periodicQuotientLevelSet
        (superellipsoidTorusPolynomial Phi frame c) (R ^ 256))
    exact isLocallyLineModeled_periodicQuotientLevel_of_regularValue
      (contDiff_superellipsoidPolynomialLift Phi frame c)
      (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c)
      hregular
  let _ : LocallyConnectedSpace Level :=
    locallyConnectedSpace_of_isLocallyLineModeled hlocal
  let components := finiteComponentDecompositionOfCompactLocallyConnected Level
  let componentCompact : ∀ k : ConnectedComponents Level,
      CompactSpace (componentPiece k) := fun k ↦
    isCompact_iff_compactSpace.mp (isClopen_componentPiece k).isClosed.isCompact
  letI : ∀ k : ConnectedComponents Level, CompactSpace (componentPiece k) :=
    componentCompact
  let orbit (k : ConnectedComponents Level) := Classical.choice
    (exists_superellipsoidOuterComponentOrbit hregular k)
  let standard (k : ConnectedComponents Level) :
      SuperellipsoidOuterStandardPeriodData (orbit k).standardLift :=
    superellipsoidOuterStandardPeriodData (orbit k)
  let circle (k : ConnectedComponents Level) : EmbeddedTorusIntersectionCircle Phi :=
    (standard k).embeddedCircle
  exact {
    index := ConnectedComponents Level
    finite_index := components.finite_index
    circle := circle
    circle_mem_outer := by
      intro k _ hx
      rw [(standard k).embeddedCircle_range_eq_component] at hx
      obtain ⟨z, _, rfl⟩ := hx
      exact ⟨⟨z, rfl⟩,
        (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).2 z.property⟩
    pairwise_disjoint := by
      intro k l hkl
      rw [(standard k).embeddedCircle_range_eq_component,
        (standard l).embeddedCircle_range_eq_component, Set.disjoint_left]
      rintro x ⟨z, hzk, rfl⟩ ⟨w, hwl, hw⟩
      have hzw : z = w := by
        apply Subtype.ext
        apply transportedTorusMap_injective Phi
        exact hw.symm
      exact Set.disjoint_left.mp (pairwise_disjoint_componentPiece hkl)
        hzk (hzw ▸ hwl)
    outer_exact := by
      ext x
      constructor
      · rintro ⟨⟨z, rfl⟩, hxboundary⟩
        let q : Level := ⟨z,
          (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).1
            hxboundary⟩
        have hq : q ∈ ⋃ k, componentPiece k := by
          rw [iUnion_componentPiece]
          exact mem_univ q
        simp only [Set.mem_iUnion] at hq ⊢
        obtain ⟨k, hk⟩ := hq
        refine ⟨k, ?_⟩
        rw [(standard k).embeddedCircle_range_eq_component]
        exact ⟨q, hk, rfl⟩
      · simp only [Set.mem_iUnion]
        rintro ⟨k, hx⟩
        rw [(standard k).embeddedCircle_range_eq_component] at hx
        obtain ⟨z, _, rfl⟩ := hx
        exact ⟨⟨z, rfl⟩,
          (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).2 z.property⟩
    smoothHeight := by
      intro k
      exact (standard k).smoothRegularLoopCutData hseam }

/-- Forget smooth provenance and expose the existing outer-family interface. -/
def toOuterCircleFamily
    (F : FiniteSuperellipsoidOuterTorusSmoothCircleFamily Phi frame c R d) :
    FiniteSuperellipsoidOuterTorusCircleFamily Phi frame c R where
  index := F.index
  finite_index := F.finite_index
  circle := F.circle
  circle_mem_outer := F.circle_mem_outer
  pairwise_disjoint := F.pairwise_disjoint
  outer_exact := F.outer_exact

/-- Expose the common finite-section interface while preserving definitional equality of its
circle parametrizations with `smoothHeight`. -/
def toFiniteEmbeddedTorusCircleSection
    (F : FiniteSuperellipsoidOuterTorusSmoothCircleFamily Phi frame c R d)
    [Fintype F.index] :
    FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R) F.index where
  circle := F.circle
  circle_mem_section := F.circle_mem_outer
  pairwise_disjoint := F.pairwise_disjoint
  section_exact := F.outer_exact

end FiniteSuperellipsoidOuterTorusSmoothCircleFamily

end Submission.Topology
