import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Smooth circle parametrizations of regular cutting sections

The ordinary coordinate-plane classifier exposes finite embedded circles but forgets the smooth
complete rotated-gradient orbits used to construct them.  This module retains those canonical
orbits, their standardized real lifts, and the exact finite-section decomposition.  The retained
lifts instantiate the cyclic cut-order interface without any new analytic hypothesis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- Smooth lifted-orbit data for one embedded coordinate-level circle, before choosing a barrier
graph that contains the circle. -/
structure SmoothCoordinateCircleLiftData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (circle : EmbeddedTorusIntersectionCircle Phi) where
  lift : ℝ → Plane
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  contDiff_lift : ContDiff ℝ 1 lift
  curve_eq : ∀ t,
    transportedTorusPlaneMap Phi (lift t) = (circle.windingLoop.curve t : R3)
  height_level : ∀ t, orientedCoordinateLift Phi frame 2 (lift t) = d
  integral : ∀ t, HasDerivAt lift
    (scale • rotatedDerivativeField (orientedCoordinateLift Phi frame 2) (lift t)) t

namespace SmoothCoordinateCircleLiftData

variable {circle : EmbeddedTorusIntersectionCircle Phi}

/-- The standard-period form of a complete regular coordinate-level orbit supplies the retained
smooth lift. -/
def ofRegularOrbitStandardPeriodData
    {component : ConnectedComponents (coordinateTorusLevelSet Phi frame d)}
    [CompactSpace (componentPiece component)]
    (O : RegularComponentCompleteOrbit Phi frame d component)
    (M : RegularOrbitStandardPeriodData O) :
    SmoothCoordinateCircleLiftData Phi frame d M.embeddedCircle where
  lift := O.standardLift
  scale := (2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period
  scale_ne_zero := mul_ne_zero (inv_ne_zero (ne_of_gt Real.two_pi_pos))
    O.cyclicLineParametrization.period_ne_zero
  contDiff_lift := O.contDiff_standardLift
  curve_eq := by
    intro t
    change transportedTorusPlaneMap Phi (O.standardLift t) =
      transportedTorusMap Phi (M.coordinates t)
    rw [transportedTorusPlaneMap_eq_expPair]
    rfl
  height_level := O.standardLift_stays_in_level
  integral := by
    intro t
    have hderiv := (O.contDiff_standardLift.differentiable (by simp) t).hasDerivAt
    rw [O.deriv_standardLift] at hderiv
    exact hderiv

/-- Once a retained smooth circle is installed as a barrier cut circle, its lift supplies the
existing cut-order input definitionally. -/
def toSmoothCutCircleLiftData
    {c : R3} {R : ℝ} {outerIndex cutIndex : Type*}
    [Fintype outerIndex] [Fintype cutIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {j : cutIndex}
    (D : SmoothCoordinateCircleLiftData Phi frame d circle)
    (hcircle : G.cut.circle j = circle) :
    FiniteSuperellipsoidBarrierGraph.SmoothCutCircleLiftData G j where
  lift := D.lift
  scale := D.scale
  scale_ne_zero := D.scale_ne_zero
  contDiff_lift := D.contDiff_lift
  curve_eq := by
    intro t
    rw [hcircle]
    exact D.curve_eq t
  height_level := D.height_level
  integral := D.integral

end SmoothCoordinateCircleLiftData

/-- The complete finite coordinate-plane section, retaining the canonical smooth lift of every
circle. -/
structure FiniteCoordinatePlaneTorusSmoothCircleFamily
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) where
  index : Type*
  finite_index : Finite index
  circle : index → EmbeddedTorusIntersectionCircle Phi
  circle_mem_plane : ∀ i, Set.range (circle i).circle ⊆ coordinateCuttingPlane frame d
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  intersection_exact : transportedTorus Phi ∩ coordinateCuttingPlane frame d =
    ⋃ i, Set.range (circle i).circle
  smoothLift : ∀ i, SmoothCoordinateCircleLiftData Phi frame d (circle i)

namespace FiniteCoordinatePlaneTorusSmoothCircleFamily

/-- A regular coordinate value canonically constructs the complete smooth cutting-circle
family. -/
noncomputable def ofRegularValue
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d) :
    FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame d := by
  let Level := coordinateTorusLevelSet Phi frame d
  let _ : CompactSpace Level :=
    isCompact_iff_compactSpace.mp (isCompact_coordinateTorusLevelSet Phi frame d)
  have hlocal : IsLocallyLineModeled Level :=
    isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hd
  let _ : LocallyConnectedSpace Level :=
    locallyConnectedSpace_of_isLocallyLineModeled hlocal
  let components := finiteComponentDecompositionOfCompactLocallyConnected Level
  let componentCompact : ∀ k : ConnectedComponents Level,
      CompactSpace (componentPiece k) := fun k ↦
    isCompact_iff_compactSpace.mp (isClopen_componentPiece k).isClosed.isCompact
  letI : ∀ k : ConnectedComponents Level, CompactSpace (componentPiece k) :=
    componentCompact
  let orbit (k : ConnectedComponents Level) :=
    Classical.choice (exists_regularComponentCompleteOrbit Phi frame hd k)
  let standard (k : ConnectedComponents Level) : RegularOrbitStandardPeriodData (orbit k) :=
    regularOrbitStandardPeriodData (orbit k)
  let circle (k : ConnectedComponents Level) : EmbeddedTorusIntersectionCircle Phi :=
    (standard k).embeddedCircle
  exact {
    index := ConnectedComponents Level
    finite_index := components.finite_index
    circle := circle
    circle_mem_plane := by
      intro k _ hx
      rw [(standard k).embeddedCircle_range_eq_component] at hx
      obtain ⟨z, _, rfl⟩ := hx
      exact z.property
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
    intersection_exact := by
      ext x
      constructor
      · rintro ⟨⟨z, rfl⟩, hxplane⟩
        let q : Level := ⟨z, hxplane⟩
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
        exact ⟨⟨z, rfl⟩, z.property⟩
    smoothLift := by
      intro k
      exact SmoothCoordinateCircleLiftData.ofRegularOrbitStandardPeriodData
        (orbit k) (standard k) }

/-- Forget smooth provenance and expose the existing coordinate-plane family interface. -/
def toCoordinateCircleFamily
    (F : FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame d) :
    FiniteCoordinatePlaneTorusCircleFamily Phi frame d where
  index := F.index
  finite_index := F.finite_index
  circle := F.circle
  circle_mem_plane := F.circle_mem_plane
  pairwise_disjoint := F.pairwise_disjoint
  intersection_exact := F.intersection_exact

/-- Expose the common finite-section interface while preserving definitional equality of the
circle parametrizations with their retained smooth lifts. -/
def toFiniteEmbeddedTorusCircleSection
    (F : FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame d)
    [Fintype F.index] :
    FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame d) F.index where
  circle := F.circle
  circle_mem_section := fun i _ hx ↦
    ⟨(F.circle i).range_subset_transportedTorus hx, F.circle_mem_plane i hx⟩
  pairwise_disjoint := F.pairwise_disjoint
  section_exact := F.intersection_exact

end FiniteCoordinatePlaneTorusSmoothCircleFamily
end Submission.Topology
