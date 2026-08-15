import Submission.Topology.LoopCarrier
import Submission.Topology.SolidTorus

/-!
# Arbitrary compressing disks for the transported torus

This module removes the affine-boundary restriction from the solid-torus
compression argument.  A boundary loop is represented by an arbitrary
continuous periodic loop with an explicit covering lift.  If it bounds an
embedded disk whose interior misses the torus, the disk lies on one of the
two closed sides.  The circle coordinate extending over that side then has
zero winding.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-! ## Winding vanishes for every filled loop -/

/-- A circle loop equipped with a covering lift has winding zero whenever it
extends continuously across the closed unit disk. -/
theorem CircleLoopLift.winding_eq_zero_of_unitDisk_filling
    {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    (g : ClosedUnitDisk → Circle) (hg : Continuous g)
    (hboundary : ∀ t, g (unitDiskBoundary t) = gamma t) :
    L.winding = 0 := by
  let gc : C(ℂ, Circle) :=
    ⟨fun z ↦ g (radialProjection z), hg.comp continuous_radialProjection⟩
  have hbase : Circle.exp (((gc 0 : Circle) : ℂ).arg) = gc (0 : ℂ) := by
    exact Circle.exp_arg _
  obtain ⟨G, _hG0, hGlift⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℂ) (((gc 0 : Circle) : ℂ).arg) hbase |>.exists
  let M : CircleLoopLift gamma := {
    angle := fun t ↦ G (unitCircleParam t)
    continuous_angle := G.continuous.comp continuous_unitCircleParam
    exp_angle := fun t ↦ by
      have hlift := congrFun hGlift (unitCircleParam t)
      change Circle.exp (G (unitCircleParam t)) = gc (unitCircleParam t) at hlift
      change Circle.exp (G (unitCircleParam t)) = _
      rw [hlift]
      change g (radialProjection (unitCircleParam t)) = gamma t
      rw [radialProjection_unitCircleParam]
      exact hboundary t
    winding := 0
    angle_add_period := fun t ↦ by
      simp only [Int.cast_zero, zero_mul, add_zero]
      rw [unitCircleParam_add_two_pi]
  }
  exact L.winding_eq M

/-- Circle-valued coordinates may be inserted after an arbitrary filled
disk; the winding of any chosen lift of the boundary coordinate is zero. -/
theorem CircleLoopLift.winding_eq_zero_of_continuous_coordinate_filling
    {X : Type*} [TopologicalSpace X] {gamma : ℝ → Circle}
    (L : CircleLoopLift gamma) (g : ClosedUnitDisk → X) (hg : Continuous g)
    (coordinate : X → Circle) (hcoordinate : Continuous coordinate)
    (hboundary : ∀ t, coordinate (g (unitDiskBoundary t)) = gamma t) :
    L.winding = 0 := by
  exact L.winding_eq_zero_of_unitDisk_filling (coordinate ∘ g)
    (hcoordinate.comp hg) hboundary

/-- Inversion followed by squaring multiplies winding by `-2`. -/
def CircleLoopLift.invSq {gamma : ℝ → Circle} (L : CircleLoopLift gamma) :
    CircleLoopLift (fun t ↦ (gamma t)⁻¹ ^ 2) where
  angle := fun t ↦ -2 * L.angle t
  continuous_angle := continuous_const.mul L.continuous_angle
  exp_angle := fun t ↦ by
    rw [← circle_exp_inv_sq, L.exp_angle]
  winding := -2 * L.winding
  angle_add_period := fun t ↦ by
    rw [L.angle_add_period]
    push_cast
    ring

/-! ## General compressing-disk data -/

/-- An embedded disk whose boundary is an arbitrary winding-certified loop
on the transported torus and whose open interior misses the torus. -/
structure GeneralCompressingDiskWitness (Phi : AmbientIsotopy) where
  boundaryLoop : TransportedWindingLoop Phi Set.univ
  disk : ClosedUnitDisk → R3
  isEmbedding : IsEmbedding disk
  boundary : ∀ t, disk (unitDiskBoundary t) = boundaryLoop.curve t
  interior_disjoint : ∀ z : ClosedUnitDisk, ‖(z : ℂ)‖ < 1 →
    disk z ∉ transportedTorus Phi
  essential : boundaryLoop.windingPair ≠ (0, 0)

namespace GeneralCompressingDiskWitness

variable {Phi : AmbientIsotopy}

theorem continuous (D : GeneralCompressingDiskWitness Phi) :
    Continuous D.disk :=
  D.isEmbedding.continuous

def LiesInTubeSide (D : GeneralCompressingDiskWitness Phi) : Prop :=
  ∀ z, D.disk z ∈ transportedTubeSide Phi

def LiesInExteriorSide (D : GeneralCompressingDiskWitness Phi) : Prop :=
  ∀ z, D.disk z ∈ transportedExteriorSide Phi

/-- Every boundary point maps to the transported torus, hence has gauge one
after applying the time-one ambient homeomorphism. -/
theorem boundary_tubeGauge_eq_one (D : GeneralCompressingDiskWitness Phi)
    {z : ClosedUnitDisk} (hz : ‖(z : ℂ)‖ = 1) :
    tubeGauge (Phi.H 1 (D.disk z)) = 1 := by
  let w : Circle := ⟨(z : ℂ), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hz⟩
  obtain ⟨t, ht⟩ := Circle.exp_surjective w
  have hzBoundary : unitDiskBoundary t = z := by
    apply Subtype.ext
    change unitCircleParam t = (z : ℂ)
    rw [← circle_exp_coe_eq_unitCircleParam, ht]
  rw [← hzBoundary, D.boundary]
  obtain ⟨zw, hzw⟩ := (D.boundaryLoop.curve t).property
  rw [← hzw, timeOne_map_transportedTorusMap]
  exact circleTorusMap_tubeGauge zw.1 zw.2

/-- Gauge of the disk after radial projection from the complex plane. -/
def radialGauge (D : GeneralCompressingDiskWitness Phi) (z : ℂ) : ℝ :=
  tubeGauge (Phi.H 1 (D.disk (radialProjection z)))

theorem continuous_radialGauge (D : GeneralCompressingDiskWitness Phi) :
    Continuous D.radialGauge := by
  exact continuous_tubeGauge.comp
    ((continuous_timeOne_map Phi).comp
      (D.continuous.comp continuous_radialProjection))

theorem radialGauge_coe (D : GeneralCompressingDiskWitness Phi)
    (z : ClosedUnitDisk) :
    D.radialGauge (z : ℂ) = tubeGauge (Phi.H 1 (D.disk z)) := by
  unfold radialGauge
  congr 3
  apply Subtype.ext
  apply radialProjection_eq_self
  have hz := z.property
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  exact hz

/-- The connected disk cannot cross from one complementary side of the torus
to the other without an interior point landing on the torus. -/
theorem liesInTubeSide_or_liesInExteriorSide
    (D : GeneralCompressingDiskWitness Phi) :
    D.LiesInTubeSide ∨ D.LiesInExteriorSide := by
  by_cases hin : ∀ z, tubeGauge (Phi.H 1 (D.disk z)) ≤ 1
  · exact Or.inl hin
  right
  intro z
  change 1 ≤ tubeGauge (Phi.H 1 (D.disk z))
  by_contra hzlow
  have hzlow' : tubeGauge (Phi.H 1 (D.disk z)) < 1 := lt_of_not_ge hzlow
  push Not at hin
  obtain ⟨w, hwhigh⟩ := hin
  have hzInterior : ‖(z : ℂ)‖ < 1 := by
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      have hz := z.property
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact hz
    refine lt_of_le_of_ne hzle ?_
    intro hzone
    have := D.boundary_tubeGauge_eq_one hzone
    linarith
  have hwInterior : ‖(w : ℂ)‖ < 1 := by
    have hwle : ‖(w : ℂ)‖ ≤ 1 := by
      have hw := w.property
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
    refine lt_of_le_of_ne hwle ?_
    intro hwone
    have := D.boundary_tubeGauge_eq_one hwone
    linarith
  have hzGauge : D.radialGauge (z : ℂ) < 1 := by
    rw [D.radialGauge_coe]
    exact hzlow'
  have hwGauge : 1 < D.radialGauge (w : ℂ) := by
    rw [D.radialGauge_coe]
    exact hwhigh
  obtain ⟨u, huBall, huGauge⟩ :=
    (convex_ball (0 : ℂ) 1).isPreconnected.intermediate_value
      (by simpa [Metric.mem_ball, dist_zero_right] using hzInterior)
      (by simpa [Metric.mem_ball, dist_zero_right] using hwInterior)
      D.continuous_radialGauge.continuousOn
      ⟨hzGauge.le, hwGauge.le⟩
  have huNorm : ‖u‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using huBall
  have huProjection : (radialProjection u : ℂ) = u :=
    radialProjection_eq_self huNorm.le
  apply D.interior_disjoint (radialProjection u) (by simpa [huProjection])
  apply mem_transportedTorus_of_tubeGauge_timeOne_eq_one Phi
  change D.radialGauge u = 1
  exact huGauge

private theorem curve_eq_transportedTorusMap_coordinates
    (D : GeneralCompressingDiskWitness Phi) (t : ℝ) :
    (D.boundaryLoop.curve t : R3) = transportedTorusMap Phi
      (transportedLoopCoordinates Phi D.boundaryLoop.curve t) := by
  change (D.boundaryLoop.curve t : R3) =
    (((transportedTorusHomeomorph Phi)
      ((transportedTorusHomeomorph Phi).symm (D.boundaryLoop.curve t))) :
        transportedTorus Phi)
  exact congrArg Subtype.val
    ((transportedTorusHomeomorph Phi).apply_symm_apply (D.boundaryLoop.curve t)).symm

/-- On the tube side, the longitude winding of an arbitrary compressing
boundary vanishes. -/
theorem first_winding_eq_zero_of_liesInTubeSide
    (D : GeneralCompressingDiskWitness Phi) (hside : D.LiesInTubeSide) :
    D.boundaryLoop.lift.first.winding = 0 := by
  let g : ClosedUnitDisk → transportedTubeSide Phi :=
    fun z ↦ ⟨D.disk z, hside z⟩
  have hg : Continuous g := D.continuous.subtype_mk _
  let L := D.boundaryLoop.lift.first.invSq
  have hboundary : ∀ t,
      transportedTubeLongitudeCoordinate Phi (g (unitDiskBoundary t)) =
        ((transportedLoopCoordinates Phi D.boundaryLoop.curve t).1)⁻¹ ^ 2 := by
    intro t
    let zw := transportedLoopCoordinates Phi D.boundaryLoop.curve t
    have hcurve := D.curve_eq_transportedTorusMap_coordinates t
    change transportedTubeLongitudeCoordinate Phi
      ⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
      apply Subtype.ext
      exact (D.boundary t).trans hcurve]
    exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2
  have hzero := L.winding_eq_zero_of_continuous_coordinate_filling
    g hg (transportedTubeLongitudeCoordinate Phi)
    (continuous_transportedTubeLongitudeCoordinate Phi) hboundary
  change -2 * D.boundaryLoop.lift.first.winding = 0 at hzero
  omega

/-- On the exterior side, the meridian winding of an arbitrary compressing
boundary vanishes. -/
theorem second_winding_eq_zero_of_liesInExteriorSide
    (D : GeneralCompressingDiskWitness Phi) (hside : D.LiesInExteriorSide) :
    D.boundaryLoop.lift.second.winding = 0 := by
  let g : ClosedUnitDisk → transportedExteriorSide Phi :=
    fun z ↦ ⟨D.disk z, hside z⟩
  have hg : Continuous g := D.continuous.subtype_mk _
  let L := D.boundaryLoop.lift.second.invSq
  have hboundary : ∀ t,
      transportedExteriorMeridianCoordinate Phi (g (unitDiskBoundary t)) =
        ((transportedLoopCoordinates Phi D.boundaryLoop.curve t).2)⁻¹ ^ 2 := by
    intro t
    let zw := transportedLoopCoordinates Phi D.boundaryLoop.curve t
    have hcurve := D.curve_eq_transportedTorusMap_coordinates t
    change transportedExteriorMeridianCoordinate Phi
      ⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨D.disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
      apply Subtype.ext
      exact (D.boundary t).trans hcurve]
    exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2
  have hzero := L.winding_eq_zero_of_continuous_coordinate_filling
    g hg (transportedExteriorMeridianCoordinate Phi)
    (continuous_transportedExteriorMeridianCoordinate Phi) hboundary
  change -2 * D.boundaryLoop.lift.second.winding = 0 at hzero
  omega

/-- Every arbitrary compressing boundary has one of its two winding
coordinates equal to zero. -/
theorem first_eq_zero_or_second_eq_zero
    (D : GeneralCompressingDiskWitness Phi) :
    D.boundaryLoop.lift.first.winding = 0 ∨
      D.boundaryLoop.lift.second.winding = 0 := by
  rcases D.liesInTubeSide_or_liesInExteriorSide with hin | hout
  · exact Or.inl (D.first_winding_eq_zero_of_liesInTubeSide hin)
  · exact Or.inr (D.second_winding_eq_zero_of_liesInExteriorSide hout)

/-- Primitivity is not needed for Pardon's lower bound: once one coordinate
vanishes and the boundary is essential, the determinant with the `(p,q)`
knot slope is already at least `min p q`. -/
theorem min_le_slopeIntersectionNumber
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) :
    min p q ≤ slopeIntersectionNumber p q
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding := by
  have hessential : D.boundaryLoop.lift.first.winding ≠ 0 ∨
      D.boundaryLoop.lift.second.winding ≠ 0 := by
    by_cases hm : D.boundaryLoop.lift.first.winding = 0
    · right
      intro hn
      apply D.essential
      simp [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair,
        hm, hn]
    · exact Or.inl hm
  rcases D.first_eq_zero_or_second_eq_zero with hm | hn
  · have hn0 : D.boundaryLoop.lift.second.winding ≠ 0 := by
      rcases hessential with hm0 | hn0
      · exact (hm0 hm).elim
      · exact hn0
    rw [slopeIntersectionNumber, slopeIntersectionDet, hm]
    simp only [Int.mul_zero, sub_zero, Int.natAbs_mul,
      Int.natAbs_natCast]
    exact (min_le_left p q).trans
      (Nat.le_mul_of_pos_right p (Int.natAbs_pos.mpr hn0))
  · have hm0 : D.boundaryLoop.lift.first.winding ≠ 0 := by
      rcases hessential with hm0 | hn0
      · exact hm0
      · exact (hn0 hn).elim
    rw [slopeIntersectionNumber, slopeIntersectionDet, hn]
    simp only [Int.mul_zero, zero_sub, Int.natAbs_neg,
      Int.natAbs_mul, Int.natAbs_natCast]
    exact (min_le_right p q).trans
      (Nat.le_mul_of_pos_right q (Int.natAbs_pos.mpr hm0))

end GeneralCompressingDiskWitness

end Submission.PardonDistortion
