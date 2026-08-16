import Mathlib.Analysis.Convex.GaugeRescale
import Submission.SuperellipsoidGeometry
import Submission.Topology.HalfSphereSurgeryDichotomy

/-!
# Convex sphere foundations for the superellipsoid surgery

The closed outer superellipsoid and its two closed half-space truncations are bounded convex
bodies.  Whenever the cutting plane leaves a strict interior point on each side, the convex-body
gauge-rescaling theorem identifies each frontier with the unit sphere.  Pulling the unit sphere
back through that ambient homeomorphism gives the embedded topological spheres used at the
singular three-page stage.

The lower and upper truncated frontiers share their cutting disk.  Accordingly, the bundled
singular-limit data below contains no disjointness assertion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped ENNReal

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion

/-! ## A reusable convex-body sphere -/

/-- The ambient homeomorphism supplied by convex gauge rescaling, retaining all three exact
image equations. -/
structure ConvexBodySphereData (s : Set R3) where
  ambientHomeomorph : R3 ≃ₜ R3
  image_interior : ambientHomeomorph '' interior s = Metric.ball 0 1
  image_closure : ambientHomeomorph '' closure s = Metric.closedBall 0 1
  image_frontier : ambientHomeomorph '' frontier s = Metric.sphere 0 1

namespace ConvexBodySphereData

/-- A bounded convex body with nonempty interior has canonical sphere data after making the
choice of the gauge-rescaling homeomorphism. -/
def ofConvexBounded {s : Set R3} (hconvex : Convex ℝ s)
    (hinterior : (interior s).Nonempty) (hbounded : Bornology.IsBounded s) :
    ConvexBodySphereData s := by
  let hexists :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hconvex hinterior hbounded
  let h := Classical.choose hexists
  let hh := Classical.choose_spec hexists
  exact
    { ambientHomeomorph := h
      image_interior := hh.1
      image_closure := hh.2.1
      image_frontier := hh.2.2 }

/-- Pull back the standard unit sphere through the convex gauge-rescaling homeomorphism. -/
def sphere {s : Set R3} (D : ConvexBodySphereData s) :
    EmbeddedTopologicalSphereInR3 where
  parametrization := fun x ↦ D.ambientHomeomorph.symm x.1
  isEmbedding := D.ambientHomeomorph.symm.isEmbedding.comp IsEmbedding.subtypeVal

/-- The pulled-back unit sphere has exactly the frontier of the original convex body as its
ambient carrier. -/
theorem sphere_carrier_eq_frontier {s : Set R3} (D : ConvexBodySphereData s) :
    D.sphere.carrier = frontier s := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hz : z.1 ∈ D.ambientHomeomorph '' frontier s := by
      rw [D.image_frontier]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := hz
    change D.ambientHomeomorph.symm z.1 ∈ frontier s
    rw [← hyz, D.ambientHomeomorph.symm_apply_apply]
    exact hy
  · intro hx
    have himage : D.ambientHomeomorph x ∈ Metric.sphere (0 : R3) 1 := by
      rw [← D.image_frontier]
      exact ⟨x, hx, rfl⟩
    refine ⟨⟨D.ambientHomeomorph x, himage⟩, ?_⟩
    exact D.ambientHomeomorph.symm_apply_apply x

/-- For a closed convex body, the recorded closure equation is an equation for the body itself. -/
theorem image_eq_closedBall_of_isClosed {s : Set R3} (D : ConvexBodySphereData s)
    (hclosed : IsClosed s) :
    D.ambientHomeomorph '' s = Metric.closedBall (0 : R3) 1 := by
  calc
    D.ambientHomeomorph '' s = D.ambientHomeomorph '' closure s :=
      congrArg (fun t : Set R3 ↦ D.ambientHomeomorph '' t) hclosed.closure_eq.symm
    _ = Metric.closedBall 0 1 := D.image_closure

end ConvexBodySphereData

/-! ## Convexity and boundedness of the smooth body -/

/-- Weighted `L^256` coordinates preserve convex combinations based at the center. -/
theorem superellipsoidCoordinates_convexCombination
    (frame : Equiv.Perm (Fin 3)) (c x y : R3) (a b : ℝ) (hab : a + b = 1) :
    superellipsoidCoordinates frame c (a • x + b • y) =
      a • superellipsoidCoordinates frame c x +
        b • superellipsoidCoordinates frame c y := by
  apply PiLp.ext
  intro i
  change
    ((a • x + b • y - c).ofLp (frame i) / axisWeight i) =
      a * ((x - c).ofLp (frame i) / axisWeight i) +
        b * ((y - c).ofLp (frame i) / axisWeight i)
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
  field_simp [ne_of_gt (axisWeight_pos i)]
  linear_combination c.ofLp (frame i) * hab

/-- The closed smooth superellipsoid is convex. -/
theorem convex_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    Convex ℝ (closedSuperellipsoidBody frame c R) := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change superellipsoidGauge frame c x ≤ R at hx
  change superellipsoidGauge frame c y ≤ R at hy
  change superellipsoidGauge frame c (a • x + b • y) ≤ R
  rw [superellipsoidGauge,
    superellipsoidCoordinates_convexCombination frame c x y a b hab]
  calc
    ‖a • superellipsoidCoordinates frame c x +
        b • superellipsoidCoordinates frame c y‖ ≤
        ‖a • superellipsoidCoordinates frame c x‖ +
          ‖b • superellipsoidCoordinates frame c y‖ := norm_add_le _ _
    _ = a * superellipsoidGauge frame c x + b * superellipsoidGauge frame c y := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      rfl
    _ ≤ a * R + b * R :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

/-- The closed smooth body has bounded diameter at every positive scale. -/
theorem isBounded_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (closedSuperellipsoidBody frame c R) := by
  rw [Metric.isBounded_iff]
  refine ⟨(9 / 2 : ℝ) * R, ?_⟩
  intro x hx y hy
  exact (dist_lt_nine_halves_mul_scale_of_mem_closedSuperellipsoidBody
    frame c hR hx hy).le

/-- The smooth gauge vanishes at its center. -/
@[simp] theorem superellipsoidGauge_center
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    superellipsoidGauge frame c c = 0 := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [superellipsoidGauge]
  rw [show superellipsoidCoordinates frame c c = 0 by
    apply PiLp.ext
    intro i
    simp [superellipsoidCoordinates, normalizedOrientedBoxCoordinates]]
  exact norm_zero

private theorem continuous_superellipsoidGauge_convexSphere
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    Continuous (superellipsoidGauge frame c) := by
  let _ : Fact (1 ≤ (256 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hcoordinates : Continuous (superellipsoidCoordinates frame c) := by
    change Continuous (fun x ↦ WithLp.toLp 256 (normalizedOrientedBoxCoordinates frame c x))
    apply (PiLp.continuous_toLp 256 (fun _ : Fin 3 ↦ ℝ)).comp
    exact continuous_pi fun i ↦
      (((coordinateCLM (frame i)).continuous.comp
        (continuous_id.sub continuous_const)).div_const (axisWeight i))
  exact (continuous_norm.comp hcoordinates).congr fun _ ↦ rfl

/-- The open smooth body is open. -/
theorem isOpen_superellipsoidBody_convexSphere
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsOpen (superellipsoidBody frame c R) :=
  isOpen_Iio.preimage (continuous_superellipsoidGauge_convexSphere frame c)

/-- The closed smooth body is closed. -/
theorem isClosed_closedSuperellipsoidBody_convexSphere
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsClosed (closedSuperellipsoidBody frame c R) :=
  isClosed_Iic.preimage (continuous_superellipsoidGauge_convexSphere frame c)

/-- At a positive scale the closed smooth body has nonempty interior. -/
theorem nonempty_interior_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    (interior (closedSuperellipsoidBody frame c R)).Nonempty := by
  have hopen : IsOpen (superellipsoidBody frame c R) :=
    isOpen_superellipsoidBody_convexSphere frame c R
  have hsubset : superellipsoidBody frame c R ⊆
      closedSuperellipsoidBody frame c R := by
    intro x hx
    change superellipsoidGauge frame c x ≤ R
    exact hx.le
  refine ⟨c, interior_maximal hsubset hopen ?_⟩
  simpa [superellipsoidBody] using hR

/-! ## Closed truncations -/

/-- The closed lower truncation of the superellipsoid by the chosen oriented coordinate. -/
def closedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : Set R3 :=
  closedSuperellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d}

/-- The closed upper truncation of the superellipsoid by the chosen oriented coordinate. -/
def closedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : Set R3 :=
  closedSuperellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)}

/-- A closed lower truncation is closed. -/
theorem isClosed_closedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsClosed (closedLowerSuperellipsoidTruncation frame c R d) :=
  (isClosed_closedSuperellipsoidBody_convexSphere frame c R).inter
    (isClosed_Iic.preimage (coordinateCLM (frame 2)).continuous)

/-- A closed upper truncation is closed. -/
theorem isClosed_closedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsClosed (closedUpperSuperellipsoidTruncation frame c R d) :=
  (isClosed_closedSuperellipsoidBody_convexSphere frame c R).inter
    (isClosed_Ici.preimage (coordinateCLM (frame 2)).continuous)

private theorem isLinearMap_orientedCoordinate
    (frame : Equiv.Perm (Fin 3)) :
    IsLinearMap ℝ (fun x : R3 ↦ x.ofLp (frame 2)) :=
  .mk (coordinateCLM (frame 2)).map_add (coordinateCLM (frame 2)).map_smul

/-- A closed lower truncation is convex. -/
theorem convex_closedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Convex ℝ (closedLowerSuperellipsoidTruncation frame c R d) :=
  (convex_closedSuperellipsoidBody frame c R).inter
    (convex_halfSpace_le (isLinearMap_orientedCoordinate frame) d)

/-- A closed upper truncation is convex. -/
theorem convex_closedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    Convex ℝ (closedUpperSuperellipsoidTruncation frame c R d) :=
  (convex_closedSuperellipsoidBody frame c R).inter
    (convex_halfSpace_ge (isLinearMap_orientedCoordinate frame) d)

/-- Closed lower truncations remain bounded. -/
theorem isBounded_closedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (closedLowerSuperellipsoidTruncation frame c R d) :=
  (isBounded_closedSuperellipsoidBody frame c hR).subset inter_subset_left

/-- Closed upper truncations remain bounded. -/
theorem isBounded_closedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (closedUpperSuperellipsoidTruncation frame c R d) :=
  (isBounded_closedSuperellipsoidBody frame c hR).subset inter_subset_left

/-- A strict point in the open body below the cut witnesses nonempty interior of the closed lower
truncation. -/
theorem nonempty_interior_closedLowerSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hwitness : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d) :
    (interior (closedLowerSuperellipsoidTruncation frame c R d)).Nonempty := by
  obtain ⟨x, hxbody, hxcut⟩ := hwitness
  let u := superellipsoidBody frame c R ∩ {y | y.ofLp (frame 2) < d}
  have huopen : IsOpen u :=
    (isOpen_superellipsoidBody_convexSphere frame c R).inter
      (isOpen_Iio.preimage (coordinateCLM (frame 2)).continuous)
  have husubset : u ⊆ closedLowerSuperellipsoidTruncation frame c R d := by
    intro y hy
    change superellipsoidGauge frame c y ≤ R ∧ y.ofLp (frame 2) ≤ d
    exact ⟨hy.1.le, hy.2.le⟩
  exact ⟨x, interior_maximal husubset huopen ⟨hxbody, hxcut⟩⟩

/-- A strict point in the open body above the cut witnesses nonempty interior of the closed upper
truncation. -/
theorem nonempty_interior_closedUpperSuperellipsoidTruncation
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hwitness : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    (interior (closedUpperSuperellipsoidTruncation frame c R d)).Nonempty := by
  obtain ⟨x, hxbody, hxcut⟩ := hwitness
  let u := superellipsoidBody frame c R ∩ {y | d < y.ofLp (frame 2)}
  have huopen : IsOpen u :=
    (isOpen_superellipsoidBody_convexSphere frame c R).inter
      (isOpen_Ioi.preimage (coordinateCLM (frame 2)).continuous)
  have husubset : u ⊆ closedUpperSuperellipsoidTruncation frame c R d := by
    intro y hy
    change superellipsoidGauge frame c y ≤ R ∧ d ≤ y.ofLp (frame 2)
    exact ⟨hy.1.le, hy.2.le⟩
  exact ⟨x, interior_maximal husubset huopen ⟨hxbody, hxcut⟩⟩

/-! ## Outer and singular-limit sphere data -/

/-- Sphere data for the frontier of the closed outer superellipsoid. -/
def outerSuperellipsoidSphereData
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    ConvexBodySphereData (closedSuperellipsoidBody frame c R) :=
  .ofConvexBounded (convex_closedSuperellipsoidBody frame c R)
    (nonempty_interior_closedSuperellipsoidBody frame c hR)
    (isBounded_closedSuperellipsoidBody frame c hR)

/-- Sphere data for the lower truncated frontier. -/
def lowerTruncatedSuperellipsoidSphereData
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hwitness : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d) :
    ConvexBodySphereData (closedLowerSuperellipsoidTruncation frame c R d) :=
  .ofConvexBounded (convex_closedLowerSuperellipsoidTruncation frame c R d)
    (nonempty_interior_closedLowerSuperellipsoidTruncation frame c R d hwitness)
    (isBounded_closedLowerSuperellipsoidTruncation frame c (d := d) hR)

/-- Sphere data for the upper truncated frontier. -/
def upperTruncatedSuperellipsoidSphereData
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hwitness : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    ConvexBodySphereData (closedUpperSuperellipsoidTruncation frame c R d) :=
  .ofConvexBounded (convex_closedUpperSuperellipsoidTruncation frame c R d)
    (nonempty_interior_closedUpperSuperellipsoidTruncation frame c R d hwitness)
    (isBounded_closedUpperSuperellipsoidTruncation frame c (d := d) hR)

/-- The outer sphere together with the two literal truncated-frontier spheres at the singular
three-page stage.  The package deliberately asserts no pairwise disjointness. -/
structure SingularSuperellipsoidSphereData
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) where
  outer : ConvexBodySphereData (closedSuperellipsoidBody frame c R)
  lower : ConvexBodySphereData (closedLowerSuperellipsoidTruncation frame c R d)
  upper : ConvexBodySphereData (closedUpperSuperellipsoidTruncation frame c R d)

/-- Construct all three singular-limit spheres from strict interior witnesses on the two sides of
the cutting plane. -/
def singularSuperellipsoidSphereData
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    SingularSuperellipsoidSphereData frame c R d where
  outer := outerSuperellipsoidSphereData frame c hR
  lower := lowerTruncatedSuperellipsoidSphereData frame c hR hlower
  upper := upperTruncatedSuperellipsoidSphereData frame c hR hupper

/-- Exact carrier of the outer singular-limit sphere. -/
theorem singularSuperellipsoidSphereData_outer_carrier
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    (singularSuperellipsoidSphereData frame c hR hlower hupper).outer.sphere.carrier =
      frontier (closedSuperellipsoidBody frame c R) :=
  ConvexBodySphereData.sphere_carrier_eq_frontier _

/-- Exact carrier of the lower truncated singular-limit sphere. -/
theorem singularSuperellipsoidSphereData_lower_carrier
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    (singularSuperellipsoidSphereData frame c hR hlower hupper).lower.sphere.carrier =
      frontier (closedLowerSuperellipsoidTruncation frame c R d) :=
  ConvexBodySphereData.sphere_carrier_eq_frontier _

/-- Exact carrier of the upper truncated singular-limit sphere. -/
theorem singularSuperellipsoidSphereData_upper_carrier
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R d : ℝ} (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧ x.ofLp (frame 2) < d)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧ d < x.ofLp (frame 2)) :
    (singularSuperellipsoidSphereData frame c hR hlower hupper).upper.sphere.carrier =
      frontier (closedUpperSuperellipsoidTruncation frame c R d) :=
  ConvexBodySphereData.sphere_carrier_eq_frontier _

end Submission.Topology
