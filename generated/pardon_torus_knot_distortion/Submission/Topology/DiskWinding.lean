import Submission.Topology.CircleDegree

namespace Submission
namespace PardonDistortion

open Set

/-- The closed unit disk, used as an elementary model of a filling disk. -/
abbrev ClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- Radially project the complex plane to the closed unit disk.  The factor is
one on the disk and rescales points outside the disk to norm one. -/
noncomputable def radialProjectionPoint (z : ℂ) : ℂ :=
  (max 1 ‖z‖)⁻¹ • z

lemma radialProjectionPoint_mem (z : ℂ) :
    radialProjectionPoint z ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, radialProjectionPoint, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  exact (inv_mul_le_one₀ (by positivity)).2 (le_max_right 1 ‖z‖)

/-- The radial projection, with its codomain bundled as the closed disk. -/
noncomputable def radialProjection (z : ℂ) : ClosedUnitDisk :=
  ⟨radialProjectionPoint z, radialProjectionPoint_mem z⟩

lemma continuous_radialProjectionPoint : Continuous radialProjectionPoint := by
  unfold radialProjectionPoint
  have hmax : Continuous (fun z : ℂ ↦ max 1 ‖z‖) :=
    continuous_const.max continuous_norm
  exact (hmax.inv₀ fun z ↦ by positivity).smul continuous_id

lemma continuous_radialProjection : Continuous radialProjection :=
  continuous_radialProjectionPoint.subtype_mk _

lemma radialProjection_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (radialProjection z : ℂ) = z := by
  simp [radialProjection, radialProjectionPoint, max_eq_left hz]

lemma unitCircleParam_norm (t : ℝ) : ‖unitCircleParam t‖ = 1 := by
  rw [show unitCircleParam t = (Circle.exp t : ℂ) by
    rw [Circle.coe_exp, Complex.exp_mul_I]
    simp [unitCircleParam]]
  exact Circle.norm_coe _

/-- The usual angular parametrization, regarded as a point on the boundary of
the closed unit disk. -/
noncomputable def unitDiskBoundary (t : ℝ) : ClosedUnitDisk :=
  ⟨unitCircleParam t, by
    rw [Metric.mem_closedBall, dist_zero_right, unitCircleParam_norm]
  ⟩

@[simp] lemma radialProjection_unitCircleParam (t : ℝ) :
    radialProjection (unitCircleParam t) = unitDiskBoundary t := by
  apply Subtype.ext
  exact radialProjection_eq_self (unitCircleParam_norm t).le

/-- A boundary map of nonzero winding cannot extend continuously over the
closed unit disk.  This is the disk form of
`no_circle_filling_of_nonzero_degree`; radial projection turns a hypothetical
disk filling into a filling defined on the whole plane. -/
theorem no_unitDisk_filling_of_nonzero_degree
    (n : ℤ) (hn : n ≠ 0) (phase : ℝ) :
    ¬ ∃ g : ClosedUnitDisk → Circle, Continuous g ∧
      ∀ t : ℝ, g (unitDiskBoundary t) = Circle.exp ((n : ℝ) * t + phase) := by
  rintro ⟨g, hg, hboundary⟩
  apply no_circle_filling_of_nonzero_degree n hn phase
  refine ⟨fun z ↦ g (radialProjection z), hg.comp continuous_radialProjection, ?_⟩
  intro t
  change g (radialProjection (unitCircleParam t)) = _
  rw [radialProjection_unitCircleParam]
  exact hboundary t

/-- Contrapositive form: if an angular boundary map extends over the closed
unit disk, then its winding coefficient must vanish. -/
theorem winding_eq_zero_of_unitDisk_filling
    (n : ℤ) (phase : ℝ) (g : ClosedUnitDisk → Circle) (hg : Continuous g)
    (hboundary : ∀ t : ℝ,
      g (unitDiskBoundary t) = Circle.exp ((n : ℝ) * t + phase)) :
    n = 0 := by
  by_contra hn
  exact no_unitDisk_filling_of_nonzero_degree n hn phase ⟨g, hg, hboundary⟩

/-- Any continuous circle-valued coordinate defined on a filled disk has zero
winding on an angularly parametrized boundary.  In applications the ambient
space can be either side of a separating torus, and `coordinate` is the
longitude or meridian coordinate that extends to that side. -/
theorem winding_eq_zero_of_continuous_coordinate_filling
    {X : Type*} [TopologicalSpace X]
    (n : ℤ) (phase : ℝ) (g : ClosedUnitDisk → X) (hg : Continuous g)
    (coordinate : X → Circle) (hcoordinate : Continuous coordinate)
    (hboundary : ∀ t : ℝ, coordinate (g (unitDiskBoundary t)) =
      Circle.exp ((n : ℝ) * t + phase)) :
    n = 0 := by
  exact winding_eq_zero_of_unitDisk_filling n phase (coordinate ∘ g)
    (hcoordinate.comp hg) hboundary

/-- A loop in the product torus that bounds a disk has zero winding in its
first circle coordinate, whenever that coordinate is presented by an explicit
angular formula. -/
theorem first_winding_eq_zero_of_torusDisk_filling
    (n : ℤ) (phase : ℝ) (g : ClosedUnitDisk → Circle × Circle)
    (hg : Continuous g)
    (hboundary : ∀ t : ℝ,
      (g (unitDiskBoundary t)).1 = Circle.exp ((n : ℝ) * t + phase)) :
    n = 0 := by
  apply winding_eq_zero_of_unitDisk_filling n phase (fun z ↦ (g z).1)
  · exact continuous_fst.comp hg
  · exact hboundary

/-- The analogous vanishing result for the second circle coordinate. -/
theorem second_winding_eq_zero_of_torusDisk_filling
    (n : ℤ) (phase : ℝ) (g : ClosedUnitDisk → Circle × Circle)
    (hg : Continuous g)
    (hboundary : ∀ t : ℝ,
      (g (unitDiskBoundary t)).2 = Circle.exp ((n : ℝ) * t + phase)) :
    n = 0 := by
  apply winding_eq_zero_of_unitDisk_filling n phase (fun z ↦ (g z).2)
  · exact continuous_snd.comp hg
  · exact hboundary

/-- Both longitude and meridian winding coefficients of an explicitly
parametrized product-torus loop vanish if the loop extends across a disk. -/
theorem torus_windings_eq_zero_of_unitDisk_filling
    (m n : ℤ) (phase₁ phase₂ : ℝ)
    (g : ClosedUnitDisk → Circle × Circle) (hg : Continuous g)
    (hboundary : ∀ t : ℝ, g (unitDiskBoundary t) =
      (Circle.exp ((m : ℝ) * t + phase₁),
        Circle.exp ((n : ℝ) * t + phase₂))) :
    m = 0 ∧ n = 0 := by
  constructor
  · apply first_winding_eq_zero_of_torusDisk_filling m phase₁ g hg
    intro t
    exact congrArg Prod.fst (hboundary t)
  · apply second_winding_eq_zero_of_torusDisk_filling n phase₂ g hg
    intro t
    exact congrArg Prod.snd (hboundary t)

/-- The winding obstruction transported through an arbitrary chosen torus
coordinate homeomorphism.  Taking the homeomorphism to be the explicit
standard-torus chart turns a geometric disk filling into the product-coordinate
statement above. -/
theorem torus_windings_eq_zero_of_homeomorphicDisk_filling
    {X : Type*} [TopologicalSpace X]
    (coordinateHomeomorph : Circle × Circle ≃ₜ X)
    (m n : ℤ) (phase₁ phase₂ : ℝ)
    (g : ClosedUnitDisk → X) (hg : Continuous g)
    (hboundary : ∀ t : ℝ,
      coordinateHomeomorph.symm (g (unitDiskBoundary t)) =
        (Circle.exp ((m : ℝ) * t + phase₁),
          Circle.exp ((n : ℝ) * t + phase₂))) :
    m = 0 ∧ n = 0 := by
  apply torus_windings_eq_zero_of_unitDisk_filling m n phase₁ phase₂
    (coordinateHomeomorph.symm ∘ g)
  · exact coordinateHomeomorph.symm.continuous.comp hg
  · exact hboundary

end PardonDistortion
end Submission
