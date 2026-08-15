import Submission.Topology.PeriodicOrbitClassification
import Submission.Topology.RegularLevelQuotientCharts
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Topology.Order.IntermediateValue

/-!
# The rotated-gradient ODE on a planar regular level

For a smooth scalar function on the plane, rotating its derivative by ninety degrees gives a
canonical tangent vector field.  The algebraic facts are independent of any manifold structure:
the field is annihilated by the derivative and is nonzero at every regular point.

The local Picard theorem is packaged in a neighborhood-uniform form.  Compactness of a
fundamental-domain level then supplies a positive common time, and explicit deck equivariance
transports those curves to the whole periodic planar fiber.  No circle classification or
periodicity of an individual orbit is assumed.
-/

open Set Topology
open scoped Manifold Topology

noncomputable section

namespace Submission.SurfaceRegularValue

/-- The two standard coordinate vectors in the planar lift. -/
def planeBasisFirst : Plane := (1, 0)

/-- The second standard coordinate vector in the planar lift. -/
def planeBasisSecond : Plane := (0, 1)

/-- Rotate the two coordinate values of `Df` by ninety degrees. -/
def rotatedDerivativeField (f : Plane → ℝ) (x : Plane) : Plane :=
  (-(fderiv ℝ f x planeBasisSecond), fderiv ℝ f x planeBasisFirst)

theorem rotatedDerivativeField_eq_linearCombination (f : Plane → ℝ) (x : Plane) :
    rotatedDerivativeField f x =
      (-(fderiv ℝ f x planeBasisSecond)) • planeBasisFirst +
        (fderiv ℝ f x planeBasisFirst) • planeBasisSecond := by
  ext <;> simp [rotatedDerivativeField, planeBasisFirst, planeBasisSecond]

/-- The rotated derivative is tangent to every level of `f`. -/
theorem fderiv_rotatedDerivativeField (f : Plane → ℝ) (x : Plane) :
    fderiv ℝ f x (rotatedDerivativeField f x) = 0 := by
  rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
  ring

/-- At a regular point the rotated derivative does not vanish. -/
theorem rotatedDerivativeField_ne_zero {f : Plane → ℝ} {x : Plane}
    (hx : fderiv ℝ f x ≠ 0) : rotatedDerivativeField f x ≠ 0 := by
  intro hzero
  have hsecond : fderiv ℝ f x planeBasisSecond = 0 := by
    have h := congrArg Prod.fst hzero
    simpa [rotatedDerivativeField] using neg_eq_zero.mp h
  have hfirst : fderiv ℝ f x planeBasisFirst = 0 := by
    have h := congrArg Prod.snd hzero
    simpa [rotatedDerivativeField] using h
  apply hx
  apply ContinuousLinearMap.ext
  intro z
  rw [show z = z.1 • planeBasisFirst + z.2 • planeBasisSecond by
    ext <;> simp [planeBasisFirst, planeBasisSecond]]
  simp [hfirst, hsecond]

/-- The rotated field is `C¹` when `f` is `C²`. -/
theorem contDiff_rotatedDerivativeField {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (rotatedDerivativeField f) := by
  have hderiv : ContDiff ℝ 1
      (fun p : Plane × Plane ↦ fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by norm_num)
  have hfirst : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisFirst) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  have hsecond : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisSecond) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  exact hsecond.neg.prodMk hfirst

/-- One local integral curve of the rotated field that remains in the specified regular fiber. -/
structure LocalRegularLevelIntegralCurve (f : Plane → ℝ) (y : ℝ)
    (x : f ⁻¹' {y}) where
  radius : ℝ
  radius_pos : 0 < radius
  curve : ℝ → Plane
  curve_zero : curve 0 = x
  integral : IsIntegralCurveOn curve (fun _ ↦ rotatedDerivativeField f)
    (Ioo (-radius) radius)
  stays_in_level : ∀ t ∈ Ioo (-radius) radius, f (curve t) = y

/-- A single Picard neighborhood supplies curves through all nearby points, with a time interval
that is uniform on that neighborhood.  This is the form of the local theorem used by the finite
compactness argument below. -/
structure LocalRegularLevelIntegralCurveFamily (f : Plane → ℝ) (y : ℝ)
    (center : f ⁻¹' {y}) where
  spatialRadius : ℝ
  spatialRadius_pos : 0 < spatialRadius
  timeRadius : ℝ
  timeRadius_pos : 0 < timeRadius
  curve : (x : f ⁻¹' {y}) →
    dist (x : Plane) center ≤ spatialRadius → ℝ → Plane
  curve_zero : ∀ x hx, curve x hx 0 = x
  integral : ∀ x hx, IsIntegralCurveOn (curve x hx)
    (fun _ ↦ rotatedDerivativeField f) (Ioo (-timeRadius) timeRadius)
  stays_in_level : ∀ x hx t, t ∈ Ioo (-timeRadius) timeRadius →
    f (curve x hx t) = y

/-- A rotated-gradient integral curve that starts in a level remains in that level on every
connected open time interval containing zero. -/
private theorem integralCurve_stays_in_level {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) {y radius : ℝ} (hradius : 0 < radius)
    {curve : ℝ → Plane} (hzero : f (curve 0) = y)
    (hcurve : ∀ t ∈ Ioo (-radius) radius,
      HasDerivAt curve (rotatedDerivativeField f (curve t)) t) :
    ∀ t ∈ Ioo (-radius) radius, f (curve t) = y := by
  intro t ht
  let g : ℝ → ℝ := f ∘ curve
  have hgderiv : ∀ u ∈ Ioo (-radius) radius, HasDerivAt g 0 u := by
    intro u hu
    have hcomp := (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt u (hcurve u hu)
    exact hcomp.congr_deriv (fderiv_rotatedDerivativeField f (curve u))
  have hgdiff : DifferentiableOn ℝ g (Ioo (-radius) radius) :=
    fun u hu ↦ (hgderiv u hu).differentiableAt.differentiableWithinAt
  have hgzero : (Ioo (-radius) radius).EqOn (deriv g) 0 :=
    fun u hu ↦ (hgderiv u hu).deriv
  have hzero_mem : (0 : ℝ) ∈ Ioo (-radius) radius := by
    exact ⟨neg_lt_zero.mpr hradius, hradius⟩
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hgdiff hgzero ht hzero_mem
  change g t = y
  rw [hconst]
  exact hzero

/-- The neighborhood-uniform form of Picard--Lindelöf for the rotated-gradient field. -/
theorem exists_localRegularLevelIntegralCurveFamily {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) {y : ℝ} (center : f ⁻¹' {y}) :
    Nonempty (LocalRegularLevelIntegralCurveFamily f y center) := by
  obtain ⟨spatialRadius, hspatial, timeRadius, htime, hcurves⟩ :=
    (contDiff_rotatedDerivativeField hf).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose curve hzero hintegral using fun (x : f ⁻¹' {y})
    (hx : dist (x : Plane) center ≤ spatialRadius) ↦
      hcurves (x : Plane) (by simpa [Metric.mem_closedBall] using hx)
  refine ⟨{
    spatialRadius := spatialRadius
    spatialRadius_pos := hspatial
    timeRadius := timeRadius
    timeRadius_pos := htime
    curve := curve
    curve_zero := hzero
    integral := fun x hx t ht ↦
      (hintegral x hx t (by simpa only [zero_sub, zero_add] using ht)).hasDerivWithinAt
    stays_in_level := ?_
  }⟩
  intro x hx
  apply integralCurve_stays_in_level hf htime
  · rw [hzero x hx]
    exact x.property
  · intro t ht
    exact hintegral x hx t (by simpa only [zero_sub, zero_add] using ht)

/-- Picard--Lindelöf gives a local rotated-gradient curve through every point of a smooth
fiber, and the tangent identity forces that curve to remain in the fiber. -/
theorem exists_localRegularLevelIntegralCurve {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) {y : ℝ} (x : f ⁻¹' {y}) :
    Nonempty (LocalRegularLevelIntegralCurve f y x) := by
  obtain ⟨curve, hzero, radius, hradius, hcurve⟩ :=
    (contDiff_rotatedDerivativeField hf).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨{
    radius := radius
    radius_pos := hradius
    curve := curve
    curve_zero := hzero
    integral := fun t ht ↦
      (hcurve t (by simpa only [zero_sub, zero_add] using ht)).hasDerivWithinAt
    stays_in_level := ?_
  }⟩
  intro t ht
  exact integralCurve_stays_in_level hf hradius
    (by rw [hzero]; exact x.property)
    (fun u hu ↦ hcurve u (by simpa only [zero_sub, zero_add] using hu)) t ht

/-- Uniform local curves through every point of the compact part of a level in one fundamental
square.  The positive time is the minimum of the finitely many Picard times selected by a finite
subcover. -/
structure CompactFundamentalRegularLevelIntegralCurves (f : Plane → ℝ) (y : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  curve : (x : fundamentalLevelSet f y) → ℝ → Plane
  curve_zero : ∀ x, curve x 0 = x
  integral : ∀ x, IsIntegralCurveOn (curve x)
    (fun _ ↦ rotatedDerivativeField f) (Ioo (-radius) radius)
  stays_in_level : ∀ x t, t ∈ Ioo (-radius) radius → f (curve x t) = y

/-- Compactness turns the neighborhood-uniform local Picard theorem into one positive time valid
at every point of the fundamental-domain level. -/
theorem exists_compactFundamentalRegularLevelIntegralCurves {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) {y : ℝ}
    (hne : (fundamentalLevelSet f y).Nonempty) :
    Nonempty (CompactFundamentalRegularLevelIntegralCurves f y) := by
  classical
  let K := fundamentalLevelSet f y
  let family : ∀ x : K, LocalRegularLevelIntegralCurveFamily f y
      ⟨x, x.property.2⟩ := fun x ↦
    Classical.choice (exists_localRegularLevelIntegralCurveFamily hf ⟨x, x.property.2⟩)
  let U : K → Set Plane := fun x ↦ Metric.ball (x : Plane) (family x).spatialRadius
  have hopen : ∀ x, IsOpen (U x) := fun _ ↦ Metric.isOpen_ball
  have hcover : K ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩,
      Metric.mem_ball_self (family ⟨x, hx⟩).spatialRadius_pos⟩
  obtain ⟨s, hs⟩ := (isCompact_fundamentalLevelSet hf.continuous y).elim_finite_subcover
    U hopen hcover
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨i, hi⟩
  let radius : ℝ := s.inf' hsne fun x ↦ (family x).timeRadius
  have hradius : 0 < radius := by
    exact (Finset.lt_inf'_iff hsne).2 fun x _ ↦ (family x).timeRadius_pos
  have hchosen : ∀ x : K, ∃ i ∈ s, (x : Plane) ∈ U i := by
    intro x
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs x.property)
    exact ⟨i, hi, hxi⟩
  let center (x : K) : K := Classical.choose (hchosen x)
  have center_mem (x : K) : center x ∈ s := (Classical.choose_spec (hchosen x)).1
  have x_mem_center (x : K) : (x : Plane) ∈ U (center x) :=
    (Classical.choose_spec (hchosen x)).2
  have x_closed (x : K) :
      dist (x : Plane) (center x : Plane) ≤ (family (center x)).spatialRadius :=
    (Metric.mem_ball.mp (x_mem_center x)).le
  let localCurve (x : K) : ℝ → Plane :=
    (family (center x)).curve ⟨x, x.property.2⟩ (x_closed x)
  have hradius_le (x : K) : radius ≤ (family (center x)).timeRadius :=
    Finset.inf'_le _ (center_mem x)
  have hinterval (x : K) : Ioo (-radius) radius ⊆
      Ioo (-(family (center x)).timeRadius) (family (center x)).timeRadius := by
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg (hradius_le x)) ht.1,
      ht.2.trans_le (hradius_le x)⟩
  refine ⟨{
    radius := radius
    radius_pos := hradius
    curve := localCurve
    curve_zero := ?_
    integral := ?_
    stays_in_level := ?_
  }⟩
  · intro x
    exact (family (center x)).curve_zero ⟨x, x.property.2⟩ (x_closed x)
  · intro x t ht
    exact ((family (center x)).integral ⟨x, x.property.2⟩ (x_closed x)
      t (hinterval x ht)).mono (hinterval x)
  · intro x t ht
    exact (family (center x)).stays_in_level ⟨x, x.property.2⟩ (x_closed x)
      t (hinterval x ht)

/-- The uniform local ODE output needed for compact continuation.  The radius is independent of
the initial point, and every supplied local curve stays in the regular fiber. -/
structure UniformRegularLevelIntegralCurves (f : Plane → ℝ) (y : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  curve : (x : f ⁻¹' {y}) → ℝ → Plane
  curve_zero : ∀ x, curve x 0 = x
  integral : ∀ x, IsIntegralCurveOn (curve x)
    (fun _ ↦ rotatedDerivativeField f) (Ioo (-radius) radius)
  stays_in_level : ∀ x t, t ∈ Ioo (-radius) radius → f (curve x t) = y

/-- Uniform local integral curves through every point of the plane.  For a periodic vector field,
this data is obtained from one compact fundamental square and deck translation. -/
structure UniformPlaneIntegralCurves (v : Plane → Plane) where
  radius : ℝ
  radius_pos : 0 < radius
  curve : Plane → ℝ → Plane
  curve_zero : ∀ x, curve x 0 = x
  integral : ∀ x, IsIntegralCurveOn (curve x) (fun _ ↦ v) (Ioo (-radius) radius)

/-- The neighborhood-uniform Picard data centered at an arbitrary planar point. -/
private structure LocalPlaneIntegralCurveFamily (v : Plane → Plane) (center : Plane) where
  spatialRadius : ℝ
  spatialRadius_pos : 0 < spatialRadius
  timeRadius : ℝ
  timeRadius_pos : 0 < timeRadius
  curve : (x : Plane) → dist x center ≤ spatialRadius → ℝ → Plane
  curve_zero : ∀ x hx, curve x hx 0 = x
  integral : ∀ x hx, IsIntegralCurveOn (curve x hx) (fun _ ↦ v)
    (Ioo (-timeRadius) timeRadius)

private theorem exists_localPlaneIntegralCurveFamily {v : Plane → Plane}
    (hv : ContDiff ℝ 1 v) (center : Plane) :
    Nonempty (LocalPlaneIntegralCurveFamily v center) := by
  obtain ⟨spatialRadius, hspatial, timeRadius, htime, hcurves⟩ :=
    hv.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose curve hzero hintegral using fun (x : Plane)
    (hx : dist x center ≤ spatialRadius) ↦
      hcurves x (by simpa [Metric.mem_closedBall] using hx)
  exact ⟨{
    spatialRadius := spatialRadius
    spatialRadius_pos := hspatial
    timeRadius := timeRadius
    timeRadius_pos := htime
    curve := curve
    curve_zero := hzero
    integral := fun x hx t ht ↦
      (hintegral x hx t (by simpa only [zero_sub, zero_add] using ht)).hasDerivWithinAt
  }⟩

/-- Compactness of the fundamental square supplies one positive Picard time there. -/
private theorem exists_uniformPlaneIntegralCurvesOnFundamentalSquare {v : Plane → Plane}
    (hv : ContDiff ℝ 1 v) :
    ∃ radius > 0, ∀ x ∈ fundamentalSquare, ∃ curve : ℝ → Plane,
      curve 0 = x ∧ IsIntegralCurveOn curve (fun _ ↦ v) (Ioo (-radius) radius) := by
  classical
  let K := fundamentalSquare
  let family : ∀ x : K, LocalPlaneIntegralCurveFamily v x := fun x ↦
    Classical.choice (exists_localPlaneIntegralCurveFamily hv x)
  let U : K → Set Plane := fun x ↦ Metric.ball (x : Plane) (family x).spatialRadius
  have hcover : K ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩,
      Metric.mem_ball_self (family ⟨x, hx⟩).spatialRadius_pos⟩
  obtain ⟨s, hs⟩ := isCompact_fundamentalSquare.elim_finite_subcover U
    (fun _ ↦ Metric.isOpen_ball) hcover
  have hsne : s.Nonempty := by
    have hzero : (0 : Plane) ∈ fundamentalSquare := by
      exact ⟨⟨le_rfl, Real.two_pi_pos.le⟩, ⟨le_rfl, Real.two_pi_pos.le⟩⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hs hzero)
    exact ⟨i, hi⟩
  let radius : ℝ := s.inf' hsne fun x ↦ (family x).timeRadius
  have hradius : 0 < radius :=
    (Finset.lt_inf'_iff hsne).2 fun x _ ↦ (family x).timeRadius_pos
  refine ⟨radius, hradius, ?_⟩
  intro x hx
  obtain ⟨center, hcenter, hxcenter⟩ := mem_iUnion₂.mp (hs hx)
  have hxclosed : dist x (center : Plane) ≤ (family center).spatialRadius :=
    (Metric.mem_ball.mp hxcenter).le
  let curve := (family center).curve x hxclosed
  refine ⟨curve, (family center).curve_zero x hxclosed, ?_⟩
  have hradius_le : radius ≤ (family center).timeRadius :=
    Finset.inf'_le _ hcenter
  apply ((family center).integral x hxclosed).mono
  intro t ht
  exact ⟨lt_of_le_of_lt (neg_le_neg hradius_le) ht.1, ht.2.trans_le hradius_le⟩

/-! ## Deck transport from the compact fundamental level -/

open LeanEval.KnotTheory.PardonDistortion
open Submission.PardonDistortion Submission.Topology Submission.Torus

/-- The deck vector associated to two integer turns in the planar torus cover. -/
def planeDeckVector (m n : ℤ) : Plane :=
  ((m : ℝ) * (2 * Real.pi), (n : ℝ) * (2 * Real.pi))

/-- Reduction of both planar coordinates to the half-open fundamental square. -/
def planeFundamentalRepresentative (uv : Plane) : Plane :=
  (toIcoMod Real.two_pi_pos 0 uv.1, toIcoMod Real.two_pi_pos 0 uv.2)

/-- The two integer turns removed by `planeFundamentalRepresentative`. -/
def planeFundamentalDeckIndex (uv : Plane) : ℤ × ℤ :=
  (toIcoDiv Real.two_pi_pos 0 uv.1, toIcoDiv Real.two_pi_pos 0 uv.2)

/-- Adding back the removed integer turns recovers the original planar point. -/
theorem planeFundamentalRepresentative_add_deck (uv : Plane) :
    planeFundamentalRepresentative uv +
        planeDeckVector (planeFundamentalDeckIndex uv).1
          (planeFundamentalDeckIndex uv).2 = uv := by
  ext
  · exact toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 uv.1
  · exact toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 uv.2

/-- Coordinate reduction lands in the closed fundamental square. -/
theorem planeFundamentalRepresentative_mem_fundamentalSquare (uv : Plane) :
    planeFundamentalRepresentative uv ∈ fundamentalSquare := by
  constructor
  · obtain ⟨hzero, htwoPi⟩ :=
      toIcoMod_mem_Ico Real.two_pi_pos 0 uv.1
    exact ⟨by simpa [planeFundamentalRepresentative] using hzero,
      by simpa [planeFundamentalRepresentative] using htwoPi.le⟩
  · obtain ⟨hzero, htwoPi⟩ :=
      toIcoMod_mem_Ico Real.two_pi_pos 0 uv.2
    exact ⟨by simpa [planeFundamentalRepresentative] using hzero,
      by simpa [planeFundamentalRepresentative] using htwoPi.le⟩

/-- The coordinate lift is invariant under every deck translation. -/
theorem orientedCoordinateLift_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    (m n : ℤ) (uv : Plane) :
    orientedCoordinateLift Phi frame i (uv + planeDeckVector m n) =
      orientedCoordinateLift Phi frame i uv := by
  unfold orientedCoordinateLift
  rw [show uv + planeDeckVector m n =
      (uv.1 + (m : ℝ) * (2 * Real.pi),
        uv.2 + (n : ℝ) * (2 * Real.pi)) by
    ext <;> rfl]
  rw [transportedTorusPlaneMap_add_int_periods]

/-- Differentiating deck invariance gives invariance of the derivative. -/
theorem fderiv_orientedCoordinateLift_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    (m n : ℤ) (uv : Plane) :
    fderiv ℝ (orientedCoordinateLift Phi frame i)
        (uv + planeDeckVector m n) =
      fderiv ℝ (orientedCoordinateLift Phi frame i) uv := by
  let deck := planeDeckVector m n
  have hfun :
      (fun z ↦ orientedCoordinateLift Phi frame i (z + deck)) =
        orientedCoordinateLift Phi frame i := by
    funext z
    exact orientedCoordinateLift_add_planeDeckVector Phi frame i m n z
  calc
    fderiv ℝ (orientedCoordinateLift Phi frame i) (uv + deck) =
        fderiv ℝ (fun z ↦ orientedCoordinateLift Phi frame i (z + deck)) uv :=
      (fderiv_comp_add_right deck).symm
    _ = fderiv ℝ (orientedCoordinateLift Phi frame i) uv :=
      congrArg (fun g : Plane → ℝ ↦ fderiv ℝ g uv) hfun

/-- Consequently the autonomous rotated-gradient field descends to the quotient torus. -/
theorem rotatedDerivativeField_orientedCoordinateLift_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    (m n : ℤ) (uv : Plane) :
    rotatedDerivativeField (orientedCoordinateLift Phi frame i)
        (uv + planeDeckVector m n) =
      rotatedDerivativeField (orientedCoordinateLift Phi frame i) uv := by
  simp only [rotatedDerivativeField,
    fderiv_orientedCoordinateLift_add_planeDeckVector]

/-- The rotated coordinate field has one positive local existence time at every point of the
plane.  Compactness is used only on the fundamental square; all other curves are fixed deck
translates. -/
theorem exists_uniformPlaneIntegralCurves_orientedCoordinateLift
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Nonempty (UniformPlaneIntegralCurves
      (rotatedDerivativeField (orientedCoordinateLift Phi frame i))) := by
  classical
  let f := orientedCoordinateLift Phi frame i
  let v := rotatedDerivativeField f
  have hv : ContDiff ℝ 1 v := contDiff_rotatedDerivativeField
    ((orientedCoordinateLift_contDiff Phi frame i).of_le
      (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨radius, hradius, hlocal⟩ :=
    exists_uniformPlaneIntegralCurvesOnFundamentalSquare hv
  choose localCurve hlocalZero hlocalIntegral using fun x : Plane ↦
    hlocal (planeFundamentalRepresentative x)
      (planeFundamentalRepresentative_mem_fundamentalSquare x)
  let deck (x : Plane) : Plane :=
    planeDeckVector (planeFundamentalDeckIndex x).1 (planeFundamentalDeckIndex x).2
  let curve (x : Plane) (t : ℝ) : Plane := localCurve x t + deck x
  refine ⟨{
    radius := radius
    radius_pos := hradius
    curve := curve
    curve_zero := ?_
    integral := ?_
  }⟩
  · intro x
    change localCurve x 0 + deck x = x
    rw [hlocalZero]
    exact planeFundamentalRepresentative_add_deck x
  · intro x t ht
    change HasDerivWithinAt (fun u ↦ localCurve x u + deck x)
      (v (localCurve x t + deck x)) (Ioo (-radius) radius) t
    exact ((hlocalIntegral x t ht).add_const (deck x)).congr_deriv
      (rotatedDerivativeField_orientedCoordinateLift_add_planeDeckVector
        Phi frame i (planeFundamentalDeckIndex x).1
          (planeFundamentalDeckIndex x).2 _).symm

/-- Coordinate reduction does not change the value of the periodic coordinate lift. -/
theorem orientedCoordinateLift_planeFundamentalRepresentative
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    (uv : Plane) :
    orientedCoordinateLift Phi frame i (planeFundamentalRepresentative uv) =
      orientedCoordinateLift Phi frame i uv := by
  let index := planeFundamentalDeckIndex uv
  calc
    orientedCoordinateLift Phi frame i (planeFundamentalRepresentative uv) =
        orientedCoordinateLift Phi frame i
          (planeFundamentalRepresentative uv + planeDeckVector index.1 index.2) :=
      (orientedCoordinateLift_add_planeDeckVector Phi frame i index.1 index.2 _).symm
    _ = orientedCoordinateLift Phi frame i uv := by
      rw [planeFundamentalRepresentative_add_deck]

/-- A point of a lifted coordinate level, reduced to the compact fundamental-domain level. -/
def fundamentalRepresentativeOfCoordinateLevel
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3) (y : ℝ)
    (x : (orientedCoordinateLift Phi frame i) ⁻¹' {y}) :
    fundamentalLevelSet (orientedCoordinateLift Phi frame i) y :=
  ⟨planeFundamentalRepresentative x,
    planeFundamentalRepresentative_mem_fundamentalSquare x,
    (orientedCoordinateLift_planeFundamentalRepresentative Phi frame i x).trans x.property⟩

/-- For a transported-torus coordinate lift, compactness of one fundamental level gives a common
positive Picard time on the entire periodic planar level.  No compactness of the full planar fiber
is asserted: its solutions are deck translates of the finitely controlled representatives. -/
theorem exists_uniformRegularLevelIntegralCurves_orientedCoordinateLift
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3) {y : ℝ}
    (hne : ((orientedCoordinateLift Phi frame i) ⁻¹' {y}).Nonempty) :
    Nonempty (UniformRegularLevelIntegralCurves
      (orientedCoordinateLift Phi frame i) y) := by
  classical
  let f := orientedCoordinateLift Phi frame i
  have hfundamental : (fundamentalLevelSet f y).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨fundamentalRepresentativeOfCoordinateLevel Phi frame i y ⟨x, hx⟩,
      (fundamentalRepresentativeOfCoordinateLevel Phi frame i y ⟨x, hx⟩).property⟩
  have hf : ContDiff ℝ 2 f :=
    (orientedCoordinateLift_contDiff Phi frame i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  let compact := Classical.choice
    (exists_compactFundamentalRegularLevelIntegralCurves (f := f) hf hfundamental)
  let representative (x : f ⁻¹' {y}) : fundamentalLevelSet f y :=
    fundamentalRepresentativeOfCoordinateLevel Phi frame i y x
  let deck (x : f ⁻¹' {y}) : Plane :=
    planeDeckVector (planeFundamentalDeckIndex x).1 (planeFundamentalDeckIndex x).2
  let curve (x : f ⁻¹' {y}) (t : ℝ) : Plane :=
    compact.curve (representative x) t + deck x
  have hrepresentative_add (x : f ⁻¹' {y}) :
      (representative x : Plane) + deck x = x :=
    planeFundamentalRepresentative_add_deck x
  refine ⟨{
    radius := compact.radius
    radius_pos := compact.radius_pos
    curve := curve
    curve_zero := ?_
    integral := ?_
    stays_in_level := ?_
  }⟩
  · intro x
    change compact.curve (representative x) 0 + deck x = x
    rw [compact.curve_zero]
    exact hrepresentative_add x
  · intro x t ht
    change HasDerivWithinAt (fun u ↦ compact.curve (representative x) u + deck x)
      (rotatedDerivativeField f
        (compact.curve (representative x) t + deck x))
      (Ioo (-compact.radius) compact.radius) t
    exact ((compact.integral (representative x) t ht).add_const (deck x)).congr_deriv
      (rotatedDerivativeField_orientedCoordinateLift_add_planeDeckVector
        Phi frame i (planeFundamentalDeckIndex x).1
          (planeFundamentalDeckIndex x).2 _).symm
  · intro x t ht
    change orientedCoordinateLift Phi frame i
      (compact.curve (representative x) t +
        planeDeckVector (planeFundamentalDeckIndex x).1
          (planeFundamentalDeckIndex x).2) = y
    rw [orientedCoordinateLift_add_planeDeckVector]
    exact compact.stays_in_level (representative x) t ht

/-- A complete lifted orbit supplied by the compact uniform-time continuation argument.  Its
fields are precisely the output to be derived from `UniformRegularLevelIntegralCurves`; no
topological classification is included. -/
structure CompleteRegularLevelIntegralCurve (f : Plane → ℝ) (y : ℝ)
    (x : f ⁻¹' {y}) where
  curve : ℝ → Plane
  curve_zero : curve 0 = x
  integral : IsIntegralCurve curve (fun _ ↦ rotatedDerivativeField f)
  stays_in_level : ∀ t, f (curve t) = y

/-- Regard an ordinary planar vector field as a section of the tangent bundle of the standard
vector-space manifold. -/
private def planeTangentVectorField (v : Plane → Plane) (z : Plane) :
    TangentSpace 𝓘(ℝ, Plane) z :=
  (NormedSpace.fromTangentSpace z).symm (v z)

/-- On a normed vector space, the manifold and Fréchet formulations of an integral curve agree. -/
private theorem isMIntegralCurveOn_iff_isIntegralCurveOn_plane
    (γ : ℝ → Plane) (v : Plane → Plane) (s : Set ℝ) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) γ (planeTangentVectorField v) s ↔
      IsIntegralCurveOn γ (fun _ ↦ v) s := by
  constructor
  · intro h t ht
    have hm := (h t ht).hasFDerivWithinAt
    change HasFDerivWithinAt γ
      (ContinuousLinearMap.toSpanSingleton ℝ (v (γ t))) s t at hm
    exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr hm
  · intro h t ht
    apply HasFDerivWithinAt.hasMFDerivWithinAt
    change HasFDerivWithinAt γ
      (ContinuousLinearMap.toSpanSingleton ℝ (v (γ t))) s t
    exact (h t ht).hasFDerivWithinAt

/-- The corresponding equivalence for complete integral curves. -/
private theorem isMIntegralCurve_iff_isIntegralCurve_plane
    (γ : ℝ → Plane) (v : Plane → Plane) :
    IsMIntegralCurve (I := 𝓘(ℝ, Plane)) γ (planeTangentVectorField v) ↔
      IsIntegralCurve γ (fun _ ↦ v) := by
  constructor
  · intro h t
    have hm := (h t).hasFDerivAt
    change HasFDerivAt γ
      (ContinuousLinearMap.toSpanSingleton ℝ (v (γ t))) t at hm
    exact hasDerivAt_iff_hasFDerivAt.mpr hm
  · intro h t
    apply HasFDerivAt.hasMFDerivAt
    change HasFDerivAt γ
      (ContinuousLinearMap.toSpanSingleton ℝ (v (γ t))) t
    exact (h t).hasFDerivAt

/-- Uniform local existence on the plane gives a complete rotated-gradient curve through every
point of a chosen fiber.  The global continuation is Mathlib's supremum-and-patching theorem;
level preservation follows afterwards from the rotated-gradient identity. -/
theorem exists_completeRegularLevelIntegralCurve_of_uniformPlane
    {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (U : UniformPlaneIntegralCurves (rotatedDerivativeField f))
    {y : ℝ} (x : f ⁻¹' {y}) :
    Nonempty (CompleteRegularLevelIntegralCurve f y x) := by
  let v := rotatedDerivativeField f
  let vm := planeTangentVectorField v
  have hvm : ContDiff ℝ 1 vm := by
    change ContDiff ℝ 1 v
    exact contDiff_rotatedDerivativeField hf
  have hv : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane).tangent 1 (T% vm) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := Plane)).mpr hvm
  obtain ⟨curve, hzero, hcurveM⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn (I := 𝓘(ℝ, Plane)) hv
      U.radius_pos (fun z ↦ ⟨U.curve z, U.curve_zero z,
        (isMIntegralCurveOn_iff_isIntegralCurveOn_plane _ _ _).mpr (U.integral z)⟩) x
  have hcurve : IsIntegralCurve curve (fun _ ↦ v) :=
    (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mp hcurveM
  refine ⟨{
    curve := curve
    curve_zero := hzero
    integral := hcurve
    stays_in_level := ?_
  }⟩
  intro t
  let radius := |t| + 1
  have hradius : 0 < radius := by positivity
  have ht : t ∈ Ioo (-radius) radius := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one |t|
  apply integralCurve_stays_in_level hf hradius
  · rw [hzero]
    exact x.property
  · exact fun u _ ↦ hcurve u
  · exact ht

/-- Every point of a transported coordinate fiber has a complete lifted rotated-gradient orbit. -/
theorem exists_completeRegularLevelIntegralCurve_orientedCoordinateLift
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    {y : ℝ} (x : (orientedCoordinateLift Phi frame i) ⁻¹' {y}) :
    Nonempty (CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame i) y x) := by
  let U := Classical.choice
    (exists_uniformPlaneIntegralCurves_orientedCoordinateLift Phi frame i)
  apply exists_completeRegularLevelIntegralCurve_of_uniformPlane
    ((orientedCoordinateLift_contDiff Phi frame i).of_le
      (WithTop.coe_le_coe.mpr le_top)) U x

/-- A complete integral curve of a `C¹` autonomous field is itself `C¹`. -/
theorem CompleteRegularLevelIntegralCurve.contDiff
    {f : Plane → ℝ} {y : ℝ} {x : f ⁻¹' {y}}
    (hf : ContDiff ℝ 2 f) (O : CompleteRegularLevelIntegralCurve f y x) :
    ContDiff ℝ 1 O.curve := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (O.integral t).differentiableAt, ?_⟩
  have hderiv : deriv O.curve = rotatedDerivativeField f ∘ O.curve := by
    funext t
    exact (O.integral t).deriv
  rw [hderiv]
  exact (contDiff_rotatedDerivativeField hf).continuous.comp
    (continuous_iff_continuousAt.mpr fun t ↦ (O.integral t).continuousAt)

/-- A `C¹` curve with nowhere-vanishing derivative is locally injective.  At each point, one
coordinate of the derivative is nonzero, and the one-dimensional inverse function theorem applied
to that coordinate supplies the required injective neighborhood. -/
private theorem isLocallyInjective_of_contDiff_deriv_ne_zero
    {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ)
    (hderiv : ∀ t, deriv γ t ≠ 0) : IsLocallyInjective γ := by
  intro t
  by_cases hfirst : (deriv γ t).1 ≠ 0
  · let g : ℝ → ℝ := fun s ↦ (γ s).1
    have hg : ContDiff ℝ 1 g :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.comp hγ
    have hgderiv : HasDerivAt g (deriv γ t).1 t := by
      exact (hγ.differentiable (by norm_num)).differentiableAt.hasDerivAt.fst
    have hstrict := hg.contDiffAt.hasStrictDerivAt' hgderiv (by norm_num)
    have hinverse := hstrict.eventually_left_inverse hfirst
    obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hinverse
    refine ⟨U, hUopen, htU, ?_⟩
    intro a ha b hb hab
    have hgab : g a = g b := congrArg Prod.fst hab
    calc
      a = hstrict.localInverse g (deriv γ t).1 t hfirst (g a) := (hUsub ha).symm
      _ = hstrict.localInverse g (deriv γ t).1 t hfirst (g b) := congrArg _ hgab
      _ = b := hUsub hb
  · have hsecond : (deriv γ t).2 ≠ 0 := by
      intro hzero
      apply hderiv t
      ext
      · exact not_ne_iff.mp hfirst
      · exact hzero
    let g : ℝ → ℝ := fun s ↦ (γ s).2
    have hg : ContDiff ℝ 1 g :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.comp hγ
    have hgderiv : HasDerivAt g (deriv γ t).2 t := by
      exact (hγ.differentiable (by norm_num)).differentiableAt.hasDerivAt.snd
    have hstrict := hg.contDiffAt.hasStrictDerivAt' hgderiv (by norm_num)
    have hinverse := hstrict.eventually_left_inverse hsecond
    obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hinverse
    refine ⟨U, hUopen, htU, ?_⟩
    intro a ha b hb hab
    have hgab : g a = g b := congrArg Prod.snd hab
    calc
      a = hstrict.localInverse g (deriv γ t).2 t hsecond (g a) := (hUsub ha).symm
      _ = hstrict.localInverse g (deriv γ t).2 t hsecond (g b) := congrArg _ hgab
      _ = b := hUsub hb

/-- At a regular value, every complete lifted orbit is locally injective. -/
theorem CompleteRegularLevelIntegralCurve.isLocallyInjective
    {f : Plane → ℝ} {y : ℝ} {x : f ⁻¹' {y}}
    (hf : ContDiff ℝ 2 f) (hy : IsRegularValue f y)
    (O : CompleteRegularLevelIntegralCurve f y x) : IsLocallyInjective O.curve := by
  apply isLocallyInjective_of_contDiff_deriv_ne_zero (O.contDiff hf)
  intro t
  rw [(O.integral t).deriv]
  exact rotatedDerivativeField_ne_zero (hy (O.curve t) (O.stays_in_level t))

/-- One-dimensional invariance of domain in the exact form needed here: a continuous locally
injective map from the real line to a Hausdorff locally-line-modelled space is a local
homeomorphism.  The proof restricts to a compact interval inside one target chart; compactness
gives an embedding, while monotonicity of the chart coordinate identifies the image of the open
interior with an open real interval. -/
private theorem isLocalHomeomorph_of_continuous_locallyInjective_locallyLineModeled
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hX : IsLocallyLineModeled X) {q : ℝ → X}
    (hq : Continuous q) (hinj : IsLocallyInjective q) : IsLocalHomeomorph q := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro t
  obtain ⟨C⟩ := hX (q t)
  obtain ⟨U, hUopen, htU, hUinj⟩ := hinj t
  have hV : U ∩ q ⁻¹' C.source ∈ 𝓝 t :=
    (hUopen.inter (C.source_open.preimage hq)).mem_nhds ⟨htU, C.mem_source⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let a := t - ε / 2
  let b := t + ε / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have htIoo : t ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith
  have hIccV : Icc a b ⊆ U ∩ q ⁻¹' C.source := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have har : t - ε / 2 ≤ r := hr.1
    have hrb : r ≤ t + ε / 2 := hr.2
    rw [abs_lt]
    constructor <;> linarith
  let W := Ioo a b
  have hWnhds : W ∈ 𝓝 t := isOpen_Ioo.mem_nhds htIoo
  let qIcc : Icc a b → X := fun r ↦ q r
  have hqIcc : Continuous qIcc := hq.comp continuous_subtype_val
  have hqIcc_injective : Function.Injective qIcc := by
    intro r s hrs
    apply Subtype.ext
    exact hUinj (hIccV r.property).1 (hIccV s.property).1 hrs
  let _ : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hqIcc_embedding : IsEmbedding qIcc :=
    (hqIcc.isClosedEmbedding hqIcc_injective).toIsEmbedding
  let inc : W → Icc a b := Set.inclusion Ioo_subset_Icc_self
  have hinc : IsOpenEmbedding inc :=
    Topology.IsOpenEmbedding.inclusion Ioo_subset_Icc_self <| by
      exact isOpen_Ioo.preimage continuous_subtype_val
  have hembedding : IsEmbedding (W.domRestrict q) := by
    have hcomp : qIcc ∘ inc = W.domRestrict q := rfl
    rw [← hcomp]
    exact hqIcc_embedding.comp hinc.toIsEmbedding
  let clamp : ℝ → Icc a b := projIcc a b hab.le
  let g : ℝ → ℝ := fun r ↦ C.equiv
    ⟨q (clamp r), (hIccV (clamp r).property).2⟩
  have hgcontinuous : Continuous g := by
    have hclamp : Continuous clamp := continuous_projIcc
    have hqclamp : Continuous (fun r ↦ q (clamp r)) :=
      hq.comp (continuous_subtype_val.comp hclamp)
    exact continuous_subtype_val.comp <| C.equiv.continuous.comp <|
      Continuous.subtype_mk hqclamp _
  have hg_eq (r : ℝ) (hr : r ∈ Icc a b) :
      g r = C.equiv ⟨q r, (hIccV hr).2⟩ := by
    change (C.equiv ⟨q (clamp r), _⟩ : ℝ) = (C.equiv ⟨q r, _⟩ : ℝ)
    apply congrArg Subtype.val
    apply congrArg C.equiv
    apply Subtype.ext
    change q (clamp r) = q r
    rw [show (clamp r : ℝ) = r by
      exact congrArg Subtype.val (projIcc_of_mem hab.le hr)]
  have hginj : InjOn g (Icc a b) := by
    intro r hr s hs hrs
    have hcoord : C.equiv ⟨q r, (hIccV hr).2⟩ =
        C.equiv ⟨q s, (hIccV hs).2⟩ := by
      apply Subtype.ext
      simpa [hg_eq r hr, hg_eq s hs] using hrs
    exact hUinj (hIccV hr).1 (hIccV hs).1 <| by
      exact congrArg Subtype.val (C.equiv.injective hcoord)
  have hopenCoord : IsOpen (g '' Ioo a b) := by
    rcases hgcontinuous.continuousOn.strictMonoOn_of_injOn_Icc' hab.le hginj with
      hmono | hanti
    · rw [hgcontinuous.continuousOn.image_Ioo_of_strictMonoOn hab.le hmono]
      exact isOpen_Ioo
    · rw [hgcontinuous.continuousOn.image_Ioo_of_strictAntiOn hab.le hanti]
      exact isOpen_Ioo
  let coordinateRange : Set C.target := Subtype.val ⁻¹' (g '' Ioo a b)
  have hcoordinateRange : IsOpen coordinateRange :=
    hopenCoord.preimage continuous_subtype_val
  have hrange : Set.range (W.domRestrict q) =
      Subtype.val '' (C.equiv.symm '' coordinateRange) := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      let zr : C.source := ⟨q r, (hIccV (Ioo_subset_Icc_self r.property)).2⟩
      refine ⟨zr, ?_, rfl⟩
      refine ⟨C.equiv zr, ?_, C.equiv.symm_apply_apply zr⟩
      exact ⟨r, r.property, by
        simpa [zr] using hg_eq r (Ioo_subset_Icc_self r.property)⟩
    · rintro ⟨zC, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨r, hr, hgr⟩ := hw
      refine ⟨⟨r, hr⟩, ?_⟩
      change q r = (C.equiv.symm w : C.source)
      have hsource : (⟨q r, (hIccV (Ioo_subset_Icc_self hr)).2⟩ : C.source) =
          C.equiv.symm w := by
        apply C.equiv.injective
        apply Subtype.ext
        simpa [hg_eq r (Ioo_subset_Icc_self hr)] using hgr
      exact congrArg (fun z : C.source ↦ (z : X)) hsource
  have hopenRange : IsOpen (Set.range (W.domRestrict q)) := by
    rw [hrange]
    exact C.source_open.isOpenEmbedding_subtypeVal.isOpenMap _
      (C.equiv.symm.isOpenMap _ hcoordinateRange)
  exact ⟨W, hWnhds, ⟨hembedding, hopenRange⟩⟩

/-- Composition preserves local injectivity when both factors are locally injective and the first
map is continuous. -/
private theorem IsLocallyInjective.comp_of_continuous
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {g : B → C} (hg : IsLocallyInjective g)
    (hf : IsLocallyInjective f) (hfc : Continuous f) :
    IsLocallyInjective (g ∘ f) := by
  intro x
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hf x
  obtain ⟨V, hVopen, hfxV, hVinj⟩ := hg (f x)
  refine ⟨U ∩ f ⁻¹' V, hUopen.inter (hVopen.preimage hfc), ⟨hxU, hfxV⟩, ?_⟩
  intro a ha b hb hab
  exact hUinj ha.1 hb.1 (hVinj ha.2 hb.2 hab)

/-- Restricting the codomain of a local homeomorphism to an open subset containing its range
preserves the local-homeomorphism property. -/
private theorem isLocalHomeomorph_codRestrict_open
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : IsLocalHomeomorph q) (s : Set B) (hs : IsOpen s)
    (hqs : ∀ a, q a ∈ s) :
    IsLocalHomeomorph (fun a ↦ (⟨q a, hqs a⟩ : s)) := by
  let q' : A → s := fun a ↦ ⟨q a, hqs a⟩
  let val : s → B := Subtype.val
  have hval : IsLocalHomeomorph val :=
    hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : val ∘ q' = q := rfl
  rw [← hcomp] at hq
  exact hq.of_comp hval (Continuous.subtype_mk hq.continuous _)

/-- Product-circle exponentiation is invariant under planar deck translation. -/
theorem planeExpPair_add_planeDeckVector (uv : Plane) (m n : ℤ) :
    planeExpPair (uv + planeDeckVector m n) = planeExpPair uv := by
  apply Prod.ext
  · apply Circle.exp_eq_exp.mpr
    exact ⟨m, by simp [planeDeckVector]⟩
  · apply Circle.exp_eq_exp.mpr
    exact ⟨n, by simp [planeDeckVector]⟩

/-- Two complete lifted orbits whose quotient projections meet agree after the corresponding time
translation in the quotient.  Equality of product exponentials supplies a deck vector, and global
ODE uniqueness compares one orbit with the deck translate of the other. -/
theorem completeRegularLevelIntegralCurves_expPair_translate_eq
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3) {y : ℝ}
    {x₁ x₂ : (orientedCoordinateLift Phi frame i) ⁻¹' {y}}
    (O₁ : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame i) y x₁)
    (O₂ : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame i) y x₂)
    {s t : ℝ} (hst : planeExpPair (O₁.curve s) = planeExpPair (O₂.curve t)) :
    ∀ u : ℝ, planeExpPair (O₁.curve (s + u)) = planeExpPair (O₂.curve (t + u)) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hst)
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hst)
  let deck := planeDeckVector m n
  have hstart : O₁.curve s = O₂.curve t + deck := by
    ext
    · simpa [deck, planeDeckVector] using hm
    · simpa [deck, planeDeckVector] using hn
  let v := rotatedDerivativeField (orientedCoordinateLift Phi frame i)
  let α : ℝ → Plane := fun u ↦ O₁.curve (u + s)
  let β : ℝ → Plane := fun u ↦ O₂.curve (u + t) + deck
  have hα : IsIntegralCurve α (fun _ ↦ v) := by
    simpa [α, v, Function.comp_def] using O₁.integral.comp_add s
  have hβ : IsIntegralCurve β (fun _ ↦ v) := by
    intro u
    have hshift : HasDerivAt (fun r ↦ O₂.curve (r + t))
        (v (O₂.curve (u + t))) u := by
      simpa [v, Function.comp_def] using
        (O₂.integral.comp_add t : IsIntegralCurve
          (O₂.curve ∘ (· + t)) ((fun _ ↦ v) ∘ (· + t))) u
    exact (hshift.add_const deck).congr_deriv <|
      (rotatedDerivativeField_orientedCoordinateLift_add_planeDeckVector
        Phi frame i m n _).symm
  let vm := planeTangentVectorField v
  have hvm : ContDiff ℝ 1 vm := by
    change ContDiff ℝ 1 v
    exact contDiff_rotatedDerivativeField <|
      (orientedCoordinateLift_contDiff Phi frame i).of_le
        (WithTop.coe_le_coe.mpr le_top)
  have hv : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane).tangent 1 (T% vm) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := Plane)).mpr hvm
  have hαM : IsMIntegralCurve (I := 𝓘(ℝ, Plane)) α vm :=
    (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr hα
  have hβM : IsMIntegralCurve (I := 𝓘(ℝ, Plane)) β vm :=
    (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr hβ
  have hαβ : α = β :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv hαM hβM <| by
      simpa [α, β, add_zero] using hstart
  intro u
  have hu := congrFun hαβ u
  calc
    planeExpPair (O₁.curve (s + u)) = planeExpPair (α u) := by simp [α, add_comm]
    _ = planeExpPair (β u) := congrArg planeExpPair hu
    _ = planeExpPair (O₂.curve (t + u)) := by
      simpa [β, add_comm] using
        planeExpPair_add_planeDeckVector (O₂.curve (u + t)) m n

/-- Project a complete lifted orbit to its genuine quotient-torus coordinate level. -/
def CompleteRegularLevelIntegralCurve.projectedCoordinateOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    {x : (orientedCoordinateLift Phi frame 2) ⁻¹' {d}}
    (O : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame 2) d x) :
    ℝ → coordinateTorusLevelSet Phi frame d :=
  fun t ↦ regularPlaneFiberToCoordinateTorusLevel Phi frame d
    ⟨O.curve t, O.stays_in_level t⟩

/-- The quotient projection of a complete lifted orbit is continuous. -/
theorem CompleteRegularLevelIntegralCurve.continuous_projectedCoordinateOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    {x : (orientedCoordinateLift Phi frame 2) ⁻¹' {d}}
    (O : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame 2) d x) :
    Continuous (O.projectedCoordinateOrbit Phi frame) := by
  apply Continuous.subtype_mk
  exact planeExpPair_isLocalHomeomorph.continuous.comp <|
    continuous_iff_continuousAt.mpr fun t ↦ (O.integral t).continuousAt

/-- At a regular value, the projected complete orbit is a local homeomorphism onto the quotient
level. -/
theorem CompleteRegularLevelIntegralCurve.isLocalHomeomorph_projectedCoordinateOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d)
    {x : (orientedCoordinateLift Phi frame 2) ⁻¹' {d}}
    (O : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame 2) d x) :
    IsLocalHomeomorph (O.projectedCoordinateOrbit Phi frame) := by
  let liftCurve : ℝ → (orientedCoordinateLift Phi frame 2 ⁻¹' {d}) :=
    fun t ↦ ⟨O.curve t, O.stays_in_level t⟩
  have hliftContinuous : Continuous liftCurve := Continuous.subtype_mk
    (continuous_iff_continuousAt.mpr fun t ↦ (O.integral t).continuousAt) _
  have hliftInjective : IsLocallyInjective liftCurve := by
    intro t
    obtain ⟨U, hUopen, htU, hUinj⟩ := O.isLocallyInjective
      ((orientedCoordinateLift_contDiff Phi frame 2).of_le
        (WithTop.coe_le_coe.mpr le_top)) hd t
    exact ⟨U, hUopen, htU, fun a ha b hb hab ↦
      hUinj ha hb (congrArg Subtype.val hab)⟩
  have hcoverInjective : IsLocallyInjective
      (regularPlaneFiberToCoordinateTorusLevel Phi frame d) :=
    (regularPlaneFiberToCoordinateTorusLevel_isLocalHomeomorph Phi frame d).isLocallyInjective
  have hlocalInjective : IsLocallyInjective
      (O.projectedCoordinateOrbit Phi frame) := by
    have hcomp := IsLocallyInjective.comp_of_continuous
      hcoverInjective hliftInjective hliftContinuous
    change IsLocallyInjective
      (regularPlaneFiberToCoordinateTorusLevel Phi frame d ∘ liftCurve)
    exact hcomp
  exact isLocalHomeomorph_of_continuous_locallyInjective_locallyLineModeled
    (isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hd)
    O.continuous_projectedCoordinateOrbit hlocalInjective

/-- A projected complete orbit remains in the connected component containing its time-zero
point. -/
theorem CompleteRegularLevelIntegralCurve.projectedCoordinateOrbit_mem_componentPiece
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    {x : (orientedCoordinateLift Phi frame 2) ⁻¹' {d}}
    (O : CompleteRegularLevelIntegralCurve
      (orientedCoordinateLift Phi frame 2) d x) (t : ℝ) :
    O.projectedCoordinateOrbit Phi frame t ∈ componentPiece
      (ConnectedComponents.mk (O.projectedCoordinateOrbit Phi frame 0)) := by
  rw [componentPiece, connectedComponents_preimage_singleton]
  have hconnected : IsConnected (Set.range (O.projectedCoordinateOrbit Phi frame)) :=
    isConnected_range O.continuous_projectedCoordinateOrbit
  apply hconnected.subset_connectedComponent
  · exact ⟨0, rfl⟩
  · exact ⟨t, rfl⟩

/-! ## Exact component-orbit output -/

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

/-- The exact result of the compact continuation, uniqueness, and orbit-openness argument for one
connected component of a quotient coordinate level.

`liftedIntegral` is the analytic output.  `localHomeomorph_curve` follows from nonstationarity and
the local line charts.  `surjective_curve` is the connectedness consequence once distinct ODE
orbits are shown to be disjoint open subsets.  `translate_eq_of_eq` is autonomous ODE uniqueness.
Keeping these fields separate prevents any circle-classification conclusion from being smuggled
into the ODE contract. -/
structure RegularComponentCompleteOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) where
  basepoint : componentPiece c
  basepointLift : Plane
  basepointLift_level : orientedCoordinateLift Phi frame 2 basepointLift = d
  basepointLift_expPair : planeExpPair basepointLift = basepoint.1.1
  liftedIntegral : CompleteRegularLevelIntegralCurve
    (orientedCoordinateLift Phi frame 2) d
    ⟨basepointLift, basepointLift_level⟩
  curve : ℝ → componentPiece c
  curve_eq_expPair : ∀ t,
    (curve t : coordinateTorusLevelSet Phi frame d).1 =
      planeExpPair (liftedIntegral.curve t)
  localHomeomorph_curve : IsLocalHomeomorph curve
  surjective_curve : Function.Surjective curve
  translate_eq_of_eq : ∀ {s t : ℝ}, curve s = curve t →
    ∀ u : ℝ, curve (s + u) = curve (t + u)

namespace RegularComponentCompleteOrbit

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)}

/-- Forget the analytic provenance and retain exactly the homogeneous local orbit used by the
period-subgroup classification. -/
def toHomogeneousLocalOrbit (O : RegularComponentCompleteOrbit Phi frame d c) :
    HomogeneousLocalOrbit (componentPiece c) where
  curve := O.curve
  localHomeomorph_curve := O.localHomeomorph_curve
  surjective_curve := O.surjective_curve
  translate_eq_of_eq := O.translate_eq_of_eq

/-- A complete regular component orbit provides its cyclic parametrization. -/
def cyclicLineParametrization (O : RegularComponentCompleteOrbit Phi frame d c)
    [CompactSpace (componentPiece c)] :
    CyclicLineParametrization (componentPiece c) :=
  O.toHomogeneousLocalOrbit.cyclicLineParametrization

end RegularComponentCompleteOrbit

/-- Complete regular orbits on every component close the existing component-classification API. -/
def componentCircleClassificationOfCompleteOrbits
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (hcompact : CompactSpace (coordinateTorusLevelSet Phi frame d))
    (hlocallyConnected : LocallyConnectedSpace
      (coordinateTorusLevelSet Phi frame d))
    (orbit : ∀ c : ConnectedComponents (coordinateTorusLevelSet Phi frame d),
      RegularComponentCompleteOrbit Phi frame d c) :
    ComponentCircleClassification (coordinateTorusLevelSet Phi frame d) := by
  let _ : CompactSpace (coordinateTorusLevelSet Phi frame d) := hcompact
  let _ : LocallyConnectedSpace (coordinateTorusLevelSet Phi frame d) :=
    hlocallyConnected
  apply componentCircleClassificationOfCyclicParametrizations
  intro c
  let _ : CompactSpace (componentPiece c) :=
    isCompact_iff_compactSpace.mp (isClopen_componentPiece c).isClosed.isCompact
  exact (orbit c).cyclicLineParametrization

/-- At a regular coordinate value, every quotient-level component is one complete projected
rotated-gradient orbit.  Distinct complete orbits are disjoint by deck-aware global uniqueness;
since every orbit is open, the orbit through a basepoint is clopen in its connected component and
therefore surjective. -/
theorem exists_regularComponentCompleteOrbit
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d)
    (c : ConnectedComponents (coordinateTorusLevelSet Phi frame d)) :
    Nonempty (RegularComponentCompleteOrbit Phi frame d c) := by
  let Level := coordinateTorusLevelSet Phi frame d
  let _ : LocallyConnectedSpace Level := locallyConnectedSpace_of_isLocallyLineModeled
    (isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hd)
  obtain ⟨basepointValue, hbasepointValue⟩ := componentPiece_nonempty c
  let basepoint : componentPiece c := ⟨basepointValue, hbasepointValue⟩
  obtain ⟨baseLiftPoint, hbaseLiftPoint⟩ :=
    regularPlaneFiberToCoordinateTorusLevel_surjective Phi frame d basepoint.1
  let liftedIntegral := Classical.choice
    (exists_completeRegularLevelIntegralCurve_orientedCoordinateLift
      Phi frame 2 baseLiftPoint)
  let levelCurve := liftedIntegral.projectedCoordinateOrbit Phi frame
  have hlevelCurveZero : levelCurve 0 = basepoint.1 := by
    rw [show levelCurve 0 = regularPlaneFiberToCoordinateTorusLevel Phi frame d
      baseLiftPoint by
      apply Subtype.ext
      simp [levelCurve, CompleteRegularLevelIntegralCurve.projectedCoordinateOrbit,
        liftedIntegral.curve_zero]]
    exact hbaseLiftPoint
  have hlevelCurveComponent (t : ℝ) : levelCurve t ∈ componentPiece c := by
    have hmem := liftedIntegral.projectedCoordinateOrbit_mem_componentPiece Phi frame t
    change levelCurve t ∈ componentPiece (ConnectedComponents.mk (levelCurve 0)) at hmem
    rwa [hlevelCurveZero, show ConnectedComponents.mk basepoint.1 = c from basepoint.2] at hmem
  let curve : ℝ → componentPiece c := fun t ↦ ⟨levelCurve t, hlevelCurveComponent t⟩
  have hlevelLocal : IsLocalHomeomorph levelCurve :=
    liftedIntegral.isLocalHomeomorph_projectedCoordinateOrbit Phi frame hd
  have hcurveLocal : IsLocalHomeomorph curve := by
    apply isLocalHomeomorph_codRestrict_open hlevelLocal (componentPiece c)
      (isClopen_componentPiece c).2
  have orbitAt : ∀ z : Level,
      ∃ (zLift : (orientedCoordinateLift Phi frame 2) ⁻¹' {d})
        (Oz : CompleteRegularLevelIntegralCurve
          (orientedCoordinateLift Phi frame 2) d zLift),
        Oz.projectedCoordinateOrbit Phi frame 0 = z := by
    intro z
    obtain ⟨zLift, hzLift⟩ :=
      regularPlaneFiberToCoordinateTorusLevel_surjective Phi frame d z
    let Oz := Classical.choice
      (exists_completeRegularLevelIntegralCurve_orientedCoordinateLift Phi frame 2 zLift)
    refine ⟨zLift, Oz, ?_⟩
    rw [show Oz.projectedCoordinateOrbit Phi frame 0 =
      regularPlaneFiberToCoordinateTorusLevel Phi frame d zLift by
      apply Subtype.ext
      simp [CompleteRegularLevelIntegralCurve.projectedCoordinateOrbit, Oz.curve_zero]]
    exact hzLift
  have hcurveSurjective : Function.Surjective curve := by
    let R : Set (componentPiece c) := Set.range curve
    have hRopen : IsOpen R := by
      simpa only [image_univ] using hcurveLocal.isOpenMap Set.univ isOpen_univ
    have hRcomplOpen : IsOpen Rᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨zLift, Oz, hOzZero⟩ := orbitAt z.1
      let zLevelCurve := Oz.projectedCoordinateOrbit Phi frame
      have hzLevelComponent (t : ℝ) : zLevelCurve t ∈ componentPiece c := by
        have hmem := Oz.projectedCoordinateOrbit_mem_componentPiece Phi frame t
        rw [hOzZero, show ConnectedComponents.mk z.1 = c from z.2] at hmem
        exact hmem
      let zCurve : ℝ → componentPiece c := fun t ↦ ⟨zLevelCurve t, hzLevelComponent t⟩
      have hzLocal : IsLocalHomeomorph zCurve := by
        apply isLocalHomeomorph_codRestrict_open
          (Oz.isLocalHomeomorph_projectedCoordinateOrbit Phi frame hd)
          (componentPiece c) (isClopen_componentPiece c).2
      refine ⟨Set.range zCurve, ?_, ?_, ⟨0, ?_⟩⟩
      · rintro w ⟨tw, rfl⟩ ⟨s, hs⟩
        have hmeet : planeExpPair (liftedIntegral.curve s) =
            planeExpPair (Oz.curve tw) := by
          have := congrArg (fun p : componentPiece c ↦ (p.1 : Circle × Circle)) hs
          simpa [curve, levelCurve, zCurve, zLevelCurve,
            CompleteRegularLevelIntegralCurve.projectedCoordinateOrbit,
            regularPlaneFiberToCoordinateTorusLevel] using this
        have htranslate := completeRegularLevelIntegralCurves_expPair_translate_eq
          Phi frame 2 liftedIntegral Oz hmeet (-tw)
        apply hz
        refine ⟨s - tw, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        calc
          planeExpPair (liftedIntegral.curve (s - tw)) =
              planeExpPair (Oz.curve 0) := by
            simpa [sub_eq_add_neg] using htranslate
          _ = (z : coordinateTorusLevelSet Phi frame d).1 :=
            congrArg Subtype.val hOzZero
      · simpa only [image_univ] using hzLocal.isOpenMap Set.univ isOpen_univ
      · apply Subtype.ext
        exact hOzZero
    have hRclosed : IsClosed R := by
      rw [← isOpen_compl_iff]
      simpa only [compl_compl] using hRcomplOpen
    have hRclopen : IsClopen R := ⟨hRclosed, hRopen⟩
    let _ : PreconnectedSpace (componentPiece c) :=
      isPreconnected_iff_preconnectedSpace.mp (isConnected_componentPiece c).2
    have hRuniv : R = Set.univ := hRclopen.eq_univ ⟨curve 0, ⟨0, rfl⟩⟩
    intro z
    have hzR : z ∈ R := hRuniv.symm ▸ mem_univ z
    exact hzR
  refine ⟨{
    basepoint := basepoint
    basepointLift := baseLiftPoint
    basepointLift_level := baseLiftPoint.property
    basepointLift_expPair := by
      exact congrArg Subtype.val hbaseLiftPoint
    liftedIntegral := liftedIntegral
    curve := curve
    curve_eq_expPair := fun t ↦ rfl
    localHomeomorph_curve := hcurveLocal
    surjective_curve := hcurveSurjective
    translate_eq_of_eq := ?_
  }⟩
  intro s t hst u
  apply Subtype.ext
  apply Subtype.ext
  have hmeet : planeExpPair (liftedIntegral.curve s) =
      planeExpPair (liftedIntegral.curve t) := by
    exact congrArg (fun p : componentPiece c ↦ (p.1 : Circle × Circle)) hst
  exact completeRegularLevelIntegralCurves_expPair_translate_eq
    Phi frame 2 liftedIntegral liftedIntegral hmeet u

/-- Every regular quotient coordinate level has its componentwise circle classification. -/
def componentCircleClassification_regularCoordinateLevel
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d) :
    ComponentCircleClassification (coordinateTorusLevelSet Phi frame d) := by
  let hcompact : CompactSpace (coordinateTorusLevelSet Phi frame d) :=
    isCompact_iff_compactSpace.mp (isCompact_coordinateTorusLevelSet Phi frame d)
  let hconnected : LocallyConnectedSpace (coordinateTorusLevelSet Phi frame d) :=
    locallyConnectedSpace_of_isLocallyLineModeled
      (isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hd)
  apply componentCircleClassificationOfCompleteOrbits Phi frame d hcompact hconnected
  intro c
  exact Classical.choice (exists_regularComponentCompleteOrbit Phi frame hd c)

/-- A packaged quotient level is classified as soon as one retains the regular-value proof used
to construct its local charts.  The older package does not itself retain that analytic proof. -/
def componentCircleClassification_of_packagedRegularValue
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {a b : ℝ}
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) S.selection.level) :
    ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level) :=
  componentCircleClassification_regularCoordinateLevel Phi frame hd

/-- Unconditionally choose a `RegularCoordinateTorusLevel` together with the componentwise circle
classification of its quotient level.  The regular-value proof is retained during selection;
the older `RegularCoordinateTorusLevel` structure stores only the resulting charts and cannot by
itself reconstruct derivative nonvanishing. -/
theorem exists_regularCoordinateTorusLevel_with_classification
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    {a b : ℝ} (hab : a < b) :
    ∃ S : RegularCoordinateTorusLevel Phi frame a b,
      Nonempty (ComponentCircleClassification
        (coordinateTorusLevelSet Phi frame S.selection.level)) := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    orientedCoordinateLift_contDiff Phi frame 2
  have hnull : CriticalValuesNull f :=
    criticalValuesNull_of_sardMoreiraConclusion (planarSardTheorem f hf)
  obtain ⟨d, hdmem, hdregular⟩ := exists_regularValue_between hnull hab
  let selection : CompactRegularLevelSelection f a b := {
    level := d
    level_mem := hdmem
    isCompact := isCompact_fundamentalLevelSet hf.continuous d
    localCharts := regularValue_has_local_charts hf hdregular
  }
  let S : RegularCoordinateTorusLevel Phi frame a b := {
    selection := selection
    quotientLocallyLineModeled :=
      isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hdregular
  }
  exact ⟨S, ⟨componentCircleClassification_of_packagedRegularValue S hdregular⟩⟩

end Submission.SurfaceRegularValue
