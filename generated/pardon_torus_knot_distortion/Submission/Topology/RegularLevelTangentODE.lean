import Submission.Topology.PeriodicOrbitClassification
import Submission.Topology.RegularLevelQuotientCharts
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
import Mathlib.Algebra.Order.ToIntervalMod

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
open scoped Topology

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

/-! ## Deck transport from the compact fundamental level -/

open LeanEval.KnotTheory.PardonDistortion
open Submission.PardonDistortion Submission.Torus

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

end Submission.SurfaceRegularValue
