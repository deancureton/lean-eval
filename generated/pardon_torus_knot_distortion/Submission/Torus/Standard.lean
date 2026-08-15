import ChallengeDeps

/-!
# The standard embedded torus and its torus-knot curves

This file separates the two angular coordinates of the standard torus.  The
real-angle parametrization `standardTorusMap` is convenient for calculations.
The map `circleTorusMap` is the corresponding map from `Circle × Circle`; it is
proved to be a closed embedding whose range is exactly the usual torus of
revolution with major radius `2` and minor radius `1`.

The standard `(p, q)` curve factors through the circle-valued lift
`torusKnotLift p q`.  Its two coordinates are literally the angle maps
`t ↦ exp (p * t)` and `t ↦ exp (q * t)`.  This makes the two winding numbers
available without having to recover them from the three ambient coordinates.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Torus

/-- The torus of revolution parametrized by its longitude angle `u` and
meridian angle `v`. -/
def standardTorusMap (u v : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then
      (2 + Real.cos v) * Real.cos u
    else if i.val = 1 then
      (2 + Real.cos v) * Real.sin u
    else
      Real.sin v)

@[simp]
theorem standardTorusMap_coord_zero (u v : ℝ) :
    standardTorusMap u v (0 : Fin 3) =
      (2 + Real.cos v) * Real.cos u :=
  rfl

@[simp]
theorem standardTorusMap_coord_one (u v : ℝ) :
    standardTorusMap u v (1 : Fin 3) =
      (2 + Real.cos v) * Real.sin u :=
  rfl

@[simp]
theorem standardTorusMap_coord_two (u v : ℝ) :
    standardTorusMap u v (2 : Fin 3) = Real.sin v :=
  rfl

/-- The curve from the challenge is the diagonal linear-angle path on the
explicit torus map. -/
theorem standardTorusCurve_eq_standardTorusMap (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t =
      standardTorusMap ((p : ℝ) * t) ((q : ℝ) * t) :=
  rfl

/-- The real-angle torus parametrization is smooth. -/
theorem standardTorusMap_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry standardTorusMap) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The explicit standard torus curve is smooth. -/
theorem standardTorusCurve_contDiff (p q : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (standardTorusCurve p q) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Adding arbitrary full turns in either angle does not change the point on
the torus. -/
theorem standardTorusMap_add_int_mul_two_pi (m n : ℤ) (u v : ℝ) :
    standardTorusMap (u + (m : ℝ) * (2 * Real.pi))
        (v + (n : ℝ) * (2 * Real.pi)) =
      standardTorusMap u v := by
  ext i
  fin_cases i <;>
    simp [standardTorusMap, Real.sin_add_int_mul_two_pi,
      Real.cos_add_int_mul_two_pi]

/-- Squared distance from the axis of revolution. -/
theorem standardTorusMap_xy_sq (u v : ℝ) :
    (standardTorusMap u v 0) ^ 2 + (standardTorusMap u v 1) ^ 2 =
      (2 + Real.cos v) ^ 2 := by
  simp only [standardTorusMap_coord_zero, standardTorusMap_coord_one]
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- The cylindrical radius of the parametrized torus point. -/
theorem standardTorusMap_radial (u v : ℝ) :
    Real.sqrt ((standardTorusMap u v 0) ^ 2 +
        (standardTorusMap u v 1) ^ 2) =
      2 + Real.cos v := by
  rw [standardTorusMap_xy_sq, Real.sqrt_sq]
  linarith [Real.neg_one_le_cos v]

/-- The squared Euclidean norm of a point of the standard torus. -/
theorem standardTorusMap_norm_sq (u v : ℝ) :
    (standardTorusMap u v 0) ^ 2 + (standardTorusMap u v 1) ^ 2 +
        (standardTorusMap u v 2) ^ 2 =
      5 + 4 * Real.cos v := by
  simp only [standardTorusMap_coord_zero, standardTorusMap_coord_one,
    standardTorusMap_coord_two]
  nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]

/-- The standard torus as the usual level set in cylindrical coordinates. -/
def geometricStandardTorus : Set R3 :=
  {x | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1}

theorem standardTorusMap_mem_geometricStandardTorus (u v : ℝ) :
    standardTorusMap u v ∈ geometricStandardTorus := by
  change (Real.sqrt ((standardTorusMap u v 0) ^ 2 +
    (standardTorusMap u v 1) ^ 2) - 2) ^ 2 +
    (standardTorusMap u v 2) ^ 2 = 1
  rw [standardTorusMap_radial, standardTorusMap_coord_two]
  nlinarith [Real.sin_sq_add_cos_sq v]

/-- The angle pair `(u, v)` is unique on the half-open fundamental square. -/
private lemma angle_eq_of_cos_eq_sin_eq {u v : ℝ}
    (hu : u ∈ Ico 0 (2 * Real.pi)) (hv : v ∈ Ico 0 (2 * Real.pi))
    (hc : Real.cos u = Real.cos v) (hs : Real.sin u = Real.sin v) :
    u = v := by
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hu hv
  apply Subtype.ext
  apply Complex.ext
  · simpa using hc
  · simpa using hs

theorem standardTorusMap_injOn :
    Set.InjOn (Function.uncurry standardTorusMap)
      (Ico (0 : ℝ) (2 * Real.pi) ×ˢ Ico (0 : ℝ) (2 * Real.pi)) := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩ ⟨u', v'⟩ ⟨hu', hv'⟩ h
  have h0 := congrArg (fun x : R3 => x (0 : Fin 3)) h
  have h1 := congrArg (fun x : R3 => x (1 : Fin 3)) h
  have h2 := congrArg (fun x : R3 => x (2 : Fin 3)) h
  change standardTorusMap u v 0 = standardTorusMap u' v' 0 at h0
  change standardTorusMap u v 1 = standardTorusMap u' v' 1 at h1
  change standardTorusMap u v 2 = standardTorusMap u' v' 2 at h2
  simp only [standardTorusMap_coord_zero] at h0
  simp only [standardTorusMap_coord_one] at h1
  simp only [standardTorusMap_coord_two] at h2
  have h0sq := congrArg (fun x : ℝ => x ^ 2) h0
  have h1sq := congrArg (fun x : ℝ => x ^ 2) h1
  have hradSq : (2 + Real.cos v) ^ 2 = (2 + Real.cos v') ^ 2 := by
    nlinarith [h0sq, h1sq, Real.sin_sq_add_cos_sq u,
      Real.sin_sq_add_cos_sq u']
  have hpos : 0 < 2 + Real.cos v := by
    linarith [Real.neg_one_le_cos v]
  have hpos' : 0 < 2 + Real.cos v' := by
    linarith [Real.neg_one_le_cos v']
  have hrad : 2 + Real.cos v = 2 + Real.cos v' := by
    nlinarith
  have hcosv : Real.cos v = Real.cos v' := by
    linarith
  have hvEq : v = v' :=
    angle_eq_of_cos_eq_sin_eq hv hv' hcosv h2
  subst v'
  have hcosu : Real.cos u = Real.cos u' :=
    mul_left_cancel₀ hpos.ne' h0
  have hsinu : Real.sin u = Real.sin u' :=
    mul_left_cancel₀ hpos.ne' h1
  exact Prod.ext (angle_eq_of_cos_eq_sin_eq hu hu' hcosu hsinu) rfl

/-- The same torus map with both angles taken modulo `2π`.  This is the
topologically useful model of the embedded surface. -/
def circleTorusMap (z w : Circle) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then
      (2 + (w : ℂ).re) * (z : ℂ).re
    else if i.val = 1 then
      (2 + (w : ℂ).re) * (z : ℂ).im
    else
      (w : ℂ).im)

@[simp]
theorem circleTorusMap_coord_zero (z w : Circle) :
    circleTorusMap z w (0 : Fin 3) =
      (2 + (w : ℂ).re) * (z : ℂ).re :=
  rfl

@[simp]
theorem circleTorusMap_coord_one (z w : Circle) :
    circleTorusMap z w (1 : Fin 3) =
      (2 + (w : ℂ).re) * (z : ℂ).im :=
  rfl

@[simp]
theorem circleTorusMap_coord_two (z w : Circle) :
    circleTorusMap z w (2 : Fin 3) = (w : ℂ).im :=
  rfl

theorem circleTorusMap_exp_exp (u v : ℝ) :
    circleTorusMap (Circle.exp u) (Circle.exp v) =
      standardTorusMap u v := by
  ext i
  fin_cases i <;> simp [circleTorusMap, standardTorusMap]

private lemma circle_re_neg_one_le (z : Circle) : -1 ≤ (z : ℂ).re := by
  have h := Complex.abs_re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at h
  exact neg_le_of_abs_le h

private lemma circle_re_im_sq (z : Circle) :
    (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  simpa [Complex.normSq_apply, pow_two] using
    (show Complex.normSq (z : ℂ) = 1 by simp)

/-- The circle-coordinate torus parametrization is globally injective. -/
theorem circleTorusMap_injective :
    Function.Injective (Function.uncurry circleTorusMap) := by
  rintro ⟨z, w⟩ ⟨z', w'⟩ h
  have h0 := congrArg (fun x : R3 => x (0 : Fin 3)) h
  have h1 := congrArg (fun x : R3 => x (1 : Fin 3)) h
  have h2 := congrArg (fun x : R3 => x (2 : Fin 3)) h
  change circleTorusMap z w 0 = circleTorusMap z' w' 0 at h0
  change circleTorusMap z w 1 = circleTorusMap z' w' 1 at h1
  change circleTorusMap z w 2 = circleTorusMap z' w' 2 at h2
  simp only [circleTorusMap_coord_zero] at h0
  simp only [circleTorusMap_coord_one] at h1
  simp only [circleTorusMap_coord_two] at h2
  have h0sq := congrArg (fun x : ℝ => x ^ 2) h0
  have h1sq := congrArg (fun x : ℝ => x ^ 2) h1
  have hradSq : (2 + (w : ℂ).re) ^ 2 =
      (2 + (w' : ℂ).re) ^ 2 := by
    nlinarith [h0sq, h1sq, circle_re_im_sq z, circle_re_im_sq z']
  have hpos : 0 < 2 + (w : ℂ).re := by
    linarith [circle_re_neg_one_le w]
  have hpos' : 0 < 2 + (w' : ℂ).re := by
    linarith [circle_re_neg_one_le w']
  have hrad : 2 + (w : ℂ).re = 2 + (w' : ℂ).re := by
    nlinarith
  have hwre : (w : ℂ).re = (w' : ℂ).re := by
    linarith
  have hw : w = w' := by
    apply Subtype.ext
    apply Complex.ext
    · exact hwre
    · exact h2
  subst w'
  have hzre : (z : ℂ).re = (z' : ℂ).re :=
    mul_left_cancel₀ hpos.ne' h0
  have hzim : (z : ℂ).im = (z' : ℂ).im :=
    mul_left_cancel₀ hpos.ne' h1
  have hz : z = z' := by
    apply Subtype.ext
    exact Complex.ext hzre hzim
  exact Prod.ext hz rfl

theorem circleTorusMap_continuous :
    Continuous (Function.uncurry circleTorusMap) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The standard torus is a closedly embedded copy of `Circle × Circle`. -/
theorem circleTorusMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (Function.uncurry circleTorusMap) :=
  circleTorusMap_continuous.isClosedEmbedding circleTorusMap_injective

theorem circleTorusMap_isEmbedding :
    Topology.IsEmbedding (Function.uncurry circleTorusMap) :=
  circleTorusMap_isClosedEmbedding.isEmbedding

private theorem circleTorusMap_range_subset_geometric :
    Set.range (Function.uncurry circleTorusMap) ⊆ geometricStandardTorus := by
  rintro x ⟨⟨z, w⟩, rfl⟩
  change circleTorusMap z w ∈ geometricStandardTorus
  rw [← Circle.exp_arg z, ← Circle.exp_arg w, circleTorusMap_exp_exp]
  exact standardTorusMap_mem_geometricStandardTorus _ _

private theorem geometric_subset_circleTorusMap_range :
    geometricStandardTorus ⊆ Set.range (Function.uncurry circleTorusMap) := by
  intro x hx
  change (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1 at hx
  let r := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have hrpos : 0 < r := by
    nlinarith [sq_nonneg (x 2)]
  have hzsq : (x 0 / r) ^ 2 + (x 1 / r) ^ 2 = 1 := by
    field_simp
    nlinarith
  let z : Circle :=
    ⟨⟨x 0 / r, x 1 / r⟩, by
      change (⟨x 0 / r, x 1 / r⟩ : ℂ) ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, Complex.norm_def, Complex.normSq_apply]
      rw [show x 0 / r * (x 0 / r) + x 1 / r * (x 1 / r) = 1 by
        nlinarith [hzsq], Real.sqrt_one]⟩
  let w : Circle :=
    ⟨⟨r - 2, x 2⟩, by
      change (⟨r - 2, x 2⟩ : ℂ) ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, Complex.norm_def, Complex.normSq_apply]
      rw [show (r - 2) * (r - 2) + x 2 * x 2 = 1 by
        dsimp [r] at hx
        nlinarith, Real.sqrt_one]⟩
  refine ⟨(z, w), ?_⟩
  change circleTorusMap z w = x
  ext i
  fin_cases i <;> simp [circleTorusMap, z, w]
  · field_simp
  · field_simp

/-- The abstract and level-set descriptions of the standard torus agree. -/
theorem circleTorusMap_range :
    Set.range (Function.uncurry circleTorusMap) = geometricStandardTorus :=
  Set.Subset.antisymm circleTorusMap_range_subset_geometric
    geometric_subset_circleTorusMap_range

theorem geometricStandardTorus_isClosed : IsClosed geometricStandardTorus := by
  rw [← circleTorusMap_range]
  exact circleTorusMap_isClosedEmbedding.isClosed_range

/-- The explicit homeomorphism from the product of circles to the geometric
level-set torus. -/
def standardTorusHomeomorph : Circle × Circle ≃ₜ geometricStandardTorus :=
  circleTorusMap_isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr circleTorusMap_range)

/-- The standard longitude: vary the first circle coordinate. -/
def standardLongitude (z : Circle) : R3 :=
  circleTorusMap z 1

/-- The standard meridian: vary the second circle coordinate. -/
def standardMeridian (w : Circle) : R3 :=
  circleTorusMap 1 w

theorem standardLongitude_continuous : Continuous standardLongitude := by
  exact circleTorusMap_continuous.comp
    (continuous_id.prodMk continuous_const)

theorem standardMeridian_continuous : Continuous standardMeridian := by
  exact circleTorusMap_continuous.comp
    (continuous_const.prodMk continuous_id)

theorem standardLongitude_injective : Function.Injective standardLongitude := by
  intro z z' h
  change Function.uncurry circleTorusMap (z, 1) =
    Function.uncurry circleTorusMap (z', 1) at h
  exact congrArg Prod.fst (circleTorusMap_injective h)

theorem standardMeridian_injective : Function.Injective standardMeridian := by
  intro w w' h
  change Function.uncurry circleTorusMap (1, w) =
    Function.uncurry circleTorusMap (1, w') at h
  exact congrArg Prod.snd (circleTorusMap_injective h)

theorem standardLongitude_isEmbedding :
    Topology.IsEmbedding standardLongitude :=
  standardLongitude_continuous.isClosedEmbedding
    standardLongitude_injective |>.isEmbedding

theorem standardMeridian_isEmbedding :
    Topology.IsEmbedding standardMeridian :=
  standardMeridian_continuous.isClosedEmbedding
    standardMeridian_injective |>.isEmbedding

/-- The `(p, q)` curve before applying the embedded-torus map. -/
def torusKnotLift (p q : ℕ) (t : ℝ) : Circle × Circle :=
  (Circle.exp ((p : ℝ) * t), Circle.exp ((q : ℝ) * t))

@[simp]
theorem torusKnotLift_fst (p q : ℕ) (t : ℝ) :
    (torusKnotLift p q t).1 = Circle.exp ((p : ℝ) * t) :=
  rfl

@[simp]
theorem torusKnotLift_snd (p q : ℕ) (t : ℝ) :
    (torusKnotLift p q t).2 = Circle.exp ((q : ℝ) * t) :=
  rfl

theorem torusKnotLift_continuous (p q : ℕ) :
    Continuous (torusKnotLift p q) := by
  unfold torusKnotLift
  fun_prop

theorem torusKnotLift_periodic (p q : ℕ) :
    Function.Periodic (torusKnotLift p q) (2 * Real.pi) := by
  intro t
  apply Prod.ext
  · apply Circle.exp_eq_exp.mpr
    refine ⟨(p : ℤ), ?_⟩
    push_cast
    ring
  · apply Circle.exp_eq_exp.mpr
    refine ⟨(q : ℤ), ?_⟩
    push_cast
    ring

/-- Coprimality makes the `(p, q)` lift one-to-one during a single turn. -/
theorem torusKnotLift_injOn (p q : ℕ) (hc : p.Coprime q) :
    Set.InjOn (torusKnotLift p q) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  have hpExp : Circle.exp ((p : ℝ) * s) = Circle.exp ((p : ℝ) * t) :=
    congrArg Prod.fst h
  have hqExp : Circle.exp ((q : ℝ) * s) = Circle.exp ((q : ℝ) * t) :=
    congrArg Prod.snd h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hpExp
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hqExp
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * q = 1 := hc.isCoprime
  have habR : (a : ℝ) * (p : ℝ) + (b : ℝ) * (q : ℝ) = 1 := by
    exact_mod_cast hab
  have hst : s = t + ((a * m + b * n : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linear_combination (a : ℝ) * hm + (b : ℝ) * hn -
      (s - t) * habR
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hs ht
  apply Circle.exp_eq_exp.mpr
  exact ⟨a * m + b * n, hst⟩

/-- The standard ambient curve is the image of its explicit circle-coordinate
lift. -/
theorem standardTorusCurve_eq_circleTorusMap (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t =
      Function.uncurry circleTorusMap (torusKnotLift p q t) := by
  rw [standardTorusCurve_eq_standardTorusMap]
  exact (circleTorusMap_exp_exp _ _).symm

theorem standardTorusCurve_periodic (p q : ℕ) :
    Function.Periodic (standardTorusCurve p q) (2 * Real.pi) := by
  intro t
  rw [standardTorusCurve_eq_circleTorusMap,
    standardTorusCurve_eq_circleTorusMap]
  congr 1
  exact torusKnotLift_periodic p q t

theorem standardTorusCurve_injOn (p q : ℕ) (hc : p.Coprime q) :
    Set.InjOn (standardTorusCurve p q) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  apply torusKnotLift_injOn p q hc hs ht
  apply circleTorusMap_injective
  rw [← standardTorusCurve_eq_circleTorusMap,
    ← standardTorusCurve_eq_circleTorusMap]
  exact h

end Submission.Torus
