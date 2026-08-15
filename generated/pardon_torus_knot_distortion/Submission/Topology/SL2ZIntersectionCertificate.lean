import Submission.Topology.CircleSignedDegree

/-!
# Direct intersection certificates from an `SL(2, Z)` coordinate

For coprime `p,q`, the character

`(z₁,z₂) ↦ z₂ ^ p / z₁ ^ q`

is the second coordinate of a unimodular torus coordinate change.  Its kernel is exactly the
image of the primitive `(p,q)` curve.  On a loop with real coordinate lifts, the character is
the exponential of `p * theta₂ - q * theta₁`, whose winding is the usual slope determinant.

Thus transverse intersections reduce to the one-dimensional roots handled by
`CircleSignedDegree`.  The only extra datum below is the exact conversion from loop-root
parameters to knot parameters in the half-open period.  This conversion is where embeddedness
and seam uniqueness enter; no homotopy continuation is used.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped BigOperators

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology

/-- The second coordinate of the determinant-one change of torus coordinates adapted to the
primitive slope `(p,q)`. -/
def slopeKernelCoordinate (p q : ℕ) (z : Circle × Circle) : Circle :=
  z.2 ^ p / z.1 ^ q

/-- The integral coordinate map with matrix `[[a,b],[-q,p]]`.  Its second component is written
multiplicatively as the adapted kernel character. -/
def adaptedTorusCoordinate (a b : ℤ) (p q : ℕ)
    (z : Circle × Circle) : Circle × Circle :=
  (z.1 ^ a * z.2 ^ b, slopeKernelCoordinate p q z)

/-- The adapted second coordinate is identically one on the `(p,q)` knot lift. -/
@[simp] theorem slopeKernelCoordinate_torusKnotLift (p q : ℕ) (t : ℝ) :
    slopeKernelCoordinate p q (Submission.Torus.torusKnotLift p q t) = 1 := by
  unfold slopeKernelCoordinate Submission.Torus.torusKnotLift
  rw [← Circle.exp_natCast_mul, ← Circle.exp_natCast_mul]
  rw [show (q : ℝ) * ((p : ℝ) * t) = (p : ℝ) * ((q : ℝ) * t) by ring]
  simp

/-- When `a*p+b*q=1`, the adapted matrix sends the knot slope to the horizontal unit slope. -/
theorem adaptedTorusCoordinate_torusKnotLift
    (a b : ℤ) (p q : ℕ) (hab : a * p + b * q = 1) (t : ℝ) :
    adaptedTorusCoordinate a b p q (Submission.Torus.torusKnotLift p q t) =
      (Circle.exp t, 1) := by
  apply Prod.ext
  · change Circle.exp ((p : ℝ) * t) ^ a * Circle.exp ((q : ℝ) * t) ^ b =
      Circle.exp t
    rw [← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, ← Circle.exp_add]
    congr 1
    have habR : (a : ℝ) * (p : ℝ) + (b : ℝ) * (q : ℝ) = 1 := by
      exact_mod_cast hab
    linear_combination t * habR
  · exact slopeKernelCoordinate_torusKnotLift p q t

/-- Coprimality supplies a determinant-one adapted coordinate matrix. -/
theorem exists_adaptedTorusCoordinate (p q : ℕ) (hc : p.Coprime q) :
    ∃ a b : ℤ, a * p + b * q = 1 ∧
      ∀ t, adaptedTorusCoordinate a b p q (Submission.Torus.torusKnotLift p q t) =
        (Circle.exp t, 1) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * q = 1 := hc.isCoprime
  exact ⟨a, b, hab, adaptedTorusCoordinate_torusKnotLift a b p q hab⟩

/-- Bézout's identity proves that the adapted character has no kernel beyond the primitive knot
circle.  This is the set-level content of the `SL(2, Z)` coordinate change. -/
theorem slopeKernelCoordinate_eq_one_iff_mem_range_torusKnotLift
    (p q : ℕ) (hc : p.Coprime q) (z : Circle × Circle) :
    slopeKernelCoordinate p q z = 1 ↔
      z ∈ Set.range (Submission.Torus.torusKnotLift p q) := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := Circle.exp_surjective z.1
    obtain ⟨y, hy⟩ := Circle.exp_surjective z.2
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * q = 1 := hc.isCoprime
    have hchar : Circle.exp ((p : ℝ) * y) = Circle.exp ((q : ℝ) * x) := by
      calc
        Circle.exp ((p : ℝ) * y) = Circle.exp y ^ p := Circle.exp_natCast_mul y p
        _ = z.2 ^ p := by rw [hy]
        _ = z.1 ^ q := div_eq_one.mp hz
        _ = Circle.exp x ^ q := by rw [hx]
        _ = Circle.exp ((q : ℝ) * x) := (Circle.exp_natCast_mul x q).symm
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hchar
    let t : ℝ := (a : ℝ) * x + (b : ℝ) * y
    refine ⟨t, ?_⟩
    apply Prod.ext
    · change Circle.exp ((p : ℝ) * t) = z.1
      rw [← hx]
      apply Circle.exp_eq_exp.mpr
      refine ⟨b * k, ?_⟩
      have habR : (a : ℝ) * (p : ℝ) + (b : ℝ) * (q : ℝ) = 1 := by
        exact_mod_cast hab
      push_cast
      dsimp [t]
      linear_combination (b : ℝ) * hk + x * habR
    · change Circle.exp ((q : ℝ) * t) = z.2
      rw [← hy]
      apply Circle.exp_eq_exp.mpr
      refine ⟨-(a * k), ?_⟩
      have habR : (a : ℝ) * (p : ℝ) + (b : ℝ) * (q : ℝ) = 1 := by
        exact_mod_cast hab
      push_cast
      dsimp [t]
      linear_combination -(a : ℝ) * hk + y * habR
  · rintro ⟨t, rfl⟩
    exact slopeKernelCoordinate_torusKnotLift p q t

/-- The real lift of the adapted second circle coordinate along a lifted torus loop. -/
def transformedSlopeAngle {gamma : ℝ → Circle × Circle}
    (p q : ℕ) (L : TorusLoopLift gamma) (t : ℝ) : ℝ :=
  (p : ℝ) * L.second.angle t - (q : ℝ) * L.first.angle t

/-- Exponentiating the transformed real lift gives the adapted circle character. -/
theorem exp_transformedSlopeAngle {gamma : ℝ → Circle × Circle}
    (p q : ℕ) (L : TorusLoopLift gamma) (t : ℝ) :
    Circle.exp (transformedSlopeAngle p q L t) =
      slopeKernelCoordinate p q (gamma t) := by
  unfold transformedSlopeAngle slopeKernelCoordinate
  rw [Circle.exp_sub, Circle.exp_natCast_mul, Circle.exp_natCast_mul,
    L.first.exp_angle, L.second.exp_angle]

/-- Smooth coordinate lifts give a smooth transformed scalar lift. -/
theorem contDiff_transformedSlopeAngle {gamma : ℝ → Circle × Circle}
    (p q : ℕ) (L : TorusLoopLift gamma)
    (hfirst : ContDiff ℝ 1 L.first.angle)
    (hsecond : ContDiff ℝ 1 L.second.angle) :
    ContDiff ℝ 1 (transformedSlopeAngle p q L) := by
  exact (contDiff_const.mul hsecond).sub (contDiff_const.mul hfirst)

/-- Exact one-dimensional reduction: transformed-coordinate roots are precisely points of the
loop lying on the primitive knot circle. -/
theorem exp_transformedSlopeAngle_eq_one_iff_mem_range_torusKnotLift
    {gamma : ℝ → Circle × Circle} (p q : ℕ) (hc : p.Coprime q)
    (L : TorusLoopLift gamma) (t : ℝ) :
    Circle.exp (transformedSlopeAngle p q L t) = 1 ↔
      gamma t ∈ Set.range (Submission.Torus.torusKnotLift p q) := by
  rw [exp_transformedSlopeAngle,
    slopeKernelCoordinate_eq_one_iff_mem_range_torusKnotLift p q hc]

/-- The transformed lift gains exactly the slope determinant over one period. -/
theorem transformedSlopeAngle_add_period {gamma : ℝ → Circle × Circle}
    (p q : ℕ) (L : TorusLoopLift gamma) (t : ℝ) :
    transformedSlopeAngle p q L (t + 2 * Real.pi) =
      transformedSlopeAngle p q L t +
        (slopeIntersectionDet p q L.first.winding L.second.winding : ℝ) *
          (2 * Real.pi) := by
  unfold transformedSlopeAngle slopeIntersectionDet
  rw [L.first.angle_add_period, L.second.angle_add_period]
  push_cast
  ring

/-- The period laws in a torus lift already imply periodicity of its underlying circle-product
loop; no separate periodicity assumption is needed. -/
theorem TorusLoopLift.periodic_gamma {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) : Function.Periodic gamma (2 * Real.pi) := by
  intro t
  apply Prod.ext
  · calc
      (gamma (t + 2 * Real.pi)).1 = Circle.exp (L.first.angle (t + 2 * Real.pi)) :=
        (L.first.exp_angle _).symm
      _ = Circle.exp (L.first.angle t +
          (L.first.winding : ℝ) * (2 * Real.pi)) := by
        rw [L.first.angle_add_period]
      _ = Circle.exp (L.first.angle t) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨L.first.winding, rfl⟩
      _ = (gamma t).1 := L.first.exp_angle t
  · calc
      (gamma (t + 2 * Real.pi)).2 = Circle.exp (L.second.angle (t + 2 * Real.pi)) :=
        (L.second.exp_angle _).symm
      _ = Circle.exp (L.second.angle t +
          (L.second.winding : ℝ) * (2 * Real.pi)) := by
        rw [L.second.angle_add_period]
      _ = Circle.exp (L.second.angle t) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨L.second.winding, rfl⟩
      _ = (gamma t).2 := L.second.exp_angle t

/-- A point in the primitive kernel has a unique knot parameter in the canonical half-open
period.  Existence uses `toIcoMod`; uniqueness is the existing coprime injectivity theorem. -/
theorem existsUnique_knotParameter_of_slopeKernelCoordinate_eq_one
    (p q : ℕ) (hc : p.Coprime q) (z : Circle × Circle)
    (hz : slopeKernelCoordinate p q z = 1) :
    ∃! t : ℝ, t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
      Submission.Torus.torusKnotLift p q t = z := by
  obtain ⟨t, ht⟩ :=
    (slopeKernelCoordinate_eq_one_iff_mem_range_torusKnotLift p q hc z).mp hz
  let u : ℝ := toIcoMod Real.two_pi_pos 0 t
  let k : ℤ := toIcoDiv Real.two_pi_pos 0 t
  have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 t
  have hukt : u + (k : ℝ) * (2 * Real.pi) = t :=
    toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 t
  have huknot : Submission.Torus.torusKnotLift p q u = z := by
    calc
      Submission.Torus.torusKnotLift p q u =
          Submission.Torus.torusKnotLift p q
            (u + (k : ℝ) * (2 * Real.pi)) :=
        ((Submission.Torus.torusKnotLift_periodic p q).int_mul k u).symm
      _ = Submission.Torus.torusKnotLift p q t := by rw [hukt]
      _ = z := ht
  refine ⟨u, ⟨hu, huknot⟩, ?_⟩
  intro v hv
  exact Submission.Torus.torusKnotLift_injOn p q hc hv.1 hu (hv.2.trans huknot.symm)

/-- Canonical half-open knot parameter of a point in the primitive kernel. -/
def canonicalKnotParameter (p q : ℕ) (hc : p.Coprime q) (z : Circle × Circle)
    (hz : slopeKernelCoordinate p q z = 1) : ℝ :=
  Classical.choose (existsUnique_knotParameter_of_slopeKernelCoordinate_eq_one p q hc z hz)

theorem canonicalKnotParameter_mem_period
    (p q : ℕ) (hc : p.Coprime q) (z : Circle × Circle)
    (hz : slopeKernelCoordinate p q z = 1) :
    canonicalKnotParameter p q hc z hz ∈ Ico (0 : ℝ) (2 * Real.pi) :=
  (Classical.choose_spec
    (existsUnique_knotParameter_of_slopeKernelCoordinate_eq_one p q hc z hz)).1.1

theorem torusKnotLift_canonicalKnotParameter
    (p q : ℕ) (hc : p.Coprime q) (z : Circle × Circle)
    (hz : slopeKernelCoordinate p q z = 1) :
    Submission.Torus.torusKnotLift p q (canonicalKnotParameter p q hc z hz) = z :=
  (Classical.choose_spec
    (existsUnique_knotParameter_of_slopeKernelCoordinate_eq_one p q hc z hz)).1.2

/-! ## From loop roots to knot parameters -/

/-- Exact half-open-period conversion between ordered loop roots and geometric knot parameters.
For an embedded periodic loop this follows from the kernel characterization and injectivity of
both parametrizations.  Keeping it explicit also supports callers with a different embedding API. -/
structure CircleRootKnotParameterization
    (p q : ℕ) (gamma : ℝ → Circle × Circle)
    {theta : ℝ → ℝ} {winding : ℤ}
    (D : OrderedRegularCircleRootData theta winding) where
  knotParameter : Fin D.count → ℝ
  knotParameter_mem_period : ∀ i, knotParameter i ∈ Ico (0 : ℝ) (2 * Real.pi)
  intersection : ∀ i,
    Submission.Torus.torusKnotLift p q (knotParameter i) = gamma (D.root i)
  knotParameter_injective : Function.Injective knotParameter
  complete : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
    Submission.Torus.torusKnotLift p q t ∈ Set.range gamma →
      ∃ i, knotParameter i = t

/-- The canonical knot parameter attached to one ordered transformed-coordinate root. -/
def rootKnotParameter {p q : ℕ} {gamma : ℝ → Circle × Circle}
    (hc : p.Coprime q) (L : TorusLoopLift gamma)
    {winding : ℤ}
    (D : OrderedRegularCircleRootData (transformedSlopeAngle p q L) winding)
    (i : Fin D.count) : ℝ :=
  canonicalKnotParameter p q hc (gamma (D.root i)) (by
    rw [← exp_transformedSlopeAngle p q L]
    exact D.root_exp_eq_one i)

theorem rootKnotParameter_mem_period {p q : ℕ} {gamma : ℝ → Circle × Circle}
    (hc : p.Coprime q) (L : TorusLoopLift gamma)
    {winding : ℤ}
    (D : OrderedRegularCircleRootData (transformedSlopeAngle p q L) winding)
    (i : Fin D.count) :
    rootKnotParameter hc L D i ∈ Ico (0 : ℝ) (2 * Real.pi) :=
  canonicalKnotParameter_mem_period _ _ _ _ _

theorem torusKnotLift_rootKnotParameter {p q : ℕ}
    {gamma : ℝ → Circle × Circle} (hc : p.Coprime q) (L : TorusLoopLift gamma)
    {winding : ℤ}
    (D : OrderedRegularCircleRootData (transformedSlopeAngle p q L) winding)
    (i : Fin D.count) :
    Submission.Torus.torusKnotLift p q (rootKnotParameter hc L D i) =
      gamma (D.root i) :=
  torusKnotLift_canonicalKnotParameter _ _ _ _ _

/-- For a loop embedded on the canonical half-open period, the `SL(2,Z)` kernel theorem builds
the complete root-to-knot parameter conversion automatically. -/
def circleRootKnotParameterization_of_injective
    (p q : ℕ) (hc : p.Coprime q) {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma)
    (D : OrderedRegularCircleRootData (transformedSlopeAngle p q L)
      (slopeIntersectionDet p q L.first.winding L.second.winding))
    (hinjective : Set.InjOn gamma (Ico (0 : ℝ) (2 * Real.pi))) :
    CircleRootKnotParameterization p q gamma D where
  knotParameter := rootKnotParameter hc L D
  knotParameter_mem_period := rootKnotParameter_mem_period hc L D
  intersection := torusKnotLift_rootKnotParameter hc L D
  knotParameter_injective := by
    intro i j hij
    apply D.strictMono_root.injective
    apply hinjective (D.root_mem_period i) (D.root_mem_period j)
    rw [← torusKnotLift_rootKnotParameter hc L D i,
      ← torusKnotLift_rootKnotParameter hc L D j, hij]
  complete := by
    intro t ht
    rintro ⟨u, hu⟩
    let v : ℝ := toIcoMod Real.two_pi_pos 0 u
    let k : ℤ := toIcoDiv Real.two_pi_pos 0 u
    have hv : v ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 u
    have hvku : v + (k : ℝ) * (2 * Real.pi) = u :=
      toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 u
    have hgamma : gamma v = gamma u := by
      calc
        gamma v = gamma (v + (k : ℝ) * (2 * Real.pi)) :=
          (L.periodic_gamma.int_mul k v).symm
        _ = gamma u := by rw [hvku]
    have hvroot : Circle.exp (transformedSlopeAngle p q L v) = 1 := by
      rw [exp_transformedSlopeAngle, hgamma, hu]
      exact slopeKernelCoordinate_torusKnotLift p q t
    obtain ⟨i, hi⟩ := D.root_complete v hv hvroot
    refine ⟨i, ?_⟩
    apply Submission.Torus.torusKnotLift_injOn p q hc
      (rootKnotParameter_mem_period hc L D i) ht
    rw [torusKnotLift_rootKnotParameter hc L D i, hi, hgamma, ← hu]

namespace CircleRootKnotParameterization

variable {p q : ℕ} {gamma : ℝ → Circle × Circle}
  {theta : ℝ → ℝ} {winding : ℤ}
  {D : OrderedRegularCircleRootData theta winding}

/-- Knot parameters corresponding to the ordered loop roots. -/
def parameterFinset (P : CircleRootKnotParameterization p q gamma D) : Finset ℝ :=
  Finset.univ.image P.knotParameter

theorem parameterFinset_eq_intersections
    (P : CircleRootKnotParameterization p q gamma D) :
    (P.parameterFinset : Set ℝ) = torusLoopIntersectionParameters p q gamma := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    subst t
    exact ⟨P.knotParameter_mem_period i, ⟨D.root i, (P.intersection i).symm⟩⟩
  · rintro ⟨ht, hintersection⟩
    obtain ⟨i, hi⟩ := P.complete t ht hintersection
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- Transport a root sign to its knot parameter.  Outside the finite parameter set its value is
irrelevant, so it is set to `1`. -/
def transportedSign (P : CircleRootKnotParameterization p q gamma D) (t : ℝ) : ℤ :=
  if h : ∃ i, P.knotParameter i = t then
    realRootCrossingSign theta (D.root (Classical.choose h))
  else 1

theorem transportedSign_knotParameter
    (P : CircleRootKnotParameterization p q gamma D) (i : Fin D.count) :
    P.transportedSign (P.knotParameter i) =
      realRootCrossingSign theta (D.root i) := by
  rw [transportedSign, dif_pos ⟨i, rfl⟩]
  have hchosen := Classical.choose_spec
    (show ∃ j, P.knotParameter j = P.knotParameter i from ⟨i, rfl⟩)
  have heq : Classical.choose
      (show ∃ j, P.knotParameter j = P.knotParameter i from ⟨i, rfl⟩) = i :=
    P.knotParameter_injective hchosen
  rw [heq]

theorem transportedSign_natAbs
    (P : CircleRootKnotParameterization p q gamma D)
    (t : ℝ) (_ht : t ∈ P.parameterFinset) :
    (P.transportedSign t).natAbs = 1 := by
  unfold transportedSign
  split <;> simp

/-- Direct transverse certificate obtained from one-dimensional signed degree, with no globally
transverse normalization homotopy. -/
def transverseIntersectionCertificate
    (P : CircleRootKnotParameterization p q gamma D)
    (m n : ℤ) (hwinding : winding = slopeIntersectionDet p q m n) :
    TransverseIntersectionCertificate p q gamma m n where
  parameters := P.parameterFinset
  parameters_eq := P.parameterFinset_eq_intersections
  sign := P.transportedSign
  sign_natAbs := P.transportedSign_natAbs
  signed_sum := by
    rw [parameterFinset, Finset.sum_image P.knotParameter_injective.injOn]
    calc
      (∑ i ∈ Finset.univ, P.transportedSign (P.knotParameter i)) =
          ∑ i : Fin D.count, realRootCrossingSign theta (D.root i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact P.transportedSign_knotParameter i
      _ = winding := D.sum_crossingSign_indices
      _ = slopeIntersectionDet p q m n := hwinding

/-- Complete direct wrapper for an embedded lifted loop: ordered regular roots of the transformed
coordinate produce the existing `TransverseIntersectionCertificate` with the loop's exact winding
pair. -/
def transverseIntersectionCertificate_of_injective
    (p q : ℕ) (hc : p.Coprime q) {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma)
    (D : OrderedRegularCircleRootData (transformedSlopeAngle p q L)
      (slopeIntersectionDet p q L.first.winding L.second.winding))
    (hinjective : Set.InjOn gamma (Ico (0 : ℝ) (2 * Real.pi))) :
    TransverseIntersectionCertificate p q gamma
      L.first.winding L.second.winding :=
  let P := circleRootKnotParameterization_of_injective p q hc L D hinjective
  P.transverseIntersectionCertificate L.first.winding L.second.winding rfl

end CircleRootKnotParameterization

end Submission.PardonDistortion
