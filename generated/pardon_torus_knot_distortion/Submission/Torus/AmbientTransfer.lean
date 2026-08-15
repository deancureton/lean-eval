import Submission.Torus.Standard

/-!
# Transporting the standard torus through an ambient isotopy

The benchmark presents an ambient isotopy by mutually inverse smooth maps
`H t` and `Hinv t`.  This file packages every time slice as a homeomorphism
and pulls the standard embedded torus back through its time-one slice.

The final lemmas turn the equality in the benchmark's isotopy-class witness
into an exact factorization of the given knot through that pulled-back torus.
They also remove the circle reparametrization from the range, using its
explicit inverse.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Torus

/-- Every time slice of an ambient isotopy, packaged as a homeomorphism. -/
def ambientHomeomorph (Phi : AmbientIsotopy) (t : ℝ) : R3 ≃ₜ R3 where
  toFun := Phi.H t
  invFun := Phi.Hinv t
  left_inv := Phi.inv_left t
  right_inv := Phi.inv_right t
  continuous_toFun := Phi.smooth.continuous.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := Phi.smooth_inv.continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp]
theorem ambientHomeomorph_apply (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    ambientHomeomorph Phi t x = Phi.H t x :=
  rfl

@[simp]
theorem ambientHomeomorph_symm_apply (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    (ambientHomeomorph Phi t).symm x = Phi.Hinv t x :=
  rfl

/-- The standard torus pulled back through the time-one ambient
homeomorphism. -/
def transportedTorusMap (Phi : AmbientIsotopy) (z : Circle × Circle) : R3 :=
  (ambientHomeomorph Phi 1).symm
    (Function.uncurry circleTorusMap z)

theorem transportedTorusMap_continuous (Phi : AmbientIsotopy) :
    Continuous (transportedTorusMap Phi) :=
  (ambientHomeomorph Phi 1).symm.continuous.comp
    circleTorusMap_continuous

theorem transportedTorusMap_injective (Phi : AmbientIsotopy) :
    Function.Injective (transportedTorusMap Phi) :=
  (ambientHomeomorph Phi 1).symm.injective.comp
    circleTorusMap_injective

/-- Pulling back by an ambient homeomorphism preserves the closed embedding
of the standard torus. -/
theorem transportedTorusMap_isClosedEmbedding (Phi : AmbientIsotopy) :
    Topology.IsClosedEmbedding (transportedTorusMap Phi) :=
  (ambientHomeomorph Phi 1).symm.isClosedEmbedding.comp
    circleTorusMap_isClosedEmbedding

theorem transportedTorusMap_isEmbedding (Phi : AmbientIsotopy) :
    Topology.IsEmbedding (transportedTorusMap Phi) :=
  (transportedTorusMap_isClosedEmbedding Phi).isEmbedding

/-- The embedded torus in the original coordinates of the given knot. -/
def transportedTorus (Phi : AmbientIsotopy) : Set R3 :=
  Set.range (transportedTorusMap Phi)

theorem transportedTorus_isClosed (Phi : AmbientIsotopy) :
    IsClosed (transportedTorus Phi) :=
  (transportedTorusMap_isClosedEmbedding Phi).isClosed_range

/-- The transported torus is exactly the image of the geometric standard
torus under the inverse time-one ambient map. -/
theorem transportedTorus_eq_timeOneInverse_image (Phi : AmbientIsotopy) :
    transportedTorus Phi = Phi.Hinv 1 '' geometricStandardTorus := by
  rw [← circleTorusMap_range]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Function.uncurry circleTorusMap z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

/-- The pulled-back surface is explicitly homeomorphic to a product of two
circles. -/
def transportedTorusHomeomorph (Phi : AmbientIsotopy) :
    Circle × Circle ≃ₜ transportedTorus Phi :=
  transportedTorusMap_isEmbedding Phi |>.toHomeomorph

/-- Applying the time-one ambient map sends the pulled-back torus map back to
the standard torus map. -/
@[simp]
theorem timeOne_map_transportedTorusMap (Phi : AmbientIsotopy)
    (z : Circle × Circle) :
    Phi.H 1 (transportedTorusMap Phi z) =
      Function.uncurry circleTorusMap z := by
  exact Phi.inv_right 1 _

/-- Set-level version of `timeOne_map_transportedTorusMap`. -/
theorem timeOne_image_transportedTorus (Phi : AmbientIsotopy) :
    Phi.H 1 '' transportedTorus Phi = geometricStandardTorus := by
  rw [← circleTorusMap_range]
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (timeOne_map_transportedTorusMap Phi z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨transportedTorusMap Phi z, ⟨z, rfl⟩,
      timeOne_map_transportedTorusMap Phi z⟩

/-- Pulling a standard torus-knot point back through the time-one map recovers
the original knot point from the benchmark's class witness. -/
theorem curve_eq_timeOneInverse_standardTorusCurve
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (t : ℝ) :
    K.curve t = Phi.Hinv 1 (standardTorusCurve p q (sigma.f t)) := by
  rw [← hclass t, Phi.inv_left]

/-- Exact factorization of the knot through the pulled-back circle-product
model of the torus. -/
theorem curve_eq_transportedTorusMap
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (t : ℝ) :
    K.curve t = transportedTorusMap Phi
      (torusKnotLift p q (sigma.f t)) := by
  rw [curve_eq_timeOneInverse_standardTorusCurve p q K Phi sigma hclass t,
    standardTorusCurve_eq_circleTorusMap]
  rfl

/-- The map underlying a circle reparametrization is onto, witnessed by its
specified inverse. -/
theorem circleReparam_surjective (sigma : CircleReparam) :
    Function.Surjective sigma.f := by
  intro t
  exact ⟨sigma.finv t, sigma.right_inv t⟩

theorem circleReparam_injective (sigma : CircleReparam) :
    Function.Injective sigma.f :=
  Function.LeftInverse.injective sigma.left_inv

theorem circleReparam_bijective (sigma : CircleReparam) :
    Function.Bijective sigma.f :=
  ⟨circleReparam_injective sigma, circleReparam_surjective sigma⟩

/-- Reparametrization changes the parametrization but not the range of the
pulled-back torus knot. -/
theorem curve_range_eq_transportedTorusKnot_range
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) :
    Set.range K.curve = Set.range
      (fun t => transportedTorusMap Phi (torusKnotLift p q t)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨sigma.f t,
      (curve_eq_transportedTorusMap p q K Phi sigma hclass t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := circleReparam_surjective sigma t
    exact ⟨s, by
      rw [curve_eq_transportedTorusMap p q K Phi sigma hclass s, hs]⟩

/-- At the level of subsets of ambient space, the time-one map sends the
given knot exactly onto the standard parametrized torus knot. -/
theorem timeOne_image_curve_range
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) :
    Phi.H 1 '' Set.range K.curve = Set.range (standardTorusCurve p q) := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨sigma.f t, (hclass t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := circleReparam_surjective sigma t
    exact ⟨K.curve s, ⟨s, rfl⟩, by rw [hclass s, hs]⟩

/-- Every point of the knot lies on the transported embedded torus. -/
theorem curve_mem_transportedTorus
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (t : ℝ) :
    K.curve t ∈ transportedTorus Phi := by
  exact ⟨torusKnotLift p q (sigma.f t),
    (curve_eq_transportedTorusMap p q K Phi sigma hclass t).symm⟩

theorem curve_range_subset_transportedTorus
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) :
    Set.range K.curve ⊆ transportedTorus Phi := by
  rintro _ ⟨t, rfl⟩
  exact curve_mem_transportedTorus p q K Phi sigma hclass t

end Submission.Torus
