import Submission.Torus.AmbientTransfer

/-!
# An explicit normal tube around the transported torus

The standard torus has major radius `2` and minor radius `1`.  Multiplying its
minor radial vector by `1 + s` therefore gives an explicit normal tube.  On
`|s| < 1 / 2`, both the minor radius and the cylindrical radius stay positive,
so the three tube coordinates are unique.

We first prove embedding on the compact closed tube and then restrict to the
open tube.  Finally, conjugation by the inverse time-one ambient homeomorphism
gives the corresponding tube around the transported torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Torus

/-- Closed normal parameters, used to obtain an embedding by compactness. -/
abbrev StandardTorusClosedNormalTube :=
  (Circle × Circle) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- The open normal tube on which later collar modifications take place. -/
abbrev StandardTorusNormalTube :=
  (Circle × Circle) × Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- Move a standard torus point signed distance `s` in its radial normal
direction. -/
def standardTorusNormalPoint (z w : Circle) (s : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 ↦
    if i.val = 0 then
      (2 + (1 + s) * (w : ℂ).re) * (z : ℂ).re
    else if i.val = 1 then
      (2 + (1 + s) * (w : ℂ).re) * (z : ℂ).im
    else
      (1 + s) * (w : ℂ).im)

@[simp]
theorem standardTorusNormalPoint_coord_zero (z w : Circle) (s : ℝ) :
    standardTorusNormalPoint z w s (0 : Fin 3) =
      (2 + (1 + s) * (w : ℂ).re) * (z : ℂ).re :=
  rfl

@[simp]
theorem standardTorusNormalPoint_coord_one (z w : Circle) (s : ℝ) :
    standardTorusNormalPoint z w s (1 : Fin 3) =
      (2 + (1 + s) * (w : ℂ).re) * (z : ℂ).im :=
  rfl

@[simp]
theorem standardTorusNormalPoint_coord_two (z w : Circle) (s : ℝ) :
    standardTorusNormalPoint z w s (2 : Fin 3) =
      (1 + s) * (w : ℂ).im :=
  rfl

@[simp]
theorem standardTorusNormalPoint_zero (z w : Circle) :
    standardTorusNormalPoint z w 0 = circleTorusMap z w := by
  ext i
  fin_cases i <;> simp [standardTorusNormalPoint, circleTorusMap]

theorem standardTorusNormalPoint_continuous :
    Continuous (fun p : (Circle × Circle) × ℝ ↦
      standardTorusNormalPoint p.1.1 p.1.2 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

private lemma circle_re_ge_neg_one (z : Circle) :
    -1 ≤ (z : ℂ).re := by
  have h := Complex.abs_re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at h
  exact neg_le_of_abs_le h

private lemma circle_re_sq_add_im_sq (z : Circle) :
    (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  simpa [Complex.normSq_apply, pow_two] using
    (show Complex.normSq (z : ℂ) = 1 by simp)

/-- Positive scaling of unit-circle coordinates remembers both the scale and
the circle point.  Keeping this elementary algebra separate prevents the
normal-tube injectivity proof from presenting one large nonlinear context to
the elaborator. -/
private theorem positive_scaled_circle_injective
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z w : Circle}
    (hre : a * (z : ℂ).re = b * (w : ℂ).re)
    (him : a * (z : ℂ).im = b * (w : ℂ).im) :
    a = b ∧ z = w := by
  have hreSq := congrArg (fun x : ℝ => x ^ 2) hre
  have himSq := congrArg (fun x : ℝ => x ^ 2) him
  have habSq : a ^ 2 = b ^ 2 := by
    nlinarith [hreSq, himSq, circle_re_sq_add_im_sq z,
      circle_re_sq_add_im_sq w]
  have hab : a = b := by
    nlinarith
  have hzre : (z : ℂ).re = (w : ℂ).re := by
    apply mul_left_cancel₀ ha.ne'
    calc
      a * (z : ℂ).re = b * (w : ℂ).re := hre
      _ = a * (w : ℂ).re :=
        congrArg (fun r : ℝ ↦ r * (w : ℂ).re) hab.symm
  have hzim : (z : ℂ).im = (w : ℂ).im := by
    apply mul_left_cancel₀ ha.ne'
    calc
      a * (z : ℂ).im = b * (w : ℂ).im := him
      _ = a * (w : ℂ).im :=
        congrArg (fun r : ℝ ↦ r * (w : ℂ).im) hab.symm
  refine ⟨hab, ?_⟩
  apply Subtype.ext
  exact Complex.ext hzre hzim

/-- On the closed half-width tube, the cylindrical radius is positive. -/
private theorem standardTorusNormal_cylindricalRadius_pos
    (w : Circle) {s : ℝ}
    (hs : s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    0 < 2 + (1 + s) * (w : ℂ).re := by
  have hrho : 0 < 1 + s := by linarith [hs.1]
  have hrhoUpper : 1 + s ≤ 3 / 2 := by linarith [hs.2]
  have hwNonneg : 0 ≤ (w : ℂ).re + 1 := by
    linarith [circle_re_ge_neg_one w]
  have hscaled : -(1 + s) ≤ (1 + s) * (w : ℂ).re := by
    nlinarith [mul_nonneg hrho.le hwNonneg]
  linarith

/-- The compact closed normal tube map. -/
def standardTorusClosedNormalTubeMap
    (p : StandardTorusClosedNormalTube) : R3 :=
  standardTorusNormalPoint p.1.1 p.1.2 p.2

theorem standardTorusClosedNormalTubeMap_continuous :
    Continuous standardTorusClosedNormalTubeMap := by
  change Continuous
    ((fun q : (Circle × Circle) × ℝ ↦
        standardTorusNormalPoint q.1.1 q.1.2 q.2) ∘
      fun p : StandardTorusClosedNormalTube ↦ (p.1, (p.2 : ℝ)))
  exact standardTorusNormalPoint_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Positivity of the two radial factors makes all three closed-tube
coordinates recoverable from the ambient point. -/
theorem standardTorusClosedNormalTubeMap_injective :
    Function.Injective standardTorusClosedNormalTubeMap := by
  rintro ⟨⟨z, w⟩, s⟩ ⟨⟨z', w'⟩, s'⟩ h
  have hrho : 0 < 1 + (s : ℝ) := by linarith [s.property.1]
  have hrho' : 0 < 1 + (s' : ℝ) := by linarith [s'.property.1]
  have hradial := standardTorusNormal_cylindricalRadius_pos w s.property
  have hradial' := standardTorusNormal_cylindricalRadius_pos w' s'.property
  have h0 := congrArg (fun x : R3 => x (0 : Fin 3)) h
  have h1 := congrArg (fun x : R3 => x (1 : Fin 3)) h
  have h2 := congrArg (fun x : R3 => x (2 : Fin 3)) h
  simp only [standardTorusClosedNormalTubeMap,
    standardTorusNormalPoint_coord_zero] at h0
  simp only [standardTorusClosedNormalTubeMap,
    standardTorusNormalPoint_coord_one] at h1
  simp only [standardTorusClosedNormalTubeMap,
    standardTorusNormalPoint_coord_two] at h2
  obtain ⟨hradialEq, hz⟩ := positive_scaled_circle_injective
    hradial hradial' h0 h1
  have hre :
      (1 + (s : ℝ)) * (w : ℂ).re =
        (1 + (s' : ℝ)) * (w' : ℂ).re := by
    linarith
  obtain ⟨hrhoEq, hw⟩ := positive_scaled_circle_injective
    hrho hrho' hre h2
  have hsEq : (s : ℝ) = (s' : ℝ) := by linarith
  exact Prod.ext (Prod.ext hz hw) (Subtype.ext hsEq)

theorem standardTorusClosedNormalTubeMap_isClosedEmbedding :
    Topology.IsClosedEmbedding standardTorusClosedNormalTubeMap :=
  standardTorusClosedNormalTubeMap_continuous.isClosedEmbedding
    standardTorusClosedNormalTubeMap_injective

lemma normalTube_open_subset_closed :
    Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩

/-- Inclusion of the working open tube into the compact tube. -/
def standardTorusNormalTubeToClosed :
    StandardTorusNormalTube → StandardTorusClosedNormalTube :=
  Prod.map id (Set.inclusion normalTube_open_subset_closed)

theorem standardTorusNormalTubeToClosed_isEmbedding :
    Topology.IsEmbedding standardTorusNormalTubeToClosed :=
  Topology.IsEmbedding.id.prodMap
    (Topology.IsEmbedding.inclusion normalTube_open_subset_closed)

/-- The standard open normal tube. -/
def standardTorusNormalTubeMap (p : StandardTorusNormalTube) : R3 :=
  standardTorusClosedNormalTubeMap (standardTorusNormalTubeToClosed p)

theorem standardTorusNormalTubeMap_isEmbedding :
    Topology.IsEmbedding standardTorusNormalTubeMap :=
  standardTorusClosedNormalTubeMap_isClosedEmbedding.isEmbedding.comp
    standardTorusNormalTubeToClosed_isEmbedding

/-- The open standard tube, bundled as a homeomorphism onto its range. -/
def standardTorusNormalTubeHomeomorph :
    StandardTorusNormalTube ≃ₜ Set.range standardTorusNormalTubeMap :=
  standardTorusNormalTubeMap_isEmbedding.toHomeomorph

/-- The distinguished zero normal parameter. -/
def standardTorusNormalZero : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  ⟨0, by norm_num⟩

@[simp]
theorem standardTorusNormalTubeMap_zero (z : Circle × Circle) :
    standardTorusNormalTubeMap (z, standardTorusNormalZero) =
      Function.uncurry circleTorusMap z := by
  rcases z with ⟨z, w⟩
  simp [standardTorusNormalTubeMap, standardTorusNormalTubeToClosed,
    standardTorusClosedNormalTubeMap, standardTorusNormalZero]

/-- Conjugate the standard tube by the inverse time-one ambient map. -/
def transportedTorusNormalTubeMap (Phi : AmbientIsotopy)
    (p : StandardTorusNormalTube) : R3 :=
  (ambientHomeomorph Phi 1).symm (standardTorusNormalTubeMap p)

theorem transportedTorusNormalTubeMap_isEmbedding (Phi : AmbientIsotopy) :
    Topology.IsEmbedding (transportedTorusNormalTubeMap Phi) :=
  (ambientHomeomorph Phi 1).symm.isEmbedding.comp
    standardTorusNormalTubeMap_isEmbedding

/-- The transported tube, bundled as a homeomorphism onto its range. -/
def transportedTorusNormalTubeHomeomorph (Phi : AmbientIsotopy) :
    StandardTorusNormalTube ≃ₜ Set.range (transportedTorusNormalTubeMap Phi) :=
  (transportedTorusNormalTubeMap_isEmbedding Phi).toHomeomorph

@[simp]
theorem transportedTorusNormalTubeMap_zero (Phi : AmbientIsotopy)
    (z : Circle × Circle) :
    transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero) =
      transportedTorusMap Phi z := by
  simp [transportedTorusNormalTubeMap, transportedTorusMap]

/-- The zero normal slice is exactly the transported torus. -/
theorem range_transportedTorusNormalTubeMap_zero (Phi : AmbientIsotopy) :
    Set.range (fun z : Circle × Circle ↦
      transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero)) =
      transportedTorus Phi := by
  simp only [transportedTorusNormalTubeMap_zero, transportedTorus]

/-- Inside the normal tube, a point lies on the transported torus exactly
when its signed normal coordinate is zero. -/
theorem transportedTorusNormalTubeMap_mem_transportedTorus_iff
    (Phi : AmbientIsotopy) (p : StandardTorusNormalTube) :
    transportedTorusNormalTubeMap Phi p ∈ transportedTorus Phi ↔
      p.2 = standardTorusNormalZero := by
  constructor
  · rintro ⟨z, hz⟩
    have hmaps : transportedTorusNormalTubeMap Phi p =
        transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero) := by
      rw [transportedTorusNormalTubeMap_zero]
      exact hz.symm
    exact congrArg Prod.snd
      ((transportedTorusNormalTubeMap_isEmbedding Phi).injective hmaps)
  · intro hp
    have hp' : p = (p.1, standardTorusNormalZero) := Prod.ext rfl hp
    rw [hp', transportedTorusNormalTubeMap_zero]
    exact ⟨p.1, rfl⟩

/-- Set-level exactness of the zero slice. -/
theorem preimage_transportedTorusNormalTubeMap_transportedTorus
    (Phi : AmbientIsotopy) :
    transportedTorusNormalTubeMap Phi ⁻¹' transportedTorus Phi =
      {p | p.2 = standardTorusNormalZero} := by
  ext p
  exact transportedTorusNormalTubeMap_mem_transportedTorus_iff Phi p

end Submission.Torus
