import Submission.Topology.SlopeNormalization

/-!
# Intersection certificates for affine axis slopes

For the primitive longitude and meridian slopes arising from a compressing
disk, intersection with the `(p,q)` torus knot reduces to a one-dimensional
circle fiber.  This file enumerates that fiber in one half-open period, proves
completeness and distinctness, and assigns constant local signs whose sum is
the slope determinant.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-- An integral affine loop in product-circle coordinates. -/
def affineSlopeLoop (m n : ℤ) (phase₁ phase₂ t : ℝ) : Circle × Circle :=
  (Circle.exp ((m : ℝ) * t + phase₁),
    Circle.exp ((n : ℝ) * t + phase₂))

lemma affineCircle_surjective_of_ne_zero (m : ℤ) (hm : m ≠ 0)
    (phase : ℝ) :
    Function.Surjective (fun t : ℝ ↦ Circle.exp ((m : ℝ) * t + phase)) := by
  intro z
  obtain ⟨u, hu⟩ := Circle.exp_surjective z
  refine ⟨(u - phase) / (m : ℝ), ?_⟩
  change Circle.exp ((m : ℝ) * ((u - phase) / (m : ℝ)) + phase) = z
  rw [show (m : ℝ) * ((u - phase) / (m : ℝ)) + phase = u by
    field_simp [by exact_mod_cast hm]
    ring]
  exact hu

lemma range_affineSlopeLoop_longitude (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ : ℝ) :
    Set.range (affineSlopeLoop m 0 phase₁ phase₂) =
      {z : Circle × Circle | z.2 = Circle.exp phase₂} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp [affineSlopeLoop]
  · intro hz
    have hm0 : m ≠ 0 := by
      intro hm0
      subst m
      simp at hm
    obtain ⟨t, ht⟩ := affineCircle_surjective_of_ne_zero m hm0 phase₁ z.1
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · simpa [affineSlopeLoop] using hz.symm

lemma range_affineSlopeLoop_meridian (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ : ℝ) :
    Set.range (affineSlopeLoop 0 n phase₁ phase₂) =
      {z : Circle × Circle | z.1 = Circle.exp phase₁} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp [affineSlopeLoop]
  · intro hz
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      simp at hn
    obtain ⟨t, ht⟩ := affineCircle_surjective_of_ne_zero n hn0 phase₂ z.2
    refine ⟨t, ?_⟩
    apply Prod.ext
    · simpa [affineSlopeLoop] using hz.symm
    · exact ht

/-- The `k`th solution of `exp (degree * t) = exp theta` in one period,
assuming `theta` itself is chosen in the half-open fundamental interval. -/
def phaseFiberTime (degree : ℕ) (theta : ℝ) (k : Fin degree) : ℝ :=
  (theta + (k : ℝ) * (2 * Real.pi)) / (degree : ℝ)

def phaseFiberParameterSet (degree : ℕ) (theta : ℝ) : Set ℝ :=
  Set.range (phaseFiberTime degree theta)

def phaseFiberFinset (degree : ℕ) (theta : ℝ) : Finset ℝ :=
  Finset.univ.image (phaseFiberTime degree theta)

lemma phaseFiberTime_injective {degree : ℕ} (hdegree : 0 < degree)
    (theta : ℝ) : Function.Injective (phaseFiberTime degree theta) := by
  intro i j hij
  unfold phaseFiberTime at hij
  have hdegreeR : (degree : ℝ) ≠ 0 := by exact_mod_cast hdegree.ne'
  field_simp [hdegreeR] at hij
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hk : (i : ℝ) = (j : ℝ) := by
    apply mul_left_cancel₀ hpi
    linarith
  exact Fin.ext (by exact_mod_cast hk)

lemma phaseFiberTime_mem_Ico {degree : ℕ} (hdegree : 0 < degree)
    {theta : ℝ} (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (k : Fin degree) :
    phaseFiberTime degree theta k ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hdR : 0 < (degree : ℝ) := by exact_mod_cast hdegree
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkd : (k : ℝ) < degree := by exact_mod_cast k.isLt
  constructor
  · unfold phaseFiberTime
    exact div_nonneg (add_nonneg htheta.1 (mul_nonneg hk0 (by positivity))) hdR.le
  · unfold phaseFiberTime
    rw [div_lt_iff₀ hdR]
    have hkSucc : (k : ℝ) + 1 ≤ (degree : ℝ) := by
      exact_mod_cast k.isLt
    have hsum : theta + (k : ℝ) * (2 * Real.pi) <
        ((k : ℝ) + 1) * (2 * Real.pi) := by
      nlinarith [htheta.2]
    calc
      theta + (k : ℝ) * (2 * Real.pi) <
          ((k : ℝ) + 1) * (2 * Real.pi) := hsum
      _ ≤ (degree : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hkSucc (by positivity)
      _ = 2 * Real.pi * (degree : ℝ) := by ring

lemma phaseFiberTime_solution {degree : ℕ} (hdegree : 0 < degree)
    (theta : ℝ) (k : Fin degree) :
    Circle.exp ((degree : ℝ) * phaseFiberTime degree theta k) =
      Circle.exp theta := by
  apply Circle.exp_eq_exp.mpr
  refine ⟨(k : ℤ), ?_⟩
  unfold phaseFiberTime
  have hdR : (degree : ℝ) ≠ 0 := by exact_mod_cast hdegree.ne'
  push_cast
  field_simp [hdR]

lemma phaseFiberTime_complete {degree : ℕ} (hdegree : 0 < degree)
    {theta t : ℝ} (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hsolution : Circle.exp ((degree : ℝ) * t) = Circle.exp theta) :
    t ∈ phaseFiberParameterSet degree theta := by
  obtain ⟨j, hj⟩ := Circle.exp_eq_exp.mp hsolution
  have hdR : 0 < (degree : ℝ) := by exact_mod_cast hdegree
  have hj0 : 0 ≤ j := by
    by_contra hjneg
    have hjle : j ≤ -1 := by omega
    have hjleR : (j : ℝ) ≤ -1 := by exact_mod_cast hjle
    have hmul := mul_le_mul_of_nonneg_right hjleR
      (show 0 ≤ 2 * Real.pi by positivity)
    have hrhs : theta + (j : ℝ) * (2 * Real.pi) < 0 := by
      calc
        theta + (j : ℝ) * (2 * Real.pi) ≤
            theta + (-1 : ℝ) * (2 * Real.pi) := by linarith
        _ < 0 := by nlinarith [htheta.2]
    have hlhs : 0 ≤ (degree : ℝ) * t := mul_nonneg hdR.le ht.1
    linarith
  have hjd : j < degree := by
    by_contra hjge
    have hjge' : (degree : ℤ) ≤ j := by omega
    have hjgeR : (degree : ℝ) ≤ j := by exact_mod_cast hjge'
    have hmul := mul_le_mul_of_nonneg_right hjgeR
      (show 0 ≤ 2 * Real.pi by positivity)
    have htMul := mul_lt_mul_of_pos_left ht.2 hdR
    have hrhs : (degree : ℝ) * (2 * Real.pi) ≤
        theta + (j : ℝ) * (2 * Real.pi) := by
      calc
        (degree : ℝ) * (2 * Real.pi) ≤
            (j : ℝ) * (2 * Real.pi) := hmul
        _ ≤ theta + (j : ℝ) * (2 * Real.pi) := by linarith [htheta.1]
    linarith
  let k : Fin degree := ⟨j.toNat, by omega⟩
  refine ⟨k, ?_⟩
  unfold phaseFiberTime
  have hjCast : (j.toNat : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj0
  rw [hjCast]
  apply (div_eq_iff hdR.ne').2
  linarith

theorem phaseFiberParameterSet_eq_solutionSet {degree : ℕ}
    (hdegree : 0 < degree) {theta : ℝ}
    (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    phaseFiberParameterSet degree theta =
      {t | t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
        Circle.exp ((degree : ℝ) * t) = Circle.exp theta} := by
  ext t
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨phaseFiberTime_mem_Ico hdegree htheta k,
      phaseFiberTime_solution hdegree theta k⟩
  · rintro ⟨ht, hsolution⟩
    exact phaseFiberTime_complete hdegree htheta ht hsolution

lemma coe_phaseFiberFinset {degree : ℕ} (_hdegree : 0 < degree)
    (theta : ℝ) :
    (phaseFiberFinset degree theta : Set ℝ) =
      phaseFiberParameterSet degree theta := by
  ext t
  simp [phaseFiberFinset, phaseFiberParameterSet]

lemma phaseFiberFinset_card {degree : ℕ} (hdegree : 0 < degree)
    (theta : ℝ) : (phaseFiberFinset degree theta).card = degree := by
  rw [phaseFiberFinset, Finset.card_image_iff.mpr]
  · simp
  · exact phaseFiberTime_injective hdegree theta |>.injOn

/-! ## Complete affine axis certificates -/

theorem torusLoopIntersectionParameters_affine_longitude
    (p q : ℕ) (hq : 0 < q) (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ theta : ℝ)
    (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hphase : Circle.exp theta = Circle.exp phase₂) :
    torusLoopIntersectionParameters p q
        (affineSlopeLoop m 0 phase₁ phase₂) =
      phaseFiberParameterSet q theta := by
  rw [phaseFiberParameterSet_eq_solutionSet hq htheta]
  ext t
  simp [torusLoopIntersectionParameters,
    range_affineSlopeLoop_longitude m hm phase₁ phase₂, hphase]

theorem torusLoopIntersectionParameters_affine_meridian
    (p q : ℕ) (hp : 0 < p) (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ theta : ℝ)
    (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hphase : Circle.exp theta = Circle.exp phase₁) :
    torusLoopIntersectionParameters p q
        (affineSlopeLoop 0 n phase₁ phase₂) =
      phaseFiberParameterSet p theta := by
  rw [phaseFiberParameterSet_eq_solutionSet hp htheta]
  ext t
  simp [torusLoopIntersectionParameters,
    range_affineSlopeLoop_meridian n hn phase₁ phase₂, hphase]

/-- Every circle phase has a representative in the chosen half-open period. -/
theorem exists_phaseRepresentative (phase : ℝ) :
    ∃ theta ∈ Ico (0 : ℝ) (2 * Real.pi),
      Circle.exp theta = Circle.exp phase := by
  let z : Circle := Circle.exp phase
  by_cases harg : (z : ℂ).arg < 0
  · refine ⟨(z : ℂ).arg + 2 * Real.pi, ?_, ?_⟩
    · constructor
      · have hlow := Complex.neg_pi_lt_arg (z : ℂ)
        nlinarith [Real.pi_pos]
      · linarith
    · calc
        Circle.exp ((z : ℂ).arg + 2 * Real.pi) =
            Circle.exp ((z : ℂ).arg) := by
          apply Circle.exp_eq_exp.mpr
          exact ⟨1, by ring⟩
        _ = z := Circle.exp_arg z
        _ = Circle.exp phase := rfl
  · refine ⟨(z : ℂ).arg, ⟨le_of_not_gt harg, ?_⟩, ?_⟩
    · have hupp := Complex.arg_le_pi (z : ℂ)
      nlinarith [Real.pi_pos]
    · calc
        Circle.exp ((z : ℂ).arg) = z := Circle.exp_arg z
        _ = Circle.exp phase := rfl

/-- The primitive affine longitude has exactly `q` regular intersection
parameters.  Its local orientation sign is constant `-m`. -/
def affineLongitudeIntersectionCertificate
    (p q : ℕ) (hq : 0 < q) (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ theta : ℝ)
    (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hphase : Circle.exp theta = Circle.exp phase₂) :
    TransverseIntersectionCertificate p q
      (affineSlopeLoop m 0 phase₁ phase₂) m 0 where
  parameters := phaseFiberFinset q theta
  parameters_eq := by
    rw [coe_phaseFiberFinset hq]
    exact (torusLoopIntersectionParameters_affine_longitude
      p q hq m hm phase₁ phase₂ theta htheta hphase).symm
  sign := fun _ ↦ -m
  sign_natAbs := by
    intro _ _
    simpa using hm
  signed_sum := by
    simp [phaseFiberFinset_card hq, slopeIntersectionDet]

/-- The primitive affine meridian has exactly `p` regular intersection
parameters.  Its local orientation sign is constant `n`. -/
def affineMeridianIntersectionCertificate
    (p q : ℕ) (hp : 0 < p) (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ theta : ℝ)
    (htheta : theta ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hphase : Circle.exp theta = Circle.exp phase₁) :
    TransverseIntersectionCertificate p q
      (affineSlopeLoop 0 n phase₁ phase₂) 0 n where
  parameters := phaseFiberFinset p theta
  parameters_eq := by
    rw [coe_phaseFiberFinset hp]
    exact (torusLoopIntersectionParameters_affine_meridian
      p q hp n hn phase₁ phase₂ theta htheta hphase).symm
  sign := fun _ ↦ n
  sign_natAbs := by
    intro _ _
    exact hn
  signed_sum := by
    simp [phaseFiberFinset_card hp, slopeIntersectionDet]

theorem exists_affineLongitudeIntersectionCertificate
    (p q : ℕ) (hq : 0 < q) (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ : ℝ) :
    Nonempty (TransverseIntersectionCertificate p q
      (affineSlopeLoop m 0 phase₁ phase₂) m 0) := by
  obtain ⟨theta, htheta, hphase⟩ := exists_phaseRepresentative phase₂
  exact ⟨affineLongitudeIntersectionCertificate p q hq m hm
    phase₁ phase₂ theta htheta hphase⟩

theorem exists_affineMeridianIntersectionCertificate
    (p q : ℕ) (hp : 0 < p) (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ : ℝ) :
    Nonempty (TransverseIntersectionCertificate p q
      (affineSlopeLoop 0 n phase₁ phase₂) 0 n) := by
  obtain ⟨theta, htheta, hphase⟩ := exists_phaseRepresentative phase₁
  exact ⟨affineMeridianIntersectionCertificate p q hp n hn
    phase₁ phase₂ theta htheta hphase⟩

/-! ## Signed continuation along a regular homotopy -/

/-- Finite continuation data supplied by a regular homotopy.  The equivalence
tracks every intersection parameter, while `sign_preserved` states that the
local orientation cannot change along a regular branch.  These are precisely
the geometric consequences of smooth transversality used in the algebraic
transport theorem below. -/
structure RegularIntersectionContinuation (p q : ℕ)
    (gamma₀ gamma₁ : ℝ → Circle × Circle) (m n : ℤ)
    (C : TransverseIntersectionCertificate p q gamma₀ m n) where
  homotopy : ℝ → ℝ → Circle × Circle
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = gamma₀
  homotopy_one : homotopy 1 = gamma₁
  targetParameters : Finset ℝ
  targetParameters_eq : (targetParameters : Set ℝ) =
    torusLoopIntersectionParameters p q gamma₁
  matching : {t // t ∈ C.parameters} ≃ {t // t ∈ targetParameters}
  targetSign : ℝ → ℤ
  targetSign_natAbs : ∀ t ∈ targetParameters, (targetSign t).natAbs = 1
  sign_preserved : ∀ x : {t // t ∈ C.parameters},
    C.sign x.1 = targetSign (matching x).1

/-- A sign-preserving bijection of regular intersection branches transports a
complete transverse certificate to the other end of the homotopy. -/
def RegularIntersectionContinuation.targetCertificate
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (R : RegularIntersectionContinuation p q gamma₀ gamma₁ m n C) :
    TransverseIntersectionCertificate p q gamma₁ m n where
  parameters := R.targetParameters
  parameters_eq := R.targetParameters_eq
  sign := R.targetSign
  sign_natAbs := R.targetSign_natAbs
  signed_sum := by
    rw [← C.signed_sum]
    symm
    apply Finset.sum_bij
        (fun t ht ↦ (R.matching ⟨t, ht⟩).1)
    · intro t ht
      exact (R.matching ⟨t, ht⟩).2
    · intro t₁ ht₁ t₂ ht₂ heq
      have hsub : R.matching ⟨t₁, ht₁⟩ = R.matching ⟨t₂, ht₂⟩ :=
        Subtype.ext heq
      exact congrArg Subtype.val (R.matching.injective hsub)
    · intro u hu
      let x := R.matching.symm ⟨u, hu⟩
      refine ⟨x.1, x.2, ?_⟩
      exact congrArg Subtype.val (R.matching.apply_symm_apply ⟨u, hu⟩)
    · intro t ht
      exact R.sign_preserved ⟨t, ht⟩

/-- The normalization homotopy itself supplies the topological part of a
regular continuation from an arbitrary lifted loop to its affine endpoint.
The remaining fields are exactly the finite branch-tracking output of a
transversality theorem. -/
def TorusLoopLift.normalizationRegularContinuation
    {p q : ℕ} {gamma : ℝ → Circle × Circle} {m n : ℤ}
    (L : TorusLoopLift gamma)
    (C : TransverseIntersectionCertificate p q gamma m n)
    (targetParameters : Finset ℝ)
    (targetParameters_eq : (targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q (affineSlopeLoop
        L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0)))
    (matching : {t // t ∈ C.parameters} ≃ {t // t ∈ targetParameters})
    (targetSign : ℝ → ℤ)
    (targetSign_natAbs : ∀ t ∈ targetParameters,
      (targetSign t).natAbs = 1)
    (sign_preserved : ∀ x : {t // t ∈ C.parameters},
      C.sign x.1 = targetSign (matching x).1) :
    RegularIntersectionContinuation p q gamma
      (affineSlopeLoop L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0)) m n C where
  homotopy := L.normalizationHomotopy
  continuous_homotopy := L.continuous_normalizationHomotopy
  periodic_homotopy := L.normalizationHomotopy_periodic
  homotopy_zero := funext L.normalizationHomotopy_zero
  homotopy_one := funext L.normalizationHomotopy_one
  targetParameters := targetParameters
  targetParameters_eq := targetParameters_eq
  matching := matching
  targetSign := targetSign
  targetSign_natAbs := targetSign_natAbs
  sign_preserved := sign_preserved

/-- The same normalization, traversed from the explicit affine endpoint back
to the original loop.  Thus an affine certificate yields a certificate for an
arbitrary normalized loop as soon as regular branch continuation and sign
preservation have been supplied. -/
def TorusLoopLift.reverseNormalizationRegularContinuation
    {p q : ℕ} {gamma : ℝ → Circle × Circle} {m n : ℤ}
    (L : TorusLoopLift gamma)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0)) m n)
    (targetParameters : Finset ℝ)
    (targetParameters_eq : (targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q gamma)
    (matching : {t // t ∈ C.parameters} ≃ {t // t ∈ targetParameters})
    (targetSign : ℝ → ℤ)
    (targetSign_natAbs : ∀ t ∈ targetParameters,
      (targetSign t).natAbs = 1)
    (sign_preserved : ∀ x : {t // t ∈ C.parameters},
      C.sign x.1 = targetSign (matching x).1) :
    RegularIntersectionContinuation p q
      (affineSlopeLoop L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0)) gamma m n C where
  homotopy := fun s t ↦ L.normalizationHomotopy (1 - s) t
  continuous_homotopy := by
    have hmap : Continuous (fun z : ℝ × ℝ ↦ (1 - z.1, z.2)) := by fun_prop
    exact L.continuous_normalizationHomotopy.comp hmap
  periodic_homotopy := fun s ↦ L.normalizationHomotopy_periodic (1 - s)
  homotopy_zero := by
    funext t
    simpa only [sub_zero, affineSlopeLoop] using L.normalizationHomotopy_one t
  homotopy_one := by
    funext t
    simpa using L.normalizationHomotopy_zero t
  targetParameters := targetParameters
  targetParameters_eq := targetParameters_eq
  matching := matching
  targetSign := targetSign
  targetSign_natAbs := targetSign_natAbs
  sign_preserved := sign_preserved

def TorusLoopLift.transverseCertificate_of_reverseNormalization
    {p q : ℕ} {gamma : ℝ → Circle × Circle} {m n : ℤ}
    (L : TorusLoopLift gamma)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0)) m n)
    (targetParameters : Finset ℝ)
    (targetParameters_eq : (targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q gamma)
    (matching : {t // t ∈ C.parameters} ≃ {t // t ∈ targetParameters})
    (targetSign : ℝ → ℤ)
    (targetSign_natAbs : ∀ t ∈ targetParameters,
      (targetSign t).natAbs = 1)
    (sign_preserved : ∀ x : {t // t ∈ C.parameters},
      C.sign x.1 = targetSign (matching x).1) :
    TransverseIntersectionCertificate p q gamma m n :=
  (L.reverseNormalizationRegularContinuation C targetParameters
    targetParameters_eq matching targetSign targetSign_natAbs
    sign_preserved).targetCertificate

end Submission.PardonDistortion
