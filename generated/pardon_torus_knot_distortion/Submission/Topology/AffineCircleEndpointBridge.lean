import Submission.Topology.CircleIntersectionLocalIFT

/-!
# The explicit affine source fiber of the circle covering

An integral affine slope descends to a genuine map from `Circle`.  This file
identifies the real intersection parameters in an affine source certificate
with the time-zero fiber of the compact two-circle intersection locus.  The
only geometric uniqueness input is injectivity of the bundled affine loop;
primitive axis slopes satisfy this directly.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-- The intrinsic circle parametrization of an integral affine slope. -/
def affineSlopeCircleLoop (m n : ℤ) (phase₁ phase₂ : ℝ)
    (z : Circle) : Circle × Circle :=
  (z ^ m * Circle.exp phase₁, z ^ n * Circle.exp phase₂)

lemma continuous_affineSlopeCircleLoop (m n : ℤ) (phase₁ phase₂ : ℝ) :
    Continuous (affineSlopeCircleLoop m n phase₁ phase₂) := by
  unfold affineSlopeCircleLoop
  fun_prop

theorem affineSlopeCircleLoop_exp (m n : ℤ) (phase₁ phase₂ t : ℝ) :
    affineSlopeCircleLoop m n phase₁ phase₂ (Circle.exp t) =
      affineSlopeLoop m n phase₁ phase₂ t := by
  apply Prod.ext
  · simp only [affineSlopeCircleLoop, affineSlopeLoop]
    rw [← Circle.exp_intCast_mul, Circle.exp_add]
  · simp only [affineSlopeCircleLoop, affineSlopeLoop]
    rw [← Circle.exp_intCast_mul, Circle.exp_add]

lemma affineSlopeCircleLoop_injective_longitude
    (m : ℤ) (hm : m.natAbs = 1) (phase₁ phase₂ : ℝ) :
    Function.Injective (affineSlopeCircleLoop m 0 phase₁ phase₂) := by
  intro z w hzw
  have hfirst := congrArg Prod.fst hzw
  simp only [affineSlopeCircleLoop, zpow_zero, one_mul] at hfirst
  have hmCases : m = 1 ∨ m = -1 := by omega
  rcases hmCases with rfl | rfl
  · simpa using mul_right_cancel hfirst
  · simp only [zpow_neg, zpow_one] at hfirst
    have hinv : z⁻¹ = w⁻¹ := mul_right_cancel hfirst
    exact inv_injective hinv

lemma affineSlopeCircleLoop_injective_meridian
    (n : ℤ) (hn : n.natAbs = 1) (phase₁ phase₂ : ℝ) :
    Function.Injective (affineSlopeCircleLoop 0 n phase₁ phase₂) := by
  intro z w hzw
  have hsecond := congrArg Prod.snd hzw
  simp only [affineSlopeCircleLoop, zpow_zero, one_mul] at hsecond
  have hnCases : n = 1 ∨ n = -1 := by omega
  rcases hnCases with rfl | rfl
  · simpa using mul_right_cancel hsecond
  · simp only [zpow_neg, zpow_one] at hsecond
    have hinv : z⁻¹ = w⁻¹ := mul_right_cancel hsecond
    exact inv_injective hinv

/-- A chosen loop parameter witnessing one certified affine intersection. -/
def affineSourceLoopParameter
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n)
    (x : {t // t ∈ C.parameters}) : Circle :=
  Circle.exp (Classical.choose <|
    ((show x.1 ∈ torusLoopIntersectionParameters p q
        (affineSlopeLoop m n phase₁ phase₂) by
      rw [← C.parameters_eq]
      exact x.2).2))

lemma affineSourceLoopParameter_spec
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n)
    (x : {t // t ∈ C.parameters}) :
    circleTorusKnot p q (Circle.exp x.1) =
      affineSlopeCircleLoop m n phase₁ phase₂
        (affineSourceLoopParameter p q m n phase₁ phase₂ C x) := by
  have hw := Classical.choose_spec <|
    ((show x.1 ∈ torusLoopIntersectionParameters p q
        (affineSlopeLoop m n phase₁ phase₂) by
      rw [← C.parameters_eq]
      exact x.2).2)
  rw [← torusKnotLift_eq_circleTorusKnot_exp]
  unfold affineSourceLoopParameter
  rw [affineSlopeCircleLoop_exp]
  exact hw.symm

def affineSourceFiberPoint
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (H : ℝ → Circle → Circle × Circle)
    (hH0 : H 0 = affineSlopeCircleLoop m n phase₁ phase₂)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n)
    (x : {t // t ∈ C.parameters}) :
    circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)} :=
  ⟨⟨((0 : unitInterval),
      (Circle.exp x.1,
        affineSourceLoopParameter p q m n phase₁ phase₂ C x)), by
    change circleTorusKnot p q (Circle.exp x.1) =
      H 0 (affineSourceLoopParameter p q m n phase₁ phase₂ C x)
    rw [hH0]
    exact affineSourceLoopParameter_spec p q m n phase₁ phase₂ C x⟩, rfl⟩

def affineSourceFiberToParameter
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (H : ℝ → Circle → Circle × Circle)
    (hH0 : H 0 = affineSlopeCircleLoop m n phase₁ phase₂)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n)
    (e : circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)}) : {t // t ∈ C.parameters} :=
  ⟨circlePhaseRepresentative e.1.1.2.1, by
    have htime : e.1.1.1 = (0 : unitInterval) := by
      have he := e.2
      change e.1.1.1 = (0 : unitInterval) at he
      exact he
    have heq := e.1.2
    rw [htime] at heq
    change circleTorusKnot p q e.1.1.2.1 = H 0 e.1.1.2.2 at heq
    rw [hH0] at heq
    have hcircle : e.1.1.2.1 ∈ circleLoopIntersectionParameters p q
        (affineSlopeCircleLoop m n phase₁ phase₂) := by
      exact ⟨e.1.1.2.2, heq.symm⟩
    have hreal := (real_intersectionParameters_iff_circle p q
      (affineSlopeCircleLoop m n phase₁ phase₂) _).2
      ⟨circlePhaseRepresentative_mem _, by
        simpa only [exp_circlePhaseRepresentative] using hcircle⟩
    have hparam : (fun u ↦ affineSlopeCircleLoop m n phase₁ phase₂
        (Circle.exp u)) = affineSlopeLoop m n phase₁ phase₂ := by
      funext u
      exact affineSlopeCircleLoop_exp m n phase₁ phase₂ u
    rw [hparam] at hreal
    show circlePhaseRepresentative e.1.1.2.1 ∈ (C.parameters : Set ℝ)
    rw [C.parameters_eq]
    exact hreal⟩

def affineSourceFiberEquiv
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (H : ℝ → Circle → Circle × Circle)
    (hH0 : H 0 = affineSlopeCircleLoop m n phase₁ phase₂)
    (hbeta : Function.Injective
      (affineSlopeCircleLoop m n phase₁ phase₂))
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n) :
    {t // t ∈ C.parameters} ≃
      (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
        {(0 : unitInterval)}) where
  toFun := affineSourceFiberPoint p q m n phase₁ phase₂ H hH0 C
  invFun := affineSourceFiberToParameter p q m n phase₁ phase₂ H hH0 C
  left_inv x := by
    apply Subtype.ext
    apply circlePhaseRepresentative_exp_of_mem_Ico
    have hx : x.1 ∈ torusLoopIntersectionParameters p q
        (affineSlopeLoop m n phase₁ phase₂) := by
      rw [← C.parameters_eq]
      exact x.2
    exact hx.1
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have htime : e.1.1.1 = (0 : unitInterval) := by
        have he := e.2
        change e.1.1.1 = (0 : unitInterval) at he
        exact he
      exact htime.symm
    · apply Prod.ext
      · exact exp_circlePhaseRepresentative e.1.1.2.1
      · apply hbeta
        change affineSlopeCircleLoop m n phase₁ phase₂
            (affineSourceLoopParameter p q m n phase₁ phase₂ C
              (affineSourceFiberToParameter p q m n phase₁ phase₂ H hH0 C e)) =
          affineSlopeCircleLoop m n phase₁ phase₂ e.1.1.2.2
        have hchosen := affineSourceLoopParameter_spec p q m n phase₁ phase₂ C
          (affineSourceFiberToParameter p q m n phase₁ phase₂ H hH0 C e)
        change circleTorusKnot p q
            (Circle.exp (circlePhaseRepresentative e.1.1.2.1)) =
          affineSlopeCircleLoop m n phase₁ phase₂
            (affineSourceLoopParameter p q m n phase₁ phase₂ C
              (affineSourceFiberToParameter p q m n phase₁ phase₂ H hH0 C e)) at hchosen
        rw [exp_circlePhaseRepresentative] at hchosen
        have heq := e.1.2
        have htime : e.1.1.1 = (0 : unitInterval) := by
          have he := e.2
          change e.1.1.1 = (0 : unitInterval) at he
          exact he
        rw [htime] at heq
        change circleTorusKnot p q e.1.1.2.1 = H 0 e.1.1.2.2 at heq
        rw [hH0] at heq
        exact hchosen.symm.trans heq

/-- Instantiation of the abstract endpoint bridge at an explicit affine
source.  Target-fiber identification remains the natural embedding/uniqueness
input for the arbitrary endpoint loop. -/
def affineCircleEndpointBridge
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop m n phase₁ phase₂)
    (hbeta : Function.Injective
      (affineSlopeCircleLoop m n phase₁ phase₂))
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n)
    (targetFiberEquiv :
      (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
        {(1 : unitInterval)}) ≃
      {z // z ∈ circleLoopIntersectionParameters p q (H 1)}) :
    CircleCoveringEndpointBridge p q H C T where
  homotopy_zero := by
    funext u
    rw [hH0]
    exact affineSlopeCircleLoop_exp m n phase₁ phase₂ u
  sourceFiberEquiv := affineSourceFiberEquiv p q m n phase₁ phase₂
    H hH0 hbeta C
  targetFiberEquiv := targetFiberEquiv

def affineLongitudeCircleEndpointBridge
    (p q : ℕ) (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ : ℝ) (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop m 0 phase₁ phase₂)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m 0 phase₁ phase₂) m 0)
    (targetFiberEquiv :
      (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
        {(1 : unitInterval)}) ≃
      {z // z ∈ circleLoopIntersectionParameters p q (H 1)}) :
    CircleCoveringEndpointBridge p q H C T :=
  affineCircleEndpointBridge p q m 0 phase₁ phase₂ H T hH0
    (affineSlopeCircleLoop_injective_longitude m hm phase₁ phase₂)
    C targetFiberEquiv

def affineMeridianCircleEndpointBridge
    (p q : ℕ) (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ : ℝ) (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop 0 n phase₁ phase₂)
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop 0 n phase₁ phase₂) 0 n)
    (targetFiberEquiv :
      (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
        {(1 : unitInterval)}) ≃
      {z // z ∈ circleLoopIntersectionParameters p q (H 1)}) :
    CircleCoveringEndpointBridge p q H C T :=
  affineCircleEndpointBridge p q 0 n phase₁ phase₂ H T hH0
    (affineSlopeCircleLoop_injective_meridian n hn phase₁ phase₂)
    C targetFiberEquiv

/-! ## Automatic target-fiber identification for an embedded endpoint loop -/

def circleTargetFiberToParameter
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (e : circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)}) :
    {z // z ∈ circleLoopIntersectionParameters p q (H 1)} :=
  ⟨e.1.1.2.1, by
    have htime : e.1.1.1 = (1 : unitInterval) := by
      have he := e.2
      change e.1.1.1 = (1 : unitInterval) at he
      exact he
    have heq := e.1.2
    rw [htime] at heq
    exact ⟨e.1.1.2.2, heq.symm⟩⟩

def circleTargetParameterToFiber
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (z : {z // z ∈ circleLoopIntersectionParameters p q (H 1)}) :
    circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)} :=
  ⟨⟨((1 : unitInterval), (z.1, Classical.choose z.2)), by
    exact (Classical.choose_spec z.2).symm⟩, rfl⟩

def circleTargetFiberEquivOfInjective
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (hinj : Function.Injective (H 1)) :
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)}) ≃
    {z // z ∈ circleLoopIntersectionParameters p q (H 1)} where
  toFun := circleTargetFiberToParameter p q H
  invFun := circleTargetParameterToFiber p q H
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have he := e.2
      change e.1.1.1 = (1 : unitInterval) at he
      exact he.symm
    · apply Prod.ext
      · rfl
      · apply hinj
        have hchosen := Classical.choose_spec
          (circleTargetFiberToParameter p q H e).2
        have htime : e.1.1.1 = (1 : unitInterval) := by
          have he := e.2
          change e.1.1.1 = (1 : unitInterval) at he
          exact he
        have heq := e.1.2
        rw [htime] at heq
        exact hchosen.trans heq
  right_inv z := rfl

/-- Fully explicit affine-to-embedded-loop bridge: both endpoint fiber
equivalences are now constructed, so `targetCertificate` from the preceding
module applies without any further finite-set or seam hypotheses. -/
def affineCircleEndpointBridgeOfInjectiveTarget
    (p q : ℕ) (m n : ℤ) (phase₁ phase₂ : ℝ)
    (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop m n phase₁ phase₂)
    (hsource : Function.Injective
      (affineSlopeCircleLoop m n phase₁ phase₂))
    (htarget : Function.Injective (H 1))
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m n phase₁ phase₂) m n) :
    CircleCoveringEndpointBridge p q H C T :=
  affineCircleEndpointBridge p q m n phase₁ phase₂ H T hH0 hsource C
    (circleTargetFiberEquivOfInjective p q H htarget)

def affineLongitudeTargetCertificate
    (p q : ℕ) (m : ℤ) (hm : m.natAbs = 1)
    (phase₁ phase₂ : ℝ) (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop m 0 phase₁ phase₂)
    (htarget : Function.Injective (H 1))
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop m 0 phase₁ phase₂) m 0) :
    TransverseIntersectionCertificate p q
      (fun u ↦ H 1 (Circle.exp u)) m 0 :=
  (affineCircleEndpointBridgeOfInjectiveTarget p q m 0 phase₁ phase₂
    H T hH0 (affineSlopeCircleLoop_injective_longitude m hm phase₁ phase₂)
    htarget C).targetCertificate

def affineMeridianTargetCertificate
    (p q : ℕ) (n : ℤ) (hn : n.natAbs = 1)
    (phase₁ phase₂ : ℝ) (H : ℝ → Circle → Circle × Circle)
    (T : CircleIntersectionTransversality p q H)
    (hH0 : H 0 = affineSlopeCircleLoop 0 n phase₁ phase₂)
    (htarget : Function.Injective (H 1))
    (C : TransverseIntersectionCertificate p q
      (affineSlopeLoop 0 n phase₁ phase₂) 0 n) :
    TransverseIntersectionCertificate p q
      (fun u ↦ H 1 (Circle.exp u)) 0 n :=
  (affineCircleEndpointBridgeOfInjectiveTarget p q 0 n phase₁ phase₂
    H T hH0 (affineSlopeCircleLoop_injective_meridian n hn phase₁ phase₂)
    htarget C).targetCertificate

end Submission.PardonDistortion
