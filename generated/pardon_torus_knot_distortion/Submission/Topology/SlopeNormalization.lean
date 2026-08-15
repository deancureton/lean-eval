import Submission.Topology.SolidTorus

/-!
# Normalizing arbitrary torus loops to integral affine slopes

A continuous `2π`-periodic circle-valued loop has a continuous real lift.  The
increment of that lift over one period is an integral multiple of `2π`; this
integer is its winding number.  Subtracting the corresponding affine function
leaves a periodic error, so straight-line interpolation gives an explicit
periodic homotopy to an affine winding loop.

Applied coordinatewise, this normalizes an arbitrary product-torus loop to the
linear slope model used by `CompressingDiskWitness`.  The last section records
the exact signed-intersection certificate supplied by a transverse intersection
theorem and proves the elementary consequence that the unsigned determinant is
bounded by the number of intersection parameters.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-- A chosen covering lift of a periodic circle loop, together with its period
increment. -/
structure CircleLoopLift (gamma : ℝ → Circle) where
  angle : ℝ → ℝ
  continuous_angle : Continuous angle
  exp_angle : ∀ t, Circle.exp (angle t) = gamma t
  winding : ℤ
  angle_add_period : ∀ t,
    angle (t + 2 * Real.pi) = angle t + (winding : ℝ) * (2 * Real.pi)

/-- Every continuous periodic circle loop has a real covering lift with an
integral period increment. -/
theorem exists_circleLoopLift (gamma : ℝ → Circle) (hgamma : Continuous gamma)
    (hperiodic : Function.Periodic gamma (2 * Real.pi)) :
    Nonempty (CircleLoopLift gamma) := by
  let gc : C(ℝ, Circle) := ⟨gamma, hgamma⟩
  have hbase : Circle.exp ((gamma 0 : ℂ).arg) = gc 0 := by
    simp [gc, Circle.exp_arg]
  obtain ⟨L, _hL0, hLifts⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℝ) ((gamma 0 : ℂ).arg) hbase |>.exists
  have hLiftAt (t : ℝ) : Circle.exp (L t) = gamma t :=
    congrFun hLifts t
  have hExpPeriod : Circle.exp (L (2 * Real.pi)) = Circle.exp (L 0) := by
    calc
      Circle.exp (L (2 * Real.pi)) = gamma (2 * Real.pi) :=
        hLiftAt (2 * Real.pi)
      _ = gamma 0 := by simpa using hperiodic 0
      _ = Circle.exp (L 0) := (hLiftAt 0).symm
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hExpPeriod
  have hbaseShift : Circle.exp (L (2 * Real.pi)) = gc 0 := by
    calc
      Circle.exp (L (2 * Real.pi)) = gamma (2 * Real.pi) :=
        hLiftAt (2 * Real.pi)
      _ = gamma 0 := by simpa only [zero_add] using hperiodic 0
      _ = gc 0 := rfl
  have hexistsUnique :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℝ) (L (2 * Real.pi)) hbaseShift
  let shifted : C(ℝ, ℝ) :=
    ⟨fun t ↦ L (t + 2 * Real.pi), L.continuous.comp
      (continuous_id.add continuous_const)⟩
  let translated : C(ℝ, ℝ) :=
    ⟨fun t ↦ L t + (n : ℝ) * (2 * Real.pi),
      L.continuous.add continuous_const⟩
  have hshifted : shifted 0 = L (2 * Real.pi) ∧
      Circle.exp ∘ shifted = gc := by
    constructor
    · simp [shifted]
    · funext t
      change Circle.exp (L (t + 2 * Real.pi)) = gamma t
      exact (hLiftAt (t + 2 * Real.pi)).trans (hperiodic t)
  have htranslated : translated 0 = L (2 * Real.pi) ∧
      Circle.exp ∘ translated = gc := by
    constructor
    · change L 0 + (n : ℝ) * (2 * Real.pi) = L (2 * Real.pi)
      exact hn.symm
    · funext t
      change Circle.exp (L t + (n : ℝ) * (2 * Real.pi)) = gamma t
      calc
        Circle.exp (L t + (n : ℝ) * (2 * Real.pi)) = Circle.exp (L t) := by
          apply Circle.exp_eq_exp.mpr
          exact ⟨n, rfl⟩
        _ = gamma t := hLiftAt t
  have hshift : shifted = translated :=
    hexistsUnique.unique hshifted htranslated
  exact ⟨{
    angle := L
    continuous_angle := L.continuous
    exp_angle := fun t ↦ congrFun hLifts t
    winding := n
    angle_add_period := fun t ↦
      congrArg (fun F : C(ℝ, ℝ) ↦ F t) hshift
  }⟩

/-- The winding integer is independent of the chosen covering lift. -/
theorem CircleLoopLift.winding_eq {gamma : ℝ → Circle}
    (L M : CircleLoopLift gamma) : L.winding = M.winding := by
  have hbaseExp : Circle.exp (L.angle 0) = Circle.exp (M.angle 0) := by
    rw [L.exp_angle, M.exp_angle]
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hbaseExp
  have hgamma : Continuous gamma :=
    (Circle.exp.continuous.comp L.continuous_angle).congr L.exp_angle
  let gc : C(ℝ, Circle) :=
    ⟨gamma, hgamma⟩
  have hbase : Circle.exp (L.angle 0) = gc 0 := by
    exact L.exp_angle 0
  have hexistsUnique :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℝ) (L.angle 0) hbase
  let liftL : C(ℝ, ℝ) := ⟨L.angle, L.continuous_angle⟩
  let liftM : C(ℝ, ℝ) :=
    ⟨fun t ↦ M.angle t + (k : ℝ) * (2 * Real.pi),
      M.continuous_angle.add continuous_const⟩
  have hliftL : liftL 0 = L.angle 0 ∧ Circle.exp ∘ liftL = gc := by
    constructor
    · rfl
    · funext t
      exact L.exp_angle t
  have hliftM : liftM 0 = L.angle 0 ∧ Circle.exp ∘ liftM = gc := by
    constructor
    · change M.angle 0 + (k : ℝ) * (2 * Real.pi) = L.angle 0
      exact hk.symm
    · funext t
      change Circle.exp (M.angle t + (k : ℝ) * (2 * Real.pi)) = gamma t
      calc
        Circle.exp (M.angle t + (k : ℝ) * (2 * Real.pi)) =
            Circle.exp (M.angle t) := by
          apply Circle.exp_eq_exp.mpr
          exact ⟨k, rfl⟩
        _ = gamma t := M.exp_angle t
  have hlifts : liftL = liftM := hexistsUnique.unique hliftL hliftM
  have hzero := congrArg (fun F : C(ℝ, ℝ) ↦ F 0) hlifts
  have hperiod := congrArg (fun F : C(ℝ, ℝ) ↦ F (2 * Real.pi)) hlifts
  change L.angle 0 = M.angle 0 + (k : ℝ) * (2 * Real.pi) at hzero
  change L.angle (2 * Real.pi) =
    M.angle (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) at hperiod
  rw [show 2 * Real.pi = 0 + 2 * Real.pi by ring,
    L.angle_add_period, M.angle_add_period] at hperiod
  have hcast : (L.winding : ℝ) = (M.winding : ℝ) := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hcast

/-- The periodic error between a lift and its affine winding representative. -/
def CircleLoopLift.error {gamma : ℝ → Circle} (L : CircleLoopLift gamma)
    (t : ℝ) : ℝ := L.angle t - ((L.winding : ℝ) * t + L.angle 0)

lemma CircleLoopLift.error_periodic {gamma : ℝ → Circle}
    (L : CircleLoopLift gamma) :
    Function.Periodic L.error (2 * Real.pi) := by
  intro t
  unfold CircleLoopLift.error
  rw [L.angle_add_period]
  ring

/-- Straight-line interpolation in the covering coordinate from an arbitrary
lift to its affine winding representative. -/
def CircleLoopLift.normalizationHomotopy {gamma : ℝ → Circle}
    (L : CircleLoopLift gamma) (s t : ℝ) : Circle :=
  Circle.exp ((1 - s) * L.angle t +
    s * ((L.winding : ℝ) * t + L.angle 0))

lemma CircleLoopLift.continuous_normalizationHomotopy
    {gamma : ℝ → Circle} (L : CircleLoopLift gamma) :
    Continuous (Function.uncurry L.normalizationHomotopy) := by
  unfold CircleLoopLift.normalizationHomotopy
  apply Circle.exp.continuous.comp
  exact ((continuous_const.sub continuous_fst).mul
    (L.continuous_angle.comp continuous_snd)).add
      (continuous_fst.mul
        ((continuous_const.mul continuous_snd).add continuous_const))

lemma CircleLoopLift.normalizationHomotopy_zero
    {gamma : ℝ → Circle} (L : CircleLoopLift gamma) (t : ℝ) :
    L.normalizationHomotopy 0 t = gamma t := by
  simp [CircleLoopLift.normalizationHomotopy, L.exp_angle]

lemma CircleLoopLift.normalizationHomotopy_one
    {gamma : ℝ → Circle} (L : CircleLoopLift gamma) (t : ℝ) :
    L.normalizationHomotopy 1 t =
      Circle.exp ((L.winding : ℝ) * t + L.angle 0) := by
  simp [CircleLoopLift.normalizationHomotopy]

lemma CircleLoopLift.normalizationHomotopy_periodic
    {gamma : ℝ → Circle} (L : CircleLoopLift gamma) (s : ℝ) :
    Function.Periodic (L.normalizationHomotopy s) (2 * Real.pi) := by
  intro t
  unfold CircleLoopLift.normalizationHomotopy
  apply Circle.exp_eq_exp.mpr
  refine ⟨L.winding, ?_⟩
  rw [L.angle_add_period]
  ring

/-- Coordinatewise covering data for a periodic loop in the product torus. -/
structure TorusLoopLift (gamma : ℝ → Circle × Circle) where
  first : CircleLoopLift (fun t ↦ (gamma t).1)
  second : CircleLoopLift (fun t ↦ (gamma t).2)

def TorusLoopLift.windingPair {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) : ℤ × ℤ :=
  (L.first.winding, L.second.winding)

theorem TorusLoopLift.windingPair_eq {gamma : ℝ → Circle × Circle}
    (L M : TorusLoopLift gamma) : L.windingPair = M.windingPair := by
  exact Prod.ext (L.first.winding_eq M.first)
    (L.second.winding_eq M.second)

theorem exists_torusLoopLift (gamma : ℝ → Circle × Circle)
    (hgamma : Continuous gamma)
    (hperiodic : Function.Periodic gamma (2 * Real.pi)) :
    Nonempty (TorusLoopLift gamma) := by
  have hfirst : Continuous (fun t ↦ (gamma t).1) := continuous_fst.comp hgamma
  have hsecond : Continuous (fun t ↦ (gamma t).2) := continuous_snd.comp hgamma
  have hpfirst : Function.Periodic (fun t ↦ (gamma t).1) (2 * Real.pi) :=
    fun t ↦ congrArg Prod.fst (hperiodic t)
  have hpsecond : Function.Periodic (fun t ↦ (gamma t).2) (2 * Real.pi) :=
    fun t ↦ congrArg Prod.snd (hperiodic t)
  obtain ⟨L₁⟩ := exists_circleLoopLift _ hfirst hpfirst
  obtain ⟨L₂⟩ := exists_circleLoopLift _ hsecond hpsecond
  exact ⟨⟨L₁, L₂⟩⟩

/-- Real-periodic parametrization of a loop whose domain is bundled as
`Circle`. -/
def circleLoopParam (beta : Circle → Circle × Circle) (t : ℝ) :
    Circle × Circle :=
  beta (Circle.exp t)

lemma continuous_circleLoopParam (beta : Circle → Circle × Circle)
    (hbeta : Continuous beta) : Continuous (circleLoopParam beta) :=
  hbeta.comp Circle.exp.continuous

lemma periodic_circleLoopParam (beta : Circle → Circle × Circle) :
    Function.Periodic (circleLoopParam beta) (2 * Real.pi) := by
  intro t
  unfold circleLoopParam
  congr 1
  apply Circle.exp_eq_exp.mpr
  exact ⟨1, by ring⟩

/-- Every continuous loop on the bundled product torus therefore has a
canonical winding pair, represented by any of its equal-winding lifts. -/
theorem exists_torusLoopLift_of_circleLoop
    (beta : Circle → Circle × Circle) (hbeta : Continuous beta) :
    Nonempty (TorusLoopLift (circleLoopParam beta)) :=
  exists_torusLoopLift _ (continuous_circleLoopParam beta hbeta)
    (periodic_circleLoopParam beta)

/-- Product-circle coordinates of a loop on the transported torus. -/
def transportedLoopCoordinates (Phi : AmbientIsotopy)
    (beta : ℝ → Submission.Torus.transportedTorus Phi) (t : ℝ) :
    Circle × Circle :=
  (Submission.Torus.transportedTorusHomeomorph Phi).symm (beta t)

lemma continuous_transportedLoopCoordinates (Phi : AmbientIsotopy)
    (beta : ℝ → Submission.Torus.transportedTorus Phi)
    (hbeta : Continuous beta) :
    Continuous (transportedLoopCoordinates Phi beta) :=
  (Submission.Torus.transportedTorusHomeomorph Phi).symm.continuous.comp hbeta

lemma periodic_transportedLoopCoordinates (Phi : AmbientIsotopy)
    (beta : ℝ → Submission.Torus.transportedTorus Phi)
    (hperiodic : Function.Periodic beta (2 * Real.pi)) :
    Function.Periodic (transportedLoopCoordinates Phi beta) (2 * Real.pi) := by
  intro t
  unfold transportedLoopCoordinates
  rw [hperiodic]

theorem exists_torusLoopLift_of_transportedLoop (Phi : AmbientIsotopy)
    (beta : ℝ → Submission.Torus.transportedTorus Phi)
    (hbeta : Continuous beta)
    (hperiodic : Function.Periodic beta (2 * Real.pi)) :
    Nonempty (TorusLoopLift (transportedLoopCoordinates Phi beta)) :=
  exists_torusLoopLift _
    (continuous_transportedLoopCoordinates Phi beta hbeta)
    (periodic_transportedLoopCoordinates Phi beta hperiodic)

/-- The coordinatewise normalization homotopy of a product-torus loop. -/
def TorusLoopLift.normalizationHomotopy {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) (s t : ℝ) : Circle × Circle :=
  (L.first.normalizationHomotopy s t,
    L.second.normalizationHomotopy s t)

lemma TorusLoopLift.continuous_normalizationHomotopy
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma) :
    Continuous (Function.uncurry L.normalizationHomotopy) := by
  exact L.first.continuous_normalizationHomotopy.prodMk
    L.second.continuous_normalizationHomotopy

lemma TorusLoopLift.normalizationHomotopy_zero
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma) (t : ℝ) :
    L.normalizationHomotopy 0 t = gamma t := by
  apply Prod.ext
  · exact L.first.normalizationHomotopy_zero t
  · exact L.second.normalizationHomotopy_zero t

lemma TorusLoopLift.normalizationHomotopy_one
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma) (t : ℝ) :
    L.normalizationHomotopy 1 t =
      (Circle.exp ((L.first.winding : ℝ) * t + L.first.angle 0),
        Circle.exp ((L.second.winding : ℝ) * t + L.second.angle 0)) := by
  exact Prod.ext (L.first.normalizationHomotopy_one t)
    (L.second.normalizationHomotopy_one t)

lemma TorusLoopLift.normalizationHomotopy_periodic
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma) (s : ℝ) :
    Function.Periodic (L.normalizationHomotopy s) (2 * Real.pi) := by
  intro t
  exact Prod.ext (L.first.normalizationHomotopy_periodic s t)
    (L.second.normalizationHomotopy_periodic s t)

/-- The normalization homotopy mapped into the transported embedded torus. -/
def TorusLoopLift.transportedNormalizationHomotopy
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    (Phi : AmbientIsotopy) (s t : ℝ) : R3 :=
  Submission.Torus.transportedTorusMap Phi (L.normalizationHomotopy s t)

lemma TorusLoopLift.continuous_transportedNormalizationHomotopy
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    (Phi : AmbientIsotopy) :
    Continuous (Function.uncurry (L.transportedNormalizationHomotopy Phi)) :=
  (Submission.Torus.transportedTorusMap_continuous Phi).comp
    L.continuous_normalizationHomotopy

lemma TorusLoopLift.transportedNormalizationHomotopy_zero
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    (Phi : AmbientIsotopy) (t : ℝ) :
    L.transportedNormalizationHomotopy Phi 0 t =
      Submission.Torus.transportedTorusMap Phi (gamma t) := by
  unfold TorusLoopLift.transportedNormalizationHomotopy
  rw [L.normalizationHomotopy_zero]

/-- The endpoint is literally the integral affine slope loop used by the
compressing-disk interface. -/
lemma TorusLoopLift.transportedNormalizationHomotopy_one
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    (Phi : AmbientIsotopy) (t : ℝ) :
    L.transportedNormalizationHomotopy Phi 1 t =
      transportedSlopeLoop Phi L.first.winding L.second.winding
        (L.first.angle 0) (L.second.angle 0) t := by
  unfold TorusLoopLift.transportedNormalizationHomotopy transportedSlopeLoop
  rw [L.normalizationHomotopy_one]

lemma TorusLoopLift.transportedNormalizationHomotopy_periodic
    {gamma : ℝ → Circle × Circle} (L : TorusLoopLift gamma)
    (Phi : AmbientIsotopy) (s : ℝ) :
    Function.Periodic (L.transportedNormalizationHomotopy Phi s)
      (2 * Real.pi) := by
  intro t
  unfold TorusLoopLift.transportedNormalizationHomotopy
  rw [L.normalizationHomotopy_periodic s]

/-! ## Transverse intersection certificates -/

/-- Parameters in one period at which the `(p,q)` lift meets an arbitrary
periodic product-torus loop. -/
def torusLoopIntersectionParameters (p q : ℕ)
    (gamma : ℝ → Circle × Circle) : Set ℝ :=
  {t | t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
    Submission.Torus.torusKnotLift p q t ∈ Set.range gamma}

/-- The finite signed-count output expected from a transverse intersection
theorem.  It records exactly the geometric input needed below: all intersection
parameters, a local sign of absolute value one, and equality of the signed sum
with the homological determinant. -/
structure TransverseIntersectionCertificate (p q : ℕ)
    (gamma : ℝ → Circle × Circle) (m n : ℤ) where
  parameters : Finset ℝ
  parameters_eq : (parameters : Set ℝ) =
    torusLoopIntersectionParameters p q gamma
  sign : ℝ → ℤ
  sign_natAbs : ∀ t ∈ parameters, (sign t).natAbs = 1
  signed_sum : (∑ t ∈ parameters, sign t) = slopeIntersectionDet p q m n

/-- A signed transverse count immediately bounds the unsigned determinant by
the number of geometric intersection parameters. -/
theorem slopeIntersectionNumber_le_ncard_of_transverseCertificate
    (p q : ℕ) (gamma : ℝ → Circle × Circle) (m n : ℤ)
    (C : TransverseIntersectionCertificate p q gamma m n) :
    slopeIntersectionNumber p q m n ≤
      (torusLoopIntersectionParameters p q gamma).ncard := by
  rw [← C.parameters_eq]
  simp only [Set.ncard_coe_finset]
  rw [slopeIntersectionNumber, ← C.signed_sum]
  calc
    (∑ t ∈ C.parameters, C.sign t).natAbs ≤
        ∑ t ∈ C.parameters, (C.sign t).natAbs :=
      Int.natAbs_sum_le C.parameters C.sign
    _ = C.parameters.card := by
      calc
        ∑ t ∈ C.parameters, (C.sign t).natAbs =
            ∑ _t ∈ C.parameters, 1 := by
          apply Finset.sum_congr rfl
          intro t ht
          exact C.sign_natAbs t ht
        _ = C.parameters.card := by simp

/-- For a primitive coordinate-axis boundary slope, a transverse certificate
therefore supplies at least `min p q` intersection parameters. -/
theorem min_le_intersection_ncard_of_axis_and_transverseCertificate
    (p q : ℕ) (gamma : ℝ → Circle × Circle) (m n : ℤ)
    (haxis : IsPrimitiveAxisSlope m n)
    (C : TransverseIntersectionCertificate p q gamma m n) :
    min p q ≤ (torusLoopIntersectionParameters p q gamma).ncard :=
  (min_le_slopeIntersectionNumber_of_axis p q m n haxis).trans
    (slopeIntersectionNumber_le_ncard_of_transverseCertificate
      p q gamma m n C)

end Submission.PardonDistortion
