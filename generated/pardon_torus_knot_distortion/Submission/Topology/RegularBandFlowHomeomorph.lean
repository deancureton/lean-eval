import Submission.Topology.RegularBandNormalizedGradientFlow

/-!
# Fixed-time homeomorphisms of the regular-band flow

The normalized-gradient construction produces a complete autonomous flow, but the previous API
retained it only as a continuous family of maps.  Uniqueness of integral curves gives the flow
law, so time `-t` is the inverse of time `t`.  This file packages that fact as homeomorphisms of
the covering plane, the product torus, and the transported torus.

These homeomorphisms are the topological collar maps needed to use height as the transverse
coordinate around a regular cutting circle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

namespace CompletePlaneIntegralFlow

/-- A fixed time of a complete, unique, deck-periodic autonomous flow is a plane
homeomorphism. -/
def timeHomeomorph {v : Plane → Plane}
    (F : CompletePlaneIntegralFlow v) (hv : ContDiff ℝ 1 v)
    (hperiodic : IsPlaneDeckPeriodic v) (t : ℝ) : Plane ≃ₜ Plane where
  toFun x := F.flow x t
  invFun x := F.flow x (-t)
  left_inv x := by
    change F.flow (F.flow x t) (-t) = x
    rw [← F.flow_add hv x t (-t)]
    simp [F.flow_zero]
  right_inv x := by
    change F.flow (F.flow x (-t)) t = x
    rw [← F.flow_add hv x (-t) t]
    simp [F.flow_zero]
  continuous_toFun :=
    (F.continuous_uncurry hv hperiodic).comp (continuous_id.prodMk continuous_const)
  continuous_invFun :=
    (F.continuous_uncurry hv hperiodic).comp (continuous_id.prodMk continuous_const)

@[simp]
theorem timeHomeomorph_apply {v : Plane → Plane}
    (F : CompletePlaneIntegralFlow v) (hv : ContDiff ℝ 1 v)
    (hperiodic : IsPlaneDeckPeriodic v) (t : ℝ) (x : Plane) :
    F.timeHomeomorph hv hperiodic t x = F.flow x t :=
  rfl

@[simp]
theorem timeHomeomorph_symm_apply {v : Plane → Plane}
    (F : CompletePlaneIntegralFlow v) (hv : ContDiff ℝ 1 v)
    (hperiodic : IsPlaneDeckPeriodic v) (t : ℝ) (x : Plane) :
    (F.timeHomeomorph hv hperiodic t).symm x = F.flow x (-t) :=
  rfl

end CompletePlaneIntegralFlow

namespace RegularBandNormalizedGradientFlowData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {B : OrientedCoordinateRegularBandData Phi frame d}

/-- The fixed-time normalized-gradient flow on the universal covering plane. -/
def planeTimeHomeomorph (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) :
    Plane ≃ₜ Plane :=
  G.flow.timeHomeomorph G.fieldData.contDiff_field G.fieldData.isPlaneDeckPeriodic t

@[simp]
theorem planeTimeHomeomorph_apply
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) (uv : Plane) :
    G.planeTimeHomeomorph t uv = G.flow.flow uv t :=
  rfl

/-- Simultaneously flow a plane point by the retained time coordinate.  Keeping time as the
second coordinate makes this a global homeomorphism, with inverse obtained by flowing backward
by that same coordinate. -/
def planeFlowSkewHomeomorph (G : RegularBandNormalizedGradientFlowData B) :
    Plane × ℝ ≃ₜ Plane × ℝ where
  toFun p := (G.flow.flow p.1 p.2, p.2)
  invFun p := (G.flow.flow p.1 (-p.2), p.2)
  left_inv p := by
    apply Prod.ext
    · change G.flow.flow (G.flow.flow p.1 p.2) (-p.2) = p.1
      rw [← G.flow.flow_add G.fieldData.contDiff_field]
      simp [G.flow.flow_zero]
    · rfl
  right_inv p := by
    apply Prod.ext
    · change G.flow.flow (G.flow.flow p.1 (-p.2)) p.2 = p.1
      rw [← G.flow.flow_add G.fieldData.contDiff_field]
      simp [G.flow.flow_zero]
    · rfl
  continuous_toFun :=
    (G.flow.continuous_uncurry G.fieldData.contDiff_field
      G.fieldData.isPlaneDeckPeriodic).prodMk continuous_snd
  continuous_invFun :=
    (G.flow.continuous_uncurry G.fieldData.contDiff_field
      G.fieldData.isPlaneDeckPeriodic).comp
        (continuous_fst.prodMk continuous_snd.neg) |>.prodMk continuous_snd

@[simp]
theorem planeFlowSkewHomeomorph_apply
    (G : RegularBandNormalizedGradientFlowData B) (p : Plane × ℝ) :
    G.planeFlowSkewHomeomorph p = (G.flow.flow p.1 p.2, p.2) :=
  rfl

@[simp]
theorem planeFlowSkewHomeomorph_symm_apply
    (G : RegularBandNormalizedGradientFlowData B) (p : Plane × ℝ) :
    G.planeFlowSkewHomeomorph.symm p = (G.flow.flow p.1 (-p.2), p.2) :=
  rfl

/-- Fixed-time flow on the product torus.  Its inverse is the descended flow at negative time. -/
def quotientTimeHomeomorph (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) :
    Circle × Circle ≃ₜ Circle × Circle where
  toFun := G.quotientFlow t
  invFun := G.quotientFlow (-t)
  left_inv z := by
    obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
    rw [G.quotientFlow_planeExpPair, G.quotientFlow_planeExpPair]
    congr 1
    rw [← G.flow.flow_add G.fieldData.contDiff_field uv t (-t)]
    simp [G.flow.flow_zero]
  right_inv z := by
    obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
    rw [G.quotientFlow_planeExpPair, G.quotientFlow_planeExpPair]
    congr 1
    rw [← G.flow.flow_add G.fieldData.contDiff_field uv (-t) t]
    simp [G.flow.flow_zero]
  continuous_toFun :=
    G.continuous_quotientFlow.comp (continuous_const.prodMk continuous_id)
  continuous_invFun :=
    G.continuous_quotientFlow.comp (continuous_const.prodMk continuous_id)

@[simp]
theorem quotientTimeHomeomorph_apply
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) (z : Circle × Circle) :
    G.quotientTimeHomeomorph t z = G.quotientFlow t z :=
  rfl

@[simp]
theorem quotientTimeHomeomorph_symm_apply
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) (z : Circle × Circle) :
    (G.quotientTimeHomeomorph t).symm z = G.quotientFlow (-t) z :=
  rfl

/-- Fixed-time flow transported to the embedded torus in ambient space. -/
def transportedTimeHomeomorph
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) :
    transportedTorus Phi ≃ₜ transportedTorus Phi :=
  (transportedTorusHomeomorph Phi).symm.trans <|
    (G.quotientTimeHomeomorph t).trans (transportedTorusHomeomorph Phi)

@[simp]
theorem transportedTimeHomeomorph_apply
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) (x : transportedTorus Phi) :
    G.transportedTimeHomeomorph t x = G.transportedFlow t x :=
  rfl

@[simp]
theorem transportedTimeHomeomorph_symm_apply
    (G : RegularBandNormalizedGradientFlowData B) (t : ℝ) (x : transportedTorus Phi) :
    (G.transportedTimeHomeomorph t).symm x = G.transportedFlow (-t) x := by
  rfl

/-! ## Exact height translation from the central level -/

private theorem lipschitzWith_const_mul_heightSpeed
    (G : RegularBandNormalizedGradientFlowData B) (tau : ℝ) :
    ∃ K : NNReal, LipschitzWith K (fun y ↦ tau * G.fieldData.heightSpeed y) := by
  obtain ⟨K, hK⟩ := G.fieldData.exists_lipschitzWith_heightSpeed
  let tauNorm : NNReal := ⟨|tau|, abs_nonneg tau⟩
  refine ⟨tauNorm * K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg tau)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul]
  change |tau * G.fieldData.heightSpeed x - tau * G.fieldData.heightSpeed y| ≤
    (tauNorm : ℝ) * (K : ℝ) * |x - y|
  rw [show (tauNorm : ℝ) = |tau| by rfl, mul_assoc, ← mul_sub, abs_mul]
  simpa [Real.dist_eq] using h

/-- Along an affine height segment starting at the central level and remaining in the regular
band, the scalar speed of the normalized-gradient field is identically one. -/
theorem heightSpeed_center_affine_eq_one
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    {tau r : ℝ} (htau : |tau| ≤ 2 * B.ε) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    G.fieldData.heightSpeed
        (orientedCoordinateLift Phi frame 2 uv + r * tau) = 1 := by
  apply G.fieldData.heightSpeed_eq_one_of_mem_band
  rw [hcenter, add_sub_cancel_left, abs_mul, abs_of_nonneg hr.1]
  exact (mul_le_of_le_one_left (abs_nonneg tau) hr.2).trans htau

/-- A normalized-gradient trajectory starting on the central level changes height exactly by
elapsed time, as long as the displayed time segment remains in the closed regular band. -/
theorem height_planeFlow_mul_eq_add
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    (tau : ℝ) (htau : |tau| ≤ 2 * B.ε)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    orientedCoordinateLift Phi frame 2 (G.flow.flow uv (r * tau)) = d + r * tau := by
  let actual : ℝ → ℝ := fun s ↦
    orientedCoordinateLift Phi frame 2 (G.flow.flow uv (s * tau))
  let affine : ℝ → ℝ := fun s ↦ d + s * tau
  obtain ⟨K, hK⟩ := G.lipschitzWith_const_mul_heightSpeed tau
  have heq : Set.EqOn actual affine (Set.Icc 0 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y ↦ tau * G.fieldData.heightSpeed y)
      (s := fun _ ↦ Set.univ) (K := K)
    · intro _ _
      exact hK.lipschitzOnWith
    · change ContinuousOn actual (Set.Icc 0 1)
      exact ((orientedCoordinateLift_contDiff Phi frame 2).continuous.comp <|
        (G.flow.integral uv).continuous.comp
          (continuous_id.mul continuous_const)).continuousOn
    · intro s _
      exact (G.hasDerivAt_heightAlongPlaneFlow_mul uv tau s).hasDerivWithinAt
    · simp
    · exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    · intro s hs
      have hspeed : G.fieldData.heightSpeed (affine s) = 1 := by
        change G.fieldData.heightSpeed (d + s * tau) = 1
        calc
          G.fieldData.heightSpeed (d + s * tau) =
              G.fieldData.heightSpeed
                (orientedCoordinateLift Phi frame 2 uv + s * tau) := by
            exact congrArg G.fieldData.heightSpeed <|
              congrArg (fun z : ℝ ↦ z + s * tau) hcenter.symm
          _ = 1 := G.heightSpeed_center_affine_eq_one uv hcenter
            (tau := tau) (r := s) htau ⟨hs.1, hs.2.le⟩
      have hderiv : HasDerivAt affine tau s := by
        change HasDerivAt (fun q : ℝ ↦ d + q * tau) tau s
        simpa only [id_eq, one_mul] using
          ((hasDerivAt_id s).mul_const tau).const_add d
      exact (hderiv.congr_deriv (by rw [hspeed, mul_one])).hasDerivWithinAt
    · simp
    · simp [actual, affine, hcenter, G.flow.flow_zero]
  exact heq hr

/-- At full time, a central-level point has height `d + tau`. -/
theorem height_planeFlow_eq_add
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    (tau : ℝ) (htau : |tau| ≤ 2 * B.ε) :
    orientedCoordinateLift Phi frame 2 (G.flow.flow uv tau) = d + tau := by
  simpa using G.height_planeFlow_mul_eq_add uv hcenter tau htau
    (r := 1) (by simp)

end RegularBandNormalizedGradientFlowData

end Submission.Topology
