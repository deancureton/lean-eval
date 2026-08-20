import Submission.Topology.RegularBandNormalizedGradientFlow
import Submission.Topology.SuperellipsoidSeamRegularBand

/-!
# A normalized tangent field on a regular superellipsoid seam band

The rotated derivative of the outer polynomial is tangent to its level sets.  Applying the
height differential to this rotated field gives the planar differential determinant.  On a
uniformly regular seam band that determinant has a positive squared lower bound on one compact
fundamental square.  A smooth regularized reciprocal therefore normalizes the tangent field so
that its height derivative is exactly one throughout the seam band.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {R d : ℝ}

/-- The closed regular part of one outer seam in a fundamental square. -/
def fundamentalClosedSuperellipsoidSeamBand
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) : Set Plane :=
  fundamentalSquare ∩
    ((superellipsoidPolynomialLift Phi frame c) ⁻¹' {R ^ 256} ∩
      {uv | |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε})

theorem isCompact_fundamentalClosedSuperellipsoidSeamBand
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    IsCompact (fundamentalClosedSuperellipsoidSeamBand B) := by
  apply isCompact_fundamentalSquare.inter_right
  apply (isClosed_singleton.preimage
    (contDiff_superellipsoidPolynomialLift Phi frame c).continuous).inter
  exact isClosed_Iic.preimage <| continuous_abs.comp <|
    (orientedCoordinateLift_contDiff Phi frame 2).continuous.sub continuous_const

/-- The determinant of two `C²` planar functions is `C¹`. -/
theorem contDiff_planarDifferentialDet {f g : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (planarDifferentialDet f g) := by
  have hfderiv : ContDiff ℝ 1
      (fun p : Plane × Plane ↦ fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by norm_num)
  have hgderiv : ContDiff ℝ 1
      (fun p : Plane × Plane ↦ fderiv ℝ g p.1 p.2) :=
    hg.contDiff_fderiv_apply (by norm_num)
  have hffirst : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisFirst) :=
    hfderiv.comp (contDiff_id.prodMk contDiff_const)
  have hfsecond : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisSecond) :=
    hfderiv.comp (contDiff_id.prodMk contDiff_const)
  have hgfirst : ContDiff ℝ 1 (fun x ↦ fderiv ℝ g x planeBasisFirst) :=
    hgderiv.comp (contDiff_id.prodMk contDiff_const)
  have hgsecond : ContDiff ℝ 1 (fun x ↦ fderiv ℝ g x planeBasisSecond) :=
    hgderiv.comp (contDiff_id.prodMk contDiff_const)
  exact (hffirst.mul hgsecond).sub (hfsecond.mul hgfirst)

/-- Compact seam regularity gives a positive lower bound for the squared determinant. -/
theorem exists_pos_le_sq_planarDifferentialDet_on_fundamentalSeamBand
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    ∃ δ > 0, ∀ uv ∈ fundamentalClosedSuperellipsoidSeamBand B,
      δ ≤ (planarDifferentialDet
        (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) uv) ^ 2 := by
  let outer := superellipsoidPolynomialLift Phi frame c
  let height := orientedCoordinateLift Phi frame 2
  let determinant := planarDifferentialDet outer height
  have hcontinuous : Continuous determinant :=
    (contDiff_planarDifferentialDet
      ((contDiff_superellipsoidPolynomialLift Phi frame c).of_le
        (WithTop.coe_le_coe.mpr le_top))
      ((orientedCoordinateLift_contDiff Phi frame 2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous
  apply (isCompact_fundamentalClosedSuperellipsoidSeamBand B).exists_forall_le'
    (hcontinuous.pow 2).continuousOn
  intro uv huv
  have hdet : determinant uv ≠ 0 :=
    B.regular (height uv) huv.2.2 uv huv.2.1 rfl
  exact sq_pos_of_ne_zero hdet

/-- Analytic data for the normalized seam-tangent field. -/
structure SuperellipsoidSeamNormalizedFieldData
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) where
  δ : ℝ
  δ_pos : 0 < δ
  fundamental_lower : ∀ uv ∈ fundamentalClosedSuperellipsoidSeamBand B,
    δ ≤ (planarDifferentialDet
      (superellipsoidPolynomialLift Phi frame c)
      (orientedCoordinateLift Phi frame 2) uv) ^ 2

theorem exists_superellipsoidSeamNormalizedFieldData
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    Nonempty (SuperellipsoidSeamNormalizedFieldData B) := by
  obtain ⟨δ, hδ, hlower⟩ :=
    exists_pos_le_sq_planarDifferentialDet_on_fundamentalSeamBand B
  exact ⟨⟨δ, hδ, hlower⟩⟩

namespace SuperellipsoidSeamNormalizedFieldData

variable {B : SuperellipsoidSeamRegularBandData Phi frame c R d}

/-- The determinant controlling height motion along the outer seam. -/
def determinant (_D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) : ℝ :=
  planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
    (orientedCoordinateLift Phi frame 2) uv

/-- A smooth regularization of the signed reciprocal determinant. -/
def coefficient (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) : ℝ :=
  regularizedGradientReciprocal D.δ (D.determinant uv ^ 2) * D.determinant uv

/-- The normalized field tangent to the outer superellipsoid level. -/
def field (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) : Plane :=
  D.coefficient uv •
    rotatedDerivativeField (superellipsoidPolynomialLift Phi frame c) uv

theorem contDiff_determinant (D : SuperellipsoidSeamNormalizedFieldData B) :
    ContDiff ℝ 1 D.determinant := by
  exact contDiff_planarDifferentialDet
    ((contDiff_superellipsoidPolynomialLift Phi frame c).of_le
      (WithTop.coe_le_coe.mpr le_top))
    ((orientedCoordinateLift_contDiff Phi frame 2).of_le
      (WithTop.coe_le_coe.mpr le_top))

theorem contDiff_coefficient (D : SuperellipsoidSeamNormalizedFieldData B) :
    ContDiff ℝ 1 D.coefficient := by
  exact (((contDiff_regularizedGradientReciprocal D.δ_pos).of_le (by simp)).comp
    (D.contDiff_determinant.pow 2)).mul D.contDiff_determinant

theorem contDiff_field (D : SuperellipsoidSeamNormalizedFieldData B) :
    ContDiff ℝ 1 D.field := by
  exact D.contDiff_coefficient.smul <| contDiff_rotatedDerivativeField <|
    (contDiff_superellipsoidPolynomialLift Phi frame c).of_le
      (WithTop.coe_le_coe.mpr le_top)

/-- Smooth height cutoff equal to one on the working collar and zero outside the regular band. -/
def heightSpeed (_D : SuperellipsoidSeamNormalizedFieldData B) (r : ℝ) : ℝ :=
  Real.smoothTransition
    (((2 * B.ε) ^ 2 - (r - d) ^ 2) / ((2 * B.ε) ^ 2 - B.ε ^ 2))

private theorem heightSpeed_denominator_pos
    (_D : SuperellipsoidSeamNormalizedFieldData B) :
    0 < (2 * B.ε) ^ 2 - B.ε ^ 2 := by
  nlinarith [B.ε_pos]

theorem contDiff_heightSpeed (D : SuperellipsoidSeamNormalizedFieldData B) :
    ContDiff ℝ (⊤ : ℕ∞) D.heightSpeed := by
  unfold heightSpeed
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem heightSpeed_eq_one_of_mem_working_band
    (D : SuperellipsoidSeamNormalizedFieldData B) {r : ℝ}
    (hr : |r - d| ≤ B.ε) : D.heightSpeed r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ D.heightSpeed_denominator_pos]
  have habs : |r - d| ≤ |B.ε| := by
    rwa [abs_of_pos B.ε_pos]
  nlinarith [sq_le_sq.mpr habs]

theorem heightSpeed_eq_zero_of_regular_band_le
    (D : SuperellipsoidSeamNormalizedFieldData B) {r : ℝ}
    (hr : 2 * B.ε ≤ |r - d|) : D.heightSpeed r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr <| sq_le_sq.mpr <| by
      rw [abs_of_nonneg (by linarith [B.ε_pos])]
      exact hr
  · exact D.heightSpeed_denominator_pos.le

theorem abs_lt_regular_band_of_heightSpeed_ne_zero
    (D : SuperellipsoidSeamNormalizedFieldData B) {r : ℝ}
    (hr : D.heightSpeed r ≠ 0) : |r - d| < 2 * B.ε := by
  exact lt_of_not_ge fun h ↦ hr (D.heightSpeed_eq_zero_of_regular_band_le h)

theorem hasCompactSupport_heightSpeed
    (D : SuperellipsoidSeamNormalizedFieldData B) :
    HasCompactSupport D.heightSpeed := by
  let outer := 2 * B.ε
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (d - outer) (d + outer)))
  intro r hr
  have hout : outer ≤ |r - d| := by
    rw [mem_Icc, not_and_or] at hr
    rcases hr with hr | hr
    · rw [abs_of_neg (by linarith [B.ε_pos])]
      linarith
    · rw [abs_of_nonneg (by linarith [B.ε_pos])]
      linarith
  exact D.heightSpeed_eq_zero_of_regular_band_le hout

theorem exists_lipschitzWith_heightSpeed
    (D : SuperellipsoidSeamNormalizedFieldData B) :
    ∃ K : NNReal, LipschitzWith K D.heightSpeed := by
  exact D.contDiff_heightSpeed.lipschitzWith_of_hasCompactSupport
    D.hasCompactSupport_heightSpeed (by simp)

/-- The complete field is cut off before leaving the uniformly regular seam band. -/
def completeField (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) : Plane :=
  D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) • D.field uv

theorem contDiff_completeField (D : SuperellipsoidSeamNormalizedFieldData B) :
    ContDiff ℝ 1 D.completeField := by
  have hheight : ContDiff ℝ 1 (orientedCoordinateLift Phi frame 2) :=
    (orientedCoordinateLift_contDiff Phi frame 2).of_le (by simp)
  exact ((D.contDiff_heightSpeed.of_le (by simp)).comp hheight).smul D.contDiff_field

theorem determinant_add_planeDeckVector
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) (m n : ℤ) :
    D.determinant (uv + planeDeckVector m n) = D.determinant uv := by
  exact planarDifferentialDet_superellipsoid_add_planeDeckVector Phi frame c m n uv

theorem coefficient_add_planeDeckVector
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) (m n : ℤ) :
    D.coefficient (uv + planeDeckVector m n) = D.coefficient uv := by
  simp only [coefficient, D.determinant_add_planeDeckVector]

theorem field_add_planeDeckVector
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) (m n : ℤ) :
    D.field (uv + planeDeckVector m n) = D.field uv := by
  simp only [field, D.coefficient_add_planeDeckVector,
    rotatedDerivativeField, fderiv_superellipsoidPolynomialLift_add_planeDeckVector]

theorem heightSpeed_add_planeDeckVector
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) (m n : ℤ) :
    D.heightSpeed (orientedCoordinateLift Phi frame 2 (uv + planeDeckVector m n)) =
      D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) := by
  rw [orientedCoordinateLift_add_planeDeckVector]

theorem completeField_add_planeDeckVector
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) (m n : ℤ) :
    D.completeField (uv + planeDeckVector m n) = D.completeField uv := by
  simp only [completeField, D.heightSpeed_add_planeDeckVector,
    D.field_add_planeDeckVector]

theorem isPlaneDeckPeriodic (D : SuperellipsoidSeamNormalizedFieldData B) :
    IsPlaneDeckPeriodic D.field :=
  D.field_add_planeDeckVector

theorem completeField_isPlaneDeckPeriodic
    (D : SuperellipsoidSeamNormalizedFieldData B) :
    IsPlaneDeckPeriodic D.completeField :=
  D.completeField_add_planeDeckVector

/-- The compact lower bound propagates to the whole lifted seam by deck periodicity. -/
theorem lower_bound_on_plane_seam_band
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (hband : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    D.δ ≤ D.determinant uv ^ 2 := by
  let representative := planeFundamentalRepresentative uv
  have hrepLevel :
      superellipsoidPolynomialLift Phi frame c representative = R ^ 256 := by
    rw [superellipsoidPolynomialLift_planeFundamentalRepresentative]
    exact hlevel
  have hrepBand :
      |orientedCoordinateLift Phi frame 2 representative - d| ≤ 2 * B.ε := by
    rw [orientedCoordinateLift_planeFundamentalRepresentative]
    exact hband
  have hlower := D.fundamental_lower representative
    ⟨planeFundamentalRepresentative_mem_fundamentalSquare uv, hrepLevel, hrepBand⟩
  calc
    D.δ ≤ D.determinant representative ^ 2 := hlower
    _ = D.determinant uv ^ 2 := by
      rw [← planeFundamentalRepresentative_add_deck uv]
      exact congrArg (fun z : ℝ ↦ z ^ 2) <|
        (D.determinant_add_planeDeckVector representative
          (planeFundamentalDeckIndex uv).1 (planeFundamentalDeckIndex uv).2).symm

/-- The field is tangent to every outer-polynomial level, without a regularity assumption. -/
theorem fderiv_outer_field_eq_zero
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) :
    fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv (D.field uv) = 0 := by
  rw [field, map_smul, fderiv_rotatedDerivativeField]
  simp

theorem fderiv_outer_completeField_eq_zero
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane) :
    fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv
        (D.completeField uv) = 0 := by
  rw [completeField, map_smul, D.fderiv_outer_field_eq_zero]
  simp

/-- On the compact fundamental seam band, the field has unit height derivative. -/
theorem fderiv_height_field_eq_one_of_mem_fundamental
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane)
    (huv : uv ∈ fundamentalClosedSuperellipsoidSeamBand B) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv (D.field uv) = 1 := by
  have hlower : D.δ ≤ D.determinant uv ^ 2 := D.fundamental_lower uv huv
  have hpos : 0 < D.determinant uv ^ 2 := D.δ_pos.trans_le hlower
  have heval : fderiv ℝ (orientedCoordinateLift Phi frame 2) uv
      (rotatedDerivativeField (superellipsoidPolynomialLift Phi frame c) uv) =
        D.determinant uv := by
    rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
    simp only [determinant, planarDifferentialDet, smul_eq_mul]
    ring
  rw [field, map_smul, heval, coefficient,
    regularizedGradientReciprocal_eq_inv D.δ_pos hlower]
  simp only [smul_eq_mul]
  calc
    (D.determinant uv ^ 2)⁻¹ * D.determinant uv * D.determinant uv =
        (D.determinant uv ^ 2)⁻¹ * D.determinant uv ^ 2 := by ring
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- The height derivative is one at every point of the lifted regular seam band. -/
theorem fderiv_height_field_eq_one_of_mem_seam_band
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (hband : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv (D.field uv) = 1 := by
  have hlower : D.δ ≤ D.determinant uv ^ 2 :=
    D.lower_bound_on_plane_seam_band uv hlevel hband
  have hpos : 0 < D.determinant uv ^ 2 := D.δ_pos.trans_le hlower
  have heval : fderiv ℝ (orientedCoordinateLift Phi frame 2) uv
      (rotatedDerivativeField (superellipsoidPolynomialLift Phi frame c) uv) =
        D.determinant uv := by
    rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
    simp only [determinant, planarDifferentialDet, smul_eq_mul]
    ring
  rw [field, map_smul, heval, coefficient,
    regularizedGradientReciprocal_eq_inv D.δ_pos hlower]
  simp only [smul_eq_mul]
  calc
    (D.determinant uv ^ 2)⁻¹ * D.determinant uv * D.determinant uv =
        (D.determinant uv ^ 2)⁻¹ * D.determinant uv ^ 2 := by ring
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- On the outer level, the height derivative of the complete field is its scalar cutoff. -/
theorem fderiv_height_completeField_eq_heightSpeed_of_mem_outer
    (D : SuperellipsoidSeamNormalizedFieldData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv (D.completeField uv) =
      D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) := by
  by_cases hspeed : D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) = 0
  · simp [completeField, hspeed]
  · have hband :
        |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε :=
      (D.abs_lt_regular_band_of_heightSpeed_ne_zero hspeed).le
    rw [completeField, map_smul,
      D.fderiv_height_field_eq_one_of_mem_seam_band uv hlevel hband]
    simp only [smul_eq_mul, mul_one]

end SuperellipsoidSeamNormalizedFieldData

/-- A normalized seam-tangent field together with its unique complete planar flow. -/
def SuperellipsoidSeamNormalizedFlowData
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :=
  Σ D : SuperellipsoidSeamNormalizedFieldData B,
    CompletePlaneIntegralFlow D.completeField

theorem exists_superellipsoidSeamNormalizedFlowData
    (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    Nonempty (SuperellipsoidSeamNormalizedFlowData B) := by
  let D := Classical.choice (exists_superellipsoidSeamNormalizedFieldData B)
  let F := Classical.choice <|
    exists_completePlaneIntegralFlow_of_isPlaneDeckPeriodic
      D.contDiff_completeField D.completeField_isPlaneDeckPeriodic
  exact ⟨⟨D, F⟩⟩

namespace SuperellipsoidSeamNormalizedFlowData

variable {B : SuperellipsoidSeamRegularBandData Phi frame c R d}

theorem hasDerivAt_outerAlongFlow
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane) (t : ℝ) :
    HasDerivAt
      (fun s ↦ superellipsoidPolynomialLift Phi frame c (G.2.flow uv s)) 0 t := by
  have houter : DifferentiableAt ℝ (superellipsoidPolynomialLift Phi frame c)
      (G.2.flow uv t) :=
    (contDiff_superellipsoidPolynomialLift Phi frame c).differentiable
      (by simp) (G.2.flow uv t)
  have hcomp := houter.hasFDerivAt.comp_hasDerivAt t (G.2.integral uv t)
  exact hcomp.congr_deriv (G.1.fderiv_outer_completeField_eq_zero _)

/-- Every complete trajectory stays on its initial outer-polynomial level. -/
theorem outer_planeFlow_eq
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane) (t : ℝ) :
    superellipsoidPolynomialLift Phi frame c (G.2.flow uv t) =
      superellipsoidPolynomialLift Phi frame c uv := by
  let g : ℝ → ℝ := fun s ↦ superellipsoidPolynomialLift Phi frame c (G.2.flow uv s)
  have hgderiv : ∀ s, HasDerivAt g 0 s := G.hasDerivAt_outerAlongFlow uv
  have hgdiff : DifferentiableOn ℝ g Set.univ :=
    fun s _ ↦ (hgderiv s).differentiableAt.differentiableWithinAt
  have hgzero : Set.univ.EqOn (deriv g) 0 := fun s _ ↦ (hgderiv s).deriv
  have hconst := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    hgdiff hgzero (Set.mem_univ t) (Set.mem_univ 0)
  calc
    superellipsoidPolynomialLift Phi frame c (G.2.flow uv t) = g t := rfl
    _ = g 0 := hconst
    _ = superellipsoidPolynomialLift Phi frame c uv := by
      change superellipsoidPolynomialLift Phi frame c (G.2.flow uv 0) = _
      rw [G.2.flow_zero]

theorem hasDerivAt_heightAlongFlow
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256) (t : ℝ) :
    HasDerivAt
      (fun s ↦ orientedCoordinateLift Phi frame 2 (G.2.flow uv s))
      (G.1.heightSpeed (orientedCoordinateLift Phi frame 2 (G.2.flow uv t))) t := by
  have hheight : DifferentiableAt ℝ (orientedCoordinateLift Phi frame 2)
      (G.2.flow uv t) :=
    (orientedCoordinateLift_contDiff Phi frame 2).differentiable
      (by simp) (G.2.flow uv t)
  have hcomp := hheight.hasFDerivAt.comp_hasDerivAt t (G.2.integral uv t)
  exact hcomp.congr_deriv <|
    G.1.fderiv_height_completeField_eq_heightSpeed_of_mem_outer _ <|
      (G.outer_planeFlow_eq uv t).trans hlevel

theorem hasDerivAt_heightAlongFlow_mul
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (tau r : ℝ) :
    HasDerivAt
      (fun s ↦ orientedCoordinateLift Phi frame 2 (G.2.flow uv (s * tau)))
      (tau * G.1.heightSpeed
        (orientedCoordinateLift Phi frame 2 (G.2.flow uv (r * tau)))) r := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s * tau) tau r :=
    by simpa using (hasDerivAt_id r).mul_const tau
  have hcomp := (G.hasDerivAt_heightAlongFlow uv hlevel (r * tau)).comp r hinner
  exact hcomp.congr_deriv (by ring)

private theorem lipschitzWith_const_mul_heightSpeed
    (G : SuperellipsoidSeamNormalizedFlowData B) (tau : ℝ) :
    ∃ K : NNReal, LipschitzWith K (fun y ↦ tau * G.1.heightSpeed y) := by
  obtain ⟨K, hK⟩ := G.1.exists_lipschitzWith_heightSpeed
  let tauNorm : NNReal := ⟨|tau|, abs_nonneg tau⟩
  refine ⟨tauNorm * K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg tau)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul]
  change |tau * G.1.heightSpeed x - tau * G.1.heightSpeed y| ≤
    (tauNorm : ℝ) * (K : ℝ) * |x - y|
  rw [show (tauNorm : ℝ) = |tau| by rfl, mul_assoc, ← mul_sub, abs_mul]
  simpa [Real.dist_eq] using h

theorem heightSpeed_center_affine_eq_one
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    {tau r : ℝ} (htau : |tau| ≤ B.ε) (hr : r ∈ Icc (0 : ℝ) 1) :
    G.1.heightSpeed (orientedCoordinateLift Phi frame 2 uv + r * tau) = 1 := by
  apply G.1.heightSpeed_eq_one_of_mem_working_band
  rw [hcenter, add_sub_cancel_left, abs_mul, abs_of_nonneg hr.1]
  exact (mul_le_of_le_one_left (abs_nonneg tau) hr.2).trans htau

/-- A central seam trajectory translates height exactly throughout the working collar. -/
theorem height_planeFlow_mul_eq_add
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    (tau : ℝ) (htau : |tau| ≤ B.ε) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    orientedCoordinateLift Phi frame 2 (G.2.flow uv (r * tau)) = d + r * tau := by
  let actual : ℝ → ℝ := fun s ↦
    orientedCoordinateLift Phi frame 2 (G.2.flow uv (s * tau))
  let affine : ℝ → ℝ := fun s ↦ d + s * tau
  obtain ⟨K, hK⟩ := G.lipschitzWith_const_mul_heightSpeed tau
  have heq : Set.EqOn actual affine (Icc 0 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y ↦ tau * G.1.heightSpeed y)
      (s := fun _ ↦ Set.univ) (K := K)
    · intro _ _
      exact hK.lipschitzOnWith
    · change ContinuousOn actual (Icc 0 1)
      exact ((orientedCoordinateLift_contDiff Phi frame 2).continuous.comp <|
        (G.2.integral uv).continuous.comp
          (continuous_id.mul continuous_const)).continuousOn
    · intro s _
      exact (G.hasDerivAt_heightAlongFlow_mul uv hlevel tau s).hasDerivWithinAt
    · simp
    · exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    · intro s hs
      have hspeed : G.1.heightSpeed (affine s) = 1 := by
        change G.1.heightSpeed (d + s * tau) = 1
        calc
          G.1.heightSpeed (d + s * tau) =
              G.1.heightSpeed
                (orientedCoordinateLift Phi frame 2 uv + s * tau) := by
            exact congrArg G.1.heightSpeed <|
              congrArg (fun z : ℝ ↦ z + s * tau) hcenter.symm
          _ = 1 := G.heightSpeed_center_affine_eq_one uv hcenter
            (tau := tau) (r := s) htau ⟨hs.1, hs.2.le⟩
      have hderiv : HasDerivAt affine tau s := by
        change HasDerivAt (fun q : ℝ ↦ d + q * tau) tau s
        simpa only [id_eq, one_mul] using
          ((hasDerivAt_id s).mul_const tau).const_add d
      exact (hderiv.congr_deriv (by rw [hspeed, mul_one])).hasDerivWithinAt
    · simp
    · simp [actual, affine, hcenter, G.2.flow_zero]
  exact heq hr

/-- At full collar time, a central seam point has height exactly `d + tau`. -/
theorem height_planeFlow_eq_add
    (G : SuperellipsoidSeamNormalizedFlowData B) (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (hcenter : orientedCoordinateLift Phi frame 2 uv = d)
    (tau : ℝ) (htau : |tau| ≤ B.ε) :
    orientedCoordinateLift Phi frame 2 (G.2.flow uv tau) = d + tau := by
  simpa using G.height_planeFlow_mul_eq_add uv hlevel hcenter tau htau
    (r := 1) (by simp)

end SuperellipsoidSeamNormalizedFlowData

end Submission.Topology
