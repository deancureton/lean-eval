import Submission.Topology.InessentialTorusCircleDisk
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Separation.Hausdorff

/-!
# Replacing a puncture of the transported torus by an inessential disk

The radial map in this file pushes the origin of the covering plane out to the closed unit disk
and is the identity outside a prescribed larger ball.  Conjugating by the ambient Schoenflies
homeomorphism gives the corresponding operation for a lifted zero-winding Jordan disk.

The compact-neighborhood lemma `Set.InjOn.exists_isOpen_superset` is used below to enlarge the
closed Jordan disk while retaining injectivity of the torus covering projection.  This avoids
making any quantitative choice of a fundamental rectangle.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

namespace RadialPuncture

/-- The radial coordinate which pushes zero to radius one and is fixed from radius `R` onward. -/
def radiusPushout (R r : ℝ) : ℝ :=
  if r ≤ R then 1 + (R - 1) * r / R else r

/-- The inverse radial coordinate to `radiusPushout`. -/
def radiusPullback (R s : ℝ) : ℝ :=
  if s ≤ R then R * (s - 1) / (R - 1) else s

theorem radiusPushout_pos {R r : ℝ} (hR : 1 < R) (hr : 0 < r) :
    1 < radiusPushout R r := by
  rw [radiusPushout]
  split_ifs with hrR
  · have hR0 : 0 < R := zero_lt_one.trans hR
    have hR1 : 0 < R - 1 := sub_pos.mpr hR
    have hquot : 0 < (R - 1) * r / R := div_pos (mul_pos hR1 hr) hR0
    linarith
  · exact hR.trans_le (le_of_not_ge hrR)

theorem radiusPullback_pos {R s : ℝ} (hR : 1 < R) (hs : 1 < s) :
    0 < radiusPullback R s := by
  rw [radiusPullback]
  split_ifs with hsR
  · exact div_pos (mul_pos (zero_lt_one.trans hR) (sub_pos.mpr hs)) (sub_pos.mpr hR)
  · exact zero_lt_one.trans hs

theorem radiusPushout_le_R {R r : ℝ} (hR : 1 < R) (_hr0 : 0 < r)
    (hrR : r ≤ R) : radiusPushout R r ≤ R := by
  rw [radiusPushout, if_pos hrR]
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hmul : (R - 1) * r ≤ (R - 1) * R :=
    mul_le_mul_of_nonneg_left hrR (sub_pos.mpr hR).le
  have hdiv : (R - 1) * r / R ≤ R - 1 := by
    rw [div_le_iff₀ hR0]
    exact hmul
  linarith

theorem radiusPullback_le_R {R s : ℝ} (hR : 1 < R) (_hs1 : 1 < s)
    (hsR : s ≤ R) : radiusPullback R s ≤ R := by
  rw [radiusPullback, if_pos hsR]
  have hR1 : 0 < R - 1 := sub_pos.mpr hR
  rw [div_le_iff₀ hR1]
  nlinarith

theorem radiusPullback_pushout {R r : ℝ} (hR : 1 < R) (hr : 0 < r) :
    radiusPullback R (radiusPushout R r) = r := by
  by_cases hrR : r ≤ R
  · have houtR : 1 + (R - 1) * r / R ≤ R := by
      simpa only [radiusPushout, if_pos hrR] using radiusPushout_le_R hR hr hrR
    rw [radiusPushout, if_pos hrR, radiusPullback, if_pos houtR]
    have hR0 : R ≠ 0 := ne_of_gt (zero_lt_one.trans hR)
    have hR1 : R - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hR)
    field_simp
    ring
  · have hRr : R < r := lt_of_not_ge hrR
    rw [radiusPushout, if_neg hrR, radiusPullback, if_neg (not_le.mpr hRr)]

theorem radiusPushout_pullback {R s : ℝ} (hR : 1 < R) (hs : 1 < s) :
    radiusPushout R (radiusPullback R s) = s := by
  by_cases hsR : s ≤ R
  · have hbackR : R * (s - 1) / (R - 1) ≤ R := by
      simpa only [radiusPullback, if_pos hsR] using radiusPullback_le_R hR hs hsR
    rw [radiusPullback, if_pos hsR, radiusPushout, if_pos hbackR]
    have hR0 : R ≠ 0 := ne_of_gt (zero_lt_one.trans hR)
    have hR1 : R - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hR)
    field_simp
    ring
  · have hRs : R < s := lt_of_not_ge hsR
    rw [radiusPullback, if_neg hsR, radiusPushout, if_neg (not_le.mpr hRs)]

theorem continuous_radiusPushout {R : ℝ} (hR : 1 < R) : Continuous (radiusPushout R) := by
  unfold radiusPushout
  apply Continuous.if_le
      (continuous_const.add
        (((continuous_const.sub continuous_const).mul continuous_id).div_const R))
      continuous_id continuous_id continuous_const
  intro r hr
  change r = R at hr
  subst r
  change 1 + (R - 1) * R / R = R
  field_simp [ne_of_gt (zero_lt_one.trans hR)]
  ring

theorem continuous_radiusPullback {R : ℝ} (hR : 1 < R) : Continuous (radiusPullback R) := by
  unfold radiusPullback
  apply Continuous.if_le
      ((continuous_const.mul (continuous_id.sub continuous_const)).div_const (R - 1))
      continuous_id continuous_id continuous_const
  intro r hr
  change r = R at hr
  subst r
  change R * (R - 1) / (R - 1) = R
  field_simp [ne_of_gt (sub_pos.mpr hR)]

/-- The fixed-tail order-preserving homeomorphism from positive radii to radii larger than one. -/
def radiusHomeomorph (R : ℝ) (hR : 1 < R) : Ioi (0 : ℝ) ≃ₜ Ioi (1 : ℝ) where
  toFun r := ⟨radiusPushout R r, radiusPushout_pos hR r.2⟩
  invFun s := ⟨radiusPullback R s, radiusPullback_pos hR s.2⟩
  left_inv r := Subtype.ext (radiusPullback_pushout hR r.2)
  right_inv s := Subtype.ext (radiusPushout_pullback hR s.2)
  continuous_toFun := Continuous.subtype_mk
    ((continuous_radiusPushout hR).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((continuous_radiusPullback hR).comp continuous_subtype_val) _

@[simp]
theorem radiusHomeomorph_coe (R : ℝ) (hR : 1 < R) (r : Ioi (0 : ℝ)) :
    (radiusHomeomorph R hR r : ℝ) = radiusPushout R r :=
  rfl

theorem radiusHomeomorph_apply_of_le {R : ℝ} (hR : 1 < R) (r : Ioi (0 : ℝ))
    (hr : R ≤ r) : (radiusHomeomorph R hR r : ℝ) = r := by
  change radiusPushout R r = r
  rw [radiusPushout]
  split_ifs with hr'
  · have hEq : (r : ℝ) = R := le_antisymm hr' hr
    rw [hEq]
    field_simp [ne_of_gt (zero_lt_one.trans hR)]
    ring
  · rfl

/-- Regard a radius larger than one as a positive radius. -/
def ioiOneToIoiZero : Ioi (1 : ℝ) → Ioi (0 : ℝ) :=
  fun r ↦ ⟨r, by exact zero_lt_one.trans (show 1 < (r : ℝ) from r.2)⟩

theorem continuous_ioiOneToIoiZero : Continuous ioiOneToIoiZero :=
  Continuous.subtype_mk continuous_subtype_val fun r ↦
    zero_lt_one.trans (show 1 < (r : ℝ) from r.2)

/-- `sphere × (1,∞)` as the corresponding subtype of `sphere × (0,∞)`. -/
def sphereIoiOneHomeomorphSubtype :
    sphere (0 : TorusCoveringPlane) 1 × Ioi (1 : ℝ) ≃ₜ
      {z : sphere (0 : TorusCoveringPlane) 1 × Ioi (0 : ℝ) // 1 < (z.2 : ℝ)} where
  toFun z := ⟨(z.1, ioiOneToIoiZero z.2), by exact z.2.2⟩
  invFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (continuous_ioiOneToIoiZero.comp continuous_snd)
  continuous_invFun := by
    exact (continuous_fst.comp continuous_subtype_val).prodMk <|
      Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)
        fun z ↦ z.2

private theorem aboveOne_mem_exterior
    (x : {x : ({0}ᶜ : Set TorusCoveringPlane) // 1 < ‖(x.1 : TorusCoveringPlane)‖}) :
    (x.1 : TorusCoveringPlane) ∈ (closedBall (0 : TorusCoveringPlane) 1)ᶜ := by
  simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using x.2

private theorem exterior_mem_nonzero
    (x : ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane)) :
    (x : TorusCoveringPlane) ∈ ({0}ᶜ : Set TorusCoveringPlane) := by
  intro hx
  have hx0 : (x : TorusCoveringPlane) = 0 := by simpa only [mem_singleton_iff] using hx
  apply x.2
  rw [hx0]
  simp

private theorem exterior_norm_above_one
    (x : ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane)) :
    1 < ‖(x : TorusCoveringPlane)‖ := by
  simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using x.2

/-- The exterior of the closed unit ball, represented as nonzero points of norm larger than one. -/
def nonzeroNormAboveOneHomeomorphExterior :
    {x : ({0}ᶜ : Set TorusCoveringPlane) // 1 < ‖(x.1 : TorusCoveringPlane)‖} ≃ₜ
      ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane) where
  toFun x := ⟨x.1, aboveOne_mem_exterior x⟩
  invFun x := ⟨⟨x, exterior_mem_nonzero x⟩, exterior_norm_above_one x⟩
  left_inv _x := rfl
  right_inv _x := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) aboveOne_mem_exterior
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val exterior_mem_nonzero)
    exterior_norm_above_one

/-- Polar coordinates for the exterior of the closed unit ball. -/
def exteriorPolarHomeomorph :
    sphere (0 : TorusCoveringPlane) 1 × Ioi (1 : ℝ) ≃ₜ
      ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane) :=
  sphereIoiOneHomeomorphSubtype.trans <|
    (((homeomorphUnitSphereProd TorusCoveringPlane).symm.subtype fun z ↦ by
      change 1 < (z.2 : ℝ) ↔
        1 < ‖(((homeomorphUnitSphereProd TorusCoveringPlane).symm z :
          ({0}ᶜ : Set TorusCoveringPlane)) : TorusCoveringPlane)‖
      rw [show ‖(((homeomorphUnitSphereProd TorusCoveringPlane).symm z :
          ({0}ᶜ : Set TorusCoveringPlane)) : TorusCoveringPlane)‖ = (z.2 : ℝ) by
        rw [homeomorphUnitSphereProd_symm_apply_coe,
          norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp z.1.2,
          abs_of_pos z.2.2]
        simp]).trans nonzeroNormAboveOneHomeomorphExterior)

/-- Radially replace the puncture at the origin by the closed unit disk, fixing all radii at
least `R`. -/
def planePunctureToExterior (R : ℝ) (hR : 1 < R) :
    ({0}ᶜ : Set TorusCoveringPlane) ≃ₜ
      ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane) :=
  (homeomorphUnitSphereProd TorusCoveringPlane).trans <|
    ((Homeomorph.refl (sphere (0 : TorusCoveringPlane) 1)).prodCongr
      (radiusHomeomorph R hR) |>.trans exteriorPolarHomeomorph)

theorem planePunctureToExterior_apply_raw (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    planePunctureToExterior R hR x = exteriorPolarHomeomorph
      ((homeomorphUnitSphereProd TorusCoveringPlane x).1,
        radiusHomeomorph R hR (homeomorphUnitSphereProd TorusCoveringPlane x).2) :=
  rfl

theorem exteriorPolarHomeomorph_coe
    (z : sphere (0 : TorusCoveringPlane) 1 × Ioi (1 : ℝ)) :
    (exteriorPolarHomeomorph z : TorusCoveringPlane) =
      ((homeomorphUnitSphereProd TorusCoveringPlane).symm
        (z.1, ioiOneToIoiZero z.2) : TorusCoveringPlane) :=
  rfl

theorem norm_planePunctureToExterior (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    ‖(planePunctureToExterior R hR x : TorusCoveringPlane)‖ =
      radiusPushout R ‖(x : TorusCoveringPlane)‖ := by
  rw [planePunctureToExterior_apply_raw, exteriorPolarHomeomorph_coe]
  change ‖(((homeomorphUnitSphereProd TorusCoveringPlane).symm
      ((homeomorphUnitSphereProd TorusCoveringPlane x).1,
        ioiOneToIoiZero
          (radiusHomeomorph R hR (homeomorphUnitSphereProd TorusCoveringPlane x).2)) :
        ({0}ᶜ : Set TorusCoveringPlane)) : TorusCoveringPlane)‖ = _
  rw [homeomorphUnitSphereProd_symm_apply_coe, norm_smul,
    Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp
      (homeomorphUnitSphereProd TorusCoveringPlane x).1.2,
    abs_of_pos (ioiOneToIoiZero
      (radiusHomeomorph R hR (homeomorphUnitSphereProd TorusCoveringPlane x).2)).2]
  simp only [mul_one, ioiOneToIoiZero, radiusHomeomorph_coe]
  rw [homeomorphUnitSphereProd_apply_snd_coe]

theorem planePunctureToExterior_apply (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    (planePunctureToExterior R hR x : TorusCoveringPlane) =
      (radiusPushout R ‖(x : TorusCoveringPlane)‖ /
        ‖(x : TorusCoveringPlane)‖) • (x : TorusCoveringPlane) := by
  rw [planePunctureToExterior_apply_raw, exteriorPolarHomeomorph_coe]
  change ((homeomorphUnitSphereProd TorusCoveringPlane).symm
      ((homeomorphUnitSphereProd TorusCoveringPlane x).1,
        ioiOneToIoiZero
          (radiusHomeomorph R hR (homeomorphUnitSphereProd TorusCoveringPlane x).2)) :
        TorusCoveringPlane) = _
  rw [homeomorphUnitSphereProd_symm_apply_coe,
    homeomorphUnitSphereProd_apply_fst_coe]
  simp only [ioiOneToIoiZero, radiusHomeomorph_coe]
  rw [homeomorphUnitSphereProd_apply_snd_coe, smul_smul]
  congr 1

theorem planePunctureToExterior_apply_of_le (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane))
    (hx : R ≤ ‖(x : TorusCoveringPlane)‖) :
    (planePunctureToExterior R hR x : TorusCoveringPlane) = x := by
  rw [planePunctureToExterior_apply, radiusPushout]
  split_ifs with hxR
  · have heq : ‖(x : TorusCoveringPlane)‖ = R := le_antisymm hxR hx
    rw [heq]
    have hpush : 1 + (R - 1) * R / R = R := by
      field_simp [ne_of_gt (zero_lt_one.trans hR)]
      ring
    rw [hpush, div_self (ne_of_gt (zero_lt_one.trans hR)), one_smul]
  · rw [div_self (norm_ne_zero_iff.mpr x.2), one_smul]

/-- Linear interpolation from the identity radius to the fixed-tail pushout radius. -/
def radiusDeformation (R : ℝ) (u : Set.Icc (0 : ℝ) 1) (r : ℝ) : ℝ :=
  (1 - u.1) * r + u.1 * radiusPushout R r

theorem radiusDeformation_pos {R r : ℝ} (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (hr : 0 < r) :
    0 < radiusDeformation R u r := by
  by_cases hu : (u : ℝ) = 0
  · simp [radiusDeformation, hu, hr]
  · have hu_pos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu)
    have hleft : 0 ≤ (1 - (u : ℝ)) * r :=
      mul_nonneg (sub_nonneg.mpr u.2.2) hr.le
    have hright : 0 < (u : ℝ) * radiusPushout R r :=
      mul_pos hu_pos (zero_lt_one.trans (radiusPushout_pos hR hr))
    exact add_pos_of_nonneg_of_pos hleft hright

theorem continuous_uncurry_radiusDeformation {R : ℝ} (hR : 1 < R) :
    Continuous (Function.uncurry (radiusDeformation R)) := by
  change Continuous (fun z : Set.Icc (0 : ℝ) 1 × ℝ ↦
    (1 - z.1.1) * z.2 + z.1.1 * radiusPushout R z.2)
  have hu : Continuous (fun z : Set.Icc (0 : ℝ) 1 × ℝ ↦ (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub hu).mul continuous_snd).add <|
    hu.mul ((continuous_radiusPushout hR).comp continuous_snd)

@[simp]
theorem radiusDeformation_zero (R r : ℝ) :
    radiusDeformation R ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ r = r := by
  simp [radiusDeformation]

@[simp]
theorem radiusDeformation_one (R r : ℝ) :
    radiusDeformation R ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ r =
      radiusPushout R r := by
  simp [radiusDeformation]

theorem radiusDeformation_eq_self_of_le {R r : ℝ} (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (hr : R ≤ r) :
    radiusDeformation R u r = r := by
  have hpush : radiusPushout R r = r := by
    simpa only [radiusHomeomorph_coe] using
      radiusHomeomorph_apply_of_le hR ⟨r, (zero_lt_one.trans hR).trans_le hr⟩ hr
  rw [radiusDeformation, hpush]
  ring

theorem radiusDeformation_le {R r : ℝ} (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (hr0 : 0 < r) (hrR : r ≤ R) :
    radiusDeformation R u r ≤ R := by
  have hpushR : radiusPushout R r ≤ R := radiusPushout_le_R hR hr0 hrR
  calc
    radiusDeformation R u r =
        (1 - (u : ℝ)) * r + (u : ℝ) * radiusPushout R r := rfl
    _ ≤ (1 - (u : ℝ)) * R + (u : ℝ) * R :=
      add_le_add
        (mul_le_mul_of_nonneg_left hrR (sub_nonneg.mpr u.2.2))
        (mul_le_mul_of_nonneg_left hpushR u.2.1)
    _ = R := by ring

/-- The radial deformation of the punctured plane.  At time one this is the underlying map of
`planePunctureToExterior`; at every earlier time it still avoids the puncture. -/
def planePunctureDeformation (R : ℝ) (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    ({0}ᶜ : Set TorusCoveringPlane) :=
  ⟨(radiusDeformation R u ‖(x : TorusCoveringPlane)‖ /
      ‖(x : TorusCoveringPlane)‖) • (x : TorusCoveringPlane), by
    have hnorm : 0 < ‖(x : TorusCoveringPlane)‖ := norm_pos_iff.mpr x.2
    have hscale : 0 < radiusDeformation R u ‖(x : TorusCoveringPlane)‖ /
        ‖(x : TorusCoveringPlane)‖ :=
      div_pos (radiusDeformation_pos hR u hnorm) hnorm
    simpa only [mem_compl_iff, mem_singleton_iff] using
      smul_ne_zero (ne_of_gt hscale) x.2⟩

theorem continuous_uncurry_planePunctureDeformation (R : ℝ) (hR : 1 < R) :
    Continuous (Function.uncurry (planePunctureDeformation R hR)) := by
  let n : Set.Icc (0 : ℝ) 1 × ({0}ᶜ : Set TorusCoveringPlane) → ℝ :=
    fun z ↦ ‖(z.2 : TorusCoveringPlane)‖
  have hn : Continuous n :=
    continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
  have hn0 : ∀ z, n z ≠ 0 := fun z ↦ norm_ne_zero_iff.mpr z.2.2
  have hradius : Continuous (fun z ↦ radiusDeformation R z.1 (n z)) :=
    (continuous_uncurry_radiusDeformation hR).comp (continuous_fst.prodMk hn)
  apply Continuous.subtype_mk
  exact (hradius.div hn hn0).smul (continuous_subtype_val.comp continuous_snd)

@[simp]
theorem planePunctureDeformation_zero (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    planePunctureDeformation R hR
      ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x := by
  apply Subtype.ext
  change (radiusDeformation R ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ ‖(x :
    TorusCoveringPlane)‖ / ‖(x : TorusCoveringPlane)‖) •
      (x : TorusCoveringPlane) = (x : TorusCoveringPlane)
  rw [radiusDeformation_zero, div_self (norm_ne_zero_iff.mpr x.2), one_smul]

@[simp]
theorem planePunctureDeformation_one (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    (planePunctureDeformation R hR
      ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x : TorusCoveringPlane) =
        planePunctureToExterior R hR x := by
  change (radiusDeformation R ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩
    ‖(x : TorusCoveringPlane)‖ / ‖(x : TorusCoveringPlane)‖) •
      (x : TorusCoveringPlane) = _
  rw [radiusDeformation_one, planePunctureToExterior_apply]

theorem planePunctureDeformation_apply_of_le (R : ℝ) (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (x : ({0}ᶜ : Set TorusCoveringPlane))
    (hx : R ≤ ‖(x : TorusCoveringPlane)‖) :
    planePunctureDeformation R hR u x = x := by
  apply Subtype.ext
  change (radiusDeformation R u ‖(x : TorusCoveringPlane)‖ /
    ‖(x : TorusCoveringPlane)‖) • (x : TorusCoveringPlane) =
      (x : TorusCoveringPlane)
  rw [radiusDeformation_eq_self_of_le hR u hx,
    div_self (norm_ne_zero_iff.mpr x.2), one_smul]

theorem planePunctureDeformation_mem_closedBall (R : ℝ) (hR : 1 < R)
    (u : Set.Icc (0 : ℝ) 1) (x : ({0}ᶜ : Set TorusCoveringPlane))
    (hx : (x : TorusCoveringPlane) ∈ closedBall (0 : TorusCoveringPlane) R) :
    (planePunctureDeformation R hR u x : TorusCoveringPlane) ∈
      closedBall (0 : TorusCoveringPlane) R := by
  have hnorm : 0 < ‖(x : TorusCoveringPlane)‖ := norm_pos_iff.mpr x.2
  rw [mem_closedBall, dist_zero_right] at hx ⊢
  rw [planePunctureDeformation, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (radiusDeformation_pos hR u hnorm) hnorm),
    div_mul_cancel₀ _ (ne_of_gt hnorm)]
  exact radiusDeformation_le hR u hnorm hx

theorem planePunctureToExterior_mem_closedBall_iff (R : ℝ) (hR : 1 < R)
    (x : ({0}ᶜ : Set TorusCoveringPlane)) :
    (planePunctureToExterior R hR x : TorusCoveringPlane) ∈
        closedBall (0 : TorusCoveringPlane) R ↔
      (x : TorusCoveringPlane) ∈ closedBall (0 : TorusCoveringPlane) R := by
  simp only [mem_closedBall, dist_zero_right, norm_planePunctureToExterior]
  constructor
  · intro hout
    by_contra hin
    have hlt : R < ‖(x : TorusCoveringPlane)‖ := lt_of_not_ge hin
    rw [radiusPushout, if_neg (not_le.mpr hlt)] at hout
    exact (not_le_of_gt hlt) hout
  · intro hin
    exact radiusPushout_le_R hR (norm_pos_iff.mpr x.2) hin

end RadialPuncture

namespace EmbeddedTorusIntersectionCircle

variable {Phi : AmbientIsotopy}

/-- The covering projection with its natural transported-torus codomain. -/
def torusCoveringProjectionToTorus (Phi : AmbientIsotopy)
    (x : TorusCoveringPlane) : transportedTorus Phi :=
  transportedTorusHomeomorph Phi (Circle.exp (x 0), Circle.exp (x 1))

@[simp]
theorem coe_torusCoveringProjectionToTorus (Phi : AmbientIsotopy)
    (x : TorusCoveringPlane) :
    (torusCoveringProjectionToTorus Phi x : R3) = torusCoveringProjection Phi x :=
  rfl

/-- The Euclidean covering plane written as its two real coordinates. -/
def coveringPlaneCoordinates : TorusCoveringPlane ≃ₜ ℝ × ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).trans
    (Homeomorph.piFinTwo (fun _ : Fin 2 ↦ ℝ))

@[simp]
theorem coveringPlaneCoordinates_apply (x : TorusCoveringPlane) :
    coveringPlaneCoordinates x = (x 0, x 1) :=
  rfl

/-- The product of the two real exponential covering maps is a local homeomorphism. -/
theorem isLocalHomeomorph_circleExpProd :
    IsLocalHomeomorph (fun x : ℝ × ℝ ↦ (Circle.exp x.1, Circle.exp x.2)) := by
  intro x
  obtain ⟨e₀, hx₀, he₀⟩ := isLocalHomeomorph_circleExp x.1
  obtain ⟨e₁, hx₁, he₁⟩ := isLocalHomeomorph_circleExp x.2
  refine ⟨e₀.prod e₁, ⟨hx₀, hx₁⟩, ?_⟩
  funext y
  change (Circle.exp y.1, Circle.exp y.2) = (e₀ y.1, e₁ y.2)
  exact Prod.ext (congrFun he₀ y.1) (congrFun he₁ y.2)

/-- The plane-to-transported-torus covering projection is a local homeomorphism. -/
theorem isLocalHomeomorph_torusCoveringProjectionToTorus (Phi : AmbientIsotopy) :
    IsLocalHomeomorph (torusCoveringProjectionToTorus Phi) := by
  have hcoordinates : IsLocalHomeomorph coveringPlaneCoordinates :=
    coveringPlaneCoordinates.isLocalHomeomorph
  have hexp : IsLocalHomeomorph
      (fun x : ℝ × ℝ ↦ (Circle.exp x.1, Circle.exp x.2)) :=
    isLocalHomeomorph_circleExpProd
  have htorus : IsLocalHomeomorph (transportedTorusHomeomorph Phi) :=
    (transportedTorusHomeomorph Phi).isLocalHomeomorph
  have hcomp := htorus.comp (hexp.comp hcoordinates)
  rw [show torusCoveringProjectionToTorus Phi =
      (transportedTorusHomeomorph Phi) ∘
        (fun x : ℝ × ℝ ↦ (Circle.exp x.1, Circle.exp x.2)) ∘
          coveringPlaneCoordinates by
    funext x
    change transportedTorusHomeomorph Phi (Circle.exp (x 0), Circle.exp (x 1)) =
      transportedTorusHomeomorph Phi
        (Circle.exp (coveringPlaneCoordinates x).1,
          Circle.exp (coveringPlaneCoordinates x).2)
    rw [coveringPlaneCoordinates_apply]]
  exact hcomp

/-- The chosen ambient Schoenflies homeomorphism for a zero-winding lifted circle. -/
def zeroWindingAmbientHomeomorph (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    TorusCoveringPlane ≃ₜ TorusCoveringPlane :=
  (C.zeroWindingRegionalExtension hzero).diskExtensionData.ambientHomeomorph

/-- The center of the Schoenflies disk in covering-plane coordinates. -/
def zeroWindingDiskCenter (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : TorusCoveringPlane :=
  (C.zeroWindingAmbientHomeomorph hzero).symm 0

/-- The center projected to the transported torus. -/
def zeroWindingTorusDiskCenter (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : transportedTorus Phi :=
  torusCoveringProjectionToTorus Phi (C.zeroWindingDiskCenter hzero)

/-- The closed lifted Jordan disk. -/
def zeroWindingClosedJordanDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Set TorusCoveringPlane :=
  closure (C.zeroWindingJordanCircle hzero).inside

/-- The chosen ambient Schoenflies homeomorphism carries the closed lifted disk exactly onto the
closed unit ball. -/
theorem zeroWindingAmbientHomeomorph_image_closedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingAmbientHomeomorph hzero '' C.zeroWindingClosedJordanDisk hzero =
      closedBall (0 : TorusCoveringPlane) 1 := by
  let E := C.zeroWindingRegionalExtension hzero
  let D := E.diskExtensionData
  change D.ambientHomeomorph '' closure (C.zeroWindingJordanCircle hzero).inside = _
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    change D.toFun x ∈ closedBall (0 : TorusCoveringPlane) 1
    simpa [Schoenflies.DiskExtensionData.toFun, hx] using D.maps_inside hx
  · intro y hy
    refine ⟨D.ambientHomeomorph.symm y, ?_, D.ambientHomeomorph.apply_symm_apply y⟩
    change D.invFun y ∈ closure (C.zeroWindingJordanCircle hzero).inside
    simpa [Schoenflies.DiskExtensionData.invFun, hy] using D.inv_maps_inside hy

theorem zeroWindingAmbientHomeomorph_mem_closedBall_iff
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (x : TorusCoveringPlane) :
    C.zeroWindingAmbientHomeomorph hzero x ∈ closedBall (0 : TorusCoveringPlane) 1 ↔
      x ∈ C.zeroWindingClosedJordanDisk hzero := by
  let e := C.zeroWindingAmbientHomeomorph hzero
  constructor
  · intro hx
    rw [← C.zeroWindingAmbientHomeomorph_image_closedJordanDisk hzero] at hx
    obtain ⟨y, hy, hey⟩ := hx
    have hyx : y = x := e.injective hey
    exact hyx ▸ hy
  · intro hx
    rw [← C.zeroWindingAmbientHomeomorph_image_closedJordanDisk hzero]
    exact ⟨x, hx, rfl⟩

/-- The lifted punctured plane, centered at the Schoenflies center. -/
def zeroWindingPlanePuncture (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Set TorusCoveringPlane :=
  {C.zeroWindingDiskCenter hzero}ᶜ

/-- The complement of the lifted closed Jordan disk. -/
def zeroWindingPlaneDiskComplement (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Set TorusCoveringPlane :=
  (C.zeroWindingClosedJordanDisk hzero)ᶜ

/-- The closed support obtained by pulling a round ball back through Schoenflies. -/
def zeroWindingSchoenfliesSupport (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    Set TorusCoveringPlane :=
  (C.zeroWindingAmbientHomeomorph hzero).symm ''
    closedBall (0 : TorusCoveringPlane) R

/-- The open radial support with the same boundary as `zeroWindingSchoenfliesSupport`. -/
def zeroWindingSchoenfliesOpenSupport (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    Set TorusCoveringPlane :=
  (C.zeroWindingAmbientHomeomorph hzero).symm ''
    ball (0 : TorusCoveringPlane) R

theorem isOpen_zeroWindingSchoenfliesOpenSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    IsOpen (C.zeroWindingSchoenfliesOpenSupport hzero R) :=
  (C.zeroWindingAmbientHomeomorph hzero).symm.isOpenMap _ isOpen_ball

theorem mem_zeroWindingSchoenfliesOpenSupport_iff
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ)
    (x : TorusCoveringPlane) :
    x ∈ C.zeroWindingSchoenfliesOpenSupport hzero R ↔
      C.zeroWindingAmbientHomeomorph hzero x ∈
        ball (0 : TorusCoveringPlane) R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨C.zeroWindingAmbientHomeomorph hzero x, hx,
      (C.zeroWindingAmbientHomeomorph hzero).symm_apply_apply x⟩

theorem zeroWindingSchoenfliesOpenSupport_subset_support
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    C.zeroWindingSchoenfliesOpenSupport hzero R ⊆
      C.zeroWindingSchoenfliesSupport hzero R :=
  image_mono ball_subset_closedBall

theorem mem_zeroWindingSchoenfliesSupport_iff
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ)
    (x : TorusCoveringPlane) :
    x ∈ C.zeroWindingSchoenfliesSupport hzero R ↔
      C.zeroWindingAmbientHomeomorph hzero x ∈
        closedBall (0 : TorusCoveringPlane) R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨C.zeroWindingAmbientHomeomorph hzero x, hx,
      (C.zeroWindingAmbientHomeomorph hzero).symm_apply_apply x⟩

theorem isCompact_zeroWindingSchoenfliesSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    IsCompact (C.zeroWindingSchoenfliesSupport hzero R) :=
  (isCompact_closedBall (0 : TorusCoveringPlane) R).image
    (C.zeroWindingAmbientHomeomorph hzero).symm.continuous

/-- The Schoenflies center belongs to the closed lifted Jordan disk. -/
theorem zeroWindingDiskCenter_mem_closedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingDiskCenter hzero ∈ C.zeroWindingClosedJordanDisk hzero := by
  rw [← C.zeroWindingAmbientHomeomorph_mem_closedBall_iff hzero]
  simp [zeroWindingDiskCenter]

/-- Every radius at least one contains the Schoenflies center. -/
theorem zeroWindingDiskCenter_mem_schoenfliesSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) {R : ℝ} (hR : 1 ≤ R) :
    C.zeroWindingDiskCenter hzero ∈ C.zeroWindingSchoenfliesSupport hzero R := by
  rw [C.mem_zeroWindingSchoenfliesSupport_iff]
  simpa [zeroWindingDiskCenter] using (show (0 : ℝ) ≤ R by linarith)

/-- A radial support of radius at least one contains the entire lifted closed Jordan disk. -/
theorem zeroWindingClosedJordanDisk_subset_schoenfliesSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) {R : ℝ} (hR : 1 ≤ R) :
    C.zeroWindingClosedJordanDisk hzero ⊆
      C.zeroWindingSchoenfliesSupport hzero R := by
  intro x hx
  rw [C.mem_zeroWindingSchoenfliesSupport_iff, mem_closedBall, dist_zero_right]
  have hxball := (C.zeroWindingAmbientHomeomorph_mem_closedBall_iff hzero x).2 hx
  have hxnorm : ‖C.zeroWindingAmbientHomeomorph hzero x‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using hxball
  exact hxnorm.trans hR

/-- Schoenflies coordinates identify the chosen puncture with the origin puncture. -/
def zeroWindingPlanePunctureToOrigin
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingPlanePuncture hzero ≃ₜ ({0}ᶜ : Set TorusCoveringPlane) :=
  (C.zeroWindingAmbientHomeomorph hzero).subtype fun x ↦ by
    change x ≠ (C.zeroWindingAmbientHomeomorph hzero).symm 0 ↔
      C.zeroWindingAmbientHomeomorph hzero x ≠ 0
    constructor
    · intro hx he0
      apply hx
      apply (C.zeroWindingAmbientHomeomorph hzero).injective
      simpa using he0
    · intro hex hx
      apply hex
      simp [hx]

/-- Conjugate the radial puncture deformation by the ambient Schoenflies homeomorphism. -/
def zeroWindingPlanePunctureDeformation
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (u : Set.Icc (0 : ℝ) 1) :
    C.zeroWindingPlanePuncture hzero → C.zeroWindingPlanePuncture hzero :=
  fun x ↦ (C.zeroWindingPlanePunctureToOrigin hzero).symm
    (RadialPuncture.planePunctureDeformation R hR u
      (C.zeroWindingPlanePunctureToOrigin hzero x))

theorem zeroWindingAmbientHomeomorph_planePunctureDeformation
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (u : Set.Icc (0 : ℝ) 1)
    (x : C.zeroWindingPlanePuncture hzero) :
    C.zeroWindingAmbientHomeomorph hzero
        (C.zeroWindingPlanePunctureDeformation hzero R hR u x) =
      RadialPuncture.planePunctureDeformation R hR u
        (C.zeroWindingPlanePunctureToOrigin hzero x) := by
  exact congrArg Subtype.val <|
    (C.zeroWindingPlanePunctureToOrigin hzero).apply_symm_apply _

theorem continuous_uncurry_zeroWindingPlanePunctureDeformation
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) :
    Continuous (Function.uncurry
      (C.zeroWindingPlanePunctureDeformation hzero R hR)) := by
  exact (C.zeroWindingPlanePunctureToOrigin hzero).symm.continuous.comp <|
    (RadialPuncture.continuous_uncurry_planePunctureDeformation R hR).comp <|
      continuous_fst.prodMk <|
        (C.zeroWindingPlanePunctureToOrigin hzero).continuous.comp continuous_snd

@[simp]
theorem zeroWindingPlanePunctureDeformation_zero
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (x : C.zeroWindingPlanePuncture hzero) :
    C.zeroWindingPlanePunctureDeformation hzero R hR
      ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x := by
  unfold zeroWindingPlanePunctureDeformation
  rw [RadialPuncture.planePunctureDeformation_zero,
    (C.zeroWindingPlanePunctureToOrigin hzero).symm_apply_apply]

theorem zeroWindingPlanePunctureDeformation_apply_of_outside_support
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (u : Set.Icc (0 : ℝ) 1)
    (x : C.zeroWindingPlanePuncture hzero)
    (hx : (x : TorusCoveringPlane) ∉ C.zeroWindingSchoenfliesSupport hzero R) :
    C.zeroWindingPlanePunctureDeformation hzero R hR u x = x := by
  have hxR : R ≤ ‖C.zeroWindingAmbientHomeomorph hzero x‖ := by
    rw [C.mem_zeroWindingSchoenfliesSupport_iff, mem_closedBall,
      dist_zero_right, not_le] at hx
    exact hx.le
  apply (C.zeroWindingPlanePunctureToOrigin hzero).injective
  simp only [zeroWindingPlanePunctureDeformation,
    Homeomorph.apply_symm_apply, zeroWindingPlanePunctureToOrigin]
  exact RadialPuncture.planePunctureDeformation_apply_of_le R hR _ _ hxR

theorem zeroWindingPlanePunctureDeformation_apply_of_radius_le
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (u : Set.Icc (0 : ℝ) 1)
    (x : C.zeroWindingPlanePuncture hzero)
    (hx : R ≤ ‖C.zeroWindingAmbientHomeomorph hzero x‖) :
    C.zeroWindingPlanePunctureDeformation hzero R hR u x = x := by
  apply (C.zeroWindingPlanePunctureToOrigin hzero).injective
  simp only [zeroWindingPlanePunctureDeformation,
    Homeomorph.apply_symm_apply, zeroWindingPlanePunctureToOrigin]
  exact RadialPuncture.planePunctureDeformation_apply_of_le R hR _ _ hx

theorem zeroWindingPlanePunctureDeformation_apply_of_not_mem_openSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (u : Set.Icc (0 : ℝ) 1)
    (x : C.zeroWindingPlanePuncture hzero)
    (hx : (x : TorusCoveringPlane) ∉ C.zeroWindingSchoenfliesOpenSupport hzero R) :
    C.zeroWindingPlanePunctureDeformation hzero R hR u x = x := by
  apply C.zeroWindingPlanePunctureDeformation_apply_of_radius_le hzero R hR u x
  rw [C.mem_zeroWindingSchoenfliesOpenSupport_iff,
    mem_ball, dist_zero_right, not_lt] at hx
  exact hx

/-- Conjugate the fixed-tail radial pushout by Schoenflies.  It replaces the chosen lifted center
by the entire closed lifted Jordan disk. -/
def zeroWindingPlanePunctureToDiskComplement
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) :
    C.zeroWindingPlanePuncture hzero ≃ₜ C.zeroWindingPlaneDiskComplement hzero := by
  let e := C.zeroWindingAmbientHomeomorph hzero
  let sourceToZero : C.zeroWindingPlanePuncture hzero ≃ₜ
      ({0}ᶜ : Set TorusCoveringPlane) :=
    e.subtype fun x ↦ by
      change x ≠ e.symm 0 ↔ e x ≠ 0
      constructor
      · intro hx he0
        apply hx
        apply e.injective
        simpa using he0
      · intro hex hx
        apply hex
        simp [hx]
  let exteriorToTarget :
      ((closedBall (0 : TorusCoveringPlane) 1)ᶜ : Set TorusCoveringPlane) ≃ₜ
        C.zeroWindingPlaneDiskComplement hzero :=
    e.symm.subtype fun y ↦ by
      dsimp only [e]
      change y ∉ closedBall (0 : TorusCoveringPlane) 1 ↔
        (C.zeroWindingAmbientHomeomorph hzero).symm y ∉
          C.zeroWindingClosedJordanDisk hzero
      have hmem := not_congr
        (C.zeroWindingAmbientHomeomorph_mem_closedBall_iff hzero
          ((C.zeroWindingAmbientHomeomorph hzero).symm y))
      simpa only [Homeomorph.apply_symm_apply] using hmem
  exact sourceToZero.trans <|
    (RadialPuncture.planePunctureToExterior R hR).trans exteriorToTarget

theorem zeroWindingPlanePunctureDeformation_one
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (x : C.zeroWindingPlanePuncture hzero) :
    (C.zeroWindingPlanePunctureDeformation hzero R hR
      ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x : TorusCoveringPlane) =
        C.zeroWindingPlanePunctureToDiskComplement hzero R hR x := by
  simp only [zeroWindingPlanePunctureDeformation,
    zeroWindingPlanePunctureToOrigin, zeroWindingPlanePunctureToDiskComplement,
    Homeomorph.trans_apply]
  change (C.zeroWindingAmbientHomeomorph hzero).symm
      (RadialPuncture.planePunctureDeformation R hR
        ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ _) =
    (C.zeroWindingAmbientHomeomorph hzero).symm
      (RadialPuncture.planePunctureToExterior R hR _)
  congr 1
  exact RadialPuncture.planePunctureDeformation_one R hR _

theorem zeroWindingAmbientHomeomorph_planePunctureToDiskComplement
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (x : C.zeroWindingPlanePuncture hzero) :
    C.zeroWindingAmbientHomeomorph hzero
        (C.zeroWindingPlanePunctureToDiskComplement hzero R hR x) =
      RadialPuncture.planePunctureToExterior R hR
        ⟨C.zeroWindingAmbientHomeomorph hzero x, by
          intro hx
          apply x.2
          apply (C.zeroWindingAmbientHomeomorph hzero).injective
          simpa [zeroWindingDiskCenter] using hx⟩ := by
  simp only [zeroWindingPlanePunctureToDiskComplement, Homeomorph.trans_apply]
  change (C.zeroWindingAmbientHomeomorph hzero)
      ((C.zeroWindingAmbientHomeomorph hzero).symm _) = _
  rw [(C.zeroWindingAmbientHomeomorph hzero).apply_symm_apply]
  congr 1

theorem planePunctureToDiskComplement_mem_support_iff
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (x : C.zeroWindingPlanePuncture hzero) :
    (C.zeroWindingPlanePunctureToDiskComplement hzero R hR x : TorusCoveringPlane) ∈
        C.zeroWindingSchoenfliesSupport hzero R ↔
      (x : TorusCoveringPlane) ∈ C.zeroWindingSchoenfliesSupport hzero R := by
  rw [C.mem_zeroWindingSchoenfliesSupport_iff,
    C.zeroWindingAmbientHomeomorph_planePunctureToDiskComplement hzero R hR,
    RadialPuncture.planePunctureToExterior_mem_closedBall_iff,
    ← C.mem_zeroWindingSchoenfliesSupport_iff]

theorem planePunctureToDiskComplement_apply_of_outside_support
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ) (hR : 1 < R) (x : C.zeroWindingPlanePuncture hzero)
    (hx : (x : TorusCoveringPlane) ∉ C.zeroWindingSchoenfliesSupport hzero R) :
    (C.zeroWindingPlanePunctureToDiskComplement hzero R hR x : TorusCoveringPlane) = x := by
  have hxR : R < ‖C.zeroWindingAmbientHomeomorph hzero x‖ := by
    rw [C.mem_zeroWindingSchoenfliesSupport_iff, mem_closedBall,
      dist_zero_right, not_le] at hx
    exact hx
  apply (C.zeroWindingAmbientHomeomorph hzero).injective
  rw [C.zeroWindingAmbientHomeomorph_planePunctureToDiskComplement hzero R hR]
  exact RadialPuncture.planePunctureToExterior_apply_of_le R hR _ hxR.le

/-- The image of a closed Schoenflies support in the transported torus. -/
def zeroWindingProjectedSupport (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    Set (transportedTorus Phi) :=
  torusCoveringProjectionToTorus Phi '' C.zeroWindingSchoenfliesSupport hzero R

/-- The projected open radial support. -/
def zeroWindingProjectedOpenSupport (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    Set (transportedTorus Phi) :=
  torusCoveringProjectionToTorus Phi '' C.zeroWindingSchoenfliesOpenSupport hzero R

theorem isOpen_zeroWindingProjectedOpenSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    IsOpen (C.zeroWindingProjectedOpenSupport hzero R) :=
  (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).isOpenMap _
    (C.isOpen_zeroWindingSchoenfliesOpenSupport hzero R)

theorem zeroWindingProjectedOpenSupport_subset_support
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    C.zeroWindingProjectedOpenSupport hzero R ⊆
      C.zeroWindingProjectedSupport hzero R :=
  image_mono (C.zeroWindingSchoenfliesOpenSupport_subset_support hzero R)

theorem isClosed_zeroWindingProjectedSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) (R : ℝ) :
    IsClosed (C.zeroWindingProjectedSupport hzero R) :=
  ((C.isCompact_zeroWindingSchoenfliesSupport hzero R).image
    (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous).isClosed

/-- On an injective support, the covering projection is a homeomorphism onto the projected
support. -/
def zeroWindingSupportProjectionHomeomorph
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ)
    (hinj : Set.InjOn (torusCoveringProjectionToTorus Phi)
      (C.zeroWindingSchoenfliesSupport hzero R)) :
    C.zeroWindingSchoenfliesSupport hzero R ≃ₜ
      C.zeroWindingProjectedSupport hzero R := by
  let f : C.zeroWindingSchoenfliesSupport hzero R → transportedTorus Phi :=
    fun x ↦ torusCoveringProjectionToTorus Phi x
  haveI : CompactSpace (C.zeroWindingSchoenfliesSupport hzero R) :=
    isCompact_iff_compactSpace.mp (C.isCompact_zeroWindingSchoenfliesSupport hzero R)
  have hfcont : Continuous f :=
    (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.comp
      continuous_subtype_val
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 hxy
  let h := (hfcont.isClosedEmbedding hfinj).isEmbedding.toHomeomorph
  exact h.trans <| Homeomorph.setCongr <| by
    ext y
    simp only [f, Set.mem_range, zeroWindingProjectedSupport, mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩

@[simp]
theorem zeroWindingSupportProjectionHomeomorph_apply
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    (R : ℝ)
    (hinj : Set.InjOn (torusCoveringProjectionToTorus Phi)
      (C.zeroWindingSchoenfliesSupport hzero R))
    (x : C.zeroWindingSchoenfliesSupport hzero R) :
    (C.zeroWindingSupportProjectionHomeomorph hzero R hinj x :
      transportedTorus Phi) = torusCoveringProjectionToTorus Phi x :=
  rfl

/-- The covering projection is injective on an open neighborhood of the closed lifted disk. -/
theorem exists_open_injOn_torusCoveringProjection_zeroWindingDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    ∃ U : Set TorusCoveringPlane,
      IsOpen U ∧ C.zeroWindingClosedJordanDisk hzero ⊆ U ∧
        Set.InjOn (torusCoveringProjectionToTorus Phi) U := by
  have hinj : Set.InjOn (torusCoveringProjectionToTorus Phi)
      (C.zeroWindingClosedJordanDisk hzero) := by
    intro x hx y hy hxy
    apply C.torusCoveringProjection_injOn_zeroWindingJordanDisk hzero hx hy
    exact congrArg Subtype.val hxy
  have hcompact : IsCompact (C.zeroWindingClosedJordanDisk hzero) :=
    (C.zeroWindingJordanCircle hzero).isCompact_closure_inside
  have hlocal :=
    (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).isLocallyInjective
  exact hinj.exists_isOpen_superset hcompact
    (fun _ _ ↦ (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.continuousAt)
    (fun x _ ↦ (isLocallyInjective_iff_nhds.mp hlocal x))

/-- A prescribed open neighborhood of the lifted disk contains a closed Schoenflies radial
support of some radius larger than one. -/
theorem exists_radius_schoenfliesSupport_subset_open
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    {U : Set TorusCoveringPlane} (hUopen : IsOpen U)
    (hKU : C.zeroWindingClosedJordanDisk hzero ⊆ U) :
    ∃ R : ℝ, 1 < R ∧
      (C.zeroWindingAmbientHomeomorph hzero).symm ''
        closedBall (0 : TorusCoveringPlane) R ⊆ U := by
  let e := C.zeroWindingAmbientHomeomorph hzero
  have hballU : closedBall (0 : TorusCoveringPlane) 1 ⊆ e '' U := by
    rw [← C.zeroWindingAmbientHomeomorph_image_closedJordanDisk hzero]
    exact image_mono hKU
  have heUopen : IsOpen (e '' U) := e.isOpenMap U hUopen
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : TorusCoveringPlane) 1).exists_cthickening_subset_open
      heUopen hballU
  have hlarge : closedBall (0 : TorusCoveringPlane) (1 + δ) ⊆ e '' U := by
    simpa only [cthickening_closedBall hδ.le (show (0 : ℝ) ≤ 1 by norm_num),
      add_comm] using hthick
  refine ⟨1 + δ, by linarith, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hey : y ∈ e '' U := hlarge hy
  obtain ⟨u, hu, heu⟩ := hey
  rw [← heu, e.symm_apply_apply]
  exact hu

/-- There is a radius larger than one whose entire Schoenflies support still projects
injectively to the transported torus. -/
theorem exists_radius_injOn_schoenfliesSupport
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    ∃ R : ℝ, 1 < R ∧
      Set.InjOn (torusCoveringProjectionToTorus Phi)
        ((C.zeroWindingAmbientHomeomorph hzero).symm ''
          closedBall (0 : TorusCoveringPlane) R) := by
  obtain ⟨U, hUopen, hKU, hinjU⟩ :=
    C.exists_open_injOn_torusCoveringProjection_zeroWindingDisk hzero
  obtain ⟨R, hR, hsupport⟩ :=
    C.exists_radius_schoenfliesSupport_subset_open hzero hUopen hKU
  exact ⟨R, hR, hinjU.mono hsupport⟩

end EmbeddedTorusIntersectionCircle

end Submission.Topology
