import Submission.Topology.RegularBandCentralCircle
import Submission.Topology.RegularBandCyclicWinding
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A regularized normalized-gradient field on a transported-torus height band

For a smooth planar function `f`, the explicit gradient in the standard planar basis is

`Df(e₀) e₀ + Df(e₁) e₁`.

Its derivative under `f` is the nonnegative scalar
`Df(e₀)^2 + Df(e₁)^2`.  On the compact fundamental part of a regular band this scalar has a
positive lower bound.  A smooth transition function replaces its reciprocal near zero while
agreeing exactly with the reciprocal above that lower bound.  The resulting vector field is
globally `C¹`, deck-periodic, and has unit height derivative throughout the closed band.

The second half constructs the complete flow, proves continuous dependence and deck equivariance,
and provides a general quotient descent through `Circle.exp × Circle.exp`.  The final scalar ODE
comparison and componentwise central-circle retraction are developed from those foundations.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology
open scoped Manifold NNReal Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- A path in a set places its endpoints in the same connected component of that set. -/
private theorem mem_connectedComponentIn_of_continuous_Icc_path
    {X : Type*} [TopologicalSpace X] {F : Set X} {x y : X}
    (p : ℝ → X) (hp : Continuous p) (hp0 : p 0 = x) (hp1 : p 1 = y)
    (hpF : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ F) :
    y ∈ connectedComponentIn F x := by
  let trace : Set X := p '' Icc 0 1
  have htracePreconnected : IsPreconnected trace :=
    (convex_Icc (0 : ℝ) 1).isPreconnected.image p hp.continuousOn
  have hxTrace : x ∈ trace := ⟨0, by simp, hp0⟩
  have htraceF : trace ⊆ F := by
    rintro z ⟨t, ht, rfl⟩
    exact hpF t ht
  apply htracePreconnected.subset_connectedComponentIn hxTrace htraceF
  exact ⟨1, by simp, hp1⟩

/-! ## The explicit planar gradient and its squared length -/

/-- The gradient written without using an adjoint or Riesz-representation API. -/
def planarDerivativeGradient (f : Plane → ℝ) (x : Plane) : Plane :=
  (fderiv ℝ f x planeBasisFirst) • planeBasisFirst +
    (fderiv ℝ f x planeBasisSecond) • planeBasisSecond

/-- The squared length of `planarDerivativeGradient`. -/
def planarDerivativeNormSq (f : Plane → ℝ) (x : Plane) : ℝ :=
  (fderiv ℝ f x planeBasisFirst) ^ 2 +
    (fderiv ℝ f x planeBasisSecond) ^ 2

theorem fderiv_planarDerivativeGradient (f : Plane → ℝ) (x : Plane) :
    fderiv ℝ f x (planarDerivativeGradient f x) = planarDerivativeNormSq f x := by
  rw [planarDerivativeGradient, map_add, map_smul, map_smul]
  simp only [planarDerivativeNormSq, smul_eq_mul]
  ring

theorem planarDerivativeNormSq_nonneg (f : Plane → ℝ) (x : Plane) :
    0 ≤ planarDerivativeNormSq f x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem fderiv_eq_zero_of_planarDerivativeNormSq_eq_zero
    {f : Plane → ℝ} {x : Plane} (hx : planarDerivativeNormSq f x = 0) :
    fderiv ℝ f x = 0 := by
  have hfirstSq : (fderiv ℝ f x planeBasisFirst) ^ 2 = 0 := by
    unfold planarDerivativeNormSq at hx
    nlinarith [sq_nonneg (fderiv ℝ f x planeBasisSecond)]
  have hsecondSq : (fderiv ℝ f x planeBasisSecond) ^ 2 = 0 := by
    unfold planarDerivativeNormSq at hx
    nlinarith [sq_nonneg (fderiv ℝ f x planeBasisFirst)]
  have hfirst : fderiv ℝ f x planeBasisFirst = 0 := sq_eq_zero_iff.mp hfirstSq
  have hsecond : fderiv ℝ f x planeBasisSecond = 0 := sq_eq_zero_iff.mp hsecondSq
  apply ContinuousLinearMap.ext
  intro z
  rw [show z = z.1 • planeBasisFirst + z.2 • planeBasisSecond by
    ext <;> simp [planeBasisFirst, planeBasisSecond]]
  simp [hfirst, hsecond]

theorem planarDerivativeNormSq_pos {f : Plane → ℝ} {x : Plane}
    (hx : fderiv ℝ f x ≠ 0) : 0 < planarDerivativeNormSq f x := by
  exact lt_of_le_of_ne (planarDerivativeNormSq_nonneg f x) <|
    fun h ↦ hx (fderiv_eq_zero_of_planarDerivativeNormSq_eq_zero h.symm)

theorem contDiff_planarDerivativeGradient {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (planarDerivativeGradient f) := by
  have hderiv : ContDiff ℝ 1 (fun p : Plane × Plane ↦ fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by norm_num)
  have hfirst : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisFirst) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  have hsecond : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisSecond) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  exact (hfirst.smul_const planeBasisFirst).add
    (hsecond.smul_const planeBasisSecond)

theorem contDiff_planarDerivativeNormSq {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (planarDerivativeNormSq f) := by
  have hderiv : ContDiff ℝ 1 (fun p : Plane × Plane ↦ fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by norm_num)
  have hfirst : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisFirst) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  have hsecond : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x planeBasisSecond) :=
    hderiv.comp (contDiff_id.prodMk contDiff_const)
  exact hfirst.pow 2 |>.add (hsecond.pow 2)

/-! ## A globally smooth reciprocal -/

/-- Smooth interpolation between the positive constant `δ / 2` and the identity.

The transition is complete before `s` reaches `δ`, so the denominator is exactly `s` for
`δ ≤ s`. -/
def regularizedGradientDenominator (δ s : ℝ) : ℝ :=
  let chi := Real.smoothTransition (2 * s / δ - 1)
  (1 - chi) * (δ / 2) + chi * s

theorem regularizedGradientDenominator_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 < regularizedGradientDenominator δ s := by
  by_cases hs : s ≤ δ / 2
  · have harg : 2 * s / δ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hδ]
      linarith
    rw [regularizedGradientDenominator,
      Real.smoothTransition.zero_of_nonpos harg]
    simpa using half_pos hδ
  · by_cases hδs : δ ≤ s
    · have harg : 1 ≤ 2 * s / δ - 1 := by
        rw [le_sub_iff_add_le]
        exact (le_div_iff₀ hδ).2 (by linarith)
      rw [regularizedGradientDenominator,
        Real.smoothTransition.one_of_one_le harg]
      simpa using hδ.trans_le hδs
    · have hs' : δ / 2 < s := lt_of_not_ge hs
      have hchi : 0 ≤ Real.smoothTransition (2 * s / δ - 1) :=
        Real.smoothTransition.nonneg _
      have hchiOne : Real.smoothTransition (2 * s / δ - 1) ≤ 1 :=
        Real.smoothTransition.le_one _
      unfold regularizedGradientDenominator
      dsimp only
      have hfirst : 0 ≤
          (1 - Real.smoothTransition (2 * s / δ - 1)) * (δ / 2) :=
        mul_nonneg (sub_nonneg.mpr hchiOne) (half_pos hδ).le
      have hsecond : 0 < Real.smoothTransition (2 * s / δ - 1) * s ∨
          0 < (1 - Real.smoothTransition (2 * s / δ - 1)) * (δ / 2) := by
        by_cases hzero : Real.smoothTransition (2 * s / δ - 1) = 0
        · right
          rw [hzero, sub_zero, one_mul]
          exact half_pos hδ
        · left
          exact mul_pos (lt_of_le_of_ne hchi (fun h ↦ hzero h.symm))
            (half_pos hδ |>.trans hs')
      rcases hsecond with hsecond | hsecond
      · exact add_pos_of_nonneg_of_pos hfirst hsecond
      · exact add_pos_of_pos_of_nonneg hsecond
          (mul_nonneg hchi (half_pos hδ |>.trans hs').le)

theorem contDiff_regularizedGradientDenominator {δ : ℝ} (_hδ : δ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedGradientDenominator δ) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ 2 * s / δ - 1) := by fun_prop
  have hchi : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ ↦ Real.smoothTransition (2 * s / δ - 1)) :=
    Real.smoothTransition.contDiff.comp harg
  exact (contDiff_const.sub hchi).mul contDiff_const |>.add (hchi.mul contDiff_id)

/-- A smooth reciprocal which agrees with `s⁻¹` whenever `δ ≤ s`. -/
def regularizedGradientReciprocal (δ s : ℝ) : ℝ :=
  (regularizedGradientDenominator δ s)⁻¹

theorem contDiff_regularizedGradientReciprocal {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedGradientReciprocal δ) := by
  exact (contDiff_regularizedGradientDenominator hδ.ne').inv
    (fun s ↦ (regularizedGradientDenominator_pos hδ s).ne')

theorem regularizedGradientReciprocal_eq_inv {δ s : ℝ}
    (hδ : 0 < δ) (hs : δ ≤ s) : regularizedGradientReciprocal δ s = s⁻¹ := by
  have harg : 1 ≤ 2 * s / δ - 1 := by
    rw [le_sub_iff_add_le]
    exact (le_div_iff₀ hδ).2 (by linarith)
  rw [regularizedGradientReciprocal, regularizedGradientDenominator,
    Real.smoothTransition.one_of_one_le harg]
  simp

/-! ## Compact lower bound on the regular band -/

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- The part of the lifted closed band in one compact fundamental square. -/
def fundamentalClosedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) : Set Plane :=
  fundamentalSquare ∩
    {uv | |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε}

/-- The same compact band enlarged by a positive height margin. -/
def fundamentalExpandedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) (margin : ℝ) : Set Plane :=
  fundamentalSquare ∩
    {uv | |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε + margin}

theorem isCompact_fundamentalClosedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    IsCompact (fundamentalClosedCoordinateBand B) := by
  apply isCompact_fundamentalSquare.inter_right
  exact isClosed_Iic.preimage <| continuous_abs.comp <|
    (orientedCoordinateLift_contDiff Phi frame 2).continuous.sub continuous_const

theorem isCompact_fundamentalExpandedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) (margin : ℝ) :
    IsCompact (fundamentalExpandedCoordinateBand B margin) := by
  apply isCompact_fundamentalSquare.inter_right
  exact isClosed_Iic.preimage <| continuous_abs.comp <|
    (orientedCoordinateLift_contDiff Phi frame 2).continuous.sub continuous_const

/-- Compactness of the critical-value image leaves a genuine open height margin around the
closed regular band. -/
theorem exists_regular_expanded_coordinate_band
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    ∃ margin > 0, ∀ uv ∈ fundamentalSquare,
      |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε + margin →
        fderiv ℝ (orientedCoordinateLift Phi frame 2) uv ≠ 0 := by
  let f := orientedCoordinateLift Phi frame 2
  let interval : Set ℝ := Icc (d - 2 * B.ε) (d + 2 * B.ε)
  have hinterval : interval ⊆ (fundamentalCriticalValues f)ᶜ := by
    intro y hy hyCritical
    obtain ⟨uv, ⟨huvSquare, huvCritical⟩, huvValue⟩ := hyCritical
    apply B.fundamental_noncritical uv huvSquare
    · change |f uv - d| ≤ 2 * B.ε
      rw [huvValue, abs_le]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · exact huvCritical
  have hopen : IsOpen (fundamentalCriticalValues f)ᶜ :=
    (isCompact_fundamentalCriticalValues
      (orientedCoordinateLift_contDiff Phi frame 2)).isClosed.isOpen_compl
  obtain ⟨rho, hrho, hthick⟩ :=
    isCompact_Icc.exists_thickening_subset_open hopen hinterval
  let margin := rho / 2
  have hmargin : 0 < margin := half_pos hrho
  refine ⟨margin, hmargin, ?_⟩
  intro uv huvSquare huvBand huvCritical
  apply hthick
  · rw [Metric.mem_thickening_iff]
    have huvBounds :
        d - (2 * B.ε + margin) ≤ f uv ∧
          f uv ≤ d + (2 * B.ε + margin) := by
      rw [abs_le] at huvBand
      exact ⟨by linarith [huvBand.1], by linarith [huvBand.2]⟩
    by_cases hlower : f uv < d - 2 * B.ε
    · refine ⟨d - 2 * B.ε, ⟨le_rfl, by linarith [B.ε_pos]⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      dsimp only [margin] at huvBounds
      linarith
    · by_cases hupper : d + 2 * B.ε < f uv
      · refine ⟨d + 2 * B.ε, ⟨by linarith [B.ε_pos], le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        change f uv - (d + 2 * B.ε) < rho
        dsimp only [margin] at huvBounds
        linarith
      · refine ⟨f uv, ⟨le_of_not_gt hlower, le_of_not_gt hupper⟩, ?_⟩
        rw [dist_self]
        exact hrho
  · exact ⟨uv, ⟨huvSquare, huvCritical⟩, rfl⟩

theorem exists_pos_le_planarDerivativeNormSq_on_fundamentalClosedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    ∃ δ > 0, ∀ uv ∈ fundamentalClosedCoordinateBand B,
      δ ≤ planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv := by
  let f := orientedCoordinateLift Phi frame 2
  have hcontinuous : Continuous (planarDerivativeNormSq f) :=
    (contDiff_planarDerivativeNormSq
      ((orientedCoordinateLift_contDiff Phi frame 2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous
  apply (isCompact_fundamentalClosedCoordinateBand B).exists_forall_le'
    hcontinuous.continuousOn
  intro uv huv
  exact planarDerivativeNormSq_pos <| B.fundamental_noncritical uv huv.1 huv.2

theorem exists_pos_le_planarDerivativeNormSq_on_fundamentalExpandedCoordinateBand
    (B : OrientedCoordinateRegularBandData Phi frame d) {margin : ℝ}
    (hregular : ∀ uv ∈ fundamentalSquare,
      |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε + margin →
        fderiv ℝ (orientedCoordinateLift Phi frame 2) uv ≠ 0) :
    ∃ δ > 0, ∀ uv ∈ fundamentalExpandedCoordinateBand B margin,
      δ ≤ planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv := by
  let f := orientedCoordinateLift Phi frame 2
  have hcontinuous : Continuous (planarDerivativeNormSq f) :=
    (contDiff_planarDerivativeNormSq
      ((orientedCoordinateLift_contDiff Phi frame 2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous
  apply (isCompact_fundamentalExpandedCoordinateBand B margin).exists_forall_le'
    hcontinuous.continuousOn
  intro uv huv
  exact planarDerivativeNormSq_pos <| hregular uv huv.1 huv.2

/-- The analytic data defining the regularized normalized-gradient field. -/
structure RegularBandNormalizedGradientFieldData
    (B : OrientedCoordinateRegularBandData Phi frame d) where
  margin : ℝ
  margin_pos : 0 < margin
  δ : ℝ
  δ_pos : 0 < δ
  fundamental_lower : ∀ uv ∈ fundamentalExpandedCoordinateBand B margin,
    δ ≤ planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv

namespace RegularBandNormalizedGradientFieldData

variable {B : OrientedCoordinateRegularBandData Phi frame d}

/-- Smooth scalar speed which is one on the closed band and zero outside its expanded
regular neighborhood.  Squared height avoids differentiability issues from `abs`. -/
def heightSpeed (D : RegularBandNormalizedGradientFieldData B) (r : ℝ) : ℝ :=
  let inner := 2 * B.ε
  let outer := inner + D.margin
  Real.smoothTransition ((outer ^ 2 - (r - d) ^ 2) / (outer ^ 2 - inner ^ 2))

private theorem heightSpeed_denominator_pos (D : RegularBandNormalizedGradientFieldData B) :
    0 < (2 * B.ε + D.margin) ^ 2 - (2 * B.ε) ^ 2 := by
  nlinarith [B.ε_pos, D.margin_pos]

theorem contDiff_heightSpeed (D : RegularBandNormalizedGradientFieldData B) :
    ContDiff ℝ (⊤ : ℕ∞) D.heightSpeed := by
  unfold heightSpeed
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem heightSpeed_eq_one_of_mem_band
    (D : RegularBandNormalizedGradientFieldData B) {r : ℝ}
    (hr : |r - d| ≤ 2 * B.ε) : D.heightSpeed r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ D.heightSpeed_denominator_pos]
  have hsquare : (r - d) ^ 2 ≤ (2 * B.ε) ^ 2 := by
    apply (sq_le_sq).2
    rw [abs_of_nonneg (mul_nonneg (by norm_num) B.ε_pos.le)]
    exact hr
  linarith

theorem abs_lt_expanded_of_heightSpeed_ne_zero
    (D : RegularBandNormalizedGradientFieldData B) {r : ℝ}
    (hr : D.heightSpeed r ≠ 0) :
    |r - d| < 2 * B.ε + D.margin := by
  have harg : 0 <
      (((2 * B.ε + D.margin) ^ 2 - (r - d) ^ 2) /
        ((2 * B.ε + D.margin) ^ 2 - (2 * B.ε) ^ 2)) := by
    apply lt_of_not_ge
    intro hnonpos
    apply hr
    exact Real.smoothTransition.zero_of_nonpos hnonpos
  have hsquare : (r - d) ^ 2 < (2 * B.ε + D.margin) ^ 2 := by
    rw [div_pos_iff] at harg
    rcases harg with harg | harg
    · linarith
    · exact False.elim <| (not_lt_of_ge D.heightSpeed_denominator_pos.le) harg.2
  exact abs_lt_of_sq_lt_sq hsquare (by linarith [B.ε_pos, D.margin_pos])

theorem heightSpeed_eq_zero_of_expanded_le
    (D : RegularBandNormalizedGradientFieldData B) {r : ℝ}
    (hr : 2 * B.ε + D.margin ≤ |r - d|) : D.heightSpeed r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · rw [sub_nonpos, sq_le_sq]
    rw [abs_of_nonneg (by linarith [B.ε_pos, D.margin_pos])]
    exact hr
  · exact D.heightSpeed_denominator_pos.le

theorem hasCompactSupport_heightSpeed
    (D : RegularBandNormalizedGradientFieldData B) :
    HasCompactSupport D.heightSpeed := by
  let outer := 2 * B.ε + D.margin
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (d - outer) (d + outer)))
  intro r hr
  have hout : outer ≤ |r - d| := by
    rw [mem_Icc, not_and_or] at hr
    rcases hr with hr | hr
    · rw [abs_of_neg (by linarith [B.ε_pos, D.margin_pos])]
      linarith
    · rw [abs_of_nonneg (by linarith [B.ε_pos, D.margin_pos])]
      linarith
  exact D.heightSpeed_eq_zero_of_expanded_le hout

/-- The autonomous scalar height speed is globally Lipschitz because it is smooth and compactly
supported. -/
theorem exists_lipschitzWith_heightSpeed
    (D : RegularBandNormalizedGradientFieldData B) :
    ∃ K : ℝ≥0, LipschitzWith K D.heightSpeed := by
  exact D.contDiff_heightSpeed.lipschitzWith_of_hasCompactSupport
    D.hasCompactSupport_heightSpeed (by simp)

/-- The globally smooth regularized normalized-gradient field. -/
def field (D : RegularBandNormalizedGradientFieldData B) (uv : Plane) : Plane :=
  D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) •
    (regularizedGradientReciprocal D.δ
        (planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv) •
      planarDerivativeGradient (orientedCoordinateLift Phi frame 2) uv)

theorem contDiff_field (D : RegularBandNormalizedGradientFieldData B) :
    ContDiff ℝ 1 D.field := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ 2 f :=
    (orientedCoordinateLift_contDiff Phi frame 2).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hfOne : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hscalar : ContDiff ℝ 1
      (fun uv ↦ regularizedGradientReciprocal D.δ (planarDerivativeNormSq f uv)) :=
    ((contDiff_regularizedGradientReciprocal D.δ_pos).of_le (by simp)).comp
      (contDiff_planarDerivativeNormSq hf)
  have hspeed : ContDiff ℝ 1
      (fun uv ↦ D.heightSpeed (orientedCoordinateLift Phi frame 2 uv)) :=
    (D.contDiff_heightSpeed.of_le (by simp)).comp hfOne
  exact hspeed.smul (hscalar.smul (contDiff_planarDerivativeGradient hf))

theorem planarDerivativeGradient_add_planeDeckVector
    (uv : Plane) (m n : ℤ) :
    planarDerivativeGradient (orientedCoordinateLift Phi frame 2)
        (uv + planeDeckVector m n) =
      planarDerivativeGradient (orientedCoordinateLift Phi frame 2) uv := by
  simp only [planarDerivativeGradient,
    fderiv_orientedCoordinateLift_add_planeDeckVector]

theorem planarDerivativeNormSq_add_planeDeckVector
    (uv : Plane) (m n : ℤ) :
    planarDerivativeNormSq (orientedCoordinateLift Phi frame 2)
        (uv + planeDeckVector m n) =
      planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv := by
  simp only [planarDerivativeNormSq,
    fderiv_orientedCoordinateLift_add_planeDeckVector]

theorem field_add_planeDeckVector (D : RegularBandNormalizedGradientFieldData B)
    (uv : Plane) (m n : ℤ) :
    D.field (uv + planeDeckVector m n) = D.field uv := by
  simp only [field, orientedCoordinateLift_add_planeDeckVector,
    planarDerivativeGradient_add_planeDeckVector,
    planarDerivativeNormSq_add_planeDeckVector]

theorem lower_bound_on_plane_band
    (D : RegularBandNormalizedGradientFieldData B) (uv : Plane)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε + D.margin) :
    D.δ ≤ planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv := by
  let representative := planeFundamentalRepresentative uv
  have hrepBand :
      |orientedCoordinateLift Phi frame 2 representative - d| ≤ 2 * B.ε + D.margin := by
    rw [orientedCoordinateLift_planeFundamentalRepresentative Phi frame 2 uv]
    exact huv
  have hlower := D.fundamental_lower representative
    ⟨planeFundamentalRepresentative_mem_fundamentalSquare uv, hrepBand⟩
  calc
    D.δ ≤ planarDerivativeNormSq
        (orientedCoordinateLift Phi frame 2) representative := hlower
    _ = planarDerivativeNormSq (orientedCoordinateLift Phi frame 2) uv := by
      rw [← planeFundamentalRepresentative_add_deck uv]
      exact (planarDerivativeNormSq_add_planeDeckVector representative
        (planeFundamentalDeckIndex uv).1 (planeFundamentalDeckIndex uv).2).symm

/-- On the closed band, applying the height differential to the field gives exactly one. -/
theorem fderiv_field_eq_one_of_mem_band
    (D : RegularBandNormalizedGradientFieldData B) (uv : Plane)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv (D.field uv) = 1 := by
  let f := orientedCoordinateLift Phi frame 2
  have hlower : D.δ ≤ planarDerivativeNormSq f uv :=
    D.lower_bound_on_plane_band uv <|
      huv.trans (le_add_of_nonneg_right D.margin_pos.le)
  have hpos : 0 < planarDerivativeNormSq f uv := D.δ_pos.trans_le hlower
  rw [field, map_smul, map_smul, fderiv_planarDerivativeGradient,
    regularizedGradientReciprocal_eq_inv D.δ_pos hlower]
  simp only [smul_eq_mul]
  rw [inv_mul_cancel₀ hpos.ne', mul_one,
    D.heightSpeed_eq_one_of_mem_band huv]

/-- Globally, the derivative of height along the regularized field is the scalar height speed.
This autonomous scalar identity removes any band-invariance bootstrap from the later flow proof. -/
theorem fderiv_field_eq_heightSpeed
    (D : RegularBandNormalizedGradientFieldData B) (uv : Plane) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv (D.field uv) =
      D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) := by
  by_cases hspeed : D.heightSpeed (orientedCoordinateLift Phi frame 2 uv) = 0
  · simp [field, hspeed]
  · have hband :
        |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε + D.margin :=
      (D.abs_lt_expanded_of_heightSpeed_ne_zero hspeed).le
    have hlower := D.lower_bound_on_plane_band uv hband
    have hpos : 0 < planarDerivativeNormSq
        (orientedCoordinateLift Phi frame 2) uv := D.δ_pos.trans_le hlower
    rw [field, map_smul, map_smul, fderiv_planarDerivativeGradient,
      regularizedGradientReciprocal_eq_inv D.δ_pos hlower]
    simp only [smul_eq_mul]
    rw [inv_mul_cancel₀ hpos.ne', mul_one]

end RegularBandNormalizedGradientFieldData

/-- Compact band regularity canonically supplies a global regularized field. -/
theorem exists_regularBandNormalizedGradientFieldData
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    Nonempty (RegularBandNormalizedGradientFieldData B) := by
  obtain ⟨margin, hmargin, hregular⟩ := exists_regular_expanded_coordinate_band B
  obtain ⟨δ, hδ, hlower⟩ :=
    exists_pos_le_planarDerivativeNormSq_on_fundamentalExpandedCoordinateBand B hregular
  exact ⟨{
    margin := margin
    margin_pos := hmargin
    δ := δ
    δ_pos := hδ
    fundamental_lower := hlower }⟩

/-! ## Generic bounds and complete flows for a deck-periodic field -/

/-- Invariance under all two-dimensional deck translations. -/
def IsPlaneDeckPeriodic {Y : Type*} (v : Plane → Y) : Prop :=
  ∀ uv (m n : ℤ), v (uv + planeDeckVector m n) = v uv

/-- Two lifts of the same point of the product torus differ by a deck vector. -/
theorem eq_add_planeDeckVector_of_planeExpPair_eq {uv wz : Plane}
    (h : planeExpPair uv = planeExpPair wz) :
    ∃ m n : ℤ, uv = wz + planeDeckVector m n := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst h)
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd h)
  refine ⟨m, n, ?_⟩
  ext
  · simpa [planeDeckVector] using hm
  · simpa [planeDeckVector] using hn

/-- The product exponential is an open quotient map. -/
theorem planeExpPair_isOpenQuotientMap : IsOpenQuotientMap planeExpPair := {
  surjective := planeExpPair_surjective
  continuous := planeExpPair_isLocalHomeomorph.continuous
  isOpenMap := planeExpPair_isLocalHomeomorph.isOpenMap
}

/-- Descend a deck-invariant planar map through the product exponential.  The `invFun`
representative is harmless because deck invariance proves exact independence of the choice. -/
def descendPlaneMap {Y : Type*} (g : Plane → Y) : Circle × Circle → Y :=
  fun z ↦ g (Function.invFun planeExpPair z)

theorem descendPlaneMap_planeExpPair {Y : Type*} (g : Plane → Y)
    (hg : IsPlaneDeckPeriodic g) (uv : Plane) :
    descendPlaneMap g (planeExpPair uv) = g uv := by
  have hprojection : planeExpPair (Function.invFun planeExpPair (planeExpPair uv)) =
      planeExpPair uv :=
    Function.rightInverse_invFun planeExpPair_surjective (planeExpPair uv)
  obtain ⟨m, n, hdeck⟩ := eq_add_planeDeckVector_of_planeExpPair_eq hprojection
  unfold descendPlaneMap
  rw [hdeck, hg]

theorem continuous_descendPlaneMap {Y : Type*} [TopologicalSpace Y]
    {g : Plane → Y} (hg : Continuous g) (hperiodic : IsPlaneDeckPeriodic g) :
    Continuous (descendPlaneMap g) := by
  rw [← planeExpPair_isOpenQuotientMap.continuous_comp_iff]
  have heq : descendPlaneMap g ∘ planeExpPair = g := by
    funext uv
    exact descendPlaneMap_planeExpPair g hperiodic uv
  rw [heq]
  exact hg

/-- Parameterwise descent of a jointly continuous deck-invariant family. -/
def descendPlaneFamily {A Y : Type*} (G : A → Plane → Y) :
    A → Circle × Circle → Y :=
  fun a ↦ descendPlaneMap (G a)

theorem descendPlaneFamily_planeExpPair {A Y : Type*} (G : A → Plane → Y)
    (hperiodic : ∀ a, IsPlaneDeckPeriodic (G a)) (a : A) (uv : Plane) :
    descendPlaneFamily G a (planeExpPair uv) = G a uv :=
  descendPlaneMap_planeExpPair (G a) (hperiodic a) uv

theorem continuous_uncurry_descendPlaneFamily
    {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    {G : A → Plane → Y} (hG : Continuous (Function.uncurry G))
    (hperiodic : ∀ a, IsPlaneDeckPeriodic (G a)) :
    Continuous (Function.uncurry (descendPlaneFamily G)) := by
  let q : A × Plane → A × (Circle × Circle) := Prod.map id planeExpPair
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.id.prodMap planeExpPair_isOpenQuotientMap
  rw [← hq.continuous_comp_iff]
  have heq : Function.uncurry (descendPlaneFamily G) ∘ q = Function.uncurry G := by
    funext p
    exact descendPlaneFamily_planeExpPair G hperiodic p.1 p.2
  rw [heq]
  exact hG

theorem RegularBandNormalizedGradientFieldData.isPlaneDeckPeriodic
    {B : OrientedCoordinateRegularBandData Phi frame d}
    (D : RegularBandNormalizedGradientFieldData B) : IsPlaneDeckPeriodic D.field :=
  D.field_add_planeDeckVector

theorem fderiv_add_planeDeckVector_of_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : IsPlaneDeckPeriodic v)
    (uv : Plane) (m n : ℤ) :
    fderiv ℝ v (uv + planeDeckVector m n) = fderiv ℝ v uv := by
  let deck := planeDeckVector m n
  have hfun : (fun z ↦ v (z + deck)) = v := by
    funext z
    exact hv z m n
  calc
    fderiv ℝ v (uv + deck) = fderiv ℝ (fun z ↦ v (z + deck)) uv :=
      (fderiv_comp_add_right deck).symm
    _ = fderiv ℝ v uv := congrArg (fun q : Plane → Plane ↦ fderiv ℝ q uv) hfun

private theorem fundamentalSquare_nonempty : fundamentalSquare.Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨⟨le_rfl, Real.two_pi_pos.le⟩, ⟨le_rfl, Real.two_pi_pos.le⟩⟩

/-- A continuous deck-periodic field is globally bounded by its maximum on one fundamental
square. -/
theorem exists_global_norm_bound_of_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : Continuous v) (hperiodic : IsPlaneDeckPeriodic v) :
    ∃ L : ℝ≥0, ∀ uv, ‖v uv‖₊ ≤ L := by
  obtain ⟨center, _hcenter, hmax⟩ := isCompact_fundamentalSquare.exists_isMaxOn
    fundamentalSquare_nonempty hv.nnnorm.continuousOn
  refine ⟨‖v center‖₊, ?_⟩
  intro uv
  let representative := planeFundamentalRepresentative uv
  let index := planeFundamentalDeckIndex uv
  calc
    ‖v uv‖₊ = ‖v (representative + planeDeckVector index.1 index.2)‖₊ := by
      rw [planeFundamentalRepresentative_add_deck]
    _ = ‖v representative‖₊ := congrArg nnnorm (hperiodic representative index.1 index.2)
    _ ≤ ‖v center‖₊ :=
      hmax (planeFundamentalRepresentative_mem_fundamentalSquare uv)

/-- A `C¹` deck-periodic field has globally bounded derivative. -/
theorem exists_global_fderiv_bound_of_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : ContDiff ℝ 1 v) (hperiodic : IsPlaneDeckPeriodic v) :
    ∃ K : ℝ≥0, ∀ uv, ‖fderiv ℝ v uv‖₊ ≤ K := by
  have hcontinuous : Continuous (fun uv ↦ ‖fderiv ℝ v uv‖₊) :=
    (hv.continuous_fderiv (by norm_num)).nnnorm
  obtain ⟨center, _hcenter, hmax⟩ := isCompact_fundamentalSquare.exists_isMaxOn
    fundamentalSquare_nonempty hcontinuous.continuousOn
  refine ⟨‖fderiv ℝ v center‖₊, ?_⟩
  intro uv
  let representative := planeFundamentalRepresentative uv
  let index := planeFundamentalDeckIndex uv
  calc
    ‖fderiv ℝ v uv‖₊ =
        ‖fderiv ℝ v (representative + planeDeckVector index.1 index.2)‖₊ := by
      rw [planeFundamentalRepresentative_add_deck]
    _ = ‖fderiv ℝ v representative‖₊ := congrArg nnnorm <|
      fderiv_add_planeDeckVector_of_isPlaneDeckPeriodic
        hperiodic representative index.1 index.2
    _ ≤ ‖fderiv ℝ v center‖₊ :=
      hmax (planeFundamentalRepresentative_mem_fundamentalSquare uv)

/-- The derivative bound upgrades a `C¹` deck-periodic field to a global Lipschitz field. -/
theorem exists_lipschitzWith_of_contDiff_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : ContDiff ℝ 1 v) (hperiodic : IsPlaneDeckPeriodic v) :
    ∃ K : ℝ≥0, LipschitzWith K v := by
  obtain ⟨K, hK⟩ := exists_global_fderiv_bound_of_isPlaneDeckPeriodic hv hperiodic
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hv.differentiable (by norm_num)) hK⟩

/-- Uniform local curves for a generic deck-periodic planar field. -/
theorem exists_uniformPlaneIntegralCurves_of_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : ContDiff ℝ 1 v) (hperiodic : IsPlaneDeckPeriodic v) :
    Nonempty (UniformPlaneIntegralCurves v) := by
  classical
  obtain ⟨radius, hradius, hlocal⟩ :=
    exists_uniformPlaneIntegralCurvesOnFundamentalSquare hv
  choose localCurve hlocalZero hlocalIntegral using fun x : Plane ↦
    hlocal (planeFundamentalRepresentative x)
      (planeFundamentalRepresentative_mem_fundamentalSquare x)
  let deck (x : Plane) : Plane :=
    planeDeckVector (planeFundamentalDeckIndex x).1 (planeFundamentalDeckIndex x).2
  let curve (x : Plane) (t : ℝ) : Plane := localCurve x t + deck x
  refine ⟨{
    radius := radius
    radius_pos := hradius
    curve := curve
    curve_zero := ?_
    integral := ?_ }⟩
  · intro x
    change localCurve x 0 + deck x = x
    rw [hlocalZero]
    exact planeFundamentalRepresentative_add_deck x
  · intro x t ht
    change HasDerivWithinAt (fun u ↦ localCurve x u + deck x)
      (v (localCurve x t + deck x)) (Ioo (-radius) radius) t
    exact ((hlocalIntegral x t ht).add_const (deck x)).congr_deriv <|
      (hperiodic (localCurve x t) (planeFundamentalDeckIndex x).1
        (planeFundamentalDeckIndex x).2).symm

/-- A complete integral curve for an arbitrary planar field. -/
structure CompletePlaneIntegralCurve (v : Plane → Plane) (x : Plane) where
  curve : ℝ → Plane
  curve_zero : curve 0 = x
  integral : IsIntegralCurve curve (fun _ ↦ v)

theorem exists_completePlaneIntegralCurve_of_uniform
    {v : Plane → Plane} (hv : ContDiff ℝ 1 v) (U : UniformPlaneIntegralCurves v)
    (x : Plane) : Nonempty (CompletePlaneIntegralCurve v x) := by
  let vm := planeTangentVectorField v
  have hvm : ContDiff ℝ 1 vm := by
    change ContDiff ℝ 1 v
    exact hv
  have hfield : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane).tangent 1 (T% vm) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := Plane)).mpr hvm
  obtain ⟨curve, hzero, hcurveM⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn (I := 𝓘(ℝ, Plane)) hfield
      U.radius_pos (fun z ↦ ⟨U.curve z, U.curve_zero z,
        (isMIntegralCurveOn_iff_isIntegralCurveOn_plane _ _ _).mpr (U.integral z)⟩) x
  exact ⟨{
    curve := curve
    curve_zero := hzero
    integral := (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mp hcurveM }⟩

/-- A simultaneous choice of the unique complete curves through every point. -/
structure CompletePlaneIntegralFlow (v : Plane → Plane) where
  flow : Plane → ℝ → Plane
  flow_zero : ∀ x, flow x 0 = x
  integral : ∀ x, IsIntegralCurve (flow x) (fun _ ↦ v)

theorem exists_completePlaneIntegralFlow_of_isPlaneDeckPeriodic
    {v : Plane → Plane} (hv : ContDiff ℝ 1 v) (hperiodic : IsPlaneDeckPeriodic v) :
    Nonempty (CompletePlaneIntegralFlow v) := by
  classical
  let U := Classical.choice
    (exists_uniformPlaneIntegralCurves_of_isPlaneDeckPeriodic hv hperiodic)
  let chosen (x : Plane) := Classical.choice
    (exists_completePlaneIntegralCurve_of_uniform hv U x)
  exact ⟨{
    flow := fun x ↦ (chosen x).curve
    flow_zero := fun x ↦ (chosen x).curve_zero
    integral := fun x ↦ (chosen x).integral }⟩

namespace CompletePlaneIntegralFlow

theorem integralCurve_eq_of_eq_zero {v : Plane → Plane} (hv : ContDiff ℝ 1 v)
    {alpha beta : ℝ → Plane}
    (halpha : IsIntegralCurve alpha (fun _ ↦ v))
    (hbeta : IsIntegralCurve beta (fun _ ↦ v)) (hzero : alpha 0 = beta 0) :
    alpha = beta := by
  let vm := planeTangentVectorField v
  have hfield : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane).tangent 1 (T% vm) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := Plane)).mpr <| by
      change ContDiff ℝ 1 v
      exact hv
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hfield
    ((isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr halpha)
    ((isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr hbeta) hzero

theorem flow_add {v : Plane → Plane} (hv : ContDiff ℝ 1 v)
    (F : CompletePlaneIntegralFlow v) (x : Plane) (s t : ℝ) :
    F.flow x (s + t) = F.flow (F.flow x s) t := by
  let alpha : ℝ → Plane := fun u ↦ F.flow x (u + s)
  let beta : ℝ → Plane := F.flow (F.flow x s)
  have halpha : IsIntegralCurve alpha (fun _ ↦ v) := by
    simpa [alpha, Function.comp_def] using (F.integral x).comp_add s
  have hbeta : IsIntegralCurve beta (fun _ ↦ v) := F.integral (F.flow x s)
  have hzero : alpha 0 = beta 0 := by simp [alpha, beta, F.flow_zero]
  have heq := integralCurve_eq_of_eq_zero hv halpha hbeta hzero
  simpa [alpha, beta, add_comm] using congrFun heq t

theorem flow_add_planeDeckVector {v : Plane → Plane}
    (hv : ContDiff ℝ 1 v) (hperiodic : IsPlaneDeckPeriodic v)
    (F : CompletePlaneIntegralFlow v) (x : Plane) (m n : ℤ) (t : ℝ) :
    F.flow (x + planeDeckVector m n) t = F.flow x t + planeDeckVector m n := by
  let deck := planeDeckVector m n
  let alpha : ℝ → Plane := F.flow (x + deck)
  let beta : ℝ → Plane := fun u ↦ F.flow x u + deck
  have halpha : IsIntegralCurve alpha (fun _ ↦ v) := F.integral (x + deck)
  have hbeta : IsIntegralCurve beta (fun _ ↦ v) := by
    intro u
    exact ((F.integral x u).add_const deck).congr_deriv
      (hperiodic (F.flow x u) m n).symm
  have hzero : alpha 0 = beta 0 := by simp [alpha, beta, F.flow_zero]
  exact congrFun (integralCurve_eq_of_eq_zero hv halpha hbeta hzero) t

theorem dist_flow_le_of_nonneg {v : Plane → Plane} {K : ℝ≥0}
    (hK : LipschitzWith K v) (F : CompletePlaneIntegralFlow v)
    (x y : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist (F.flow x t) (F.flow y t) ≤
      dist x y * Real.exp ((K : ℝ) * |t|) := by
  have hbound := dist_le_of_trajectories_ODE
    (v := fun _ ↦ v) (a := 0) (b := t) (δ := dist x y)
    (fun _ ↦ hK)
    (F.integral x).continuous.continuousOn
    (fun u _ ↦ (F.integral x u).hasDerivWithinAt)
    (F.integral y).continuous.continuousOn
    (fun u _ ↦ (F.integral y u).hasDerivWithinAt)
    (by simp [F.flow_zero]) t ⟨ht, le_rfl⟩
  simpa [abs_of_nonneg ht] using hbound

theorem dist_flow_le_of_nonpos {v : Plane → Plane} {K : ℝ≥0}
    (hK : LipschitzWith K v) (F : CompletePlaneIntegralFlow v)
    (x y : Plane) {t : ℝ} (ht : t ≤ 0) :
    dist (F.flow x t) (F.flow y t) ≤
      dist x y * Real.exp ((K : ℝ) * |t|) := by
  let alpha : ℝ → Plane := fun u ↦ F.flow x (-u)
  let beta : ℝ → Plane := fun u ↦ F.flow y (-u)
  let w : ℝ → Plane → Plane := -(fun _ ↦ v)
  have halpha : IsIntegralCurve alpha w := by
    have h := (F.integral x).comp_mul (-1)
    simpa [alpha, w, Function.comp_def] using h
  have hbeta : IsIntegralCurve beta w := by
    have h := (F.integral y).comp_mul (-1)
    simpa [beta, w, Function.comp_def] using h
  have hbound := dist_le_of_trajectories_ODE
    (v := w) (a := 0) (b := -t) (δ := dist x y)
    (fun _ ↦ hK.neg)
    halpha.continuous.continuousOn
    (fun u _ ↦ (halpha u).hasDerivWithinAt)
    hbeta.continuous.continuousOn
    (fun u _ ↦ (hbeta u).hasDerivWithinAt)
    (by simp [alpha, beta, F.flow_zero]) (-t) ⟨neg_nonneg.mpr ht, le_rfl⟩
  simpa [alpha, beta, abs_of_nonpos ht] using hbound

/-- Grönwall control of the complete flow in its initial point. -/
theorem dist_flow_le {v : Plane → Plane} {K : ℝ≥0}
    (hK : LipschitzWith K v) (F : CompletePlaneIntegralFlow v)
    (x y : Plane) (t : ℝ) :
    dist (F.flow x t) (F.flow y t) ≤
      dist x y * Real.exp ((K : ℝ) * |t|) := by
  rcases le_total 0 t with ht | ht
  · exact F.dist_flow_le_of_nonneg hK x y ht
  · exact F.dist_flow_le_of_nonpos hK x y ht

/-- Global Lipschitz control in space and integral-curve continuity in time give joint
continuity of the complete flow. -/
theorem continuous_uncurry {v : Plane → Plane} (hv : ContDiff ℝ 1 v)
    (hperiodic : IsPlaneDeckPeriodic v) (F : CompletePlaneIntegralFlow v) :
    Continuous (Function.uncurry F.flow) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff_isPlaneDeckPeriodic hv hperiodic
  rw [continuous_iff_continuousAt]
  rintro ⟨x, t⟩
  change Filter.Tendsto (Function.uncurry F.flow) (nhds (x, t))
    (nhds (Function.uncurry F.flow (x, t)))
  rw [tendsto_iff_dist_tendsto_zero]
  let upper : Plane × ℝ → ℝ := fun p ↦
    dist p.1 x * Real.exp ((K : ℝ) * |p.2|) +
      dist (F.flow x p.2) (F.flow x t)
  refine squeeze_zero
    (f := fun p ↦ dist (Function.uncurry F.flow p)
      (Function.uncurry F.flow (x, t))) (g := upper)
    (fun _ ↦ dist_nonneg) ?_ ?_
  · intro p
    calc
      dist (Function.uncurry F.flow p) (Function.uncurry F.flow (x, t)) ≤
          dist (F.flow p.1 p.2) (F.flow x p.2) +
            dist (F.flow x p.2) (F.flow x t) := dist_triangle _ _ _
      _ ≤ upper p := add_le_add (F.dist_flow_le hK p.1 x p.2) le_rfl
  · have hcurve : Continuous (F.flow x) := (F.integral x).continuous
    have hupper : ContinuousAt upper (x, t) := by
      dsimp only [upper]
      fun_prop
    convert hupper.tendsto using 1
    · simp [upper]

end CompletePlaneIntegralFlow

/-! ## The normalized-gradient flow and its quotient descent -/

/-- The chosen regularized field together with its unique complete flow. -/
structure RegularBandNormalizedGradientFlowData
    (B : OrientedCoordinateRegularBandData Phi frame d) where
  fieldData : RegularBandNormalizedGradientFieldData B
  flow : CompletePlaneIntegralFlow fieldData.field

namespace RegularBandNormalizedGradientFlowData

variable {B : OrientedCoordinateRegularBandData Phi frame d}

theorem continuous_planeFlow (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.flow.flow) :=
  G.flow.continuous_uncurry G.fieldData.contDiff_field
    G.fieldData.isPlaneDeckPeriodic

theorem planeFlow_add_planeDeckVector (G : RegularBandNormalizedGradientFlowData B)
    (uv : Plane) (m n : ℤ) (t : ℝ) :
    G.flow.flow (uv + planeDeckVector m n) t =
      G.flow.flow uv t + planeDeckVector m n :=
  G.flow.flow_add_planeDeckVector G.fieldData.contDiff_field
    G.fieldData.isPlaneDeckPeriodic uv m n t

/-- Product-torus flow obtained by descending the complete planar flow. -/
def quotientFlow (G : RegularBandNormalizedGradientFlowData B) :
    ℝ → Circle × Circle → Circle × Circle :=
  descendPlaneFamily fun t uv ↦ planeExpPair (G.flow.flow uv t)

theorem quotientFlow_planeExpPair (G : RegularBandNormalizedGradientFlowData B)
    (t : ℝ) (uv : Plane) :
    G.quotientFlow t (planeExpPair uv) = planeExpPair (G.flow.flow uv t) := by
  apply descendPlaneFamily_planeExpPair
  intro s wz m n
  change planeExpPair (G.flow.flow (wz + planeDeckVector m n) s) =
    planeExpPair (G.flow.flow wz s)
  rw [G.planeFlow_add_planeDeckVector, planeExpPair_add_planeDeckVector]

theorem continuous_quotientFlow (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.quotientFlow) := by
  apply continuous_uncurry_descendPlaneFamily
  · exact planeExpPair_isLocalHomeomorph.continuous.comp <| by
      have hswap : Continuous (fun p : ℝ × Plane ↦ (p.2, p.1)) :=
        continuous_snd.prodMk continuous_fst
      exact G.continuous_planeFlow.comp hswap
  · intro t uv m n
    change planeExpPair (G.flow.flow (uv + planeDeckVector m n) t) =
      planeExpPair (G.flow.flow uv t)
    rw [G.planeFlow_add_planeDeckVector, planeExpPair_add_planeDeckVector]

theorem quotientFlow_zero (G : RegularBandNormalizedGradientFlowData B)
    (z : Circle × Circle) : G.quotientFlow 0 z = z := by
  obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
  rw [G.quotientFlow_planeExpPair, G.flow.flow_zero]

/-- The descended flow in transported-torus coordinates. -/
def transportedFlow (G : RegularBandNormalizedGradientFlowData B) :
    ℝ → transportedTorus Phi → transportedTorus Phi :=
  fun t x ↦ transportedTorusHomeomorph Phi <|
    G.quotientFlow t ((transportedTorusHomeomorph Phi).symm x)

theorem continuous_transportedFlow (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.transportedFlow) := by
  exact (transportedTorusHomeomorph Phi).continuous.comp <|
    G.continuous_quotientFlow.comp <|
      continuous_fst.prodMk
        ((transportedTorusHomeomorph Phi).symm.continuous.comp continuous_snd)

theorem transportedFlow_zero (G : RegularBandNormalizedGradientFlowData B)
    (x : transportedTorus Phi) : G.transportedFlow 0 x = x := by
  rw [transportedFlow, G.quotientFlow_zero,
    (transportedTorusHomeomorph Phi).apply_symm_apply]

theorem hasDerivAt_heightAlongPlaneFlow
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane) (t : ℝ) :
    HasDerivAt
      (fun s ↦ orientedCoordinateLift Phi frame 2 (G.flow.flow uv s))
      (G.fieldData.heightSpeed
        (orientedCoordinateLift Phi frame 2 (G.flow.flow uv t))) t := by
  have hheight : DifferentiableAt ℝ (orientedCoordinateLift Phi frame 2)
      (G.flow.flow uv t) :=
    (orientedCoordinateLift_contDiff Phi frame 2).differentiable
      (by simp) (G.flow.flow uv t)
  have hcomp := hheight.hasFDerivAt.comp_hasDerivAt t (G.flow.integral uv t)
  exact hcomp.congr_deriv (G.fieldData.fderiv_field_eq_heightSpeed _)

theorem heightSpeed_affine_eq_one
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane) {r : ℝ}
    (hr : r ∈ Icc 0 1)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    G.fieldData.heightSpeed
        (orientedCoordinateLift Phi frame 2 uv +
          r * (d - orientedCoordinateLift Phi frame 2 uv)) = 1 := by
  apply G.fieldData.heightSpeed_eq_one_of_mem_band
  let a := orientedCoordinateLift Phi frame 2 uv - d
  have hrewrite :
      orientedCoordinateLift Phi frame 2 uv +
          r * (d - orientedCoordinateLift Phi frame 2 uv) - d = (1 - r) * a := by
    dsimp only [a]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2)]
  have hone : 1 - r ≤ 1 := by linarith [hr.1]
  exact (mul_le_of_le_one_left (abs_nonneg a) hone).trans huv

theorem hasDerivAt_heightAlongPlaneFlow_mul
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane) (tau r : ℝ) :
    HasDerivAt
      (fun s ↦ orientedCoordinateLift Phi frame 2 (G.flow.flow uv (s * tau)))
      (tau * G.fieldData.heightSpeed
        (orientedCoordinateLift Phi frame 2 (G.flow.flow uv (r * tau)))) r := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s * tau) tau r :=
    by simpa using (hasDerivAt_id r).mul_const tau
  have hcomp := (G.hasDerivAt_heightAlongPlaneFlow uv (r * tau)).comp r hinner
  exact hcomp.congr_deriv (by ring)

private theorem lipschitzWith_const_mul_heightSpeed
    (G : RegularBandNormalizedGradientFlowData B) (tau : ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun y ↦ tau * G.fieldData.heightSpeed y) := by
  obtain ⟨K, hK⟩ := G.fieldData.exists_lipschitzWith_heightSpeed
  let tauNorm : ℝ≥0 := ⟨|tau|, abs_nonneg tau⟩
  refine ⟨tauNorm * K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg tau)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul]
  change |tau * G.fieldData.heightSpeed x - tau * G.fieldData.heightSpeed y| ≤
    (tauNorm : ℝ) * (K : ℝ) * |x - y|
  rw [show (tauNorm : ℝ) = |tau| by rfl, mul_assoc]
  rw [← mul_sub, abs_mul]
  simpa [Real.dist_eq] using h

/-- On the unit interpolation interval, the height of the actual flow agrees with the affine
height path.  This is the scalar Picard--Lindelöf comparison that avoids a first-exit argument. -/
theorem height_planeFlow_mul_eq_affine
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε)
    {r : ℝ} (hr : r ∈ Icc 0 1) :
    orientedCoordinateLift Phi frame 2
        (G.flow.flow uv (r * (d - orientedCoordinateLift Phi frame 2 uv))) =
      orientedCoordinateLift Phi frame 2 uv +
        r * (d - orientedCoordinateLift Phi frame 2 uv) := by
  let tau := d - orientedCoordinateLift Phi frame 2 uv
  let actual : ℝ → ℝ := fun s ↦
    orientedCoordinateLift Phi frame 2 (G.flow.flow uv (s * tau))
  let affine : ℝ → ℝ := fun s ↦
    orientedCoordinateLift Phi frame 2 uv + s * tau
  obtain ⟨K, hK⟩ := G.lipschitzWith_const_mul_heightSpeed tau
  have heq : Set.EqOn actual affine (Icc 0 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y ↦ tau * G.fieldData.heightSpeed y)
      (s := fun _ ↦ Set.univ) (K := K)
    · intro _ _
      exact hK.lipschitzOnWith
    · change ContinuousOn actual (Icc 0 1)
      exact ((orientedCoordinateLift_contDiff Phi frame 2).continuous.comp <|
        (G.flow.integral uv).continuous.comp
          (continuous_id.mul continuous_const)).continuousOn
    · intro s _
      exact (G.hasDerivAt_heightAlongPlaneFlow_mul uv tau s).hasDerivWithinAt
    · simp
    · exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    · intro s hs
      have hspeed : G.fieldData.heightSpeed (affine s) = 1 := by
        exact G.heightSpeed_affine_eq_one uv ⟨hs.1, hs.2.le⟩ huv
      have hderiv : HasDerivAt affine tau s := by
        change HasDerivAt (fun q : ℝ ↦
          orientedCoordinateLift Phi frame 2 uv + q * tau) tau s
        simpa using ((hasDerivAt_id s).mul_const tau).const_add
          (orientedCoordinateLift Phi frame 2 uv)
      exact hderiv.congr_deriv (by simp [hspeed]) |>.hasDerivWithinAt
    · simp
    · simp [actual, affine, tau, G.flow.flow_zero]
  exact heq hr

theorem height_planeFlow_to_center
    (G : RegularBandNormalizedGradientFlowData B) (uv : Plane)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    orientedCoordinateLift Phi frame 2
        (G.flow.flow uv (d - orientedCoordinateLift Phi frame 2 uv)) = d := by
  simpa using G.height_planeFlow_mul_eq_affine uv huv (r := 1) (by simp)

/-- Clamp an arbitrary homotopy parameter to the unit interval. -/
def clampedUnit (u : ℝ) : ℝ := Set.projIcc 0 1 zero_le_one u

theorem clampedUnit_mem (u : ℝ) : clampedUnit u ∈ Icc 0 1 :=
  (Set.projIcc 0 1 zero_le_one u).property

theorem continuous_clampedUnit : Continuous clampedUnit :=
  continuous_subtype_val.comp continuous_projIcc

@[simp]
theorem clampedUnit_zero : clampedUnit 0 = 0 := by
  rw [clampedUnit, Set.projIcc_left]

@[simp]
theorem clampedUnit_one : clampedUnit 1 = 1 := by
  rw [clampedUnit, Set.projIcc_right]

/-- The planar deformation moves each point for the fraction `clampedUnit u` of the time needed
to reach the central height. -/
def planeRetraction (G : RegularBandNormalizedGradientFlowData B)
    (u : ℝ) (uv : Plane) : Plane :=
  G.flow.flow uv
    (clampedUnit u * (d - orientedCoordinateLift Phi frame 2 uv))

theorem planeRetraction_add_planeDeckVector
    (G : RegularBandNormalizedGradientFlowData B)
    (u : ℝ) (uv : Plane) (m n : ℤ) :
    G.planeRetraction u (uv + planeDeckVector m n) =
      G.planeRetraction u uv + planeDeckVector m n := by
  rw [planeRetraction, planeRetraction,
    orientedCoordinateLift_add_planeDeckVector,
    G.planeFlow_add_planeDeckVector]

theorem continuous_uncurry_planeRetraction
    (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.planeRetraction) := by
  have hinput : Continuous (fun p : ℝ × Plane ↦
      (p.2, clampedUnit p.1 *
        (d - orientedCoordinateLift Phi frame 2 p.2))) :=
    continuous_snd.prodMk <|
    (continuous_clampedUnit.comp continuous_fst).mul <|
      continuous_const.sub <|
        (orientedCoordinateLift_contDiff Phi frame 2).continuous.comp continuous_snd
  change Continuous (Function.uncurry G.flow.flow ∘ fun p : ℝ × Plane ↦
    (p.2, clampedUnit p.1 * (d - orientedCoordinateLift Phi frame 2 p.2)))
  exact G.continuous_planeFlow.comp hinput

/-- The clamped retraction descended to the product torus. -/
def quotientRetraction (G : RegularBandNormalizedGradientFlowData B) :
    ℝ → Circle × Circle → Circle × Circle :=
  descendPlaneFamily fun u uv ↦ planeExpPair (G.planeRetraction u uv)

theorem quotientRetraction_planeExpPair
    (G : RegularBandNormalizedGradientFlowData B) (u : ℝ) (uv : Plane) :
    G.quotientRetraction u (planeExpPair uv) =
      planeExpPair (G.planeRetraction u uv) := by
  apply descendPlaneFamily_planeExpPair
  intro s wz m n
  change planeExpPair (G.planeRetraction s (wz + planeDeckVector m n)) =
    planeExpPair (G.planeRetraction s wz)
  rw [G.planeRetraction_add_planeDeckVector,
    planeExpPair_add_planeDeckVector]

theorem continuous_quotientRetraction
    (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.quotientRetraction) := by
  apply continuous_uncurry_descendPlaneFamily
  · exact planeExpPair_isLocalHomeomorph.continuous.comp
      G.continuous_uncurry_planeRetraction
  · intro u uv m n
    change planeExpPair (G.planeRetraction u (uv + planeDeckVector m n)) =
      planeExpPair (G.planeRetraction u uv)
    rw [G.planeRetraction_add_planeDeckVector,
      planeExpPair_add_planeDeckVector]

theorem quotientRetraction_zero
    (G : RegularBandNormalizedGradientFlowData B) (z : Circle × Circle) :
    G.quotientRetraction 0 z = z := by
  obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
  rw [G.quotientRetraction_planeExpPair, planeRetraction,
    clampedUnit_zero, zero_mul, G.flow.flow_zero]

/-- The clamped central-fiber retraction on the transported torus. -/
def transportedRetraction (G : RegularBandNormalizedGradientFlowData B) :
    ℝ → transportedTorus Phi → transportedTorus Phi :=
  fun u x ↦ transportedTorusHomeomorph Phi <|
    G.quotientRetraction u ((transportedTorusHomeomorph Phi).symm x)

theorem continuous_transportedRetraction
    (G : RegularBandNormalizedGradientFlowData B) :
    Continuous (Function.uncurry G.transportedRetraction) := by
  exact (transportedTorusHomeomorph Phi).continuous.comp <|
    G.continuous_quotientRetraction.comp <|
      continuous_fst.prodMk
        ((transportedTorusHomeomorph Phi).symm.continuous.comp continuous_snd)

/-- Continuity of the transported retraction at a fixed homotopy parameter. -/
theorem continuous_transportedRetraction_fixed
    (G : RegularBandNormalizedGradientFlowData B) (u : ℝ) :
    Continuous (G.transportedRetraction u) := by
  change Continuous (fun x : transportedTorus Phi ↦
    transportedTorusHomeomorph Phi <|
      G.quotientRetraction u ((transportedTorusHomeomorph Phi).symm x))
  exact (transportedTorusHomeomorph Phi).continuous.comp <|
    G.continuous_quotientRetraction.comp <|
      continuous_const.prodMk (transportedTorusHomeomorph Phi).symm.continuous

/-- Continuity of a linearly reparametrized transported trajectory. -/
theorem continuous_transportedRetraction_mul
    (G : RegularBandNormalizedGradientFlowData B)
    (u : ℝ) (x : transportedTorus Phi) :
    Continuous (fun s ↦ G.transportedRetraction (s * u) x) := by
  change Continuous (fun s : ℝ ↦ transportedTorusHomeomorph Phi <|
    G.quotientRetraction (s * u) ((transportedTorusHomeomorph Phi).symm x))
  exact (transportedTorusHomeomorph Phi).continuous.comp <|
    G.continuous_quotientRetraction.comp <|
      (continuous_id.mul continuous_const).prodMk continuous_const

theorem transportedRetraction_zero
    (G : RegularBandNormalizedGradientFlowData B) (x : transportedTorus Phi) :
    G.transportedRetraction 0 x = x := by
  rw [transportedRetraction, G.quotientRetraction_zero,
    (transportedTorusHomeomorph Phi).apply_symm_apply]

theorem torusLongCoordinate_quotientRetraction_planeExpPair
    (G : RegularBandNormalizedGradientFlowData B) (u : ℝ) (uv : Plane)
    (huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε) :
    torusLongCoordinate Phi frame
        (G.quotientRetraction u (planeExpPair uv)) =
      orientedCoordinateLift Phi frame 2 uv + clampedUnit u *
        (d - orientedCoordinateLift Phi frame 2 uv) := by
  rw [G.quotientRetraction_planeExpPair,
    ← orientedCoordinateLift_eq_torusLongCoordinate_expPair]
  exact G.height_planeFlow_mul_eq_affine uv huv (clampedUnit_mem u)

theorem quotientRetraction_mem_closedBand
    (G : RegularBandNormalizedGradientFlowData B) (u : ℝ)
    {z : Circle × Circle}
    (hz : z ∈ coordinateTorusClosedRegularBand Phi frame d B.ε) :
    G.quotientRetraction u z ∈ coordinateTorusClosedRegularBand Phi frame d B.ε := by
  obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
  have huv : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε := by
    rwa [orientedCoordinateLift_eq_torusLongCoordinate_expPair]
  rw [coordinateTorusClosedRegularBand, mem_ofPred_eq,
    G.torusLongCoordinate_quotientRetraction_planeExpPair u uv huv]
  let r := clampedUnit u
  have hr := clampedUnit_mem u
  have hrewrite : orientedCoordinateLift Phi frame 2 uv +
      r * (d - orientedCoordinateLift Phi frame 2 uv) - d =
        (1 - r) * (orientedCoordinateLift Phi frame 2 uv - d) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2)]
  have hone : 1 - r ≤ 1 := by linarith [hr.1]
  exact (mul_le_of_le_one_left
    (abs_nonneg (orientedCoordinateLift Phi frame 2 uv - d))
    hone).trans huv

theorem transportedRetraction_mem_closedBand
    (G : RegularBandNormalizedGradientFlowData B) (u : ℝ)
    {x : transportedTorus Phi} (hx : x ∈ B.transportedClosedBand) :
    G.transportedRetraction u x ∈ B.transportedClosedBand := by
  change (transportedTorusHomeomorph Phi).symm (G.transportedRetraction u x) ∈
    coordinateTorusClosedRegularBand Phi frame d B.ε
  rw [transportedRetraction, (transportedTorusHomeomorph Phi).symm_apply_apply]
  exact G.quotientRetraction_mem_closedBand u hx

theorem torusLongCoordinate_transportedRetraction_one
    (G : RegularBandNormalizedGradientFlowData B)
    {x : transportedTorus Phi} (hx : x ∈ B.transportedClosedBand) :
    torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm (G.transportedRetraction 1 x)) = d := by
  obtain ⟨uv, huv⟩ := planeExpPair_surjective
    ((transportedTorusHomeomorph Phi).symm x)
  have huvBand : |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * B.ε := by
    change |torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm x) - d| ≤ 2 * B.ε at hx
    rw [← huv, ← orientedCoordinateLift_eq_torusLongCoordinate_expPair] at hx
    exact hx
  rw [transportedRetraction,
    (transportedTorusHomeomorph Phi).symm_apply_apply]
  rw [← huv]
  have hheight :=
    G.torusLongCoordinate_quotientRetraction_planeExpPair 1 uv huvBand
  rw [clampedUnit_one] at hheight
  calc
    torusLongCoordinate Phi frame (G.quotientRetraction 1 (planeExpPair uv)) =
        orientedCoordinateLift Phi frame 2 uv +
          (d - orientedCoordinateLift Phi frame 2 uv) := by simpa using hheight
    _ = d := by ring

/-- The clamped trajectory from a point stays in its connected band component. -/
theorem transportedRetraction_mem_closedBandComponent
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (_hbase : base ∈ B.transportedClosedBand)
    (u : ℝ) {x : transportedTorus Phi} (hx : x ∈ B.closedBandComponent base) :
    G.transportedRetraction u x ∈ B.closedBandComponent base := by
  have hxBand : x ∈ B.transportedClosedBand := B.closedBandComponent_subset base hx
  change G.transportedRetraction u x ∈ connectedComponentIn B.transportedClosedBand base
  rw [connectedComponentIn_eq hx]
  apply mem_connectedComponentIn_of_continuous_Icc_path
    (p := fun s ↦ G.transportedRetraction (s * u) x)
  · exact G.continuous_transportedRetraction_mul u x
  · simpa using G.transportedRetraction_zero x
  · simp
  · intro s hs
    exact G.transportedRetraction_mem_closedBand (s * u) hxBand

/-- Central-level point reached from a point of the closed band. -/
def centralEndpointLevelPoint
    (G : RegularBandNormalizedGradientFlowData B)
    (x : transportedTorus Phi) (hx : x ∈ B.transportedClosedBand) :
    coordinateTorusLevelSet Phi frame d :=
  ⟨(transportedTorusHomeomorph Phi).symm (G.transportedRetraction 1 x),
    G.torusLongCoordinate_transportedRetraction_one hx⟩

/-- The endpoint map restricted to one connected band component. -/
def centralEndpointOnComponent
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) :
    B.closedBandComponent base → coordinateTorusLevelSet Phi frame d :=
  fun x ↦ G.centralEndpointLevelPoint x <|
    B.closedBandComponent_subset base x.property

theorem continuous_centralEndpointOnComponent
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) :
    Continuous (G.centralEndpointOnComponent base) := by
  apply Continuous.subtype_mk
  have hendpoint : Continuous (fun x : B.closedBandComponent base ↦
      G.transportedRetraction 1 x.1) :=
    (G.continuous_transportedRetraction_fixed 1).comp continuous_subtype_val
  exact (transportedTorusHomeomorph Phi).symm.continuous.comp hendpoint

theorem centralEndpointOnComponent_mem_componentPiece
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand)
    (x : B.closedBandComponent base) :
    G.centralEndpointOnComponent base x ∈
      componentPiece (ConnectedComponents.mk
        (G.centralEndpointLevelPoint base hbase)) := by
  let _ : PreconnectedSpace (B.closedBandComponent base) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
  let endpoint := G.centralEndpointOnComponent base
  have hpre : IsPreconnected (Set.range endpoint) :=
    isPreconnected_range (G.continuous_centralEndpointOnComponent base)
  let basePoint : B.closedBandComponent base :=
    ⟨base, mem_connectedComponentIn hbase⟩
  have hbaseRange : endpoint basePoint ∈ Set.range endpoint := ⟨basePoint, rfl⟩
  have hxRange : endpoint x ∈ Set.range endpoint := ⟨x, rfl⟩
  have hxConnected : endpoint x ∈ connectedComponent (endpoint basePoint) :=
    hpre.subset_connectedComponent hbaseRange hxRange
  change ConnectedComponents.mk (endpoint x) =
    ConnectedComponents.mk (G.centralEndpointLevelPoint base hbase)
  have hbasePoint : endpoint basePoint = G.centralEndpointLevelPoint base hbase := by
    rfl
  rw [← hbasePoint]
  exact ConnectedComponents.coe_eq_coe'.mpr hxConnected

/-- The canonical central regular-fiber circle through the endpoint of the base point. -/
def centralCore
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand) :
    EmbeddedTorusIntersectionCircle Phi :=
  B.embeddedCentralCircleThrough (G.transportedRetraction 1 base)
    (G.torusLongCoordinate_transportedRetraction_one hbase)

theorem transportedRetraction_one_mem_centralCore
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand)
    {x : transportedTorus Phi} (hx : x ∈ B.closedBandComponent base) :
    (G.transportedRetraction 1 x : R3) ∈ Set.range (G.centralCore base hbase).circle := by
  rw [centralCore, OrientedCoordinateRegularBandData.embeddedCentralCircleThrough,
    B.range_embeddedCentralCircle]
  let xComponent : B.closedBandComponent base := ⟨x, hx⟩
  let z := G.centralEndpointOnComponent base xComponent
  refine ⟨z, G.centralEndpointOnComponent_mem_componentPiece base hbase xComponent, ?_⟩
  change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm (G.transportedRetraction 1 x)) =
    (G.transportedRetraction 1 x : R3)
  exact congrArg Subtype.val <|
    (transportedTorusHomeomorph Phi).apply_symm_apply
      (G.transportedRetraction 1 x)

theorem centralCore_windingLoop_mem_closedBand
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand)
    (t : ℝ) :
    (G.centralCore base hbase).windingLoop.curve t ∈ B.transportedClosedBand := by
  let core := G.centralCore base hbase
  have hcircle : core.circle (Circle.exp t) ∈ Set.range core.circle :=
    ⟨Circle.exp t, rfl⟩
  dsimp only [core] at hcircle
  rw [centralCore, OrientedCoordinateRegularBandData.embeddedCentralCircleThrough,
    B.range_embeddedCentralCircle] at hcircle
  obtain ⟨z, _hzComponent, hzCircle⟩ := hcircle
  change |torusLongCoordinate Phi frame
      ((transportedTorusHomeomorph Phi).symm (core.windingLoop.curve t)) - d| ≤
        2 * B.ε
  have hcoordinates :
      (transportedTorusHomeomorph Phi).symm (core.windingLoop.curve t) = z.1 := by
    apply transportedTorusMap_injective Phi
    calc
      transportedTorusMap Phi
          ((transportedTorusHomeomorph Phi).symm (core.windingLoop.curve t)) =
          (core.windingLoop.curve t : R3) := congrArg Subtype.val <|
        (transportedTorusHomeomorph Phi).apply_symm_apply (core.windingLoop.curve t)
      _ = core.circle (Circle.exp t) := (core.parametrization t).symm
      _ = transportedTorusMap Phi z.1 := hzCircle.symm
  rw [hcoordinates, z.property, sub_self, abs_zero]
  exact mul_nonneg (by norm_num) B.ε_pos.le

theorem centralCore_windingLoop_mem_component
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand)
    (t : ℝ) :
    (G.centralCore base hbase).windingLoop.curve t ∈ B.closedBandComponent base := by
  let core := G.centralCore base hbase
  let loopRange : Set (transportedTorus Phi) := Set.range core.windingLoop.curve
  have hpre : IsPreconnected loopRange :=
    (isConnected_range core.windingLoop.continuous_curve).isPreconnected
  have hsubset : loopRange ⊆ B.transportedClosedBand := by
    rintro _ ⟨s, rfl⟩
    exact G.centralCore_windingLoop_mem_closedBand base hbase s
  have hendpointCircle := G.transportedRetraction_one_mem_centralCore
    base hbase (mem_connectedComponentIn hbase)
  obtain ⟨z, hz⟩ := hendpointCircle
  obtain ⟨s, hs⟩ := Circle.exp_surjective z
  have hendpointLoop : G.transportedRetraction 1 base ∈ loopRange := by
    refine ⟨s, Subtype.ext ?_⟩
    rw [← core.parametrization s, hs]
    exact hz
  have hloopEndpointComponent : loopRange ⊆
      connectedComponentIn B.transportedClosedBand (G.transportedRetraction 1 base) :=
    hpre.subset_connectedComponentIn hendpointLoop hsubset
  have hendpointComponent : G.transportedRetraction 1 base ∈
      B.closedBandComponent base :=
    G.transportedRetraction_mem_closedBandComponent base hbase 1
      (mem_connectedComponentIn hbase)
  change (G.centralCore base hbase).windingLoop.curve t ∈
    connectedComponentIn B.transportedClosedBand base
  rw [connectedComponentIn_eq hendpointComponent]
  exact hloopEndpointComponent ⟨t, rfl⟩

/-- The complete normalized-gradient flow supplies the required cyclic deformation on one band
component. -/
def componentCyclicRetractionData
    (G : RegularBandNormalizedGradientFlowData B)
    (base : transportedTorus Phi) (hbase : base ∈ B.transportedClosedBand) :
    RegularBandComponentCyclicRetractionData B base where
  base_mem := hbase
  core := G.centralCore base hbase
  core_mem_component := G.centralCore_windingLoop_mem_component base hbase
  deformation := G.transportedRetraction
  continuous_deformation := G.continuous_transportedRetraction
  deformation_mem_component := fun u _x hx ↦
    G.transportedRetraction_mem_closedBandComponent base hbase u hx
  deformation_zero := fun x _ ↦ G.transportedRetraction_zero x
  deformation_one_mem_core := fun _ hx ↦
    G.transportedRetraction_one_mem_centralCore base hbase hx

end RegularBandNormalizedGradientFlowData

/-- The compact regular band canonically supplies a complete normalized-gradient flow. -/
theorem exists_regularBandNormalizedGradientFlowData
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    Nonempty (RegularBandNormalizedGradientFlowData B) := by
  let D := Classical.choice (exists_regularBandNormalizedGradientFieldData B)
  let F := Classical.choice <|
    exists_completePlaneIntegralFlow_of_isPlaneDeckPeriodic
      D.contDiff_field D.isPlaneDeckPeriodic
  exact ⟨{ fieldData := D, flow := F }⟩

/-- Every connected component of an oriented-coordinate regular band retracts onto its canonical
central regular-fiber circle. -/
theorem orientedCoordinateRegularBandCyclicRetractionData
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    OrientedCoordinateRegularBandCyclicRetractionData B := by
  let G := Classical.choice (exists_regularBandNormalizedGradientFlowData B)
  exact {
    componentRetraction := fun base hbase ↦
      ⟨G.componentCyclicRetractionData base hbase⟩
  }

end Submission.Topology
