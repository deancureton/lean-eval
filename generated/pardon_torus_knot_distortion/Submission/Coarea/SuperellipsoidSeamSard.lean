import Submission.Coarea.SuperellipsoidCutSelection

/-!
# One-dimensional Sard data for a regular superellipsoid seam

The intersection of a regular outer superellipsoid with the transported torus is a compact
one-manifold.  The geometric decomposition still needed downstream is precisely a finite family
of smooth integral-curve charts whose height branches cover every critical seam height.  Once
that honest chart contract is available, ordinary one-dimensional Sard proves the required
nullity immediately.  This avoids putting nullity itself, or the desired cut, into the contract.
-/

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology
open Submission.SurfaceRegularValue

/-- Along a rotated-gradient integral curve of `f`, the derivative of `g` is exactly the
determinant of their two planar differentials. -/
lemma hasDerivAt_comp_rotatedDerivativeField
    {f g : Plane → ℝ} {γ : ℝ → Plane} {t : ℝ}
    (hg : DifferentiableAt ℝ g (γ t))
    (hγ : HasDerivAt γ (rotatedDerivativeField f (γ t)) t) :
    HasDerivAt (g ∘ γ) (planarDifferentialDet f g (γ t)) t := by
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt t hγ
  have heval :
      fderiv ℝ g (γ t) (rotatedDerivativeField f (γ t)) =
        planarDifferentialDet f g (γ t) := by
    rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, planarDifferentialDet]
    ring
  rwa [heval] at hcomp

/-- The outer polynomial lift is invariant under all deck translations. -/
lemma superellipsoidPolynomialLift_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (m n : ℤ) (uv : Plane) :
    superellipsoidPolynomialLift Phi frame c (uv + planeDeckVector m n) =
      superellipsoidPolynomialLift Phi frame c uv := by
  unfold superellipsoidPolynomialLift
  rw [show uv + planeDeckVector m n =
      (uv.1 + (m : ℝ) * (2 * Real.pi),
        uv.2 + (n : ℝ) * (2 * Real.pi)) by
    ext <;> rfl]
  rw [transportedTorusPlaneMap_add_int_periods]

/-- Its planar differential is likewise deck invariant. -/
lemma fderiv_superellipsoidPolynomialLift_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (m n : ℤ) (uv : Plane) :
    fderiv ℝ (superellipsoidPolynomialLift Phi frame c)
        (uv + planeDeckVector m n) =
      fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv := by
  let deck := planeDeckVector m n
  have hfun :
      (fun z ↦ superellipsoidPolynomialLift Phi frame c (z + deck)) =
        superellipsoidPolynomialLift Phi frame c := by
    funext z
    exact superellipsoidPolynomialLift_add_planeDeckVector Phi frame c m n z
  calc
    fderiv ℝ (superellipsoidPolynomialLift Phi frame c) (uv + deck) =
        fderiv ℝ
          (fun z ↦ superellipsoidPolynomialLift Phi frame c (z + deck)) uv :=
      (fderiv_comp_add_right deck).symm
    _ = fderiv ℝ (superellipsoidPolynomialLift Phi frame c) uv :=
      congrArg (fun g : Plane → ℝ ↦ fderiv ℝ g uv) hfun

/-- The determinant detecting critical cutting heights descends to the quotient torus. -/
lemma planarDifferentialDet_superellipsoid_add_planeDeckVector
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (m n : ℤ) (uv : Plane) :
    planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) (uv + planeDeckVector m n) =
      planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) uv := by
  simp only [planarDifferentialDet,
    fderiv_superellipsoidPolynomialLift_add_planeDeckVector,
    fderiv_orientedCoordinateLift_add_planeDeckVector]

/-- A finite smooth chart cover of the critical part of one regular outer seam.

The curves are intended to be the cyclic parametrizations of the rotated-gradient orbits of the
outer polynomial level.  `covers` asks only for the exact output of that geometric construction:
every critical seam point has the same cutting height as a determinant-critical point on one of
the finitely many integral curves. -/
structure FiniteSuperellipsoidSeamCriticalChartCover
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) where
  branchCount : ℕ
  curve : Fin branchCount → ℝ → Plane
  curve_contDiff : ∀ i, ContDiff ℝ 1 (curve i)
  curve_level : ∀ i t,
    superellipsoidPolynomialLift Phi frame c (curve i t) = R ^ 256
  curve_integral : ∀ i t, HasDerivAt (curve i)
    (rotatedDerivativeField (superellipsoidPolynomialLift Phi frame c) (curve i t)) t
  covers : ∀ uv, uv ∈ superellipsoidSeamHeightCriticalPoints Phi frame c R →
    ∃ (i : Fin branchCount) (t : ℝ),
      orientedCoordinateLift Phi frame 2 uv =
        orientedCoordinateLift Phi frame 2 (curve i t) ∧
      planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) (curve i t) = 0

/-- A geometric finite-orbit decomposition of the whole lifted seam modulo deck translation.
This is the natural output of compact regular-level classification on `Circle × Circle`. -/
structure FiniteSuperellipsoidSeamOrbitCover
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) where
  branchCount : ℕ
  curve : Fin branchCount → ℝ → Plane
  curve_contDiff : ∀ i, ContDiff ℝ 1 (curve i)
  curve_level : ∀ i t,
    superellipsoidPolynomialLift Phi frame c (curve i t) = R ^ 256
  curve_integral : ∀ i t, HasDerivAt (curve i)
    (rotatedDerivativeField (superellipsoidPolynomialLift Phi frame c) (curve i t)) t
  quotient_covers : ∀ uv,
    superellipsoidPolynomialLift Phi frame c uv = R ^ 256 →
      ∃ (i : Fin branchCount) (t : ℝ) (m n : ℤ),
        curve i t = uv + planeDeckVector m n

namespace FiniteSuperellipsoidSeamOrbitCover

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}

/-- A finite cover of the full regular seam modulo deck translations supplies the narrower
critical-height chart contract automatically. -/
def toCriticalChartCover
    (O : FiniteSuperellipsoidSeamOrbitCover Phi frame c R) :
    FiniteSuperellipsoidSeamCriticalChartCover Phi frame c R where
  branchCount := O.branchCount
  curve := O.curve
  curve_contDiff := O.curve_contDiff
  curve_level := O.curve_level
  curve_integral := O.curve_integral
  covers := by
    rintro uv ⟨hlevel, hdet⟩
    obtain ⟨i, t, m, n, hcurve⟩ := O.quotient_covers uv hlevel
    refine ⟨i, t, ?_, ?_⟩
    · rw [hcurve, orientedCoordinateLift_add_planeDeckVector]
    · rw [hcurve, planarDifferentialDet_superellipsoid_add_planeDeckVector]
      exact hdet

end FiniteSuperellipsoidSeamOrbitCover

namespace FiniteSuperellipsoidSeamCriticalChartCover

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}

/-- The height function along one smooth seam chart. -/
def heightBranch
    (C : FiniteSuperellipsoidSeamCriticalChartCover Phi frame c R)
    (i : Fin C.branchCount) : ℝ → ℝ :=
  orientedCoordinateLift Phi frame 2 ∘ C.curve i

lemma heightBranch_contDiff
    (C : FiniteSuperellipsoidSeamCriticalChartCover Phi frame c R)
    (i : Fin C.branchCount) :
    ContDiff ℝ 1 (C.heightBranch i) := by
  exact ((orientedCoordinateLift_contDiff Phi frame 2).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp (C.curve_contDiff i)

/-- Critical seam heights lie in the finite union of ordinary one-dimensional critical-value
sets of the chart height branches. -/
lemma criticalValues_subset_iUnion
    (C : FiniteSuperellipsoidSeamCriticalChartCover Phi frame c R) :
    superellipsoidSeamHeightCriticalValues Phi frame c R ⊆
      ⋃ i : Fin C.branchCount, Submission.Coarea.criticalValues (C.heightBranch i) := by
  rintro d ⟨uv, huv, rfl⟩
  obtain ⟨i, t, hheight, hdet⟩ := C.covers uv huv
  refine mem_iUnion.2 ⟨i, ?_⟩
  refine ⟨t, ?_, ?_⟩
  · have hderiv := hasDerivAt_comp_rotatedDerivativeField
      ((orientedCoordinateLift_contDiff Phi frame 2).differentiable
        (by simp) (C.curve i t)) (C.curve_integral i t)
    rw [hdet] at hderiv
    exact hderiv.deriv
  exact hheight.symm

/-- The finite chart contract implies nullity of all critical seam heights by one-dimensional
Sard, with no further regularity assumption. -/
theorem criticalValues_volume_eq_zero
    (C : FiniteSuperellipsoidSeamCriticalChartCover Phi frame c R) :
    volume (superellipsoidSeamHeightCriticalValues Phi frame c R) = 0 := by
  apply measure_mono_null C.criticalValues_subset_iUnion
  exact measure_iUnion_null fun i ↦
    Submission.Coarea.volume_criticalValues_eq_zero (C.heightBranch_contDiff i)

end FiniteSuperellipsoidSeamCriticalChartCover

/-- The regular cut selector, now with the seam nullity discharged from finite smooth chart data. -/
theorem exists_superellipsoidRegularCutSelection_of_seamChartCover
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r))
    (outer : SuperellipsoidOuterSelection K Phi frame c r)
    (charts : FiniteSuperellipsoidSeamCriticalChartCover
      Phi frame c outer.scale) :
    Nonempty (SuperellipsoidRegularCutSelection K Phi frame c r
      (distortion K).toReal W outer) := by
  exact exists_superellipsoidRegularCutSelection_of_seamCriticalValues_null
    K Phi frame c hr hfinite W outer charts.criticalValues_volume_eq_zero

end Submission.PardonDistortion
