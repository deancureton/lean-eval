import Submission.Coarea.SuperellipsoidSeamFubini
import Submission.Coarea.SuperellipsoidSeamSard
import Submission.Topology.SuperellipsoidBarrierGraph

/-!
# A uniform regular-height band on an outer superellipsoid seam

Transversality at one cutting height is open uniformly along the compact outer section of the
transported torus.  We prove this in covering coordinates: determinant-critical points in one
fundamental square form a compact set, so their height image is compact and misses the selected
regular height.  Deck invariance promotes the resulting margin to the whole covering plane.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- Determinant-critical points on one outer level in the closed fundamental square. -/
def fundamentalSuperellipsoidSeamCriticalSet
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set Plane :=
  fundamentalSquare ∩
    (superellipsoidPolynomialLift Phi frame c) ⁻¹' {R ^ 256} ∩
      {uv | (fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv).det = 0}

theorem isCompact_fundamentalSuperellipsoidSeamCriticalSet
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsCompact (fundamentalSuperellipsoidSeamCriticalSet Phi frame c R) := by
  have hdet : Continuous fun uv : Plane ↦
      (fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv).det :=
    ContinuousLinearMap.continuous_det.comp
      ((contDiff_superellipsoidSeamPairMap Phi frame c).continuous_fderiv (by simp))
  exact (isCompact_fundamentalSquare.inter_right
    (isClosed_singleton.preimage
      (contDiff_superellipsoidPolynomialLift Phi frame c).continuous)).inter_right
        (isClosed_singleton.preimage hdet)

/-- Critical cutting heights attained on the fundamental outer seam. -/
def fundamentalSuperellipsoidSeamCriticalValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set ℝ :=
  orientedCoordinateLift Phi frame 2 ''
    fundamentalSuperellipsoidSeamCriticalSet Phi frame c R

theorem isCompact_fundamentalSuperellipsoidSeamCriticalValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsCompact (fundamentalSuperellipsoidSeamCriticalValues Phi frame c R) :=
  (isCompact_fundamentalSuperellipsoidSeamCriticalSet Phi frame c R).image
    (orientedCoordinateLift_contDiff Phi frame 2).continuous

/-- A positive uniform band of transverse cutting heights on one fixed outer section. -/
structure SuperellipsoidSeamRegularBandData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) where
  ε : ℝ
  ε_pos : 0 < ε
  regular : ∀ y, |y - d| ≤ 2 * ε →
    IsRegularSuperellipsoidSeamHeight Phi frame c R y

namespace SuperellipsoidSeamRegularBandData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}

/-- The lower endpoint of a seam-regular band is transverse. -/
theorem lowerRegular (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    IsRegularSuperellipsoidSeamHeight Phi frame c R (d - B.ε) := by
  apply B.regular
  rw [sub_sub_cancel_left, abs_neg, abs_of_pos B.ε_pos]
  linarith [B.ε_pos]

/-- The upper endpoint of a seam-regular band is transverse. -/
theorem upperRegular (B : SuperellipsoidSeamRegularBandData Phi frame c R d) :
    IsRegularSuperellipsoidSeamHeight Phi frame c R (d + B.ε) := by
  apply B.regular
  rw [add_sub_cancel_left, abs_of_pos B.ε_pos]
  linarith [B.ε_pos]

end SuperellipsoidSeamRegularBandData

/-- Compactness gives a positive band of transverse heights around any transverse seam cut. -/
theorem exists_superellipsoidSeamRegularBandData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hd : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    Nonempty (SuperellipsoidSeamRegularBandData Phi frame c R d) := by
  let criticalValues := fundamentalSuperellipsoidSeamCriticalValues Phi frame c R
  have hcompact : IsCompact criticalValues :=
    isCompact_fundamentalSuperellipsoidSeamCriticalValues Phi frame c R
  have hdNot : d ∉ criticalValues := by
    rintro ⟨uv, huv, huvHeight⟩
    have hlevel := huv.1.2
    have hdetPair := huv.2
    have hdet : planarDifferentialDet
        (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) uv = 0 := by
      rw [← det_fderiv_superellipsoidSeamPairMap Phi frame c uv]
      exact hdetPair
    exact hd uv hlevel huvHeight hdet
  have hopen : IsOpen criticalValuesᶜ := hcompact.isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen d hdNot
  let ε := δ / 3
  have hε : 0 < ε := div_pos hδ (by norm_num)
  refine ⟨{
    ε := ε
    ε_pos := hε
    regular := ?_ }⟩
  intro y hy uv huvLevel huvHeight huvDet
  let representative := planeFundamentalRepresentative uv
  let index := planeFundamentalDeckIndex uv
  have hrepLevel : superellipsoidPolynomialLift Phi frame c representative = R ^ 256 := by
    rw [superellipsoidPolynomialLift_planeFundamentalRepresentative]
    exact huvLevel
  have hrepHeight : orientedCoordinateLift Phi frame 2 representative = y := by
    rw [orientedCoordinateLift_planeFundamentalRepresentative]
    exact huvHeight
  have hrepDet : planarDifferentialDet
      (superellipsoidPolynomialLift Phi frame c)
      (orientedCoordinateLift Phi frame 2) representative = 0 := by
    have hperiodic := planarDifferentialDet_superellipsoid_add_planeDeckVector
      Phi frame c index.1 index.2 representative
    rw [planeFundamentalRepresentative_add_deck] at hperiodic
    exact hperiodic.symm.trans huvDet
  apply hball
  · rw [mem_ball, Real.dist_eq]
    dsimp [ε] at hy
    linarith
  · refine ⟨representative, ⟨⟨
      planeFundamentalRepresentative_mem_fundamentalSquare uv, hrepLevel⟩, ?_⟩, hrepHeight⟩
    change (fderiv ℝ (superellipsoidSeamPairMap Phi frame c) representative).det = 0
    rw [det_fderiv_superellipsoidSeamPairMap]
    exact hrepDet

end Submission.Topology
