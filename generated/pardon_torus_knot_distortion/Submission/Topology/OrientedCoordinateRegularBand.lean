import Submission.Topology.RegularLevelQuotientCharts
import Submission.Topology.RegularLevelTangentODE

/-!
# A uniform regular band around a regular transported-torus height

Regularity on one fiber and compactness of the covering-plane fundamental square separate the
chosen height from all critical values attained in that square.  Periodicity then promotes the
result to every covering-plane lift, producing a closed torus band on which the lifted
differential is nowhere zero.  This is the compact analytic input for a later normalized-gradient
or product-annulus construction; no noncarrier conclusion is asserted here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- Critical points restricted to one closed fundamental square. -/
def fundamentalCriticalSet (f : Plane → ℝ) : Set Plane :=
  fundamentalSquare ∩ criticalPoints f

theorem isCompact_fundamentalCriticalSet {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : IsCompact (fundamentalCriticalSet f) := by
  apply isCompact_fundamentalSquare.inter_right
  exact isClosed_singleton.preimage (hf.continuous_fderiv (by simp))

/-- Critical values attained in one fundamental square form a compact subset of the line. -/
def fundamentalCriticalValues (f : Plane → ℝ) : Set ℝ :=
  f '' fundamentalCriticalSet f

theorem isCompact_fundamentalCriticalValues {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : IsCompact (fundamentalCriticalValues f) :=
  (isCompact_fundamentalCriticalSet hf).image hf.continuous

/-- The closed height band on the product-circle model of the transported torus. -/
def coordinateTorusClosedRegularBand
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d ε : ℝ) :
    Set (Circle × Circle) :=
  {z | |torusLongCoordinate Phi frame z - d| ≤ 2 * ε}

theorem isClosed_coordinateTorusClosedRegularBand
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d ε : ℝ) :
    IsClosed (coordinateTorusClosedRegularBand Phi frame d ε) := by
  exact isClosed_Iic.preimage <| continuous_abs.comp <|
    (continuous_torusLongCoordinate Phi frame).sub continuous_const

theorem isCompact_coordinateTorusClosedRegularBand
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d ε : ℝ) :
    IsCompact (coordinateTorusClosedRegularBand Phi frame d ε) :=
  (isClosed_coordinateTorusClosedRegularBand Phi frame d ε).isCompact

/-- Uniform regularity data around one regular height. -/
structure OrientedCoordinateRegularBandData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) where
  ε : ℝ
  ε_pos : 0 < ε
  fundamental_noncritical : ∀ uv ∈ fundamentalSquare,
    |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * ε →
      fderiv ℝ (orientedCoordinateLift Phi frame 2) uv ≠ 0
  plane_noncritical : ∀ uv,
    |orientedCoordinateLift Phi frame 2 uv - d| ≤ 2 * ε →
      fderiv ℝ (orientedCoordinateLift Phi frame 2) uv ≠ 0

namespace OrientedCoordinateRegularBandData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- Every height in the closed band is a regular value of the periodic lift. -/
theorem isRegularValue_of_mem_closedBand
    (B : OrientedCoordinateRegularBandData Phi frame d) {y : ℝ}
    (hy : |y - d| ≤ 2 * B.ε) :
    IsRegularValue (orientedCoordinateLift Phi frame 2) y := by
  intro uv huv
  exact B.plane_noncritical uv (by simpa [huv] using hy)

/-- The pullback of every point of the descended torus band has nonzero differential. -/
theorem plane_noncritical_of_expPair_mem
    (B : OrientedCoordinateRegularBandData Phi frame d) (uv : Plane)
    (huv : planeExpPair uv ∈ coordinateTorusClosedRegularBand Phi frame d B.ε) :
    fderiv ℝ (orientedCoordinateLift Phi frame 2) uv ≠ 0 := by
  apply B.plane_noncritical uv
  change |torusLongCoordinate Phi frame (planeExpPair uv) - d| ≤ 2 * B.ε at huv
  rwa [orientedCoordinateLift_eq_torusLongCoordinate_expPair]

/-- The regular band is nonempty whenever the selected fiber is nonempty. -/
theorem coordinateTorusLevelSet_subset_closedBand
    (B : OrientedCoordinateRegularBandData Phi frame d) :
    coordinateTorusLevelSet Phi frame d ⊆
      coordinateTorusClosedRegularBand Phi frame d B.ε := by
  intro z hz
  change |torusLongCoordinate Phi frame z - d| ≤ 2 * B.ε
  rw [hz]
  simpa using B.ε_pos.le

end OrientedCoordinateRegularBandData

/-- Compactness of the fundamental critical-value image produces a positive uniform regular
band, and deck periodicity propagates it to the whole covering plane. -/
theorem exists_orientedCoordinateRegularBandData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d) :
    Nonempty (OrientedCoordinateRegularBandData Phi frame d) := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := orientedCoordinateLift_contDiff Phi frame 2
  have hcompact : IsCompact (fundamentalCriticalValues f) :=
    isCompact_fundamentalCriticalValues hf
  have hdNot : d ∉ fundamentalCriticalValues f := by
    rintro ⟨uv, ⟨huvSquare, huvCritical⟩, huvValue⟩
    exact hd uv huvValue huvCritical
  have hopen : IsOpen (fundamentalCriticalValues f)ᶜ := hcompact.isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen d hdNot
  let ε := δ / 3
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hfundamental : ∀ uv ∈ fundamentalSquare,
      |f uv - d| ≤ 2 * ε → fderiv ℝ f uv ≠ 0 := by
    intro uv huvSquare huvBand huvCritical
    exact (hball (show f uv ∈ ball d δ by
      rw [mem_ball, Real.dist_eq]
      dsimp [ε] at huvBand
      linarith)) ⟨uv, ⟨huvSquare, huvCritical⟩, rfl⟩
  have hplane : ∀ uv,
      |f uv - d| ≤ 2 * ε → fderiv ℝ f uv ≠ 0 := by
    intro uv huvBand
    let representative := planeFundamentalRepresentative uv
    let index := planeFundamentalDeckIndex uv
    have hrepBand : |f representative - d| ≤ 2 * ε := by
      rw [show f representative = f uv by
        exact orientedCoordinateLift_planeFundamentalRepresentative Phi frame 2 uv]
      exact huvBand
    have hrep := hfundamental representative
      (planeFundamentalRepresentative_mem_fundamentalSquare uv) hrepBand
    intro huvCritical
    apply hrep
    have hperiodic := fderiv_orientedCoordinateLift_add_planeDeckVector
      Phi frame 2 index.1 index.2 representative
    rw [planeFundamentalRepresentative_add_deck] at hperiodic
    exact hperiodic.symm.trans huvCritical
  exact ⟨{
    ε := ε
    ε_pos := hε
    fundamental_noncritical := hfundamental
    plane_noncritical := hplane }⟩

end Submission.Topology
