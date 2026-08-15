import Submission.Topology.LoopHalfspaceCut
import Submission.Coarea.General

/-!
# Constructing periodic arc replacements

This module supplies two pieces of the geometric input isolated by `LoopHalfspaceCut`.

First, a `C¹` cutting-height function and a regular value canonically give a finite crossing
finset on one half-open period.  Every connected crossing-free parameter arc has constant strict
sign, so it lies wholly on one side of the cutting plane.

Second, `PeriodicSpliceData` records only local replacement paths on a periodic union of bad
arcs.  Boundary compatibility is stated on the frontier of the corresponding cylinder.  The
global `if`-splice is then proved continuous, periodic, contained in the chosen side at its final
time, and periodically homotopic to the original loop.  Its covering lift is constructed from
continuity and periodicity, rather than included as extra geometric data.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-! ## Regular crossings of a smooth winding loop -/

/-- Signed cutting height of an arbitrary transported-torus loop. -/
def windingLoopCutHeight {Phi : AmbientIsotopy}
    {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) (u : ℝ) : ℝ :=
  (L.curve u : R3).ofLp (frame 2) - d

/-- The analytic hypotheses needed to obtain a finite transverse crossing set. -/
structure SmoothRegularLoopCutData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) : Prop where
  contDiff_height : ContDiff ℝ 1 (windingLoopCutHeight frame d L)
  regular_zero : Submission.Coarea.IsRegularValue
    (windingLoopCutHeight frame d L) 0

namespace SmoothRegularLoopCutData

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-- The regular crossings in the canonical half-open period. -/
def crossings (H : SmoothRegularLoopCutData frame d L) : Finset ℝ := by
  let f := windingLoopCutHeight frame d L
  have hfiniteIcc : (Submission.Coarea.fiberSet f
      (Icc (0 : ℝ) (2 * Real.pi)) 0).Finite :=
    Submission.Coarea.finite_fiberSet_of_isCompact_of_regularValue
      isCompact_Icc H.contDiff_height H.regular_zero
  have hfiniteIco : (Submission.Coarea.fiberSet f
      (Ico (0 : ℝ) (2 * Real.pi)) 0).Finite := by
    apply hfiniteIcc.subset
    intro u hu
    exact ⟨Ico_subset_Icc_self hu.1, hu.2⟩
  exact hfiniteIco.toFinset

theorem mem_crossings_iff (H : SmoothRegularLoopCutData frame d L) (u : ℝ) :
    u ∈ H.crossings ↔
      u ∈ Ico (0 : ℝ) (2 * Real.pi) ∧ windingLoopCutHeight frame d L u = 0 := by
  simp only [crossings, Set.Finite.mem_toFinset, Submission.Coarea.fiberSet,
    mem_inter_iff, mem_preimage, mem_singleton_iff]

theorem crossings_subset_period (H : SmoothRegularLoopCutData frame d L) :
    (H.crossings : Set ℝ) ⊆ Ico (0 : ℝ) (2 * Real.pi) := by
  intro u hu
  exact (H.mem_crossings_iff u).mp hu |>.1

theorem mem_crossings_iff_mem_plane
    (H : SmoothRegularLoopCutData frame d L) (u : ℝ)
    (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    u ∈ H.crossings ↔ L.curve u ∈ planeSurfaceRegion Phi parent frame d := by
  rw [H.mem_crossings_iff]
  simp only [hu, true_and, windingLoopCutHeight, planeSurfaceRegion,
    transportedTorusPart, coordinateCuttingPlane, mem_inter_iff, mem_preimage,
    mem_ofPred_eq, sub_eq_zero]
  constructor
  · exact fun h ↦ ⟨L.curve_mem u, h⟩
  · exact fun h ↦ h.2

theorem hasDerivAt_height (H : SmoothRegularLoopCutData frame d L) (u : ℝ) :
    HasDerivAt (windingLoopCutHeight frame d L)
      (deriv (windingLoopCutHeight frame d L) u) u :=
  (H.contDiff_height.differentiable_one u).hasDerivAt

theorem deriv_height_ne_zero_of_mem_crossings
    (H : SmoothRegularLoopCutData frame d L) {u : ℝ} (hu : u ∈ H.crossings) :
    deriv (windingLoopCutHeight frame d L) u ≠ 0 := by
  apply H.regular_zero u
  exact (H.mem_crossings_iff u).mp hu |>.2

/-- The cutting height inherits the loop's period. -/
theorem periodic_height (_H : SmoothRegularLoopCutData frame d L) :
    Function.Periodic (windingLoopCutHeight frame d L) (2 * Real.pi) := by
  intro u
  simp only [windingLoopCutHeight]
  rw [L.periodic_curve]

/-- A connected crossing-free parameter arc has a constant strict sign. -/
theorem crossingFreeArc_all_neg_or_all_pos
    (H : SmoothRegularLoopCutData frame d L)
    {s : Set ℝ} (hs : IsPreconnected s) (hsne : s.Nonempty)
    (hzero : ∀ u ∈ s, windingLoopCutHeight frame d L u ≠ 0) :
    (∀ u ∈ s, windingLoopCutHeight frame d L u < 0) ∨
      (∀ u ∈ s, 0 < windingLoopCutHeight frame d L u) := by
  obtain ⟨u₀, hu₀⟩ := hsne
  rcases lt_or_gt_of_ne (hzero u₀ hu₀) with hneg | hpos
  · left
    intro u hu
    by_contra hn
    have huNonneg : 0 ≤ windingLoopCutHeight frame d L u := le_of_not_gt hn
    have hbetween : 0 ∈ Icc (windingLoopCutHeight frame d L u₀)
        (windingLoopCutHeight frame d L u) := ⟨hneg.le, huNonneg⟩
    obtain ⟨v, hv, hvzero⟩ := hs.intermediate_value hu₀ hu
      H.contDiff_height.continuous.continuousOn hbetween
    exact hzero v hv hvzero
  · right
    intro u hu
    by_contra hn
    have huNonpos : windingLoopCutHeight frame d L u ≤ 0 := le_of_not_gt hn
    have hbetween : 0 ∈ Icc (windingLoopCutHeight frame d L u)
        (windingLoopCutHeight frame d L u₀) := ⟨huNonpos, hpos.le⟩
    obtain ⟨v, hv, hvzero⟩ := hs.intermediate_value hu hu₀
      H.contDiff_height.continuous.continuousOn hbetween
    exact hzero v hv hvzero

/-- A connected crossing-free arc is contained in one of the two closed surface regions. -/
theorem crossingFreeArc_mem_lower_or_upper
    (H : SmoothRegularLoopCutData frame d L)
    {s : Set ℝ} (hs : IsPreconnected s) (hsne : s.Nonempty)
    (hzero : ∀ u ∈ s, windingLoopCutHeight frame d L u ≠ 0) :
    (∀ u ∈ s, L.curve u ∈ lowerSurfaceRegion Phi parent frame d) ∨
      (∀ u ∈ s, L.curve u ∈ upperSurfaceRegion Phi parent frame d) := by
  rcases H.crossingFreeArc_all_neg_or_all_pos hs hsne hzero with hneg | hpos
  · left
    intro u hu
    exact ⟨L.curve_mem u, (sub_neg.mp (hneg u hu)).le⟩
  · right
    intro u hu
    exact ⟨L.curve_mem u, (sub_pos.mp (hpos u hu)).le⟩

end SmoothRegularLoopCutData

/-! ## An explicit periodic splice -/

/-- The parameter cylinder over a periodic union of arcs. -/
def parameterCylinder (active : Set ℝ) : Set (ℝ × ℝ) :=
  Prod.snd ⁻¹' active

/-- Local path data sufficient to splice all selected periodic arcs at once.

`patch s t` is the replacement path at homotopy time `s`.  Only its values on `active` are used.
The frontier condition is exactly endpoint compatibility; `original_mem_target_off` says that
all portions not replaced already lie in the chosen halfspace. -/
structure PeriodicSpliceData
    {Phi : AmbientIsotopy} {parent target : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent) where
  active : Set ℝ
  active_periodic : ∀ t, t + 2 * Real.pi ∈ active ↔ t ∈ active
  patch : ℝ → ℝ → transportedTorus Phi
  continuous_patch : Continuous (Function.uncurry patch)
  periodic_patch : ∀ s, Function.Periodic (patch s) (2 * Real.pi)
  patch_frontier : ∀ z ∈ frontier (parameterCylinder active),
    patch z.1 z.2 = original.curve z.2
  patch_zero : ∀ t ∈ active, patch 0 t = original.curve t
  patch_one_mem_target : ∀ t ∈ active, patch 1 t ∈ target
  original_mem_target_off : ∀ t, t ∉ active → original.curve t ∈ target

namespace PeriodicSpliceData

variable {Phi : AmbientIsotopy} {parent target : Set (transportedTorus Phi)}
  {original : TransportedWindingLoop Phi parent}

/-- The global homotopy obtained by using the patch precisely on the selected arcs. -/
def splicedHomotopy (D : PeriodicSpliceData (target := target) original)
    (s t : ℝ) : transportedTorus Phi := by
  classical
  exact if t ∈ D.active then D.patch s t else original.curve t

/-- The final rerouted periodic loop. -/
def splicedCurve (D : PeriodicSpliceData (target := target) original)
    (t : ℝ) : transportedTorus Phi :=
  D.splicedHomotopy 1 t

theorem continuous_splicedHomotopy
    (D : PeriodicSpliceData (target := target) original) :
    Continuous (Function.uncurry D.splicedHomotopy) := by
  classical
  change Continuous (fun z : ℝ × ℝ ↦
    if z.2 ∈ D.active then D.patch z.1 z.2 else original.curve z.2)
  apply continuous_if
  · intro z hz
    exact D.patch_frontier z hz
  · exact D.continuous_patch.continuousOn
  · exact original.continuous_curve.comp continuous_snd |>.continuousOn

theorem periodic_splicedHomotopy
    (D : PeriodicSpliceData (target := target) original) (s : ℝ) :
    Function.Periodic (D.splicedHomotopy s) (2 * Real.pi) := by
  intro t
  classical
  by_cases ht : t ∈ D.active
  · have ht' : t + 2 * Real.pi ∈ D.active := (D.active_periodic t).mpr ht
    simp only [splicedHomotopy, if_pos ht, if_pos ht']
    exact D.periodic_patch s t
  · have ht' : t + 2 * Real.pi ∉ D.active := by
      intro h
      exact ht ((D.active_periodic t).mp h)
    simp only [splicedHomotopy, if_neg ht, if_neg ht']
    exact original.periodic_curve t

theorem splicedHomotopy_zero
    (D : PeriodicSpliceData (target := target) original) :
    D.splicedHomotopy 0 = original.curve := by
  funext t
  classical
  by_cases ht : t ∈ D.active
  · simp [splicedHomotopy, ht, D.patch_zero t ht]
  · simp [splicedHomotopy, ht]

theorem continuous_splicedCurve
    (D : PeriodicSpliceData (target := target) original) :
    Continuous D.splicedCurve := by
  exact D.continuous_splicedHomotopy.comp
    (continuous_const.prodMk continuous_id)

theorem periodic_splicedCurve
    (D : PeriodicSpliceData (target := target) original) :
    Function.Periodic D.splicedCurve (2 * Real.pi) :=
  D.periodic_splicedHomotopy 1

theorem splicedCurve_mem
    (D : PeriodicSpliceData (target := target) original) (t : ℝ) :
    D.splicedCurve t ∈ target := by
  classical
  by_cases ht : t ∈ D.active
  · simpa only [splicedCurve, splicedHomotopy, if_pos ht] using
      D.patch_one_mem_target t ht
  · simpa only [splicedCurve, splicedHomotopy, if_neg ht] using
      D.original_mem_target_off t ht

theorem splicedHomotopy_one
    (D : PeriodicSpliceData (target := target) original) :
    D.splicedHomotopy 1 = D.splicedCurve := rfl

/-- The splice produces all of `PeriodicArcReplacement`, including a newly constructed lift. -/
def toPeriodicArcReplacement
    (D : PeriodicSpliceData (target := target) original) :
    PeriodicArcReplacement (target := target) original where
  rerouted := D.splicedCurve
  continuous_rerouted := D.continuous_splicedCurve
  periodic_rerouted := D.periodic_splicedCurve
  rerouted_mem := D.splicedCurve_mem
  reroutedLift := (exists_torusLoopLift_of_transportedLoop Phi D.splicedCurve
    D.continuous_splicedCurve D.periodic_splicedCurve).some
  homotopy := D.splicedHomotopy
  continuous_homotopy := D.continuous_splicedHomotopy
  periodic_homotopy := D.periodic_splicedHomotopy
  homotopy_zero := D.splicedHomotopy_zero
  homotopy_one := D.splicedHomotopy_one

/-- Consequently the explicit splice preserves the full winding pair. -/
theorem windingPair_splice
    (D : PeriodicSpliceData (target := target) original) :
    D.toPeriodicArcReplacement.toWindingLoop.windingPair = original.windingPair :=
  D.toPeriodicArcReplacement.windingPair_toWindingLoop

end PeriodicSpliceData

/-! ## Specialization to a coordinate halfspace -/

/-- Local path data rerouting all upper excursions into the lower closed halfspace. -/
abbrev LowerHalfspaceSpliceData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) :=
  PeriodicSpliceData
    (target := lowerSurfaceRegion Phi parent frame d) L

/-- Local path data rerouting all lower excursions into the upper closed halfspace. -/
abbrev UpperHalfspaceSpliceData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) :=
  PeriodicSpliceData
    (target := upperSurfaceRegion Phi parent frame d) L

/-- The periodic union of strict upper excursions, all of which must be replaced to obtain a
lower-halfspace loop. -/
def upperExcursions {Phi : AmbientIsotopy}
    {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) : Set ℝ :=
  {t | 0 < windingLoopCutHeight frame d L t}

/-- The periodic union of strict lower excursions. -/
def lowerExcursions {Phi : AmbientIsotopy}
    {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) : Set ℝ :=
  {t | windingLoopCutHeight frame d L t < 0}

/-- Honest local path input for replacing every strict upper excursion.  Its boundary condition
means that paths assigned to adjacent crossing endpoints glue to the original loop. -/
structure UpperExcursionPatchFamily
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) where
  patch : ℝ → ℝ → transportedTorus Phi
  continuous_patch : Continuous (Function.uncurry patch)
  periodic_patch : ∀ s, Function.Periodic (patch s) (2 * Real.pi)
  patch_frontier : ∀ z ∈ frontier (parameterCylinder (upperExcursions frame d L)),
    patch z.1 z.2 = L.curve z.2
  patch_zero : ∀ t ∈ upperExcursions frame d L, patch 0 t = L.curve t
  patch_one_mem_lower : ∀ t ∈ upperExcursions frame d L,
    patch 1 t ∈ lowerSurfaceRegion Phi parent frame d

/-- Honest local path input for replacing every strict lower excursion. -/
structure LowerExcursionPatchFamily
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) where
  patch : ℝ → ℝ → transportedTorus Phi
  continuous_patch : Continuous (Function.uncurry patch)
  periodic_patch : ∀ s, Function.Periodic (patch s) (2 * Real.pi)
  patch_frontier : ∀ z ∈ frontier (parameterCylinder (lowerExcursions frame d L)),
    patch z.1 z.2 = L.curve z.2
  patch_zero : ∀ t ∈ lowerExcursions frame d L, patch 0 t = L.curve t
  patch_one_mem_upper : ∀ t ∈ lowerExcursions frame d L,
    patch 1 t ∈ upperSurfaceRegion Phi parent frame d

namespace UpperExcursionPatchFamily

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-- Replacing precisely the upper excursions gives complete lower-halfspace splice data. -/
def toLowerHalfspaceSpliceData
    (H : SmoothRegularLoopCutData frame d L)
    (P : UpperExcursionPatchFamily frame d L) :
    LowerHalfspaceSpliceData frame d L where
  active := upperExcursions frame d L
  active_periodic := fun t ↦ by
    change 0 < windingLoopCutHeight frame d L (t + 2 * Real.pi) ↔
      0 < windingLoopCutHeight frame d L t
    rw [H.periodic_height t]
  patch := P.patch
  continuous_patch := P.continuous_patch
  periodic_patch := P.periodic_patch
  patch_frontier := P.patch_frontier
  patch_zero := P.patch_zero
  patch_one_mem_target := P.patch_one_mem_lower
  original_mem_target_off := fun t ht ↦ by
    refine ⟨L.curve_mem t, ?_⟩
    change (L.curve t : R3).ofLp (frame 2) ≤ d
    have hnot : ¬ 0 < windingLoopCutHeight frame d L t := ht
    exact sub_nonpos.mp (le_of_not_gt hnot)

end UpperExcursionPatchFamily

namespace LowerExcursionPatchFamily

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-- Replacing precisely the lower excursions gives complete upper-halfspace splice data. -/
def toUpperHalfspaceSpliceData
    (H : SmoothRegularLoopCutData frame d L)
    (P : LowerExcursionPatchFamily frame d L) :
    UpperHalfspaceSpliceData frame d L where
  active := lowerExcursions frame d L
  active_periodic := fun t ↦ by
    change windingLoopCutHeight frame d L (t + 2 * Real.pi) < 0 ↔
      windingLoopCutHeight frame d L t < 0
    rw [H.periodic_height t]
  patch := P.patch
  continuous_patch := P.continuous_patch
  periodic_patch := P.periodic_patch
  patch_frontier := P.patch_frontier
  patch_zero := P.patch_zero
  patch_one_mem_target := P.patch_one_mem_upper
  original_mem_target_off := fun t ht ↦ by
    refine ⟨L.curve_mem t, ?_⟩
    change d ≤ (L.curve t : R3).ofLp (frame 2)
    have hnot : ¬ windingLoopCutHeight frame d L t < 0 := ht
    exact sub_nonneg.mp (le_of_not_gt hnot)

end LowerExcursionPatchFamily

/-- A regular smooth loop equipped with upper-excursion paths has a winding-preserving
lower-halfspace replacement. -/
def periodicArcReplacement_inLower_of_upperExcursionPaths
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent)
    (H : SmoothRegularLoopCutData frame d L)
    (P : UpperExcursionPatchFamily frame d L) :
    PeriodicArcReplacement
      (target := lowerSurfaceRegion Phi parent frame d) L :=
  (P.toLowerHalfspaceSpliceData H).toPeriodicArcReplacement

/-- The corresponding upper-halfspace replacement. -/
def periodicArcReplacement_inUpper_of_lowerExcursionPaths
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent)
    (H : SmoothRegularLoopCutData frame d L)
    (P : LowerExcursionPatchFamily frame d L) :
    PeriodicArcReplacement
      (target := upperSurfaceRegion Phi parent frame d) L :=
  (P.toUpperHalfspaceSpliceData H).toPeriodicArcReplacement

def lowerLoopReroutingOutcome_of_spliceData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent)
    (D : LowerHalfspaceSpliceData frame d L) :
    LoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .inLeft D.toPeriodicArcReplacement

def upperLoopReroutingOutcome_of_spliceData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent)
    (D : UpperHalfspaceSpliceData frame d L) :
    LoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .inRight D.toPeriodicArcReplacement

end Submission.Topology
