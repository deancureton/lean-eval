import Submission.Topology.SuperellipsoidSeamRegularBand
import Submission.Topology.SuperellipsoidTwoLevelRegularBand

/-!
# Canonical simultaneous regularity at the two endpoint heights

The selected cut is regular both as a transported-torus coordinate level and along the fixed
outer superellipsoid section.  The two compactness arguments give independent positive margins.
Narrowing to their minimum produces one endpoint package whose lower and upper heights satisfy
both regularity conditions and retain the strict convex-body witnesses.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- Endpoint heights with simultaneous torus-coordinate and outer-seam regularity. -/
structure CanonicalEndpointRegularityData
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) where
  scale_pos : 0 < S.outer.scale
  heightData : CanonicalEndpointHeightData S
  seamRegular : ∀ y,
    |y - S.cut.height| ≤ 2 * heightData.band.ε →
      IsRegularSuperellipsoidSeamHeight Phi frame c S.outer.scale y
  lowerSeamRegular : IsRegularSuperellipsoidSeamHeight Phi frame c S.outer.scale
    (S.cut.height - heightData.band.ε)
  upperSeamRegular : IsRegularSuperellipsoidSeamHeight Phi frame c S.outer.scale
    (S.cut.height + heightData.band.ε)

namespace CanonicalEndpointRegularityData

variable {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

/-- The retained uniform seam-regular band at the canonical endpoint width. -/
def seamRegularBand (D : CanonicalEndpointRegularityData S) :
    SuperellipsoidSeamRegularBandData Phi frame c S.outer.scale S.cut.height where
  ε := D.heightData.band.ε
  ε_pos := D.heightData.band.ε_pos
  regular := D.seamRegular

/-- Shrink the canonical endpoint band while retaining every regularity and convexity witness. -/
def narrow (D : CanonicalEndpointRegularityData S) (η : ℝ) (hη : 0 < η) :
    CanonicalEndpointRegularityData S := by
  let band := D.heightData.band.narrow η hη
  have hband : band.ε ≤ D.heightData.band.ε := min_le_left _ _
  let heightData : CanonicalEndpointHeightData S := {
    band := band
    width_le := hband.trans D.heightData.width_le
    lowerPoint := by
      obtain ⟨x, hxBody, hxHeight⟩ := D.heightData.lowerPoint
      exact ⟨x, hxBody, by linarith⟩
    upperPoint := by
      obtain ⟨x, hxBody, hxHeight⟩ := D.heightData.upperPoint
      exact ⟨x, hxBody, by linarith⟩ }
  have hregular : ∀ y,
      |y - S.cut.height| ≤ 2 * heightData.band.ε →
        IsRegularSuperellipsoidSeamHeight Phi frame c S.outer.scale y := by
    intro y hy
    apply D.seamRegular y
    exact hy.trans (mul_le_mul_of_nonneg_left hband (by norm_num))
  exact {
    scale_pos := D.scale_pos
    heightData := heightData
    seamRegular := hregular
    lowerSeamRegular := hregular _ <| by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos heightData.band.ε_pos]
      linarith [heightData.band.ε_pos]
    upperSeamRegular := hregular _ <| by
      rw [add_sub_cancel_left, abs_of_pos heightData.band.ε_pos]
      linarith [heightData.band.ε_pos] }

@[simp]
theorem narrow_epsilon (D : CanonicalEndpointRegularityData S) (η : ℝ) (hη : 0 < η) :
    (D.narrow η hη).heightData.band.ε = min D.heightData.band.ε η :=
  rfl

theorem narrow_epsilon_le_right
    (D : CanonicalEndpointRegularityData S) (η : ℝ) (hη : 0 < η) :
    (D.narrow η hη).heightData.band.ε ≤ η :=
  min_le_right _ _

/-- The lower endpoint is a regular transported-torus coordinate level. -/
theorem lowerSurfaceRegular (D : CanonicalEndpointRegularityData S) :
    IsRegularValue (orientedCoordinateLift Phi frame 2)
      (S.cut.height - D.heightData.band.ε) :=
  D.heightData.lowerSurfaceRegular

/-- The upper endpoint is a regular transported-torus coordinate level. -/
theorem upperSurfaceRegular (D : CanonicalEndpointRegularityData S) :
    IsRegularValue (orientedCoordinateLift Phi frame 2)
      (S.cut.height + D.heightData.band.ε) :=
  D.heightData.upperSurfaceRegular

end CanonicalEndpointRegularityData

/-- The two compact regularity margins have a common positive narrowing. -/
theorem exists_canonicalEndpointRegularityData
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (hr : 0 < r) : Nonempty (CanonicalEndpointRegularityData S) := by
  obtain ⟨D⟩ := exists_canonicalEndpointHeightData S hr
  obtain ⟨B⟩ := exists_superellipsoidSeamRegularBandData
    Phi frame c S.outer.scale S.cut.height S.cut.seamRegular
  let band := D.band.narrow B.ε B.ε_pos
  have hbandOld : band.ε ≤ D.band.ε := by
    exact min_le_left _ _
  have hbandSeam : band.ε ≤ B.ε := by
    exact min_le_right _ _
  let heightData : CanonicalEndpointHeightData S := {
    band := band
    width_le := hbandOld.trans D.width_le
    lowerPoint := by
      obtain ⟨x, hxBody, hxHeight⟩ := D.lowerPoint
      exact ⟨x, hxBody, by linarith⟩
    upperPoint := by
      obtain ⟨x, hxBody, hxHeight⟩ := D.upperPoint
      exact ⟨x, hxBody, by linarith⟩ }
  refine ⟨{
    scale_pos := S.outer.scale_pos hr
    heightData := heightData
    seamRegular := by
      intro y hy
      apply B.regular y
      have hε : 0 ≤ heightData.band.ε := heightData.band.ε_pos.le
      have hBε : 0 ≤ B.ε := B.ε_pos.le
      rw [abs_le] at hy ⊢
      constructor <;> linarith
    lowerSeamRegular := B.regular _ ?_
    upperSeamRegular := B.regular _ ?_ }⟩
  · rw [sub_sub_cancel_left, abs_neg, abs_of_pos heightData.band.ε_pos]
    linarith [heightData.band.ε_pos]
  · rw [add_sub_cancel_left, abs_of_pos heightData.band.ε_pos]
    linarith [heightData.band.ε_pos]

/-- Fix the canonical endpoint package once and for all by classical choice. -/
noncomputable def canonicalEndpointRegularityData
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (hr : 0 < r) : CanonicalEndpointRegularityData S :=
  Classical.choice (exists_canonicalEndpointRegularityData S hr)

end SuperellipsoidDoubleBubbleSelection
end Submission.Topology
