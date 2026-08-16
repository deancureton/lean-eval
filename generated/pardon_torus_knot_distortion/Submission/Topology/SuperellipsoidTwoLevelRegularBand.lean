import Submission.Topology.OrientedCoordinateRegularBand
import Submission.Topology.SuperellipsoidGlobalNeckPinchRounding
import Submission.SuperellipsoidDoubleBubbleSelection

/-!
# A narrow regular band and its two separated convex endpoint spheres

The selected cutting height is regular on the transported torus.  Compactness therefore gives a
regular band around it.  This file shrinks that band once more so its half-width is at most one
quarter of the incoming box scale.  The two axial points one box scale below and above the center
then witness nonempty interiors for the separated convex truncations at the endpoint heights.

No assertion about the torus intersections of the endpoint spheres is made here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue

namespace OrientedCoordinateRegularBandData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- Shrink a regular band to a prescribed positive half-width. -/
def narrow (B : OrientedCoordinateRegularBandData Phi frame d)
    (η : ℝ) (hη : 0 < η) : OrientedCoordinateRegularBandData Phi frame d where
  ε := min B.ε η
  ε_pos := lt_min B.ε_pos hη
  fundamental_noncritical := by
    intro uv huv huvBand
    apply B.fundamental_noncritical uv huv
    exact huvBand.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  plane_noncritical := by
    intro uv huvBand
    apply B.plane_noncritical uv
    exact huvBand.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))

@[simp] theorem narrow_epsilon
    (B : OrientedCoordinateRegularBandData Phi frame d) (η : ℝ) (hη : 0 < η) :
    (B.narrow η hη).ε = min B.ε η :=
  rfl

theorem narrow_epsilon_le_right
    (B : OrientedCoordinateRegularBandData Phi frame d) (η : ℝ) (hη : 0 < η) :
    (B.narrow η hη).ε ≤ η :=
  min_le_right _ _

end OrientedCoordinateRegularBandData

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

private theorem lower_axis_point_mem_originalBox (hr : 0 < r) :
    replaceCoord c (frame 2) (c.ofLp (frame 2) - r) ∈ orientedBox frame c r := by
  rw [mem_orientedBox_iff]
  intro i
  by_cases hi : frame i = frame 2
  · have hi2 : i = 2 := frame.injective hi
    subst i
    rw [replaceCoord_same]
    simp only [axisWeight_two]
    rw [show c.ofLp (frame 2) - r - c.ofLp (frame 2) = -r by ring,
      abs_neg, abs_of_pos hr]
    nlinarith [show 1 < aspect ^ 2 by norm_num [aspect]]
  · rw [replaceCoord_of_ne c hi]
    simp only [sub_self, abs_zero]
    exact mul_pos (axisWeight_pos i) hr

private theorem upper_axis_point_mem_originalBox (hr : 0 < r) :
    replaceCoord c (frame 2) (c.ofLp (frame 2) + r) ∈ orientedBox frame c r := by
  rw [mem_orientedBox_iff]
  intro i
  by_cases hi : frame i = frame 2
  · have hi2 : i = 2 := frame.injective hi
    subst i
    rw [replaceCoord_same]
    simp only [axisWeight_two]
    rw [show c.ofLp (frame 2) + r - c.ofLp (frame 2) = r by ring,
      abs_of_pos hr]
    nlinarith [show 1 < aspect ^ 2 by norm_num [aspect]]
  · rw [replaceCoord_of_ne c hi]
    simp only [sub_self, abs_zero]
    exact mul_pos (axisWeight_pos i) hr

/-- A regular band narrowed to the incoming scale has honest separated convex endpoint spheres.

The endpoint sphere construction is the explicit separated-truncation rounding, while regularity
of every height in the wider closed band is retained by `B` itself. -/
theorem exists_narrowRegularBand_and_neckPinchRounding
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (hr : 0 < r) :
    ∃ B : OrientedCoordinateRegularBandData Phi frame S.cut.height,
      B.ε ≤ r / 4 ∧
        Nonempty (SuperellipsoidGlobalNeckPinchRoundingData
          frame c S.outer.scale S.cut.height (S.outer.scale_pos hr)) := by
  obtain ⟨B₀⟩ := exists_orientedCoordinateRegularBandData
    Phi frame S.cut.height S.cut.surfaceRegular
  let B := B₀.narrow (r / 4) (div_pos hr (by norm_num))
  have hε : B.ε ≤ r / 4 := B₀.narrow_epsilon_le_right _ _
  have hlower : ∃ x, x ∈ superellipsoidBody frame c S.outer.scale ∧
      x.ofLp (frame 2) < S.cut.height - B.ε := by
    refine ⟨replaceCoord c (frame 2) (c.ofLp (frame 2) - r), ?_, ?_⟩
    · exact S.originalBox_subset_outerBody hr (lower_axis_point_mem_originalBox hr)
    · rw [replaceCoord_same]
      have hcut := S.cutHeight_mem.1
      dsimp [shellEpsilon] at hcut
      linarith
  have hupper : ∃ x, x ∈ superellipsoidBody frame c S.outer.scale ∧
      S.cut.height + B.ε < x.ofLp (frame 2) := by
    refine ⟨replaceCoord c (frame 2) (c.ofLp (frame 2) + r), ?_, ?_⟩
    · exact S.originalBox_subset_outerBody hr (upper_axis_point_mem_originalBox hr)
    · rw [replaceCoord_same]
      have hcut := S.cutHeight_mem.2
      dsimp [shellEpsilon] at hcut
      linarith
  exact ⟨B, hε, ⟨separatedTruncationGlobalNeckPinchRoundingData
    (S.outer.scale_pos hr) B.ε_pos hlower hupper⟩⟩

end SuperellipsoidDoubleBubbleSelection

end Submission.Topology
