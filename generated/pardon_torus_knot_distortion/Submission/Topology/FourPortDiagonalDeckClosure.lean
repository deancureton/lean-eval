import Submission.Topology.PlanarFourPortDiagonalObstruction
import Submission.Topology.TorusPlaneCircleLiftAlignment

/-!
# Deck closure for the diagonal four-port graph

After the lower and upper exterior paths are lifted from their canonical starting sheets, their
terminal points may differ from the canonical local-rectangle vertices by displacement vectors.
Closing the vertical and horizontal resolutions gives the equations `lower + upper = 0` and
`-lower + upper = 0`.  Since the covering plane is a real vector space, both displacements
vanish.  Thus the two exterior lifts have the same four endpoints as the local rectangle lift.
-/

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-- The two potentially displaced exterior lifts and the closure equations supplied by the
zero-winding vertical and horizontal resolution circles. -/
structure FourPortDiagonalDeckClosureData where
  leftBottom : TorusCoveringPlane
  leftTop : TorusCoveringPlane
  rightBottom : TorusCoveringPlane
  rightTop : TorusCoveringPlane
  lowerDisplacement : TorusCoveringPlane
  upperDisplacement : TorusCoveringPlane
  lowerRaw : Path leftTop (rightBottom + lowerDisplacement)
  upperRaw : Path rightTop (leftBottom + upperDisplacement)
  preClosure : lowerDisplacement + upperDisplacement = 0
  postClosure : -lowerDisplacement + upperDisplacement = 0

namespace FourPortDiagonalDeckClosureData

variable (D : FourPortDiagonalDeckClosureData)

/-- The two closure equations force the lower deck displacement to vanish. -/
theorem lowerDisplacement_eq_zero : D.lowerDisplacement = 0 := by
  rw [WithLp.ext_iff]
  funext i
  have hpre := congrArg (fun x : TorusCoveringPlane ↦ x i) D.preClosure
  have hpost := congrArg (fun x : TorusCoveringPlane ↦ x i) D.postClosure
  change D.lowerDisplacement i + D.upperDisplacement i = 0 at hpre
  change -D.lowerDisplacement i + D.upperDisplacement i = 0 at hpost
  change D.lowerDisplacement i = (0 : ℝ)
  linarith

/-- The two closure equations force the upper deck displacement to vanish. -/
theorem upperDisplacement_eq_zero : D.upperDisplacement = 0 := by
  rw [WithLp.ext_iff]
  funext i
  have hpre := congrArg (fun x : TorusCoveringPlane ↦ x i) D.preClosure
  have hpost := congrArg (fun x : TorusCoveringPlane ↦ x i) D.postClosure
  change D.lowerDisplacement i + D.upperDisplacement i = 0 at hpre
  change -D.lowerDisplacement i + D.upperDisplacement i = 0 at hpost
  change D.upperDisplacement i = (0 : ℝ)
  linarith

private theorem rightBottom_eq_displaced :
    D.rightBottom = D.rightBottom + D.lowerDisplacement := by
  rw [D.lowerDisplacement_eq_zero, add_zero]

private theorem leftBottom_eq_displaced :
    D.leftBottom = D.leftBottom + D.upperDisplacement := by
  rw [D.upperDisplacement_eq_zero, add_zero]

/-- The lower exterior lift with its terminal endpoint identified with the canonical vertex. -/
def lower : Path D.leftTop D.rightBottom :=
  D.lowerRaw.cast rfl D.rightBottom_eq_displaced

/-- The upper exterior lift with its terminal endpoint identified with the canonical vertex. -/
def upper : Path D.rightTop D.leftBottom :=
  D.upperRaw.cast rfl D.leftBottom_eq_displaced

@[simp] theorem lower_apply (t : unitInterval) : D.lower t = D.lowerRaw t :=
  rfl

@[simp] theorem upper_apply (t : unitInterval) : D.upper t = D.upperRaw t :=
  rfl

theorem range_lower : Set.range D.lower = Set.range D.lowerRaw :=
  rfl

theorem range_upper : Set.range D.upper = Set.range D.upperRaw :=
  rfl

theorem lower_injective (h : Function.Injective D.lowerRaw) : Function.Injective D.lower :=
  h

theorem upper_injective (h : Function.Injective D.upperRaw) : Function.Injective D.upper :=
  h

end FourPortDiagonalDeckClosureData
end Submission.Topology
