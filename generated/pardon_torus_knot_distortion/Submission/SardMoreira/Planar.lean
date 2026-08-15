import Submission.SardMoreira.MainTheorem
import Submission.Topology.SurfaceRegularValue

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Submission
namespace SurfaceRegularValue

noncomputable section

/-!
# The planar Sard theorem

This file specializes Moreira's quantitative Sard theorem to smooth real-valued
maps on the plane.  It discharges the sole analytic hypothesis left abstract in
`Submission.Topology.SurfaceRegularValue`.
-/

/-- Every smooth real-valued map on the plane has one-dimensional Hausdorff-null
critical values. -/
theorem planarSardTheorem : PlanarSardTheorem := by
  intro f hf
  have h := hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le
    (E := Plane) (F := ℝ) (p := 0) (k := 2) (α := 0)
    (f := f) (s := criticalPoints f) (by norm_num)
    (by norm_num)
    (fun x _ ↦ hf.contDiffAt.contDiffMoreiraHolderAt (by
      exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top 2)) 0)
    (fun x hx ↦ by
      rw [show fderiv ℝ f x = 0 from hx]
      simp)
  have hdim : Module.finrank ℝ Plane = 2 := by
    simp [Plane]
  rw [hdim] at h
  have hbound : sardMoreiraBound 2 2 0 0 = 1 := by
    rw [sardMoreiraBound]
    apply NNReal.eq
    norm_num
    rfl
  change μH[1] (f '' criticalPoints f) = 0
  simpa only [hbound, NNReal.coe_one] using h

end
end SurfaceRegularValue
end Submission
