import Submission.Topology.FourPortDiagonalCyclePlanePaths
import Submission.Topology.TorusPlanePathLiftAlignment

/-!
# Deck alignment of the duplicated diagonal four-port edges

Each edge of the diagonal six-edge graph occurs in two of the three zero-winding lifted cycles.
The two occurrences differ by a single constant lattice vector.  This file chooses those six
vectors and records the pointwise equalities used by the vertex cancellation argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy}

namespace FourPortDiagonalPathSystem.ZeroWindingData

variable {G : FourPortDiagonalPathSystem (transportedTorus Phi)}
variable (Z : G.ZeroWindingData)

private theorem exists_upperShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.preUpperPlanePath t = Z.postUpperPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.preUpperPlanePath.continuous
  · exact Z.postUpperPlanePath.continuous
  · intro t
    rw [Z.projection_preUpperPlanePath, Z.projection_postUpperPlanePath]

private theorem exists_lowerShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.preLowerPlanePath t = Z.postLowerPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.preLowerPlanePath.continuous
  · exact Z.postLowerPlanePath.continuous
  · intro t
    rw [Z.projection_preLowerPlanePath, Z.projection_postLowerPlanePath]

private theorem exists_leftShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.preLeftPlanePath t = Z.rectangleLeftPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.preLeftPlanePath.continuous
  · exact Z.rectangleLeftPlanePath.continuous
  · intro t
    rw [Z.projection_preLeftPlanePath, Z.projection_rectangleLeftPlanePath]

private theorem exists_rightShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.preRightPlanePath t = Z.rectangleRightPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.preRightPlanePath.continuous
  · exact Z.rectangleRightPlanePath.continuous
  · intro t
    rw [Z.projection_preRightPlanePath, Z.projection_rectangleRightPlanePath]

private theorem exists_bottomShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.postBottomPlanePath t = Z.rectangleBottomPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.postBottomPlanePath.continuous
  · exact Z.rectangleBottomPlanePath.continuous
  · intro t
    rw [Z.projection_postBottomPlanePath, Z.projection_rectangleBottomPlanePath]

private theorem exists_topShift :
    ∃ k : Fin 2 → ℤ, ∀ t,
      Z.postTopPlanePath t = Z.rectangleTopPlanePath t +
        EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  apply exists_planePathLift_eq_add_lattice
  · exact Z.postTopPlanePath.continuous
  · exact Z.rectangleTopPlanePath.continuous
  · intro t
    rw [Z.projection_postTopPlanePath, Z.projection_rectangleTopPlanePath]

/-- Deck index aligning the two copies of the upper diagonal. -/
def upperShift : Fin 2 → ℤ := Classical.choose Z.exists_upperShift

/-- Deck index aligning the two copies of the lower diagonal. -/
def lowerShift : Fin 2 → ℤ := Classical.choose Z.exists_lowerShift

/-- Deck index aligning the pre-cycle and rectangle copies of the left edge. -/
def leftShift : Fin 2 → ℤ := Classical.choose Z.exists_leftShift

/-- Deck index aligning the pre-cycle and rectangle copies of the right edge. -/
def rightShift : Fin 2 → ℤ := Classical.choose Z.exists_rightShift

/-- Deck index aligning the post-cycle and rectangle copies of the bottom edge. -/
def bottomShift : Fin 2 → ℤ := Classical.choose Z.exists_bottomShift

/-- Deck index aligning the post-cycle and rectangle copies of the top edge. -/
def topShift : Fin 2 → ℤ := Classical.choose Z.exists_topShift

theorem preUpper_eq_postUpper_add_shift (t : unitInterval) :
    Z.preUpperPlanePath t = Z.postUpperPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.upperShift :=
  Classical.choose_spec Z.exists_upperShift t

theorem preLower_eq_postLower_add_shift (t : unitInterval) :
    Z.preLowerPlanePath t = Z.postLowerPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.lowerShift :=
  Classical.choose_spec Z.exists_lowerShift t

theorem preLeft_eq_rectangleLeft_add_shift (t : unitInterval) :
    Z.preLeftPlanePath t = Z.rectangleLeftPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.leftShift :=
  Classical.choose_spec Z.exists_leftShift t

theorem preRight_eq_rectangleRight_add_shift (t : unitInterval) :
    Z.preRightPlanePath t = Z.rectangleRightPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.rightShift :=
  Classical.choose_spec Z.exists_rightShift t

theorem postBottom_eq_rectangleBottom_add_shift (t : unitInterval) :
    Z.postBottomPlanePath t = Z.rectangleBottomPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.bottomShift :=
  Classical.choose_spec Z.exists_bottomShift t

theorem postTop_eq_rectangleTop_add_shift (t : unitInterval) :
    Z.postTopPlanePath t = Z.rectangleTopPlanePath t +
      EmbeddedTorusIntersectionCircle.torusLatticeVector Z.topShift :=
  Classical.choose_spec Z.exists_topShift t

end FourPortDiagonalPathSystem.ZeroWindingData
end Submission.Topology
