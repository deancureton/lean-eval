import Submission.Topology.CoherentThetaCoveringNeighborhood

/-!
# Deck alignment of covering-plane path lifts

Two continuous lifts of the same transported-torus path differ by one constant period-lattice
vector.  This is the interval analogue of `exists_planeCircleLift_eq_add_lattice`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy}

/-- Two path lifts with the same transported-torus projection differ by one deck translation. -/
theorem exists_planePathLift_eq_add_lattice
    (p q : unitInterval → TorusCoveringPlane)
    (hp : Continuous p) (hq : Continuous q)
    (hprojection : ∀ t,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p t) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q t)) :
    ∃ k : Fin 2 → ℤ, ∀ t,
      p t = q t + EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  have hsourceProjection :
      EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi (p 0) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi (q 0) :=
    congrArg Subtype.val (hprojection 0)
  obtain ⟨k, hsource⟩ :=
    EmbeddedTorusIntersectionCircle.exists_latticeVector_of_torusCoveringProjection_eq
      hsourceProjection
  let qShift : unitInterval → TorusCoveringPlane := fun t ↦
    q t + EmbeddedTorusIntersectionCircle.torusLatticeVector k
  have hqShift : Continuous qShift := hq.add continuous_const
  have hprojectionShift : ∀ t,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p t) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (qShift t) := by
    intro t
    change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p t) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (q t + EmbeddedTorusIntersectionCircle.torusLatticeVector k)
    rw [EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice]
    exact hprojection t
  have heq : p = qShift :=
    TorusThetaPathSystem.ZeroWindingThetaData.planePathLift_eq_of_projection_eq
      p qShift hp hqShift hprojectionShift hsource
  exact ⟨k, fun t ↦ congrFun heq t⟩

end Submission.Topology
