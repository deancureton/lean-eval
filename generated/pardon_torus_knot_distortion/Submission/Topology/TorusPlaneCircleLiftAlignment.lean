import Submission.Topology.MaximalInessentialDiskFamilyExistence

/-!
# Deck alignment of plane-circle lifts

Two continuous lifts from `Circle` to the torus covering plane with the same transported-torus
projection differ by one fixed period-lattice vector.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

private theorem exp_apply_eq_of_projection_eq
    {x y : TorusCoveringPlane}
    (h : EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi y)
    (i : Fin 2) : Circle.exp (x i) = Circle.exp (y i) := by
  change transportedTorusHomeomorph Phi
      (Circle.exp (x 0), Circle.exp (x 1)) =
    transportedTorusHomeomorph Phi
      (Circle.exp (y 0), Circle.exp (y 1)) at h
  have hpair := (transportedTorusHomeomorph Phi).injective h
  fin_cases i
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

private theorem planeCircleLift_eq_of_projection_eq
    (p q : Circle → TorusCoveringPlane)
    (hp : Continuous p) (hq : Continuous q)
    (hprojection : ∀ z,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p z) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q z))
    (hbase : p 1 = q 1) : p = q := by
  funext z
  rw [WithLp.ext_iff]
  funext i
  let pLift : C(Circle, ℝ) :=
    ⟨fun w ↦ p w i,
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp hp⟩
  let qLift : C(Circle, ℝ) :=
    ⟨fun w ↦ q w i,
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp hq⟩
  have hcomp : Circle.exp ∘ pLift = Circle.exp ∘ qLift := by
    funext w
    exact exp_apply_eq_of_projection_eq (hprojection w) i
  have heq : (pLift : Circle → ℝ) = qLift := Circle.isCoveringMap_exp.eq_of_comp_eq
    pLift.continuous qLift.continuous hcomp 1 <|
      congrArg (fun x : TorusCoveringPlane ↦ x i) hbase
  exact congrFun heq z

/-- Two circle lifts of the same torus map differ by one constant deck translation. -/
theorem exists_planeCircleLift_eq_add_lattice
    (p q : Circle → TorusCoveringPlane)
    (hp : Continuous p) (hq : Continuous q)
    (hprojection : ∀ z,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p z) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q z)) :
    ∃ k : Fin 2 → ℤ, ∀ z,
      p z = q z + EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
  have hzero := exp_apply_eq_of_projection_eq (hprojection 1) 0
  have hone := exp_apply_eq_of_projection_eq (hprojection 1) 1
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hzero
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hone
  let k : Fin 2 → ℤ := ![m, n]
  have hbase : p 1 = q 1 + EmbeddedTorusIntersectionCircle.torusLatticeVector k := by
    rw [WithLp.ext_iff]
    funext i
    fin_cases i
    · simpa [k, EmbeddedTorusIntersectionCircle.torusLatticeVector] using hm
    · simpa [k, EmbeddedTorusIntersectionCircle.torusLatticeVector] using hn
  let qShift : Circle → TorusCoveringPlane := fun z ↦
    q z + EmbeddedTorusIntersectionCircle.torusLatticeVector k
  have hqShift : Continuous qShift := hq.add continuous_const
  have hprojectionShift : ∀ z,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p z) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (qShift z) := by
    intro z
    change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p z) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (q z + EmbeddedTorusIntersectionCircle.torusLatticeVector k)
    rw [EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice]
    exact hprojection z
  have heq : p = qShift := planeCircleLift_eq_of_projection_eq
    p qShift hp hqShift hprojectionShift hbase
  exact ⟨k, fun z ↦ congrFun heq z⟩

end Submission.Topology
