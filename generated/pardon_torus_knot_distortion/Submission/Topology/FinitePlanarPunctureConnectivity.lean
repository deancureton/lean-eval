import Submission.PlaneSchoenflies.Schoenflies.CompleteRegionalExtension
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectivity of finitely punctured planar Jordan regions

The plane minus finitely many points is connected.  The standard homeomorphism from the plane
to its open unit ball transports this fact to a finitely punctured ball, and the bounded-side
Schoenflies homeomorphism then transports it to the inside of any planar Jordan circle.
-/

open Metric Set Topology

noncomputable section

namespace Submission.Topology

open JordanCurve.Arcs

/-- The open unit ball in the plane remains connected after deleting a finite family of points. -/
theorem isConnected_unitBall_avoiding_finite
    {kappa : Type*} [Fintype kappa]
    (center : kappa → ball (0 : Plane) 1) :
    IsConnected {x : ball (0 : Plane) 1 | ∀ i, x ≠ center i} := by
  let sourceCenter : kappa → Plane := fun i ↦ Homeomorph.unitBall.symm (center i)
  have hsource : IsConnected (Set.range sourceCenter)ᶜ :=
    (Set.finite_range sourceCenter).countable.isConnected_compl_of_one_lt_rank (by
      apply Module.one_lt_rank_of_one_lt_finrank
      simp [Plane])
  have himage : Homeomorph.unitBall '' (Set.range sourceCenter)ᶜ =
      {x : ball (0 : Plane) 1 | ∀ i, x ≠ center i} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i hi
      apply hy
      refine ⟨i, ?_⟩
      apply Homeomorph.unitBall.injective
      simpa only [sourceCenter, Homeomorph.apply_symm_apply] using hi.symm
    · intro hx
      refine ⟨Homeomorph.unitBall.symm x, ?_,
        (Homeomorph.unitBall : Plane ≃ₜ ball (0 : Plane) 1).apply_symm_apply x⟩
      intro hcenter
      obtain ⟨i, hi⟩ := hcenter
      apply hx i
      apply Homeomorph.unitBall.symm.injective
      simpa only [sourceCenter, Homeomorph.symm_apply_apply] using hi.symm
  rw [← himage]
  exact hsource.image _ Homeomorph.unitBall.continuous.continuousOn

end Submission.Topology
namespace Schoenflies.JordanCircle

/-- The open inside of a Jordan circle is homeomorphic to the open unit ball. -/
def insideHomeomorphUnitBall (J : JordanCircle) :
    J.inside ≃ₜ ball (0 : Plane) 1 := by
  let E := J.regionalExtensionData
  let toClosedInside : J.inside → closure J.inside :=
    fun x ↦ ⟨x, subset_closure x.2⟩
  let toClosedBall : ball (0 : Plane) 1 → closedBall (0 : Plane) 1 :=
    fun y ↦ ⟨y, ball_subset_closedBall y.2⟩
  exact {
    toFun := fun x ↦ ⟨E.insideHomeomorph (toClosedInside x), E.inside_maps_open x⟩
    invFun := fun y ↦
      ⟨E.insideHomeomorph.symm (toClosedBall y), E.inside_inverse_maps_open y⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (E.insideHomeomorph.symm
        (E.insideHomeomorph (toClosedInside x)) : Plane) = x
      exact congrArg Subtype.val (E.insideHomeomorph.symm_apply_apply (toClosedInside x))
    right_inv := by
      intro y
      apply Subtype.ext
      change (E.insideHomeomorph
        (E.insideHomeomorph.symm (toClosedBall y)) : Plane) = y
      exact congrArg Subtype.val (E.insideHomeomorph.apply_symm_apply (toClosedBall y))
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp <|
        E.insideHomeomorph.continuous.comp <|
          continuous_subtype_val.subtype_mk fun x ↦ subset_closure x.2
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp <|
        E.insideHomeomorph.symm.continuous.comp <|
          continuous_subtype_val.subtype_mk fun y ↦ ball_subset_closedBall y.2
  }

/-- The open inside of a Jordan circle remains connected after deleting finitely many points. -/
theorem isConnected_inside_avoiding_finite
    (J : JordanCircle) {kappa : Type*} [Fintype kappa]
    (center : kappa → J.inside) :
    IsConnected {x : J.inside | ∀ i, x ≠ center i} := by
  let e := J.insideHomeomorphUnitBall
  let mappedCenter : kappa → ball (0 : Plane) 1 := fun i ↦ e (center i)
  have hball := Submission.Topology.isConnected_unitBall_avoiding_finite mappedCenter
  have himage : e.symm '' {x : ball (0 : Plane) 1 | ∀ i, x ≠ mappedCenter i} =
      {x : J.inside | ∀ i, x ≠ center i} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i hi
      apply hy i
      apply e.symm.injective
      simpa only [mappedCenter, Homeomorph.symm_apply_apply] using hi
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      intro i hi
      apply hx i
      apply e.injective
      simpa only [mappedCenter, Homeomorph.apply_symm_apply] using hi
  rw [← himage]
  exact hball.image _ e.symm.continuous.continuousOn

end Schoenflies.JordanCircle
