import Submission.Topology.GeneralCompression
import Submission.Topology.IntersectionCertificate
import Submission.Torus.AmbientTransfer

/-!
# Counting intersections with a general compressing disk

This file packages the quantitative consequence of the compression-side
topology.  An essential disk boundary has at least `min p q` signed
intersections with the `(p,q)` torus knot.  Any injective accounting of those
intersection parameters in a finite geometric set therefore has the same
lower bound.
-/

open Set

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Torus

noncomputable section

/-- Ambient intersection points of the original knot with the boundary loop
of a general compressing disk. -/
def compressionBoundaryIntersections {Phi : AmbientIsotopy}
    (K : Knot) (D : GeneralCompressingDiskWitness Phi) : Set R3 :=
  Set.range K.curve ∩ Set.range (fun t ↦ (D.boundaryLoop.curve t : R3))

/-- Send a standard torus-knot parameter to its point on the transported
torus. -/
def compressionParameterPoint (Phi : AmbientIsotopy) (p q : ℕ)
    (t : ℝ) : R3 :=
  transportedTorusMap Phi (torusKnotLift p q t)

theorem compressionParameterPoint_injOn
    (Phi : AmbientIsotopy) (p q : ℕ) (hc : p.Coprime q) :
    Set.InjOn (compressionParameterPoint Phi p q)
      (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  apply torusKnotLift_injOn p q hc hs ht
  exact transportedTorusMap_injective Phi hst

/-- A coordinate intersection parameter represents an actual ambient
intersection of the knot and disk boundary. -/
theorem compressionParameterPoint_mem_boundaryIntersections
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (D : GeneralCompressingDiskWitness Phi)
    {t : ℝ}
    (ht : t ∈ torusLoopIntersectionParameters p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)) :
    compressionParameterPoint Phi p q t ∈
      compressionBoundaryIntersections K D := by
  rcases ht with ⟨htIco, u, hu⟩
  constructor
  · rw [curve_range_eq_transportedTorusKnot_range p q K Phi sigma hclass]
    exact ⟨t, rfl⟩
  · refine ⟨u, ?_⟩
    change (D.boundaryLoop.curve u : R3) =
      transportedTorusMap Phi (torusKnotLift p q t)
    change (transportedTorusHomeomorph Phi).symm
      (D.boundaryLoop.curve u) = torusKnotLift p q t at hu
    calc
      (D.boundaryLoop.curve u : R3) =
          transportedTorusMap Phi ((transportedTorusHomeomorph Phi).symm
            (D.boundaryLoop.curve u)) := by
        exact congrArg Subtype.val
          ((transportedTorusHomeomorph Phi).apply_symm_apply
            (D.boundaryLoop.curve u)).symm
      _ = transportedTorusMap Phi (torusKnotLift p q t) :=
        congrArg (transportedTorusMap Phi) hu

/-- A transverse certificate for a general essential compressing boundary
already forces at least `min p q` coordinate intersection parameters. -/
theorem GeneralCompressingDiskWitness.min_le_intersectionParameters
    {Phi : AmbientIsotopy} (D : GeneralCompressingDiskWitness Phi)
    (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding) :
    min p q ≤ (torusLoopIntersectionParameters p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)).ncard :=
  (D.min_le_slopeIntersectionNumber p q).trans
    (slopeIntersectionNumber_le_ncard_of_transverseCertificate
      p q (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding C)

/-- Consequently, any injective charging of all compression-boundary
intersection parameters into a finite counted set contains at least
`min p q` elements.  This is the exact interface used by the double-bubble
accounting argument. -/
theorem GeneralCompressingDiskWitness.min_le_ncard_of_injective_charging
    {Phi : AmbientIsotopy} (D : GeneralCompressingDiskWitness Phi)
    (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding)
    {α : Type*} (counted : Set α) (hcounted : counted.Finite)
    (encode : ℝ → α)
    (hencode : ∀ t ∈ torusLoopIntersectionParameters p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve), encode t ∈ counted)
    (hinj : Set.InjOn encode (torusLoopIntersectionParameters p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve))) :
    min p q ≤ counted.ncard :=
  (D.min_le_intersectionParameters p q C).trans
    (Set.ncard_le_ncard_of_injOn encode hencode hinj hcounted)

end

end Submission.PardonDistortion
