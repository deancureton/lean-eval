import Submission.CompressionExclusion
import Submission.Torus.AmbientTransfer

/-!
# Reparametrizing geometric intersections into the counted fundamental period

The geometric torus-knot intersection certificate is parametrized by the
standard `(p,q)` curve.  The coarea counts use the given knot's parameter.
This file supplies the exact, injective bridge between those parameter sets,
including reduction to `[0,2π)` and the two tagged copies of cutting-plane
events.
-/

open Set

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Torus

noncomputable section

/-- The parameter of the given knot corresponding to a standard torus-knot
parameter, reduced to the half-open fundamental period. -/
def knotFundamentalParameter (sigma : CircleReparam) (t : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0 (sigma.finv t)

theorem knotFundamentalParameter_mem_Ico
    (sigma : CircleReparam) (t : ℝ) :
    knotFundamentalParameter sigma t ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  simpa [knotFundamentalParameter] using
    toIcoMod_mem_Ico Real.two_pi_pos 0 (sigma.finv t)

private theorem knot_curve_periodic (K : Knot) :
    Function.Periodic K.curve (2 * Real.pi) :=
  K.periodic

theorem knot_curve_knotFundamentalParameter
    (K : Knot) (sigma : CircleReparam) (t : ℝ) :
    K.curve (knotFundamentalParameter sigma t) = K.curve (sigma.finv t) := by
  let n : ℤ := toIcoDiv Real.two_pi_pos 0 (sigma.finv t)
  have hsum : knotFundamentalParameter sigma t + n • (2 * Real.pi) =
      sigma.finv t := by
    simp [knotFundamentalParameter, n]
  calc
    K.curve (knotFundamentalParameter sigma t) =
        K.curve (knotFundamentalParameter sigma t + n • (2 * Real.pi)) :=
      ((knot_curve_periodic K).zsmul n
        (knotFundamentalParameter sigma t)).symm
    _ = K.curve (sigma.finv t) := congrArg K.curve hsum

/-- The reduced parameter evaluates to the transported standard torus-knot
point with the original standard parameter. -/
theorem curve_knotFundamentalParameter_eq_transportedTorusKnot
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (t : ℝ) :
    K.curve (knotFundamentalParameter sigma t) =
      transportedTorusMap Phi (torusKnotLift p q t) := by
  rw [knot_curve_knotFundamentalParameter K sigma t,
    curve_eq_transportedTorusMap p q K Phi sigma hclass,
    sigma.right_inv]

/-- Coprimality makes the standard-to-given fundamental parameter bridge
injective on one standard period. -/
theorem knotFundamentalParameter_injOn
    (p q : ℕ) (hc : p.Coprime q) (K : Knot) (Phi : AmbientIsotopy)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) :
    Set.InjOn (knotFundamentalParameter sigma)
      (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  apply torusKnotLift_injOn p q hc hs ht
  apply transportedTorusMap_injective Phi
  rw [← curve_knotFundamentalParameter_eq_transportedTorusKnot
      p q K Phi sigma hclass s,
    ← curve_knotFundamentalParameter_eq_transportedTorusKnot
      p q K Phi sigma hclass t,
    hst]

namespace DoubleBubbleSelection

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {Phi : AmbientIsotopy}

/-- Geometric assignment of every compression-boundary intersection either
to the outer boundary or to one of the two copies of the cutting plane. -/
structure BoundaryEventAssignment
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (sigma : CircleReparam) where
  tag : ℝ → Sum Unit Bool
  mem_event : ∀ t ∈ torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve),
    match tag t with
    | Sum.inl _ => knotFundamentalParameter sigma t ∈
        Submission.Coarea.fiberSet (orientedShellParameter K frame c)
          (Ico (0 : ℝ) (2 * Real.pi)) S.outerScale
    | Sum.inr _ => knotFundamentalParameter sigma t ∈
        orientedCutParameterSet K frame c S.outerScale S.cutHeight

/-- Encode a geometric event in the concrete disjoint-sum finset used by the
`160D` accounting. -/
def BoundaryEventAssignment.encode
    {S : DoubleBubbleSelection K frame c r}
    {D : GeneralCompressingDiskWitness Phi} {p q : ℕ}
    {sigma : CircleReparam} (A : BoundaryEventAssignment S D p q sigma)
    (t : ℝ) : Sum ℝ (Bool × ℝ) :=
  match A.tag t with
  | Sum.inl _ => Sum.inl (knotFundamentalParameter sigma t)
  | Sum.inr side => Sum.inr (side, knotFundamentalParameter sigma t)

/-- A geometric event assignment canonically gives the injective charging
required by the compression-exclusion theorem. -/
def BoundaryEventAssignment.toCompressionCharging
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (A : BoundaryEventAssignment S D p q sigma) :
    S.CompressionCharging D p q where
  encode := A.encode
  mem_counted := by
    intro t ht
    have hevent := A.mem_event t ht
    cases htag : A.tag t with
    | inl u =>
        simpa [DoubleBubbleSelection.countedEvents,
          BoundaryEventAssignment.encode, htag] using hevent
    | inr side =>
        simpa [DoubleBubbleSelection.countedEvents,
          BoundaryEventAssignment.encode, htag] using hevent
  injOn := by
    intro s hs t ht hst
    have hbridge := knotFundamentalParameter_injOn
      p q hc K Phi sigma hclass
    apply hbridge hs.1 ht.1
    cases htags : A.tag s with
    | inl us =>
        cases htagt : A.tag t with
        | inl ut => simpa [BoundaryEventAssignment.encode, htags, htagt] using hst
        | inr sidet => simp [BoundaryEventAssignment.encode, htags, htagt] at hst
    | inr sides =>
        cases htagt : A.tag t with
        | inl ut => simp [BoundaryEventAssignment.encode, htags, htagt] at hst
        | inr sidet =>
            have hp := congrArg (fun z : Sum ℝ (Bool × ℝ) ↦
              match z with
              | Sum.inl _ => 0
              | Sum.inr v => v.2) hst
            simpa [BoundaryEventAssignment.encode, htags, htagt] using hp

end DoubleBubbleSelection

end

end Submission.PardonDistortion
