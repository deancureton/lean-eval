import Submission.Topology.WindingSafeSplice

/-!
# Additive winding decompositions across a cut

Replacing upper and lower excursions separately need not preserve the winding of either resulting
loop.  The correct weaker invariant is additive: if the same interface paths are used with
opposite orientations, the original winding class is the sum of the lower and upper classes.

This file proves all covering-lift and determinant algebra after isolating the precise remaining
topological assertion as zero winding of the *combined splice defect*.  Endpoint connectivity by
itself is not silently promoted to that assertion.  The final alternative says that one side
carries two independent loops, or there is an independent mixed pair; the existing honest
mixed-pair-to-double-bubble hypothesis turns the latter into a double bubble.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

variable {Phi : AmbientIsotopy}
  {parent left right interface : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-! ## Product-loop lift algebra -/

/-- Pointwise product in product-circle coordinates, transported back to the embedded torus. -/
def transportedLoopProductCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) (u : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi
    (transportedLoopCoordinates Phi A.curve u * transportedLoopCoordinates Phi B.curve u)

theorem continuous_transportedLoopProductCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    Continuous (transportedLoopProductCurve A B) := by
  apply (transportedTorusHomeomorph Phi).continuous.comp
  have hA := continuous_transportedLoopCoordinates Phi A.curve A.continuous_curve
  have hB := continuous_transportedLoopCoordinates Phi B.curve B.continuous_curve
  exact (hA.fst.mul hB.fst).prodMk (hA.snd.mul hB.snd)

theorem periodic_transportedLoopProductCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    Function.Periodic (transportedLoopProductCurve A B) (2 * Real.pi) := by
  intro u
  simp only [transportedLoopProductCurve]
  rw [periodic_transportedLoopCoordinates Phi A.curve A.periodic_curve u,
    periodic_transportedLoopCoordinates Phi B.curve B.periodic_curve u]

/-- Adding coordinate lifts lifts the pointwise product, and adds winding pairs. -/
def transportedLoopProductLift
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    TorusLoopLift (transportedLoopCoordinates Phi (transportedLoopProductCurve A B)) where
  first := {
    angle := fun u ↦ A.lift.first.angle u + B.lift.first.angle u
    continuous_angle := A.lift.first.continuous_angle.add B.lift.first.continuous_angle
    exp_angle := fun u ↦ by
      simp only [transportedLoopCoordinates, transportedLoopProductCurve,
        Homeomorph.symm_apply_apply, Prod.fst_mul]
      rw [Circle.exp_add, A.lift.first.exp_angle, B.lift.first.exp_angle]
      rfl
    winding := A.lift.first.winding + B.lift.first.winding
    angle_add_period := fun u ↦ by
      rw [A.lift.first.angle_add_period, B.lift.first.angle_add_period]
      push_cast
      ring
  }
  second := {
    angle := fun u ↦ A.lift.second.angle u + B.lift.second.angle u
    continuous_angle := A.lift.second.continuous_angle.add B.lift.second.continuous_angle
    exp_angle := fun u ↦ by
      simp only [transportedLoopCoordinates, transportedLoopProductCurve,
        Homeomorph.symm_apply_apply, Prod.snd_mul]
      rw [Circle.exp_add, A.lift.second.exp_angle, B.lift.second.exp_angle]
      rfl
    winding := A.lift.second.winding + B.lift.second.winding
    angle_add_period := fun u ↦ by
      rw [A.lift.second.angle_add_period, B.lift.second.angle_add_period]
      push_cast
      ring
  }

/-- The product loop, placed in `univ` because pointwise torus multiplication need not preserve
either geometric side of the cut. -/
def transportedLoopProduct
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    TransportedWindingLoop Phi Set.univ where
  curve := transportedLoopProductCurve A B
  continuous_curve := continuous_transportedLoopProductCurve A B
  periodic_curve := periodic_transportedLoopProductCurve A B
  curve_mem := fun _ ↦ mem_univ _
  lift := transportedLoopProductLift A B

theorem windingPair_transportedLoopProduct
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    (transportedLoopProduct A B).windingPair =
      (A.windingPair.1 + B.windingPair.1, A.windingPair.2 + B.windingPair.2) := by
  rfl

/-! ## The honest cancellation contract -/

/-- The combined defect compares the parent loop with the pointwise product of its lower and
upper splices.  Zero winding of this loop is precisely the homological cancellation assertion
supplied, mathematically, by concatenating the common interface paths in opposite directions. -/
def CombinedSpliceDefectHasZeroWinding
    {s t : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent)
    (lower : TransportedWindingLoop Phi s) (upper : TransportedWindingLoop Phi t) : Prop :=
  (transportedLoopDifferenceLift original (transportedLoopProduct lower upper)).windingPair =
    (0, 0)

/-- The explicit product/difference lifts turn zero combined defect into the desired additive
winding formula. -/
theorem windingPair_eq_add_of_combinedSpliceDefect_zero
    {s t : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent)
    (lower : TransportedWindingLoop Phi s) (upper : TransportedWindingLoop Phi t)
    (hzero : CombinedSpliceDefectHasZeroWinding original lower upper) :
    original.windingPair =
      (lower.windingPair.1 + upper.windingPair.1,
        lower.windingPair.2 + upper.windingPair.2) := by
  change
    (original.windingPair.1 -
      (lower.windingPair.1 + upper.windingPair.1),
     original.windingPair.2 -
      (lower.windingPair.2 + upper.windingPair.2)) = (0, 0) at hzero
  apply Prod.ext
  · exact sub_eq_zero.mp (congrArg Prod.fst hzero)
  · exact sub_eq_zero.mp (congrArg Prod.snd hzero)

/-- A stronger sufficient condition: if the combined defect loop actually lies in an interface
whose loops all have zero winding, cancellation follows.  No claim is made that ordinary plane
slice paths imply this range condition. -/
theorem combinedSpliceDefect_zero_of_mem_zeroWindingInterface
    {s t : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent)
    (lower : TransportedWindingLoop Phi s) (upper : TransportedWindingLoop Phi t)
    (hinterface : PlaneSliceLoopsHaveZeroWinding Phi interface)
    (hmem : ∀ u,
      transportedLoopDifferenceCurve original (transportedLoopProduct lower upper) u ∈
        interface) :
    CombinedSpliceDefectHasZeroWinding original lower upper := by
  have h := hinterface
    (transportedLoopDifference original (transportedLoopProduct lower upper) hmem)
  exact h

/-! ## Paired direct slice-path assembly -/

/-- Both direct splices assembled from one family of interface paths.  This is the endpoint/path
input; cancellation of their total winding is deliberately a separate field in
`AdditiveWindingCutDecomposition`. -/
structure PairedSlicePathDirectSpliceAssembly
    {H : SmoothRegularLoopCutData frame d L}
    (B : FiniteCyclicExcursionBookkeeping H) where
  paths : ChosenPlaneSlicePaths B
  lowerSplice : DirectPeriodicSpliceData
    (target := lowerSurfaceRegion Phi parent frame d) L
  upperSplice : DirectPeriodicSpliceData
    (target := upperSurfaceRegion Phi parent frame d) L
  lower_active : lowerSplice.active = upperExcursions frame d L
  upper_active : upperSplice.active = lowerExcursions frame d L
  lower_replacement : ∀ (i : Fin B.count), (B.excursion i).upper = true →
    ∀ u : unitInterval,
      lowerSplice.replacement ((B.excursion i).left +
        ((B.excursion i).right - (B.excursion i).left) * (u : ℝ)) = paths.path i u
  upper_replacement : ∀ (i : Fin B.count), (B.excursion i).upper = false →
    ∀ u : unitInterval,
      upperSplice.replacement ((B.excursion i).left +
        ((B.excursion i).right - (B.excursion i).left) * (u : ℝ)) = paths.path i u

/-- A parent loop decomposed into a lower and upper winding loop with additive winding pair. -/
structure AdditiveWindingCutDecomposition
    (left right : Set (transportedTorus Phi))
    (original : TransportedWindingLoop Phi parent) where
  lower : TransportedWindingLoop Phi left
  upper : TransportedWindingLoop Phi right
  winding_add : original.windingPair =
    (lower.windingPair.1 + upper.windingPair.1,
      lower.windingPair.2 + upper.windingPair.2)

/-- Paired direct splices give an additive decomposition once their combined defect cancellation
is supplied. -/
def PairedSlicePathDirectSpliceAssembly.toAdditiveWindingCutDecomposition
    {H : SmoothRegularLoopCutData frame d L}
    {B : FiniteCyclicExcursionBookkeeping H}
    (A : PairedSlicePathDirectSpliceAssembly B)
    (hzero : CombinedSpliceDefectHasZeroWinding L
      A.lowerSplice.toWindingLoop A.upperSplice.toWindingLoop) :
    AdditiveWindingCutDecomposition
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d) L where
  lower := A.lowerSplice.toWindingLoop
  upper := A.upperSplice.toWindingLoop
  winding_add := windingPair_eq_add_of_combinedSpliceDefect_zero _ _ _ hzero

/-! ## Determinant case algebra -/

/-- An independent pair split across the two sides. -/
structure MixedIndependentWindingPair
    (Phi : AmbientIsotopy)
    (left right : Set (transportedTorus Phi)) where
  lower : TransportedWindingLoop Phi left
  upper : TransportedWindingLoop Phi right
  independent : windingDet lower.windingPair.1 lower.windingPair.2
    upper.windingPair.1 upper.windingPair.2 ≠ 0

/-- Determinant bilinearity for two additive winding decompositions. -/
theorem windingDet_add_add
    (l₁ u₁ l₂ u₂ : ℤ × ℤ) :
    windingDet (l₁.1 + u₁.1) (l₁.2 + u₁.2)
      (l₂.1 + u₂.1) (l₂.2 + u₂.2) =
      windingDet l₁.1 l₁.2 l₂.1 l₂.2 +
      windingDet l₁.1 l₁.2 u₂.1 u₂.2 +
      windingDet u₁.1 u₁.2 l₂.1 l₂.2 +
      windingDet u₁.1 u₁.2 u₂.1 u₂.2 := by
  simp only [windingDet]
  ring

/-- Two independent parent classes with additive decompositions yield a same-side carrier or an
independent mixed pair. -/
theorem loopCarrier_or_mixed_of_additiveDecompositions
    (W : LoopCarrierWitness Phi parent)
    (D₁ : AdditiveWindingCutDecomposition left right W.first)
    (D₂ : AdditiveWindingCutDecomposition left right W.second) :
    CarriesLoopTorusGenus Phi left ∨ CarriesLoopTorusGenus Phi right ∨
      Nonempty (MixedIndependentWindingPair Phi left right) := by
  let dll := windingDet D₁.lower.windingPair.1 D₁.lower.windingPair.2
    D₂.lower.windingPair.1 D₂.lower.windingPair.2
  let dlu := windingDet D₁.lower.windingPair.1 D₁.lower.windingPair.2
    D₂.upper.windingPair.1 D₂.upper.windingPair.2
  let dul := windingDet D₁.upper.windingPair.1 D₁.upper.windingPair.2
    D₂.lower.windingPair.1 D₂.lower.windingPair.2
  let duu := windingDet D₁.upper.windingPair.1 D₁.upper.windingPair.2
    D₂.upper.windingPair.1 D₂.upper.windingPair.2
  by_cases hll : dll ≠ 0
  · exact Or.inl ⟨{
      first := D₁.lower
      second := D₂.lower
      independent := hll
    }⟩
  by_cases huu : duu ≠ 0
  · exact Or.inr (Or.inl ⟨{
      first := D₁.upper
      second := D₂.upper
      independent := huu
    }⟩)
  by_cases hlu : dlu ≠ 0
  · exact Or.inr (Or.inr ⟨{
      lower := D₁.lower
      upper := D₂.upper
      independent := hlu
    }⟩)
  have hul : dul ≠ 0 := by
    intro hul0
    have hll0 : dll = 0 := not_ne_iff.mp hll
    have hlu0 : dlu = 0 := not_ne_iff.mp hlu
    have huu0 : duu = 0 := not_ne_iff.mp huu
    apply W.independent
    rw [D₁.winding_add, D₂.winding_add, windingDet_add_add]
    change dll + dlu + dul + duu = 0
    rw [hll0, hlu0, hul0, huu0]
    norm_num
  exact Or.inr (Or.inr ⟨{
    lower := D₂.lower
    upper := D₁.upper
    independent := by
      intro hzero
      apply hul
      change windingDet D₁.upper.windingPair.1 D₁.upper.windingPair.2
        D₂.lower.windingPair.1 D₂.lower.windingPair.2 = 0
      calc
        windingDet D₁.upper.windingPair.1 D₁.upper.windingPair.2
            D₂.lower.windingPair.1 D₂.lower.windingPair.2 =
            -windingDet D₂.lower.windingPair.1 D₂.lower.windingPair.2
              D₁.upper.windingPair.1 D₁.upper.windingPair.2 := by
          simp only [windingDet]
          ring
        _ = 0 := neg_eq_zero.mpr hzero
  }⟩)

/-- Under the existing explicit mixed-connectivity contract, the algebraic mixed branch becomes
a double bubble. -/
theorem loopCarrier_or_doubleBubble_of_additiveDecompositions
    (W : LoopCarrierWitness Phi parent)
    (D₁ : AdditiveWindingCutDecomposition left right W.first)
    (D₂ : AdditiveWindingCutDecomposition left right W.second)
    (hmixed : MixedLoopReroutingProducesBubble Phi left right interface) :
    CarriesLoopTorusGenus Phi left ∨ CarriesLoopTorusGenus Phi right ∨
      Nonempty (DoubleBubbleConnectivityWitness left right interface) := by
  rcases loopCarrier_or_mixed_of_additiveDecompositions W D₁ D₂ with
    hleft | hrest
  · exact Or.inl hleft
  · rcases hrest with hright | hmixedPair
    · exact Or.inr (Or.inl hright)
    · obtain ⟨M⟩ := hmixedPair
      exact Or.inr (Or.inr (hmixed M.lower M.upper M.independent))

end Submission.Topology
