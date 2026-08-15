import Submission.Topology.CrossingSignFlip

/-!
# Winding-safe splices without a relative homotopy

This module separates the two issues in an excursion replacement.  A direct splice only needs a
continuous periodic replacement curve with endpoint agreement.  Preservation of winding is then
an algebraic question, detected by the coordinatewise difference between the old and new loops.

Merely assuming that loops *in the plane slice* have zero winding does not settle that algebraic
question: an excursion followed by the reverse slice path lies in a closed halfspace piece, not
in the plane slice.  The results below therefore state explicitly the additional condition under
which the difference loop is in the interface.  This is strictly weaker than a relative homotopy
and makes the remaining geometric obstruction visible rather than hiding it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

variable {Phi : AmbientIsotopy}
  {parent target interface : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-! ## The interface hypothesis -/

/-- Every periodic loop contained in the interface has trivial winding in both torus
coordinates. -/
def PlaneSliceLoopsHaveZeroWinding (Phi : AmbientIsotopy)
    (interface : Set (transportedTorus Phi)) : Prop :=
  ∀ K : TransportedWindingLoop Phi interface, K.windingPair = (0, 0)

theorem PlaneSliceLoopsHaveZeroWinding.mono
    {small large : Set (transportedTorus Phi)} (hsub : small ⊆ large)
    (hlarge : PlaneSliceLoopsHaveZeroWinding Phi large) :
    PlaneSliceLoopsHaveZeroWinding Phi small := by
  intro K
  exact hlarge (K.mono hsub)

/-! ## Direct splicing -/

/-- Homotopy-free data for replacing a periodic family of open arcs.  Agreement on the frontier
is exactly the endpoint condition needed for the piecewise curve to be continuous. -/
structure DirectPeriodicSpliceData
    {Phi : AmbientIsotopy} {parent target : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent) where
  active : Set ℝ
  active_periodic : ∀ t, t + 2 * Real.pi ∈ active ↔ t ∈ active
  replacement : ℝ → transportedTorus Phi
  continuous_replacement : Continuous replacement
  periodic_replacement : Function.Periodic replacement (2 * Real.pi)
  replacement_frontier : ∀ t ∈ frontier active, replacement t = original.curve t
  replacement_mem_target : ∀ t ∈ active, replacement t ∈ target
  original_mem_target_off : ∀ t, t ∉ active → original.curve t ∈ target

namespace DirectPeriodicSpliceData

variable {original : TransportedWindingLoop Phi parent}

/-- The direct piecewise splice. -/
def splicedCurve (D : DirectPeriodicSpliceData (target := target) original) (t : ℝ) :
    transportedTorus Phi := by
  classical
  exact if t ∈ D.active then D.replacement t else original.curve t

theorem continuous_splicedCurve
    (D : DirectPeriodicSpliceData (target := target) original) :
    Continuous D.splicedCurve := by
  classical
  change Continuous (fun t ↦ if t ∈ D.active then D.replacement t else original.curve t)
  apply continuous_if
  · exact D.replacement_frontier
  · exact D.continuous_replacement.continuousOn
  · exact original.continuous_curve.continuousOn

theorem periodic_splicedCurve
    (D : DirectPeriodicSpliceData (target := target) original) :
    Function.Periodic D.splicedCurve (2 * Real.pi) := by
  intro t
  classical
  by_cases ht : t ∈ D.active
  · have ht' : t + 2 * Real.pi ∈ D.active := (D.active_periodic t).mpr ht
    simp only [splicedCurve, if_pos ht, if_pos ht']
    exact D.periodic_replacement t
  · have ht' : t + 2 * Real.pi ∉ D.active := by
      intro h
      exact ht ((D.active_periodic t).mp h)
    simp only [splicedCurve, if_neg ht, if_neg ht']
    exact original.periodic_curve t

theorem splicedCurve_mem
    (D : DirectPeriodicSpliceData (target := target) original) (t : ℝ) :
    D.splicedCurve t ∈ target := by
  classical
  by_cases ht : t ∈ D.active
  · simpa only [splicedCurve, if_pos ht] using D.replacement_mem_target t ht
  · simpa only [splicedCurve, if_neg ht] using D.original_mem_target_off t ht

/-- The directly spliced curve bundled with a chosen covering lift. -/
def toWindingLoop (D : DirectPeriodicSpliceData (target := target) original) :
    TransportedWindingLoop Phi target where
  curve := D.splicedCurve
  continuous_curve := D.continuous_splicedCurve
  periodic_curve := D.periodic_splicedCurve
  curve_mem := D.splicedCurve_mem
  lift := (exists_torusLoopLift_of_transportedLoop Phi D.splicedCurve
    D.continuous_splicedCurve D.periodic_splicedCurve).some

end DirectPeriodicSpliceData

/-! ## Chosen slice paths and their direct assembly -/

/-- A path-component choice for every excursion in finite cyclic bookkeeping.  The actual paths
are obtained canonically from these proofs and lie in the plane slice. -/
structure ChosenPlaneSlicePaths
    {H : SmoothRegularLoopCutData frame d L}
    (B : FiniteCyclicExcursionBookkeeping H) : Prop where
  joined : ∀ i, (B.excursion i).EndpointsJoinedInPlane

namespace ChosenPlaneSlicePaths

variable {H : SmoothRegularLoopCutData frame d L}
  {B : FiniteCyclicExcursionBookkeeping H}

def path (P : ChosenPlaneSlicePaths B) (i : Fin B.count) :
    Path (L.curve (B.excursion i).left) (L.curve (B.excursion i).right) :=
  (B.excursion i).sliceReplacementPath (P.joined i)

theorem path_mem (P : ChosenPlaneSlicePaths B) (i : Fin B.count) (u : unitInterval) :
    P.path i u ∈ planeSurfaceRegion Phi parent frame d :=
  (B.excursion i).sliceReplacementPath_mem (P.joined i) u

end ChosenPlaneSlicePaths

/-- Direct global assembly of the chosen slice paths replacing every upper excursion.  This
contains no two-dimensional homotopy; `replacement_on_excursion` only records the finite path
gluing performed by the assembly. -/
structure UpperSlicePathDirectSpliceAssembly
    {H : SmoothRegularLoopCutData frame d L}
    (B : FiniteCyclicExcursionBookkeeping H) where
  paths : ChosenPlaneSlicePaths B
  splice : DirectPeriodicSpliceData
    (target := lowerSurfaceRegion Phi parent frame d) L
  active_eq : splice.active = upperExcursions frame d L
  replacement_on_excursion : ∀ (i : Fin B.count), (B.excursion i).upper = true →
    ∀ u : unitInterval,
      splice.replacement ((B.excursion i).left +
        ((B.excursion i).right - (B.excursion i).left) * (u : ℝ)) = paths.path i u

/-- Symmetric direct assembly replacing every lower excursion. -/
structure LowerSlicePathDirectSpliceAssembly
    {H : SmoothRegularLoopCutData frame d L}
    (B : FiniteCyclicExcursionBookkeeping H) where
  paths : ChosenPlaneSlicePaths B
  splice : DirectPeriodicSpliceData
    (target := upperSurfaceRegion Phi parent frame d) L
  active_eq : splice.active = lowerExcursions frame d L
  replacement_on_excursion : ∀ (i : Fin B.count), (B.excursion i).upper = false →
    ∀ u : unitInterval,
      splice.replacement ((B.excursion i).left +
        ((B.excursion i).right - (B.excursion i).left) * (u : ℝ)) = paths.path i u

/-! ## Coordinate-difference winding algebra -/

/-- Pointwise coordinate quotient of two transported-torus loops, transported back to the
embedded torus.  Its winding is the difference of their winding pairs. -/
def transportedLoopDifferenceCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) (u : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi
    (transportedLoopCoordinates Phi A.curve u / transportedLoopCoordinates Phi B.curve u)

theorem continuous_transportedLoopDifferenceCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    Continuous (transportedLoopDifferenceCurve A B) := by
  apply (transportedTorusHomeomorph Phi).continuous.comp
  have hA := continuous_transportedLoopCoordinates Phi A.curve A.continuous_curve
  have hB := continuous_transportedLoopCoordinates Phi B.curve B.continuous_curve
  exact (hA.fst.mul hB.fst.inv).prodMk (hA.snd.mul hB.snd.inv)

theorem periodic_transportedLoopDifferenceCurve
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    Function.Periodic (transportedLoopDifferenceCurve A B) (2 * Real.pi) := by
  intro u
  simp only [transportedLoopDifferenceCurve]
  rw [periodic_transportedLoopCoordinates Phi A.curve A.periodic_curve u,
    periodic_transportedLoopCoordinates Phi B.curve B.periodic_curve u]

/-- The explicit difference lift. -/
def transportedLoopDifferenceLift
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t) :
    TorusLoopLift (transportedLoopCoordinates Phi (transportedLoopDifferenceCurve A B)) where
  first := {
    angle := fun u ↦ A.lift.first.angle u - B.lift.first.angle u
    continuous_angle := A.lift.first.continuous_angle.sub B.lift.first.continuous_angle
    exp_angle := fun u ↦ by
      simp only [transportedLoopCoordinates, transportedLoopDifferenceCurve,
        Homeomorph.symm_apply_apply, Prod.fst_div]
      rw [Circle.exp_sub, A.lift.first.exp_angle, B.lift.first.exp_angle]
      rfl
    winding := A.lift.first.winding - B.lift.first.winding
    angle_add_period := fun u ↦ by
      rw [A.lift.first.angle_add_period, B.lift.first.angle_add_period]
      push_cast
      ring
  }
  second := {
    angle := fun u ↦ A.lift.second.angle u - B.lift.second.angle u
    continuous_angle := A.lift.second.continuous_angle.sub B.lift.second.continuous_angle
    exp_angle := fun u ↦ by
      simp only [transportedLoopCoordinates, transportedLoopDifferenceCurve,
        Homeomorph.symm_apply_apply, Prod.snd_div]
      rw [Circle.exp_sub, A.lift.second.exp_angle, B.lift.second.exp_angle]
      rfl
    winding := A.lift.second.winding - B.lift.second.winding
    angle_add_period := fun u ↦ by
      rw [A.lift.second.angle_add_period, B.lift.second.angle_add_period]
      push_cast
      ring
  }

/-- Bundle the difference loop when its range is known to lie in a specified set. -/
def transportedLoopDifference
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t)
    (hmem : ∀ u, transportedLoopDifferenceCurve A B u ∈ interface) :
    TransportedWindingLoop Phi interface where
  curve := transportedLoopDifferenceCurve A B
  continuous_curve := continuous_transportedLoopDifferenceCurve A B
  periodic_curve := periodic_transportedLoopDifferenceCurve A B
  curve_mem := hmem
  lift := transportedLoopDifferenceLift A B

theorem windingPair_transportedLoopDifference
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t)
    (hmem : ∀ u, transportedLoopDifferenceCurve A B u ∈ interface) :
    (transportedLoopDifference A B hmem).windingPair =
      (A.windingPair.1 - B.windingPair.1, A.windingPair.2 - B.windingPair.2) := by
  rfl

/-- If the coordinate-difference loop lies in a zero-winding interface, the two original loops
have identical winding pairs.  This is the covering-lift algebra required by a splice. -/
theorem windingPair_eq_of_difference_mem_zeroWindingInterface
    {s t : Set (transportedTorus Phi)}
    (A : TransportedWindingLoop Phi s) (B : TransportedWindingLoop Phi t)
    (hzero : PlaneSliceLoopsHaveZeroWinding Phi interface)
    (hmem : ∀ u, transportedLoopDifferenceCurve A B u ∈ interface) :
    A.windingPair = B.windingPair := by
  have h := hzero (transportedLoopDifference A B hmem)
  rw [windingPair_transportedLoopDifference] at h
  apply Prod.ext
  · exact sub_eq_zero.mp (congrArg Prod.fst h)
  · exact sub_eq_zero.mp (congrArg Prod.snd h)

/-! ## Winding-preserving outcomes -/

/-- Rerouting output with exactly the invariant needed by a loop carrier.  Unlike
`PeriodicArcReplacement`, this does not assert a periodic homotopy. -/
inductive WindingLoopReroutingOutcome
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (left right interface : Set (transportedTorus Phi))
    (original : TransportedWindingLoop Phi parent) : Type
  | inLeft (rerouted : TransportedWindingLoop Phi left)
      (winding_eq : rerouted.windingPair = original.windingPair)
  | inRight (rerouted : TransportedWindingLoop Phi right)
      (winding_eq : rerouted.windingPair = original.windingPair)
  | bubble (witness : DoubleBubbleConnectivityWitness left right interface)

/-- A direct lower splice gives a winding-preserving outcome once its coordinate defect lies in
the zero-winding interface. -/
def lowerWindingReroutingOutcomeOfDirectSplice
    (D : DirectPeriodicSpliceData
      (target := lowerSurfaceRegion Phi parent frame d) L)
    (hzero : PlaneSliceLoopsHaveZeroWinding Phi
      (planeSurfaceRegion Phi parent frame d))
    (hmem : ∀ u, transportedLoopDifferenceCurve D.toWindingLoop L u ∈
      planeSurfaceRegion Phi parent frame d) :
    WindingLoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .inLeft D.toWindingLoop
    (windingPair_eq_of_difference_mem_zeroWindingInterface D.toWindingLoop L hzero hmem)

/-- Symmetric direct upper-splice outcome. -/
def upperWindingReroutingOutcomeOfDirectSplice
    (D : DirectPeriodicSpliceData
      (target := upperSurfaceRegion Phi parent frame d) L)
    (hzero : PlaneSliceLoopsHaveZeroWinding Phi
      (planeSurfaceRegion Phi parent frame d))
    (hmem : ∀ u, transportedLoopDifferenceCurve D.toWindingLoop L u ∈
      planeSurfaceRegion Phi parent frame d) :
    WindingLoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .inRight D.toWindingLoop
    (windingPair_eq_of_difference_mem_zeroWindingInterface D.toWindingLoop L hzero hmem)

/-! ## The separated-endpoint branch -/

/-- A separated upper excursion, together with the genuinely geometric connection through the
opposite side, remains an explicit double-bubble outcome. -/
def windingReroutingOutcomeBubbleOfSeparatedUpper
    {H : SmoothRegularLoopCutData frame d L}
    (E : CyclicExcursionInterval H) (hupper : E.upper = true)
    (hsep : ¬ E.EndpointsJoinedInPlane)
    (hlower : JoinedIn (lowerSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right)) :
    WindingLoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .bubble (E.doubleBubble_of_upper_of_separated_of_joined_lower hupper hsep hlower)

/-- Symmetric lower-excursion double-bubble outcome. -/
def windingReroutingOutcomeBubbleOfSeparatedLower
    {H : SmoothRegularLoopCutData frame d L}
    (E : CyclicExcursionInterval H) (hlower : E.upper = false)
    (hsep : ¬ E.EndpointsJoinedInPlane)
    (hupper : JoinedIn (upperSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right)) :
    WindingLoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L :=
  .bubble (E.doubleBubble_of_lower_of_separated_of_joined_upper hlower hsep hupper)

/-! ## A complete honest certificate -/

/-- The alternatives needed after finite excursion bookkeeping.  In the joined cases the chosen
slice paths have been assembled into a direct splice and the coordinate defect is explicitly
known to lie in the zero-winding interface.  In a separated case only the opposite-side
connection needed for a double bubble is assumed. -/
inductive ExcursionReroutingCertificate
    {H : SmoothRegularLoopCutData frame d L}
    (B : FiniteCyclicExcursionBookkeeping H) : Type
  | lower (A : UpperSlicePathDirectSpliceAssembly B)
      (difference_mem : ∀ u,
        transportedLoopDifferenceCurve A.splice.toWindingLoop L u ∈
          planeSurfaceRegion Phi parent frame d)
  | upper (A : LowerSlicePathDirectSpliceAssembly B)
      (difference_mem : ∀ u,
        transportedLoopDifferenceCurve A.splice.toWindingLoop L u ∈
          planeSurfaceRegion Phi parent frame d)
  | separatedUpper (i : Fin B.count) (upper : (B.excursion i).upper = true)
      (separated : ¬ (B.excursion i).EndpointsJoinedInPlane)
      (joinedLower : JoinedIn (lowerSurfaceRegion Phi parent frame d)
        (L.curve (B.excursion i).left) (L.curve (B.excursion i).right))
  | separatedLower (i : Fin B.count) (lower : (B.excursion i).upper = false)
      (separated : ¬ (B.excursion i).EndpointsJoinedInPlane)
      (joinedUpper : JoinedIn (upperSurfaceRegion Phi parent frame d)
        (L.curve (B.excursion i).left) (L.curve (B.excursion i).right))

/-- A finite-excursion certificate produces the homotopy-free rerouting-or-double-bubble output.
The sole global winding hypothesis is that interface loops have zero winding; application of that
hypothesis is justified by the explicit difference-range field of the joined constructors. -/
def ExcursionReroutingCertificate.toOutcome
    {H : SmoothRegularLoopCutData frame d L}
    {B : FiniteCyclicExcursionBookkeeping H}
    (C : ExcursionReroutingCertificate B)
    (hzero : PlaneSliceLoopsHaveZeroWinding Phi
      (planeSurfaceRegion Phi parent frame d)) :
    WindingLoopReroutingOutcome
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) L := by
  cases C with
  | lower A hmem =>
      exact lowerWindingReroutingOutcomeOfDirectSplice A.splice hzero hmem
  | upper A hmem =>
      exact upperWindingReroutingOutcomeOfDirectSplice A.splice hzero hmem
  | separatedUpper i hu hsep hlower =>
      exact windingReroutingOutcomeBubbleOfSeparatedUpper (B.excursion i) hu hsep hlower
  | separatedLower i hl hsep hupper =>
      exact windingReroutingOutcomeBubbleOfSeparatedLower (B.excursion i) hl hsep hupper

end Submission.Topology
