import Submission.Topology.ArcReplacementConstruction

/-!
# Cyclic excursions and components of a plane slice

This module records finite cyclic interval bookkeeping for a regular periodic cutting height and
isolates the exact plane-slice connectivity issue at the endpoints of each excursion.

A path in the plane slice supplies a genuine replacement path.  It does not, by itself, supply a
relative homotopy from the original excursion to that path: on a torus, two paths with the same
endpoints can represent different relative homotopy classes.  Accordingly the results below do
not silently promote path connectivity to a winding-preserving arc replacement.  They construct
the slice path, and turn failure of slice connectivity plus a connection through the opposite
halfspace into the precise `DoubleBubbleConnectivityWitness` used downstream.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

variable {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {L : TransportedWindingLoop Phi parent}

/-! ## Cyclic interval bookkeeping -/

/-- One lifted excursion interval between consecutive crossings.  The right endpoint may lie in
the next period; this avoids a special case for the cyclic interval crossing the seam at `0`. -/
structure CyclicExcursionInterval
    (H : SmoothRegularLoopCutData frame d L) where
  left : ℝ
  right : ℝ
  left_mem_period : left ∈ Ico (0 : ℝ) (2 * Real.pi)
  left_lt_right : left < right
  right_le_next_period : right ≤ left + 2 * Real.pi
  left_crossing : windingLoopCutHeight frame d L left = 0
  right_crossing : windingLoopCutHeight frame d L right = 0
  /-- `true` denotes a strict upper excursion, `false` a strict lower excursion. -/
  upper : Bool
  strict_side : ∀ t ∈ Ioo left right,
    if upper then 0 < windingLoopCutHeight frame d L t
      else windingLoopCutHeight frame d L t < 0

namespace CyclicExcursionInterval

variable {H : SmoothRegularLoopCutData frame d L}

/-- The open parameter interval of an excursion. -/
def params (E : CyclicExcursionInterval H) : Set ℝ := Ioo E.left E.right

/-- Integer translate of an excursion interval. -/
def translatedParams (E : CyclicExcursionInterval H) (n : ℤ) : Set ℝ :=
  Ioo (E.left + (n : ℝ) * (2 * Real.pi))
    (E.right + (n : ℝ) * (2 * Real.pi))

theorem left_mem_plane (E : CyclicExcursionInterval H) :
    L.curve E.left ∈ planeSurfaceRegion Phi parent frame d := by
  exact ⟨L.curve_mem E.left, sub_eq_zero.mp E.left_crossing⟩

theorem right_mem_plane (E : CyclicExcursionInterval H) :
    L.curve E.right ∈ planeSurfaceRegion Phi parent frame d := by
  exact ⟨L.curve_mem E.right, sub_eq_zero.mp E.right_crossing⟩

theorem curve_mem_upper_of_mem_Icc (E : CyclicExcursionInterval H)
    (hupper : E.upper = true) {t : ℝ} (ht : t ∈ Icc E.left E.right) :
    L.curve t ∈ upperSurfaceRegion Phi parent frame d := by
  refine ⟨L.curve_mem t, ?_⟩
  change d ≤ (L.curve t : R3).ofLp (frame 2)
  rcases ht.1.eq_or_lt with rfl | hleft
  · exact (sub_eq_zero.mp E.left_crossing).ge
  rcases ht.2.eq_or_lt with rfl | hright
  · exact (sub_eq_zero.mp E.right_crossing).ge
  · have h := E.strict_side t ⟨hleft, hright⟩
    rw [hupper] at h
    exact (sub_pos.mp h).le

theorem curve_mem_lower_of_mem_Icc (E : CyclicExcursionInterval H)
    (hlower : E.upper = false) {t : ℝ} (ht : t ∈ Icc E.left E.right) :
    L.curve t ∈ lowerSurfaceRegion Phi parent frame d := by
  refine ⟨L.curve_mem t, ?_⟩
  change (L.curve t : R3).ofLp (frame 2) ≤ d
  rcases ht.1.eq_or_lt with rfl | hleft
  · exact (sub_eq_zero.mp E.left_crossing).le
  rcases ht.2.eq_or_lt with rfl | hright
  · exact (sub_eq_zero.mp E.right_crossing).le
  · have h := E.strict_side t ⟨hleft, hright⟩
    rw [hlower] at h
    exact (sub_neg.mp h).le

/-- The original parametrized excursion joins its two plane endpoints through the upper side. -/
theorem joinedIn_upper (E : CyclicExcursionInterval H) (hupper : E.upper = true) :
    JoinedIn (upperSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right) := by
  let f : ℝ → transportedTorus Phi :=
    fun s ↦ L.curve (E.left + (E.right - E.left) * s)
  apply JoinedIn.ofLine (f := f)
  · exact L.continuous_curve.comp
      (continuous_const.add (continuous_const.mul continuous_id)) |>.continuousOn
  · simp [f]
  · simp [f]
  · rintro _ ⟨s, hs, rfl⟩
    apply E.curve_mem_upper_of_mem_Icc hupper
    constructor <;> nlinarith [hs.1, hs.2, E.left_lt_right]

/-- The analogous connection through the lower side. -/
theorem joinedIn_lower (E : CyclicExcursionInterval H) (hlower : E.upper = false) :
    JoinedIn (lowerSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right) := by
  let f : ℝ → transportedTorus Phi :=
    fun s ↦ L.curve (E.left + (E.right - E.left) * s)
  apply JoinedIn.ofLine (f := f)
  · exact L.continuous_curve.comp
      (continuous_const.add (continuous_const.mul continuous_id)) |>.continuousOn
  · simp [f]
  · simp [f]
  · rintro _ ⟨s, hs, rfl⟩
    apply E.curve_mem_lower_of_mem_Icc hlower
    constructor <;> nlinarith [hs.1, hs.2, E.left_lt_right]

end CyclicExcursionInterval

/-- Complete finite cyclic bookkeeping.  Integer translates of the finitely many representatives
cover every noncrossing parameter, and distinct translated open intervals are disjoint. -/
structure FiniteCyclicExcursionBookkeeping
    (H : SmoothRegularLoopCutData frame d L) where
  count : ℕ
  excursion : Fin count → CyclicExcursionInterval H
  translated_pairwise_disjoint : Pairwise fun p q : Fin count × ℤ ↦
    Disjoint (excursion p.1 |>.translatedParams p.2)
      (excursion q.1 |>.translatedParams q.2)
  cover_noncrossings : ∀ t,
    windingLoopCutHeight frame d L t ≠ 0 →
      ∃ (i : Fin count) (n : ℤ), t ∈ (excursion i).translatedParams n
  no_crossing_in_excursion : ∀ (i : Fin count) (n : ℤ) t,
    t ∈ (excursion i).translatedParams n →
      windingLoopCutHeight frame d L t ≠ 0
  alternating_at_common_endpoint : ∀ i j,
    i ≠ j → (excursion i).right = (excursion j).left →
      (excursion i).upper ≠ (excursion j).upper

/-! ## Plane-slice path components -/

/-- Two crossing parameters represent the same path component of the plane slice. -/
def PlaneSliceEndpointEquivalent (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) (a b : ℝ) : Prop :=
  JoinedIn (planeSurfaceRegion Phi parent frame d) (L.curve a) (L.curve b)

/-- Crossing parameters, without choosing a particular fundamental period. -/
def CrossingParameter (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) :=
  {t : ℝ // windingLoopCutHeight frame d L t = 0}

theorem crossingParameter_mem_plane
    (t : CrossingParameter frame d L) :
    L.curve t.1 ∈ planeSurfaceRegion Phi parent frame d :=
  ⟨L.curve_mem t.1, sub_eq_zero.mp t.2⟩

/-- Plane-slice path-component equivalence is an actual setoid on crossing parameters. -/
def planeSliceEndpointSetoid : Setoid (CrossingParameter frame d L) where
  r a b := PlaneSliceEndpointEquivalent frame d L a.1 b.1
  iseqv := {
    refl := fun a ↦ JoinedIn.refl (crossingParameter_mem_plane a)
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂
  }

namespace CyclicExcursionInterval

variable {H : SmoothRegularLoopCutData frame d L}

/-- The exact component condition needed merely to choose a plane-slice replacement path. -/
def EndpointsJoinedInPlane (E : CyclicExcursionInterval H) : Prop :=
  PlaneSliceEndpointEquivalent frame d L E.left E.right

/-- A chosen replacement path inside the plane slice. -/
def sliceReplacementPath (E : CyclicExcursionInterval H)
    (h : E.EndpointsJoinedInPlane) : Path (L.curve E.left) (L.curve E.right) :=
  h.somePath

theorem sliceReplacementPath_mem (E : CyclicExcursionInterval H)
    (h : E.EndpointsJoinedInPlane) (t : unitInterval) :
    E.sliceReplacementPath h t ∈ planeSurfaceRegion Phi parent frame d :=
  h.somePath_mem t

/-- Failure of the endpoint condition is a precise separated-interface excursion: the endpoints
lie in the interface and are connected through one side, but not through the interface. -/
structure SeparatedPlaneExcursionWitness
    (E : CyclicExcursionInterval H) : Prop where
  separated : ¬ E.EndpointsJoinedInPlane

/-- An upper excursion whose endpoints are separated in the plane slice becomes a double bubble
as soon as the same endpoints are connected through the lower side. -/
def doubleBubble_of_upper_of_separated_of_joined_lower
    (E : CyclicExcursionInterval H) (hupper : E.upper = true)
    (hsep : ¬ E.EndpointsJoinedInPlane)
    (hlower : JoinedIn (lowerSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right)) :
    DoubleBubbleConnectivityWitness
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) where
  first := L.curve E.left
  second := L.curve E.right
  first_mem := E.left_mem_plane
  second_mem := E.right_mem_plane
  interface_subset := by
    intro x hx
    rw [lower_inter_upper_surfaceRegion]
    exact hx
  joined_left := hlower
  joined_right := E.joinedIn_upper hupper
  separated_interface := hsep

/-- Symmetric lower-excursion form. -/
def doubleBubble_of_lower_of_separated_of_joined_upper
    (E : CyclicExcursionInterval H) (hlower : E.upper = false)
    (hsep : ¬ E.EndpointsJoinedInPlane)
    (hupper : JoinedIn (upperSurfaceRegion Phi parent frame d)
      (L.curve E.left) (L.curve E.right)) :
    DoubleBubbleConnectivityWitness
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) where
  first := L.curve E.left
  second := L.curve E.right
  first_mem := E.left_mem_plane
  second_mem := E.right_mem_plane
  interface_subset := by
    intro x hx
    rw [lower_inter_upper_surfaceRegion]
    exact hx
  joined_left := E.joinedIn_lower hlower
  joined_right := hupper
  separated_interface := hsep

end CyclicExcursionInterval

/-! ## The relative-homotopy obstruction -/

/-- A relative homotopy between an original excursion and a selected slice path.  This is
strictly stronger than the endpoints merely belonging to the same slice path component. -/
structure RelativeSliceArcHomotopy
    {H : SmoothRegularLoopCutData frame d L}
    (E : CyclicExcursionInterval H) (slice : Path (L.curve E.left) (L.curve E.right)) where
  homotopy : unitInterval → unitInterval → transportedTorus Phi
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  zero : ∀ t, homotopy 0 t =
    L.curve (E.left + (E.right - E.left) * (t : ℝ))
  one : ∀ t, homotopy 1 t = slice t
  left_fixed : ∀ s, homotopy s 0 = L.curve E.left
  right_fixed : ∀ s, homotopy s 1 = L.curve E.right

/-- The strongest honest local input: a slice path together with the relative homotopy needed
for winding-preserving splicing. -/
structure HomotopicallyReroutableExcursion
    {H : SmoothRegularLoopCutData frame d L}
    (E : CyclicExcursionInterval H) where
  joined : E.EndpointsJoinedInPlane
  relative : RelativeSliceArcHomotopy E (E.sliceReplacementPath joined)

/-! ## Path connectivity cannot supply the missing relative homotopy -/

/-- The standard longitude in product-circle coordinates. -/
def standardLongitudeCoordinates (t : ℝ) : Circle × Circle :=
  (Circle.exp t, 1)

/-- The constant loop at the longitude basepoint. -/
def constantProductCoordinates (_t : ℝ) : Circle × Circle :=
  (1, 1)

/-- Explicit winding `(1,0)` for the standard longitude. -/
def standardLongitudeCoordinatesLift :
    TorusLoopLift standardLongitudeCoordinates where
  first := {
    angle := id
    continuous_angle := continuous_id
    exp_angle := fun _ ↦ rfl
    winding := 1
    angle_add_period := fun _ ↦ by simp
  }
  second := {
    angle := fun _ ↦ 0
    continuous_angle := continuous_const
    exp_angle := fun _ ↦ by simp [standardLongitudeCoordinates]
    winding := 0
    angle_add_period := fun _ ↦ by simp
  }

/-- Explicit winding `(0,0)` for the constant loop. -/
def constantProductCoordinatesLift :
    TorusLoopLift constantProductCoordinates where
  first := {
    angle := fun _ ↦ 0
    continuous_angle := continuous_const
    exp_angle := fun _ ↦ by simp [constantProductCoordinates]
    winding := 0
    angle_add_period := fun _ ↦ by simp
  }
  second := {
    angle := fun _ ↦ 0
    continuous_angle := continuous_const
    exp_angle := fun _ ↦ by simp [constantProductCoordinates]
    winding := 0
    angle_add_period := fun _ ↦ by simp
  }

/-- Although the longitude starts and ends at the constant loop's basepoint, it cannot be
periodically homotoped to that constant loop.  Thus endpoint path connectivity cannot justify the
relative homotopy field needed by a winding-preserving splice. -/
theorem not_periodicHomotopy_standardLongitude_constant :
    ¬ Nonempty (PeriodicTorusLoopHomotopy
      standardLongitudeCoordinates constantProductCoordinates) := by
  rintro ⟨K⟩
  have hwind := TorusLoopLift.windingPair_eq_of_periodicHomotopy K
    standardLongitudeCoordinatesLift constantProductCoordinatesLift
  have hfirst := congrArg Prod.fst hwind
  norm_num [TorusLoopLift.windingPair, standardLongitudeCoordinatesLift,
    constantProductCoordinatesLift] at hfirst

end Submission.Topology
