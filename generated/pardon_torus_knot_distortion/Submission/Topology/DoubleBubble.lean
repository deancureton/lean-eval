import Submission.Topology.Carrier

/-!
# The explicit double-bubble alternative for a binary cut

Mathlib currently has no singular-homology Mayer--Vietoris sequence from which to extract the
usual rank-two carrier argument.  This file therefore isolates its exact geometric conclusion as
an explicit connectivity witness.  Two interface points form a double bubble when they are joined
through each side of a cut but are not joined inside the interface itself.

Such a witness supplies two genuine excursions from the interface and a glued loop in the union
of the sides.  The final section packages the precise carrier-or-double-bubble cut principle and
proves the logical consequences needed by a nested-carrier construction.  The principle remains
an explicit hypothesis; no homology or surface-classification theorem is hidden in its name.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

/-! ## A concrete connectivity witness -/

/-- Two interface points joined through both sides, but lying in distinct path components of the
interface.  This is the path-level content of the double-bubble conclusion of Mayer--Vietoris. -/
structure DoubleBubbleConnectivityWitness {X : Type*} [TopologicalSpace X]
    (left right interface : Set X) where
  first : X
  second : X
  first_mem : first ∈ interface
  second_mem : second ∈ interface
  interface_subset : interface ⊆ left ∩ right
  joined_left : JoinedIn left first second
  joined_right : JoinedIn right first second
  separated_interface : ¬ JoinedIn interface first second

namespace DoubleBubbleConnectivityWitness

variable {X : Type*} [TopologicalSpace X]
  {left right interface : Set X}

/-- The two marked interface points of a double bubble are distinct. -/
theorem first_ne_second
    (W : DoubleBubbleConnectivityWitness left right interface) :
    W.first ≠ W.second := by
  intro heq
  apply W.separated_interface
  rw [heq]
  exact JoinedIn.refl W.second_mem

/-- A double-bubble interface is not path connected. -/
theorem not_isPathConnected_interface
    (W : DoubleBubbleConnectivityWitness left right interface) :
    ¬ IsPathConnected interface := by
  intro hconnected
  exact W.separated_interface
    (hconnected.joinedIn W.first W.first_mem W.second W.second_mem)

/-- If every pair of interface points is joined inside the interface, no double-bubble witness
can exist.  Unlike `IsPathConnected`, this hypothesis also handles the empty interface. -/
theorem isEmpty_of_forall_joinedIn
    (hinterface : ∀ x ∈ interface, ∀ y ∈ interface, JoinedIn interface x y) :
    IsEmpty (DoubleBubbleConnectivityWitness left right interface) :=
  ⟨fun W ↦ W.separated_interface
    (hinterface W.first W.first_mem W.second W.second_mem)⟩

/-- In particular, a path-connected interface admits no double bubble. -/
theorem isEmpty_of_isPathConnected
    (hinterface : IsPathConnected interface) :
    IsEmpty (DoubleBubbleConnectivityWitness left right interface) :=
  isEmpty_of_forall_joinedIn fun x hx y hy ↦
    hinterface.joinedIn x hx y hy

/-- An interface containing at most one point admits no double bubble. -/
theorem isEmpty_of_subsingleton
    (hinterface : interface.Subsingleton) :
    IsEmpty (DoubleBubbleConnectivityWitness left right interface) :=
  ⟨fun W ↦ W.first_ne_second (hinterface W.first_mem W.second_mem)⟩

/-- A chosen path through the left side. -/
def leftPath (W : DoubleBubbleConnectivityWitness left right interface) :
    Path W.first W.second :=
  W.joined_left.somePath

/-- A chosen path through the right side. -/
def rightPath (W : DoubleBubbleConnectivityWitness left right interface) :
    Path W.first W.second :=
  W.joined_right.somePath

/-- Traverse the left path and return along the right path. -/
def gluedLoop (W : DoubleBubbleConnectivityWitness left right interface) :
    Path W.first W.first :=
  W.leftPath.trans W.rightPath.symm

/-- The glued double-bubble loop stays in the union of the two sides. -/
theorem range_gluedLoop_subset_union
    (W : DoubleBubbleConnectivityWitness left right interface) :
    Set.range W.gluedLoop ⊆ left ∪ right := by
  rw [gluedLoop, Path.trans_range, Path.symm_range]
  apply union_subset_union
  · rintro _ ⟨t, rfl⟩
    exact W.joined_left.somePath_mem t
  · rintro _ ⟨t, rfl⟩
    exact W.joined_right.somePath_mem t

/-- The left connecting path genuinely leaves the interface. -/
theorem exists_leftPath_not_mem_interface
    (W : DoubleBubbleConnectivityWitness left right interface) :
    ∃ t, W.leftPath t ∉ interface := by
  by_contra h
  apply W.separated_interface
  refine ⟨W.leftPath, ?_⟩
  intro t
  by_contra ht
  exact h ⟨t, ht⟩

/-- The right connecting path also genuinely leaves the interface. -/
theorem exists_rightPath_not_mem_interface
    (W : DoubleBubbleConnectivityWitness left right interface) :
    ∃ t, W.rightPath t ∉ interface := by
  by_contra h
  apply W.separated_interface
  refine ⟨W.rightPath, ?_⟩
  intro t
  by_contra ht
  exact h ⟨t, ht⟩

/-- Enlarge the two sides while keeping the same interface and double-bubble witness. -/
def mono_sides {left' right' : Set X}
    (W : DoubleBubbleConnectivityWitness left right interface)
    (hleft : left ⊆ left') (hright : right ⊆ right') :
    DoubleBubbleConnectivityWitness left' right' interface where
  first := W.first
  second := W.second
  first_mem := W.first_mem
  second_mem := W.second_mem
  interface_subset _ hx := ⟨hleft (W.interface_subset hx).1,
    hright (W.interface_subset hx).2⟩
  joined_left := W.joined_left.mono hleft
  joined_right := W.joined_right.mono hright
  separated_interface := W.separated_interface

/-- Shrink the named interface, provided both marked points remain in it. -/
def shrink_interface {interface' : Set X}
    (W : DoubleBubbleConnectivityWitness left right interface)
    (hinterface : interface' ⊆ interface)
    (hfirst : W.first ∈ interface') (hsecond : W.second ∈ interface') :
    DoubleBubbleConnectivityWitness left right interface' where
  first := W.first
  second := W.second
  first_mem := hfirst
  second_mem := hsecond
  interface_subset := hinterface.trans W.interface_subset
  joined_left := W.joined_left
  joined_right := W.joined_right
  separated_interface hjoined := W.separated_interface (hjoined.mono hinterface)

end DoubleBubbleConnectivityWitness

/-! ## Carrier cut alternatives on the transported torus -/

/-- The exact topological alternative required of a binary cut of a carrier.  It is deliberately
defined as a hypothesis: a proof from geometric sphere-and-disk data is the missing
Mayer--Vietoris/cut theorem, not a consequence of set containment alone. -/
def HasCarrierCutAlternative (Phi : AmbientIsotopy)
    (parent left right interface : Set (Submission.Torus.transportedTorus Phi)) : Prop :=
  CarriesTorusGenus Phi parent →
    CarriesTorusGenus Phi left ∨
      CarriesTorusGenus Phi right ∨
        Nonempty (DoubleBubbleConnectivityWitness left right interface)

/-- Under the cut alternative, excluding a double bubble leaves a carrying child. -/
theorem carries_left_or_right_of_cutAlternative_of_noDoubleBubble
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (Submission.Torus.transportedTorus Phi)}
    (hcut : HasCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTorusGenus Phi parent)
    (hnobubble : IsEmpty (DoubleBubbleConnectivityWitness left right interface)) :
    CarriesTorusGenus Phi left ∨ CarriesTorusGenus Phi right := by
  rcases hcut hparent with hleft | hright | hbubble
  · exact Or.inl hleft
  · exact Or.inr hright
  · exact False.elim (isEmpty_iff.mp hnobubble hbubble.some)

/-- A path-connected interface rules out the bubble branch, so one child carries. -/
theorem carries_left_or_right_of_cutAlternative_of_isPathConnected_interface
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (Submission.Torus.transportedTorus Phi)}
    (hcut : HasCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTorusGenus Phi parent)
    (hinterface : IsPathConnected interface) :
    CarriesTorusGenus Phi left ∨ CarriesTorusGenus Phi right :=
  carries_left_or_right_of_cutAlternative_of_noDoubleBubble hcut hparent
    (DoubleBubbleConnectivityWitness.isEmpty_of_isPathConnected hinterface)

/-- If neither child carries, the carrier cut alternative produces a double bubble. -/
theorem exists_doubleBubble_of_cutAlternative_of_children_noncarrier
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (Submission.Torus.transportedTorus Phi)}
    (hcut : HasCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTorusGenus Phi parent)
    (hleft : ¬ CarriesTorusGenus Phi left)
    (hright : ¬ CarriesTorusGenus Phi right) :
    Nonempty (DoubleBubbleConnectivityWitness left right interface) := by
  rcases hcut hparent with hcarrier | hcarrier | hbubble
  · exact False.elim (hleft hcarrier)
  · exact False.elim (hright hcarrier)
  · exact hbubble

/-- Boolean selection form of the no-double-bubble conclusion, convenient for choosing the next
member of a nested sequence. -/
theorem exists_carrying_side_of_cutAlternative_of_noDoubleBubble
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (Submission.Torus.transportedTorus Phi)}
    (hcut : HasCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTorusGenus Phi parent)
    (hnobubble : IsEmpty (DoubleBubbleConnectivityWitness left right interface)) :
    ∃ side : Bool,
      CarriesTorusGenus Phi (if side then left else right) := by
  rcases carries_left_or_right_of_cutAlternative_of_noDoubleBubble
      hcut hparent hnobubble with hleft | hright
  · exact ⟨true, hleft⟩
  · exact ⟨false, hright⟩

/-- If both children lie in local planar charts, the carrier cut alternative forces a double
bubble. -/
theorem exists_doubleBubble_of_cutAlternative_of_children_in_charts
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (Submission.Torus.transportedTorus Phi)}
    (hcut : HasCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTorusGenus Phi parent)
    (xleft xright : Submission.Torus.transportedTorus Phi)
    (hleft : left ⊆ (transportedTorusChart Phi xleft).source)
    (hright : right ⊆ (transportedTorusChart Phi xright).source) :
    Nonempty (DoubleBubbleConnectivityWitness left right interface) := by
  apply exists_doubleBubble_of_cutAlternative_of_children_noncarrier hcut hparent
  · exact not_carriesTorusGenus_of_subset_transportedTorusChart_source
      Phi left xleft hleft
  · exact not_carriesTorusGenus_of_subset_transportedTorusChart_source
      Phi right xright hright

/-! ## Ambient sphere-and-disk regions -/

/-- The double-bubble witness on the surface parts of three ambient regions. -/
abbrev TransportedTorusDoubleBubbleWitness (Phi : AmbientIsotopy)
    (left right interface : Set R3) :=
  DoubleBubbleConnectivityWitness
    (transportedTorusPart Phi left)
    (transportedTorusPart Phi right)
    (transportedTorusPart Phi interface)

/-- Ambient formulation of the exact carrier-or-double-bubble cut principle. -/
def HasAmbientCarrierCutAlternative (Phi : AmbientIsotopy)
    (parent left right interface : Set R3) : Prop :=
  CarriesTransportedTorusGenus Phi parent →
    CarriesTransportedTorusGenus Phi left ∨
      CarriesTransportedTorusGenus Phi right ∨
        Nonempty (TransportedTorusDoubleBubbleWitness Phi left right interface)

/-- The ambient cut principle yields a carrying side whenever the interface has no double-bubble
connectivity witness. -/
theorem carries_ambient_left_or_right_of_cutAlternative_of_noDoubleBubble
    {Phi : AmbientIsotopy} {parent left right interface : Set R3}
    (hcut : HasAmbientCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTransportedTorusGenus Phi parent)
    (hnobubble : IsEmpty
      (TransportedTorusDoubleBubbleWitness Phi left right interface)) :
    CarriesTransportedTorusGenus Phi left ∨
      CarriesTransportedTorusGenus Phi right := by
  rcases hcut hparent with hleft | hright | hbubble
  · exact Or.inl hleft
  · exact Or.inr hright
  · exact False.elim (isEmpty_iff.mp hnobubble hbubble.some)

/-- The precise one-step implication consumed by a nested-box argument: if both cut regions have
controlled scale, one of them is a smaller carrier unless a double bubble exists. -/
theorem exists_carrying_ambient_side_with_scale
    {Phi : AmbientIsotopy} {parent left right interface : Set R3}
    (hcut : HasAmbientCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTransportedTorusGenus Phi parent)
    (hnobubble : IsEmpty
      (TransportedTorusDoubleBubbleWitness Phi left right interface))
    (leftScale rightScale parentScale factor : ℝ)
    (hleftScale : leftScale ≤ factor * parentScale)
    (hrightScale : rightScale ≤ factor * parentScale) :
    ∃ side : Bool,
      CarriesTransportedTorusGenus Phi (if side then left else right) ∧
        (if side then leftScale else rightScale) ≤ factor * parentScale := by
  rcases carries_ambient_left_or_right_of_cutAlternative_of_noDoubleBubble
      hcut hparent hnobubble with hleft | hright
  · exact ⟨true, hleft, hleftScale⟩
  · exact ⟨false, hright, hrightScale⟩

end Submission.Topology
