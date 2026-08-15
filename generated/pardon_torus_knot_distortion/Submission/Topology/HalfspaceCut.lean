import Submission.Topology.DoubleBubble
import Submission.Coarea.PlaneSlice

/-!
# Carrier alternatives for a coordinate halfspace cut

This file specializes the abstract double-bubble interface to the closed lower and upper
halfspaces of the long coordinate of an oriented box.  It also records the finite data that a
future transverse plane-slice theorem must produce for a slope loop: finitely many crossings in
one period and finitely many disjoint, alternating side arcs between them.

The actual rerouting step is represented honestly by `ReroutedSlopeOutcome`.  Once each of the two
independent carrier slopes has such an outcome, the remaining argument is finite case analysis:
two reroutings to the same side give a carrier there, an already detected bubble is returned, and
opposite-side reroutings give a bubble under one explicit mixed-rerouting hypothesis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-! ## The geometric halfspaces -/

/-- The closed halfspace below a plane perpendicular to the old long axis. -/
def lowerClosedHalfspace (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set R3 :=
  {x | x.ofLp (frame 2) ≤ d}

/-- The closed halfspace above the same plane. -/
def upperClosedHalfspace (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set R3 :=
  {x | d ≤ x.ofLp (frame 2)}

/-- The common cutting plane. -/
def coordinateCuttingPlane (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set R3 :=
  {x | x.ofLp (frame 2) = d}

theorem isClosed_lowerClosedHalfspace (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsClosed (lowerClosedHalfspace frame d) := by
  exact isClosed_Iic.preimage (Submission.PardonDistortion.coordinateCLM (frame 2)).continuous

theorem isClosed_upperClosedHalfspace (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsClosed (upperClosedHalfspace frame d) := by
  exact isClosed_Ici.preimage (Submission.PardonDistortion.coordinateCLM (frame 2)).continuous

theorem isClosed_coordinateCuttingPlane (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsClosed (coordinateCuttingPlane frame d) := by
  exact isClosed_singleton.preimage
    (Submission.PardonDistortion.coordinateCLM (frame 2)).continuous

/-- The two closed halfspaces cover ambient space. -/
theorem lower_union_upper_eq_univ (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    lowerClosedHalfspace frame d ∪ upperClosedHalfspace frame d = Set.univ := by
  ext x
  simp only [lowerClosedHalfspace, upperClosedHalfspace, mem_union, mem_ofPred_eq,
    mem_univ, iff_true]
  exact le_total (x.ofLp (frame 2)) d

/-- Their overlap is exactly the cutting plane. -/
theorem lower_inter_upper_eq_plane (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    lowerClosedHalfspace frame d ∩ upperClosedHalfspace frame d =
      coordinateCuttingPlane frame d := by
  ext x
  simp only [lowerClosedHalfspace, upperClosedHalfspace, coordinateCuttingPlane,
    mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hlower, hupper⟩
    exact le_antisymm hlower hupper
  · intro hplane
    exact ⟨hplane.le, hplane.ge⟩

/-- The lower part of a surface subset cut by the coordinate plane. -/
def lowerSurfaceRegion (Phi : AmbientIsotopy)
    (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set (transportedTorus Phi) :=
  parent ∩ transportedTorusPart Phi (lowerClosedHalfspace frame d)

/-- The upper part of a surface subset cut by the coordinate plane. -/
def upperSurfaceRegion (Phi : AmbientIsotopy)
    (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set (transportedTorus Phi) :=
  parent ∩ transportedTorusPart Phi (upperClosedHalfspace frame d)

/-- The portion of the parent surface lying in the cutting plane. -/
def planeSurfaceRegion (Phi : AmbientIsotopy)
    (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set (transportedTorus Phi) :=
  parent ∩ transportedTorusPart Phi (coordinateCuttingPlane frame d)

/-- Every point of the parent surface lies in at least one closed halfspace piece. -/
theorem parent_subset_lower_union_upper
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    parent ⊆ lowerSurfaceRegion Phi parent frame d ∪
      upperSurfaceRegion Phi parent frame d := by
  intro x hx
  rcases le_total ((x : R3).ofLp (frame 2)) d with hlower | hupper
  · exact Or.inl ⟨hx, hlower⟩
  · exact Or.inr ⟨hx, hupper⟩

/-- The overlap of the two surface pieces is precisely their plane section. -/
theorem lower_inter_upper_surfaceRegion
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    lowerSurfaceRegion Phi parent frame d ∩
        upperSurfaceRegion Phi parent frame d =
      planeSurfaceRegion Phi parent frame d := by
  ext x
  simp only [lowerSurfaceRegion, upperSurfaceRegion, planeSurfaceRegion,
    transportedTorusPart, mem_inter_iff, mem_preimage, lowerClosedHalfspace,
    upperClosedHalfspace, coordinateCuttingPlane, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hp, hlower⟩, _, hupper⟩
    exact ⟨hp, le_antisymm hlower hupper⟩
  · rintro ⟨hp, hplane⟩
    exact ⟨⟨hp, hplane.le⟩, hp, hplane.ge⟩

/-! ## Slope realizations and finite transverse arc data -/

/-- One integral winding vector realized by a complete slope loop inside a surface subset. -/
structure SlopeRealization (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) (m n : ℤ) where
  phase₁ : ℝ
  phase₂ : ℝ
  loop_mem : ∀ t, transportedSlopePoint Phi m n phase₁ phase₂ t ∈ s

namespace SlopeRealization

variable {Phi : AmbientIsotopy} {s t : Set (transportedTorus Phi)} {m n : ℤ}

/-- The bundled point on a realized slope loop. -/
def point (R : SlopeRealization Phi s m n) (u : ℝ) : transportedTorus Phi :=
  transportedSlopePoint Phi m n R.phase₁ R.phase₂ u

theorem point_mem (R : SlopeRealization Phi s m n) (u : ℝ) : R.point u ∈ s :=
  R.loop_mem u

/-- A slope realization remains valid after enlarging its containing subset. -/
def mono (R : SlopeRealization Phi s m n) (hst : s ⊆ t) :
    SlopeRealization Phi t m n where
  phase₁ := R.phase₁
  phase₂ := R.phase₂
  loop_mem u := hst (R.loop_mem u)

end SlopeRealization

/-- Signed height of a realized slope loop over the cutting plane. -/
def slopeCutHeight {Phi : AmbientIsotopy} {s : Set (transportedTorus Phi)}
    {m n : ℤ} (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (R : SlopeRealization Phi s m n) (u : ℝ) : ℝ :=
  (R.point u : R3).ofLp (frame 2) - d

/-- Finite, transverse, alternating-arc data for one period of a slope loop cut by the plane.
The `arc` sets are intentionally explicit: a future analytic plane-slice result may choose closed,
open, or half-open parameter arcs without changing the downstream combinatorics. -/
structure FiniteTransverseSlopeCutData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)} {m n : ℤ}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (R : SlopeRealization Phi parent m n) where
  crossings : Finset ℝ
  crossings_subset_period : (crossings : Set ℝ) ⊆ Ico 0 (2 * Real.pi)
  crossings_exact : ∀ u ∈ Ico (0 : ℝ) (2 * Real.pi),
    u ∈ crossings ↔ R.point u ∈ planeSurfaceRegion Phi parent frame d
  derivative : ℝ → ℝ
  hasDerivAt_crossing : ∀ u ∈ crossings,
    HasDerivAt (slopeCutHeight frame d R) (derivative u) u
  derivative_ne_zero : ∀ u ∈ crossings, derivative u ≠ 0
  arcCount : ℕ
  arcCount_pos : 0 < arcCount
  arc : Fin arcCount → Set ℝ
  side : Fin arcCount → Bool
  arc_subset_period : ∀ i, arc i ⊆ Ico 0 (2 * Real.pi)
  arc_pairwise_disjoint : Pairwise fun i j ↦ Disjoint (arc i) (arc j)
  crossings_disjoint_arc : ∀ i, Disjoint (crossings : Set ℝ) (arc i)
  cover_period : Ico (0 : ℝ) (2 * Real.pi) ⊆
    (crossings : Set ℝ) ∪ ⋃ i, arc i
  arc_mem_side : ∀ i u, u ∈ arc i →
    R.point u ∈ if side i then lowerSurfaceRegion Phi parent frame d
      else upperSurfaceRegion Phi parent frame d
  alternating : ∀ i j, i ≠ j →
    (closure (arc i) ∩ closure (arc j)).Nonempty → side i ≠ side j

/-! ## Rerouting outcomes -/

/-- The result of cutting and rerouting one slope: it is realized wholly on one side, or the
rerouting has already exposed a double bubble. -/
inductive ReroutedSlopeOutcome (Phi : AmbientIsotopy)
    (left right interface : Set (transportedTorus Phi)) (m n : ℤ) : Type
  | inLeft (realization : SlopeRealization Phi left m n)
  | inRight (realization : SlopeRealization Phi right m n)
  | bubble (witness : DoubleBubbleConnectivityWitness left right interface)

/-- Two opposite-side reroutings of independent slopes produce a double bubble.  This isolates
the geometric path-rerouting step that finite alternating arcs must justify. -/
def MixedReroutingProducesBubble (Phi : AmbientIsotopy)
    (left right interface : Set (transportedTorus Phi)) : Prop :=
  ∀ (mleft nleft mright nright : ℤ),
    windingDet mleft nleft mright nright ≠ 0 →
    SlopeRealization Phi left mleft nleft →
    SlopeRealization Phi right mright nright →
    Nonempty (DoubleBubbleConnectivityWitness left right interface)

/-- Swapping two winding vectors negates their determinant. -/
theorem windingDet_swap (m₁ n₁ m₂ n₂ : ℤ) :
    windingDet m₂ n₂ m₁ n₁ = -windingDet m₁ n₁ m₂ n₂ := by
  simp only [windingDet]
  ring

theorem windingDet_swap_ne_zero {m₁ n₁ m₂ n₂ : ℤ}
    (h : windingDet m₁ n₁ m₂ n₂ ≠ 0) :
    windingDet m₂ n₂ m₁ n₁ ≠ 0 := by
  rw [windingDet_swap]
  exact neg_ne_zero.mpr h

/-- Two independent slope realizations in the same subset make it a carrier. -/
def TorusCarrierWitness.ofRealizations
    {Phi : AmbientIsotopy} {s : Set (transportedTorus Phi)}
    {m₁ n₁ m₂ n₂ : ℤ}
    (R₁ : SlopeRealization Phi s m₁ n₁)
    (R₂ : SlopeRealization Phi s m₂ n₂)
    (hindependent : windingDet m₁ n₁ m₂ n₂ ≠ 0) :
    TorusCarrierWitness Phi s where
  m₁ := m₁
  n₁ := n₁
  m₂ := m₂
  n₂ := n₂
  phase₁₁ := R₁.phase₁
  phase₁₂ := R₁.phase₂
  phase₂₁ := R₂.phase₁
  phase₂₂ := R₂.phase₂
  firstLoop_mem := R₁.loop_mem
  secondLoop_mem := R₂.loop_mem
  independent := hindependent

/-- The complete combinatorial implication for two independently rerouted slopes. -/
theorem carrier_or_doubleBubble_of_two_rerouted_slopes
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (transportedTorus Phi)}
    (W : TorusCarrierWitness Phi parent)
    (out₁ : ReroutedSlopeOutcome Phi left right interface W.m₁ W.n₁)
    (out₂ : ReroutedSlopeOutcome Phi left right interface W.m₂ W.n₂)
    (hmixed : MixedReroutingProducesBubble Phi left right interface) :
    CarriesTorusGenus Phi left ∨ CarriesTorusGenus Phi right ∨
      Nonempty (DoubleBubbleConnectivityWitness left right interface) := by
  rcases out₁ with R₁ | R₁ | bubble₁
  · rcases out₂ with R₂ | R₂ | bubble₂
    · exact Or.inl ⟨TorusCarrierWitness.ofRealizations R₁ R₂ W.independent⟩
    · exact Or.inr (Or.inr (hmixed _ _ _ _ W.independent R₁ R₂))
    · exact Or.inr (Or.inr ⟨bubble₂⟩)
  · rcases out₂ with R₂ | R₂ | bubble₂
    · exact Or.inr (Or.inr <|
        hmixed _ _ _ _ (windingDet_swap_ne_zero W.independent) R₂ R₁)
    · exact Or.inr (Or.inl
        ⟨TorusCarrierWitness.ofRealizations R₁ R₂ W.independent⟩)
    · exact Or.inr (Or.inr ⟨bubble₂⟩)
  · exact Or.inr (Or.inr ⟨bubble₁⟩)

/-! ## Input contract for a future plane-slice rerouting theorem -/

/-- The original first slope realization contained in a carrier witness. -/
def TorusCarrierWitness.firstRealization
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (W : TorusCarrierWitness Phi parent) :
    SlopeRealization Phi parent W.m₁ W.n₁ where
  phase₁ := W.phase₁₁
  phase₂ := W.phase₁₂
  loop_mem := W.firstLoop_mem

/-- The original second slope realization contained in a carrier witness. -/
def TorusCarrierWitness.secondRealization
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (W : TorusCarrierWitness Phi parent) :
    SlopeRealization Phi parent W.m₂ W.n₂ where
  phase₁ := W.phase₂₁
  phase₂ := W.phase₂₂
  loop_mem := W.secondLoop_mem

/-- Explicit hypotheses supplied after a transverse halfspace cut.  The finite-data field matches
the intended output of an upgraded `PlaneSlice`; `reroute` is the geometric arc-gluing theorem;
and `mixed` is precisely the opposite-side double-bubble lemma. -/
structure HalfspaceCutReroutingHypotheses
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) where
  finiteData : ∀ {m n : ℤ} (R : SlopeRealization Phi parent m n),
    Nonempty (FiniteTransverseSlopeCutData frame d R)
  reroute : ∀ {m n : ℤ} (R : SlopeRealization Phi parent m n),
    FiniteTransverseSlopeCutData frame d R →
      ReroutedSlopeOutcome Phi
        (lowerSurfaceRegion Phi parent frame d)
        (upperSurfaceRegion Phi parent frame d)
        (planeSurfaceRegion Phi parent frame d) m n
  mixed : MixedReroutingProducesBubble Phi
    (lowerSurfaceRegion Phi parent frame d)
    (upperSurfaceRegion Phi parent frame d)
    (planeSurfaceRegion Phi parent frame d)

/-- Finite transverse decomposition plus the two stated rerouting principles proves the abstract
carrier cut alternative for coordinate halfspaces. -/
theorem hasCarrierCutAlternative_of_halfspaceRerouting
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (H : HalfspaceCutReroutingHypotheses Phi parent frame d) :
    HasCarrierCutAlternative Phi parent
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) := by
  intro hcarrier
  obtain ⟨W⟩ := hcarrier
  let R₁ := W.firstRealization
  let R₂ := W.secondRealization
  let D₁ := (H.finiteData R₁).some
  let D₂ := (H.finiteData R₂).some
  exact carrier_or_doubleBubble_of_two_rerouted_slopes W
    (H.reroute R₁ D₁) (H.reroute R₂ D₂) H.mixed

/-- Ambient halfspace formulation of the cut alternative. -/
theorem hasAmbientCarrierCutAlternative_of_halfspaceRerouting
    (Phi : AmbientIsotopy) (parent : Set R3)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (H : HalfspaceCutReroutingHypotheses Phi
      (transportedTorusPart Phi parent) frame d) :
    HasAmbientCarrierCutAlternative Phi parent
      (parent ∩ lowerClosedHalfspace frame d)
      (parent ∩ upperClosedHalfspace frame d)
      (parent ∩ coordinateCuttingPlane frame d) := by
  have hsurface := hasCarrierCutAlternative_of_halfspaceRerouting
    Phi (transportedTorusPart Phi parent) frame d H
  intro hparent
  simpa only [HasCarrierCutAlternative, CarriesTransportedTorusGenus,
    TransportedTorusDoubleBubbleWitness,
    lowerSurfaceRegion, upperSurfaceRegion, planeSurfaceRegion,
    transportedTorusPart, preimage_inter] using hsurface hparent

/-- Exact nested-box successor supplied by a successful halfspace rerouting.  The topological
hypotheses choose the carrying side; the existing oriented-box lemmas then enlarge that side to a
new box at the controlled successor scale. -/
theorem exists_carrying_successorBox_of_halfspaceRerouting
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R r d : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hRle : R ≤ (1 + Submission.PardonDistortion.shellEpsilon) * r)
    (hd : |d - c.ofLp (frame 2)| ≤
      Submission.PardonDistortion.shellEpsilon * r)
    (hparent : CarriesTransportedTorusGenus Phi
      (Submission.PardonDistortion.orientedBox frame c R))
    (H : HalfspaceCutReroutingHypotheses Phi
      (transportedTorusPart Phi
        (Submission.PardonDistortion.orientedBox frame c R)) frame d)
    (hnobubble : IsEmpty (TransportedTorusDoubleBubbleWitness Phi
      (Submission.PardonDistortion.orientedBox frame c R ∩
        lowerClosedHalfspace frame d)
      (Submission.PardonDistortion.orientedBox frame c R ∩
        upperClosedHalfspace frame d)
      (Submission.PardonDistortion.orientedBox frame c R ∩
        coordinateCuttingPlane frame d))) :
    ∃ c' : R3,
      CarriesTransportedTorusGenus Phi
        (Submission.PardonDistortion.orientedBox
          (Submission.PardonDistortion.axisCycle.trans frame) c'
          (Submission.PardonDistortion.successorScale R r)) ∧
      Submission.PardonDistortion.successorScale R r ≤
        Submission.PardonDistortion.shrinkFactor * r := by
  let parent := Submission.PardonDistortion.orientedBox frame c R
  have hcut := hasAmbientCarrierCutAlternative_of_halfspaceRerouting
    Phi parent frame d H
  have hsides :=
    carries_ambient_left_or_right_of_cutAlternative_of_noDoubleBubble
      hcut hparent hnobubble
  have hscale := Submission.PardonDistortion.successorScale_le_shrinkFactor_mul
    hr.le hRle
  rcases hsides with hlower | hupper
  · refine ⟨Submission.PardonDistortion.lowerHalfCenter frame c R d, ?_, hscale⟩
    apply CarriesTransportedTorusGenus.mono ?_ hlower
    simpa only [parent, lowerClosedHalfspace] using
      Submission.PardonDistortion.lowerHalf_subset_successor
        frame c hR hr hd
  · refine ⟨Submission.PardonDistortion.upperHalfCenter frame c R d, ?_, hscale⟩
    apply CarriesTransportedTorusGenus.mono ?_ hupper
    simpa only [parent, upperClosedHalfspace] using
      Submission.PardonDistortion.upperHalf_subset_successor
        frame c hR hr hd

end Submission.Topology
