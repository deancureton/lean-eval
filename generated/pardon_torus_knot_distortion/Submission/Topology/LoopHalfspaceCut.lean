import Submission.Topology.LoopCarrier
import Submission.Topology.HalfspaceCut

/-!
# Halfspace cuts for arbitrary winding-loop carriers

This module replaces the straight-slope rerouting interface by arbitrary continuous periodic
loops.  Its main technical lemma proves that winding is invariant under a continuous periodic
homotopy, directly from uniqueness of lifts through `Circle.exp`.  Consequently a local
arc-replacement witness only needs to provide the spliced periodic loop, its range containment,
and a periodic homotopy from the original loop; winding preservation is then a theorem.

The finite transverse data and the actual construction of each spliced loop remain explicit
inputs.  After those local inputs, all algebraic case analysis, the loop-carrier cut alternative,
and the controlled oriented-box successor are proved here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-! ## Winding invariance under periodic homotopy -/

/-- A continuous homotopy through `2π`-periodic circle loops. -/
structure PeriodicCircleLoopHomotopy (gamma₀ gamma₁ : ℝ → Circle) where
  homotopy : ℝ → ℝ → Circle
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = gamma₀
  homotopy_one : homotopy 1 = gamma₁

/-- Winding is invariant under a continuous periodic circle-loop homotopy. -/
theorem CircleLoopLift.winding_eq_of_periodicHomotopy
    {gamma₀ gamma₁ : ℝ → Circle}
    (H : PeriodicCircleLoopHomotopy gamma₀ gamma₁)
    (L₀ : CircleLoopLift gamma₀) (L₁ : CircleLoopLift gamma₁) :
    L₀.winding = L₁.winding := by
  let hc : C(ℝ × ℝ, Circle) :=
    ⟨Function.uncurry H.homotopy, H.continuous_homotopy⟩
  let gc₀ : C(ℝ, Circle) :=
    ⟨gamma₀,
      (Circle.exp.continuous.comp L₀.continuous_angle).congr L₀.exp_angle⟩
  have hbase : Circle.exp (L₀.angle 0) = hc (0, 0) := by
    rw [L₀.exp_angle]
    change gamma₀ 0 = H.homotopy 0 0
    rw [H.homotopy_zero]
  obtain ⟨A, hA0, hAlift⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      hc (0, 0) (L₀.angle 0) hbase |>.exists
  let Astart : C(ℝ, ℝ) :=
    ⟨fun t ↦ A (0, t), A.continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  let lift₀ : C(ℝ, ℝ) := ⟨L₀.angle, L₀.continuous_angle⟩
  have hAstart : Astart 0 = L₀.angle 0 ∧ Circle.exp ∘ Astart = gc₀ := by
    constructor
    · exact hA0
    · funext t
      change Circle.exp (A (0, t)) = gamma₀ t
      calc
        Circle.exp (A (0, t)) = H.homotopy 0 t := congrFun hAlift (0, t)
        _ = gamma₀ t := congrFun H.homotopy_zero t
  have hlift₀ : lift₀ 0 = L₀.angle 0 ∧ Circle.exp ∘ lift₀ = gc₀ :=
    ⟨rfl, funext L₀.exp_angle⟩
  have hstartEq : Astart = lift₀ :=
    (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc₀ 0 (L₀.angle 0) (L₀.exp_angle 0)).unique hAstart hlift₀
  let shifted : C(ℝ × ℝ, ℝ) :=
    ⟨fun z ↦ A (z.1, z.2 + 2 * Real.pi), A.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))⟩
  let translated : C(ℝ × ℝ, ℝ) :=
    ⟨fun z ↦ A z + (L₀.winding : ℝ) * (2 * Real.pi),
      A.continuous.add continuous_const⟩
  have hshifted :
      shifted (0, 0) = A (0, 0) + (L₀.winding : ℝ) * (2 * Real.pi) ∧
        Circle.exp ∘ shifted = hc := by
    constructor
    · have hperiod := L₀.angle_add_period 0
      have hperiodValue :=
        congrArg (fun F : C(ℝ, ℝ) ↦ F (2 * Real.pi)) hstartEq
      have hzeroValue := congrArg (fun F : C(ℝ, ℝ) ↦ F 0) hstartEq
      dsimp [shifted, Astart, lift₀] at hperiodValue hzeroValue ⊢
      simp only [zero_add]
      rw [hperiodValue, hzeroValue]
      simpa only [zero_add] using hperiod
    · funext z
      change Circle.exp (A (z.1, z.2 + 2 * Real.pi)) = H.homotopy z.1 z.2
      calc
        Circle.exp (A (z.1, z.2 + 2 * Real.pi)) =
            H.homotopy z.1 (z.2 + 2 * Real.pi) := congrFun hAlift _
        _ = H.homotopy z.1 z.2 := H.periodic_homotopy z.1 z.2
  have htranslated :
      translated (0, 0) = A (0, 0) + (L₀.winding : ℝ) * (2 * Real.pi) ∧
        Circle.exp ∘ translated = hc := by
    constructor
    · rfl
    · funext z
      change Circle.exp (A z + (L₀.winding : ℝ) * (2 * Real.pi)) =
        H.homotopy z.1 z.2
      calc
        Circle.exp (A z + (L₀.winding : ℝ) * (2 * Real.pi)) =
            Circle.exp (A z) := by
          apply Circle.exp_eq_exp.mpr
          exact ⟨L₀.winding, rfl⟩
        _ = H.homotopy z.1 z.2 := congrFun hAlift z
  have htranslatedBase :
      Circle.exp (A (0, 0) + (L₀.winding : ℝ) * (2 * Real.pi)) =
        H.homotopy 0 0 := by
    calc
      Circle.exp (A (0, 0) + (L₀.winding : ℝ) * (2 * Real.pi)) =
          Circle.exp (A (0, 0)) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨L₀.winding, rfl⟩
      _ = H.homotopy 0 0 := congrFun hAlift (0, 0)
  have hshift : shifted = translated :=
    (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts hc (0, 0)
      (A (0, 0) + (L₀.winding : ℝ) * (2 * Real.pi))
      htranslatedBase).unique hshifted htranslated
  let endLift : CircleLoopLift gamma₁ := {
    angle := fun t ↦ A (1, t)
    continuous_angle := A.continuous.comp
      (continuous_const.prodMk continuous_id)
    exp_angle := fun t ↦ by
      calc
        Circle.exp (A (1, t)) = H.homotopy 1 t := congrFun hAlift (1, t)
        _ = gamma₁ t := congrFun H.homotopy_one t
    winding := L₀.winding
    angle_add_period := fun t ↦ by
      exact congrArg (fun F : C(ℝ × ℝ, ℝ) ↦ F (1, t)) hshift
  }
  exact endLift.winding_eq L₁

/-- A continuous homotopy through periodic product-torus loops. -/
structure PeriodicTorusLoopHomotopy
    (gamma₀ gamma₁ : ℝ → Circle × Circle) where
  homotopy : ℝ → ℝ → Circle × Circle
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = gamma₀
  homotopy_one : homotopy 1 = gamma₁

/-- Coordinatewise winding pairs are invariant under periodic product-torus homotopy. -/
theorem TorusLoopLift.windingPair_eq_of_periodicHomotopy
    {gamma₀ gamma₁ : ℝ → Circle × Circle}
    (H : PeriodicTorusLoopHomotopy gamma₀ gamma₁)
    (L₀ : TorusLoopLift gamma₀) (L₁ : TorusLoopLift gamma₁) :
    L₀.windingPair = L₁.windingPair := by
  apply Prod.ext
  · exact Submission.Topology.CircleLoopLift.winding_eq_of_periodicHomotopy
      {
        homotopy := fun s t ↦ (H.homotopy s t).1
        continuous_homotopy := continuous_fst.comp H.continuous_homotopy
        periodic_homotopy := fun s t ↦ congrArg Prod.fst (H.periodic_homotopy s t)
        homotopy_zero := by funext t; exact congrArg Prod.fst (congrFun H.homotopy_zero t)
        homotopy_one := by funext t; exact congrArg Prod.fst (congrFun H.homotopy_one t)
      } L₀.first L₁.first
  · exact Submission.Topology.CircleLoopLift.winding_eq_of_periodicHomotopy
      {
        homotopy := fun s t ↦ (H.homotopy s t).2
        continuous_homotopy := continuous_snd.comp H.continuous_homotopy
        periodic_homotopy := fun s t ↦ congrArg Prod.snd (H.periodic_homotopy s t)
        homotopy_zero := by funext t; exact congrArg Prod.snd (congrFun H.homotopy_zero t)
        homotopy_one := by funext t; exact congrArg Prod.snd (congrFun H.homotopy_one t)
      } L₀.second L₁.second

/-! ## Local arc-replacement witnesses -/

/-- A local splicing result: `rerouted` lies in the target side and is periodically homotopic to
the original loop.  The homotopy is stated in the transported torus itself, so it records exactly
what endpoint-compatible path replacements must construct. -/
structure PeriodicArcReplacement
    {Phi : AmbientIsotopy} {parent target : Set (transportedTorus Phi)}
    (original : TransportedWindingLoop Phi parent) where
  rerouted : ℝ → transportedTorus Phi
  continuous_rerouted : Continuous rerouted
  periodic_rerouted : Function.Periodic rerouted (2 * Real.pi)
  rerouted_mem : ∀ t, rerouted t ∈ target
  reroutedLift : TorusLoopLift (transportedLoopCoordinates Phi rerouted)
  homotopy : ℝ → ℝ → transportedTorus Phi
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = original.curve
  homotopy_one : homotopy 1 = rerouted

namespace PeriodicArcReplacement

variable {Phi : AmbientIsotopy} {parent target : Set (transportedTorus Phi)}
  {original : TransportedWindingLoop Phi parent}

/-- The rerouted curve bundled as a winding loop in the target side. -/
def toWindingLoop (R : PeriodicArcReplacement (target := target) original) :
    TransportedWindingLoop Phi target where
  curve := R.rerouted
  continuous_curve := R.continuous_rerouted
  periodic_curve := R.periodic_rerouted
  curve_mem := R.rerouted_mem
  lift := R.reroutedLift

/-- Arc replacement preserves the complete winding pair. -/
theorem windingPair_toWindingLoop
    (R : PeriodicArcReplacement (target := target) original) :
    R.toWindingLoop.windingPair = original.windingPair := by
  symm
  exact Submission.Topology.TorusLoopLift.windingPair_eq_of_periodicHomotopy {
    homotopy := fun s t ↦
      (transportedTorusHomeomorph Phi).symm (R.homotopy s t)
    continuous_homotopy :=
      (transportedTorusHomeomorph Phi).symm.continuous.comp R.continuous_homotopy
    periodic_homotopy := fun s t ↦
      congrArg (transportedTorusHomeomorph Phi).symm (R.periodic_homotopy s t)
    homotopy_zero := by
      funext t
      rw [R.homotopy_zero]
      rfl
    homotopy_one := by
      funext t
      rw [R.homotopy_one]
      rfl
  } original.lift R.reroutedLift

end PeriodicArcReplacement

/-! ## Finite transverse input and rerouting outcomes -/

/-- Finite transverse alternating-arc data for an arbitrary periodic loop.  This is the exact
analytic input expected before path replacements are spliced. -/
structure FiniteTransverseLoopCutData
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (L : TransportedWindingLoop Phi parent) where
  crossings : Finset ℝ
  crossings_subset_period : (crossings : Set ℝ) ⊆ Ico 0 (2 * Real.pi)
  crossings_exact : ∀ u ∈ Ico (0 : ℝ) (2 * Real.pi),
    u ∈ crossings ↔ L.curve u ∈ planeSurfaceRegion Phi parent frame d
  derivative : ℝ → ℝ
  hasDerivAt_crossing : ∀ u ∈ crossings,
    HasDerivAt (fun t ↦ (L.curve t : R3).ofLp (frame 2) - d) (derivative u) u
  derivative_ne_zero : ∀ u ∈ crossings, derivative u ≠ 0
  arcCount : ℕ
  arcCount_pos : 0 < arcCount
  arc : Fin arcCount → Set ℝ
  side : Fin arcCount → Bool
  arc_pairwise_disjoint : Pairwise fun i j ↦ Disjoint (arc i) (arc j)
  crossings_disjoint_arc : ∀ i, Disjoint (crossings : Set ℝ) (arc i)
  cover_period : Ico (0 : ℝ) (2 * Real.pi) ⊆
    (crossings : Set ℝ) ∪ ⋃ i, arc i
  arc_mem_side : ∀ i u, u ∈ arc i →
    L.curve u ∈ if side i then lowerSurfaceRegion Phi parent frame d
      else upperSurfaceRegion Phi parent frame d
  alternating : ∀ i j, i ≠ j →
    (closure (arc i) ∩ closure (arc j)).Nonempty → side i ≠ side j

/-- The output of splicing one loop: a winding-preserving replacement on one side, or a detected
double bubble. -/
inductive LoopReroutingOutcome
    {Phi : AmbientIsotopy} {parent : Set (transportedTorus Phi)}
    (left right interface : Set (transportedTorus Phi))
    (L : TransportedWindingLoop Phi parent) : Type
  | inLeft (replacement : PeriodicArcReplacement (target := left) L)
  | inRight (replacement : PeriodicArcReplacement (target := right) L)
  | bubble (witness : DoubleBubbleConnectivityWitness left right interface)

/-- Opposite-side independent reroutings force a double bubble. -/
def MixedLoopReroutingProducesBubble
    (Phi : AmbientIsotopy)
    (left right interface : Set (transportedTorus Phi)) : Prop :=
  ∀ (Lleft : TransportedWindingLoop Phi left)
    (Lright : TransportedWindingLoop Phi right),
    windingDet Lleft.windingPair.1 Lleft.windingPair.2
      Lright.windingPair.1 Lright.windingPair.2 ≠ 0 →
    Nonempty (DoubleBubbleConnectivityWitness left right interface)

/-- Complete case analysis for two arbitrary-loop rerouting outcomes. -/
theorem loopCarrier_or_doubleBubble_of_two_rerouted_loops
    {Phi : AmbientIsotopy}
    {parent left right interface : Set (transportedTorus Phi)}
    (W : LoopCarrierWitness Phi parent)
    (out₁ : LoopReroutingOutcome left right interface W.first)
    (out₂ : LoopReroutingOutcome left right interface W.second)
    (hmixed : MixedLoopReroutingProducesBubble Phi left right interface) :
    CarriesLoopTorusGenus Phi left ∨ CarriesLoopTorusGenus Phi right ∨
      Nonempty (DoubleBubbleConnectivityWitness left right interface) := by
  rcases out₁ with R₁ | R₁ | bubble₁
  · rcases out₂ with R₂ | R₂ | bubble₂
    · exact Or.inl ⟨{
        first := R₁.toWindingLoop
        second := R₂.toWindingLoop
        independent := by simpa [R₁.windingPair_toWindingLoop,
          R₂.windingPair_toWindingLoop] using W.independent
      }⟩
    · exact Or.inr (Or.inr <| hmixed R₁.toWindingLoop R₂.toWindingLoop <| by
        simpa [R₁.windingPair_toWindingLoop,
          R₂.windingPair_toWindingLoop] using W.independent)
    · exact Or.inr (Or.inr ⟨bubble₂⟩)
  · rcases out₂ with R₂ | R₂ | bubble₂
    · exact Or.inr (Or.inr <| hmixed R₂.toWindingLoop R₁.toWindingLoop <| by
        rw [R₂.windingPair_toWindingLoop, R₁.windingPair_toWindingLoop]
        exact windingDet_swap_ne_zero W.independent)
    · exact Or.inr (Or.inl ⟨{
        first := R₁.toWindingLoop
        second := R₂.toWindingLoop
        independent := by simpa [R₁.windingPair_toWindingLoop,
          R₂.windingPair_toWindingLoop] using W.independent
      }⟩)
    · exact Or.inr (Or.inr ⟨bubble₂⟩)
  · exact Or.inr (Or.inr ⟨bubble₁⟩)

/-! ## Cut alternative and nested successor -/

/-- Loop-carrier analogue of the binary carrier cut alternative. -/
def HasLoopCarrierCutAlternative (Phi : AmbientIsotopy)
    (parent left right interface : Set (transportedTorus Phi)) : Prop :=
  CarriesLoopTorusGenus Phi parent →
    CarriesLoopTorusGenus Phi left ∨ CarriesLoopTorusGenus Phi right ∨
      Nonempty (DoubleBubbleConnectivityWitness left right interface)

/-- Complete finite-data and local-splicing contract for a coordinate halfspace cut. -/
structure LoopHalfspaceCutReroutingHypotheses
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) where
  finiteData : ∀ L : TransportedWindingLoop Phi parent,
    Nonempty (FiniteTransverseLoopCutData frame d L)
  reroute : ∀ (L : TransportedWindingLoop Phi parent),
    FiniteTransverseLoopCutData frame d L →
      LoopReroutingOutcome
        (lowerSurfaceRegion Phi parent frame d)
        (upperSurfaceRegion Phi parent frame d)
        (planeSurfaceRegion Phi parent frame d) L
  mixed : MixedLoopReroutingProducesBubble Phi
    (lowerSurfaceRegion Phi parent frame d)
    (upperSurfaceRegion Phi parent frame d)
    (planeSurfaceRegion Phi parent frame d)

/-- The local finite-data and splicing hypotheses imply the loop-carrier cut alternative. -/
theorem hasLoopCarrierCutAlternative_of_rerouting
    (Phi : AmbientIsotopy) (parent : Set (transportedTorus Phi))
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (H : LoopHalfspaceCutReroutingHypotheses Phi parent frame d) :
    HasLoopCarrierCutAlternative Phi parent
      (lowerSurfaceRegion Phi parent frame d)
      (upperSurfaceRegion Phi parent frame d)
      (planeSurfaceRegion Phi parent frame d) := by
  rintro ⟨W⟩
  exact loopCarrier_or_doubleBubble_of_two_rerouted_loops W
    (H.reroute W.first (H.finiteData W.first).some)
    (H.reroute W.second (H.finiteData W.second).some) H.mixed

/-- Ambient loop-carrier cut alternative. -/
def HasAmbientLoopCarrierCutAlternative (Phi : AmbientIsotopy)
    (parent left right interface : Set R3) : Prop :=
  CarriesTransportedLoopGenus Phi parent →
    CarriesTransportedLoopGenus Phi left ∨
      CarriesTransportedLoopGenus Phi right ∨
        Nonempty (TransportedTorusDoubleBubbleWitness Phi left right interface)

/-- Surface rerouting data induces the ambient halfspace cut alternative. -/
theorem hasAmbientLoopCarrierCutAlternative_of_rerouting
    (Phi : AmbientIsotopy) (parent : Set R3)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (H : LoopHalfspaceCutReroutingHypotheses Phi
      (transportedTorusPart Phi parent) frame d) :
    HasAmbientLoopCarrierCutAlternative Phi parent
      (parent ∩ lowerClosedHalfspace frame d)
      (parent ∩ upperClosedHalfspace frame d)
      (parent ∩ coordinateCuttingPlane frame d) := by
  have hsurface := hasLoopCarrierCutAlternative_of_rerouting
    Phi (transportedTorusPart Phi parent) frame d H
  intro hparent
  simpa only [HasLoopCarrierCutAlternative, CarriesTransportedLoopGenus,
    TransportedTorusDoubleBubbleWitness, lowerSurfaceRegion, upperSurfaceRegion,
    planeSurfaceRegion, transportedTorusPart, preimage_inter] using hsurface hparent

/-- Without a double bubble, an ambient loop-carrier cut has a carrying side. -/
theorem carriesAmbientLoop_left_or_right_of_noDoubleBubble
    {Phi : AmbientIsotopy} {parent left right interface : Set R3}
    (hcut : HasAmbientLoopCarrierCutAlternative Phi parent left right interface)
    (hparent : CarriesTransportedLoopGenus Phi parent)
    (hnobubble : IsEmpty
      (TransportedTorusDoubleBubbleWitness Phi left right interface)) :
    CarriesTransportedLoopGenus Phi left ∨
      CarriesTransportedLoopGenus Phi right := by
  rcases hcut hparent with hleft | hright | hbubble
  · exact Or.inl hleft
  · exact Or.inr hright
  · exact False.elim (isEmpty_iff.mp hnobubble hbubble.some)

/-- Exact controlled successor-box theorem for arbitrary-loop carriers. -/
theorem exists_carrying_loop_successorBox_of_rerouting
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R r d : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hRle : R ≤ (1 + shellEpsilon) * r)
    (hd : |d - c.ofLp (frame 2)| ≤ shellEpsilon * r)
    (hparent : CarriesTransportedLoopGenus Phi (orientedBox frame c R))
    (H : LoopHalfspaceCutReroutingHypotheses Phi
      (transportedTorusPart Phi (orientedBox frame c R)) frame d)
    (hnobubble : IsEmpty (TransportedTorusDoubleBubbleWitness Phi
      (orientedBox frame c R ∩ lowerClosedHalfspace frame d)
      (orientedBox frame c R ∩ upperClosedHalfspace frame d)
      (orientedBox frame c R ∩ coordinateCuttingPlane frame d))) :
    ∃ c' : R3,
      CarriesTransportedLoopGenus Phi
        (orientedBox (axisCycle.trans frame) c' (successorScale R r)) ∧
      successorScale R r ≤ shrinkFactor * r := by
  let parent := orientedBox frame c R
  have hcut := hasAmbientLoopCarrierCutAlternative_of_rerouting Phi parent frame d H
  have hsides := carriesAmbientLoop_left_or_right_of_noDoubleBubble
    hcut hparent hnobubble
  have hscale := successorScale_le_shrinkFactor_mul hr.le hRle
  rcases hsides with hlower | hupper
  · refine ⟨lowerHalfCenter frame c R d, ?_, hscale⟩
    apply CarriesTransportedLoopGenus.mono ?_ hlower
    simpa only [parent, lowerClosedHalfspace] using
      lowerHalf_subset_successor frame c hR hr hd
  · refine ⟨upperHalfCenter frame c R d, ?_, hscale⟩
    apply CarriesTransportedLoopGenus.mono ?_ hupper
    simpa only [parent, upperClosedHalfspace] using
      upperHalf_subset_successor frame c hR hr hd

end Submission.Topology
