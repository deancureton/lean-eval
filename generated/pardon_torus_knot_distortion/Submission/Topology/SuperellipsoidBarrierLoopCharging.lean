import Submission.Topology.SuperellipsoidSmoothedChargingTransport

/-!
# Charging an analytic barrier loop

The source of a transverse continuation need not bound the final compressing
disk.  This module assigns its knot-intersection parameters directly to the
selected outer or cutting-disk events.  The continuation layer can then pull
that finite injective charge to a smoothed target loop.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- A geometric outer/cut tag for the intersections of an arbitrary product-torus loop. -/
structure BarrierLoopEventCover
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (gamma : ℝ → Circle × Circle) where
  tag : ℝ → Sum Unit Bool
  point_mem_event : ∀ t ∈ torusLoopIntersectionParameters p q gamma,
    match tag t with
    | Sum.inl _ => compressionParameterPoint Phi p q t ∈
        superellipsoidBoundary frame c S.outer.scale
    | Sum.inr _ => compressionParameterPoint Phi p q t ∈ S.cutDisk

namespace BarrierLoopEventCover

/-- A source loop on the analytic outer/cut barrier receives the canonical page tag. -/
def ofRangeSubset
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) {gamma : ℝ → Circle × Circle}
    (hbarrier : Set.range (fun u ↦ transportedTorusMap Phi (gamma u)) ⊆
      superellipsoidBoundary frame c S.outer.scale ∪ S.cutDisk) :
    BarrierLoopEventCover S p q gamma := by
  classical
  let outerPoint : ℝ → Prop := fun t ↦
    compressionParameterPoint Phi p q t ∈
      superellipsoidBoundary frame c S.outer.scale
  refine {
    tag := fun t ↦ if outerPoint t then Sum.inl () else Sum.inr false
    point_mem_event := ?_
  }
  intro t ht
  obtain ⟨u, hu⟩ := ht.2
  have hpoint : compressionParameterPoint Phi p q t =
      transportedTorusMap Phi (gamma u) := by
    exact congrArg (transportedTorusMap Phi) hu.symm
  have hevent : compressionParameterPoint Phi p q t ∈
      superellipsoidBoundary frame c S.outer.scale ∪ S.cutDisk := by
    rw [hpoint]
    exact hbarrier ⟨u, rfl⟩
  by_cases houter : outerPoint t
  · simpa only [if_pos houter] using houter
  · simpa only [if_neg houter] using hevent.resolve_left houter

/-- A source loop lying on the selected outer surface has the constant outer tag. -/
def ofOuterRangeSubset
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) {gamma : ℝ → Circle × Circle}
    (houter : Set.range (fun u ↦ transportedTorusMap Phi (gamma u)) ⊆
      superellipsoidBoundary frame c S.outer.scale) :
    BarrierLoopEventCover S p q gamma where
  tag := fun _ ↦ Sum.inl ()
  point_mem_event := by
    intro t ht
    obtain ⟨u, hu⟩ := ht.2
    have hpoint : compressionParameterPoint Phi p q t =
        transportedTorusMap Phi (gamma u) := by
      exact congrArg (transportedTorusMap Phi) hu.symm
    simpa only using hpoint.symm ▸ houter ⟨u, rfl⟩

/-- A source loop lying on the selected cutting disk has the constant cut tag. -/
def ofCutRangeSubset
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) {gamma : ℝ → Circle × Circle}
    (hcut : Set.range (fun u ↦ transportedTorusMap Phi (gamma u)) ⊆ S.cutDisk) :
    BarrierLoopEventCover S p q gamma where
  tag := fun _ ↦ Sum.inr false
  point_mem_event := by
    intro t ht
    obtain ⟨u, hu⟩ := ht.2
    have hpoint : compressionParameterPoint Phi p q t =
        transportedTorusMap Phi (gamma u) := by
      exact congrArg (transportedTorusMap Phi) hu.symm
    simpa only using hpoint.symm ▸ hcut ⟨u, rfl⟩

/-- Encode a source-loop event in the finite selected event set. -/
def encode
    {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
    {p q : ℕ} {gamma : ℝ → Circle × Circle}
    (sigma : CircleReparam) (G : BarrierLoopEventCover S p q gamma)
    (t : ℝ) : Sum ℝ (Bool × ℝ) :=
  match G.tag t with
  | Sum.inl _ => Sum.inl (knotFundamentalParameter sigma t)
  | Sum.inr side => Sum.inr (side, knotFundamentalParameter sigma t)

/-- A geometric outer/cut event cover is an injective charge for the source loop. -/
def toLoopCharging
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (hc : p.Coprime q) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    {gamma : ℝ → Circle × Circle}
    (G : BarrierLoopEventCover S p q gamma) :
    LoopCharging S p q gamma where
  encode := G.encode sigma
  mem_counted := by
    intro t ht
    have hpoint := G.point_mem_event t ht
    have hsIco := knotFundamentalParameter_mem_Ico sigma t
    have hcurve := curve_knotFundamentalParameter_eq_transportedTorusKnot
      p q K Phi sigma hclass t
    cases htag : G.tag t with
    | inl u =>
        rw [htag] at hpoint
        have hevent : knotFundamentalParameter sigma t ∈ S.outerEventSet := by
          change knotFundamentalParameter sigma t ∈
            Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
              (Ico (0 : ℝ) (2 * Real.pi)) S.outer.scale
          change knotFundamentalParameter sigma t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
            superellipsoidShellParameter K frame c
              (knotFundamentalParameter sigma t) = S.outer.scale
          refine ⟨hsIco, ?_⟩
          change superellipsoidGauge frame c
            (K.curve (knotFundamentalParameter sigma t)) = S.outer.scale
          rw [hcurve]
          simpa [superellipsoidBoundary, compressionParameterPoint] using hpoint
        simpa [SuperellipsoidDoubleBubbleSelection.countedEvents,
          BarrierLoopEventCover.encode, htag] using hevent
    | inr side =>
        rw [htag] at hpoint
        have hevent : knotFundamentalParameter sigma t ∈ S.cutEventSet := by
          change knotFundamentalParameter sigma t ∈ superellipsoidCutParameterSet S.cut
          change knotFundamentalParameter sigma t ∈
              Submission.Coarea.fiberSet (longCoordinate K frame)
                (closedSuperellipsoidParameters K frame c S.outer.scale) S.cut.height
          change knotFundamentalParameter sigma t ∈
              closedSuperellipsoidParameters K frame c S.outer.scale ∧
            longCoordinate K frame (knotFundamentalParameter sigma t) = S.cut.height
          constructor
          · constructor
            · exact ⟨hsIco.1, hsIco.2.le⟩
            · change K.curve (knotFundamentalParameter sigma t) ∈
                closedSuperellipsoidBody frame c S.outer.scale
              rw [hcurve]
              simpa [cutDisk, compressionParameterPoint] using hpoint.1
          · change (K.curve (knotFundamentalParameter sigma t)).ofLp (frame 2) =
              S.cut.height
            rw [hcurve]
            simpa [cutDisk, coordinateCuttingPlane,
              compressionParameterPoint] using hpoint.2
        simpa [SuperellipsoidDoubleBubbleSelection.countedEvents,
          BarrierLoopEventCover.encode, htag] using hevent
  injOn := by
    intro s hs t ht hst
    have hbridge := knotFundamentalParameter_injOn p q hc K Phi sigma hclass
    apply hbridge hs.1 ht.1
    cases htags : G.tag s with
    | inl us =>
        cases htagt : G.tag t with
        | inl ut =>
            simpa [BarrierLoopEventCover.encode, htags, htagt] using hst
        | inr sidet =>
            simp [BarrierLoopEventCover.encode, htags, htagt] at hst
    | inr sides =>
        cases htagt : G.tag t with
        | inl ut =>
            simp [BarrierLoopEventCover.encode, htags, htagt] at hst
        | inr sidet =>
            have hp := congrArg (fun z : Sum ℝ (Bool × ℝ) ↦
              match z with
              | Sum.inl _ => 0
              | Sum.inr v => v.2) hst
            simpa [BarrierLoopEventCover.encode, htags, htagt] using hp

/-- An analytically tagged source loop and its noncolliding transverse branches give the full
charging transport to a smoothed target loop. -/
def toSmoothedLoopChargingTransport
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (hc : p.Coprime q) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    {sourceLoop targetLoop : ℝ → Circle × Circle} {m n : ℤ}
    (G : BarrierLoopEventCover S p q sourceLoop)
    (C : TransverseIntersectionCertificate p q sourceLoop m n)
    (B : TransverseBranchFamily p q sourceLoop targetLoop m n C) :
    SmoothedLoopChargingTransport S p q targetLoop m n :=
  SmoothedLoopChargingTransport.ofTransverseBranches C
    (G.toLoopCharging S p q hc sigma hclass) B

end BarrierLoopEventCover

end SuperellipsoidDoubleBubbleSelection

end Submission.PardonDistortion
