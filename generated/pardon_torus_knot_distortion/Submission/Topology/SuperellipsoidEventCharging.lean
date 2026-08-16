import Submission.SuperellipsoidCompressionExclusion
import Submission.Topology.HalfSphereSurgeryDichotomy
import Submission.Topology.ShiftedCompressingDisk

/-!
# Charging compressions on a selected superellipsoid barrier

An event-covered compression is quantitatively useful only after every boundary intersection is
assigned to the selected outer surface or to one of the two tagged copies of the cutting disk.
This module derives that assignment from an ambient event-region containment, converts it to the
finite `156D` charging interface, and combines it with the canonical shifted transverse
certificate for raw regular boundary data.
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

/-- The closed cutting disk selected inside the outer superellipsoid. -/
def cutDisk (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) : Set R3 :=
  closedSuperellipsoidBody frame c S.outer.scale ∩
    coordinateCuttingPlane frame S.cut.height

/-- A geometric tag assigning each compression-boundary intersection to the selected outer
surface or to one of the two counted copies of the cutting disk. -/
structure CompressionBoundaryEventCover
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) where
  tag : ℝ → Sum Unit Bool
  point_mem_event : ∀ t ∈ torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve),
    match tag t with
    | Sum.inl _ => compressionParameterPoint Phi p q t ∈
        superellipsoidBoundary frame c S.outer.scale
    | Sum.inr _ => compressionParameterPoint Phi p q t ∈ S.cutDisk

/-- Ambient containment of an event-covered boundary in the outer surface and cutting disk
canonically supplies a boundary-event tag. -/
def CompressionBoundaryEventCover.ofEventRegionSubset
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    {eventRegion : Set R3}
    (E : EventCoveredCompressingDisk (Phi := Phi) eventRegion)
    (p q : ℕ)
    (hregion : eventRegion ⊆
      superellipsoidBoundary frame c S.outer.scale ∪ S.cutDisk) :
    CompressionBoundaryEventCover S E.disk p q := by
  classical
  let outerPoint : ℝ → Prop := fun t ↦
    compressionParameterPoint Phi p q t ∈
      superellipsoidBoundary frame c S.outer.scale
  refine {
    tag := fun t ↦ if outerPoint t then Sum.inl () else Sum.inr false
    point_mem_event := ?_
  }
  intro t ht
  have hboundary : compressionParameterPoint Phi p q t ∈ eventRegion := by
    rcases ht with ⟨_, u, hu⟩
    have heq : (E.disk.boundaryLoop.curve u : R3) =
        compressionParameterPoint Phi p q t := by
      change (transportedTorusHomeomorph Phi).symm
        (E.disk.boundaryLoop.curve u) = torusKnotLift p q t at hu
      calc
        (E.disk.boundaryLoop.curve u : R3) =
            transportedTorusMap Phi ((transportedTorusHomeomorph Phi).symm
              (E.disk.boundaryLoop.curve u)) := by
          exact congrArg Subtype.val
            ((transportedTorusHomeomorph Phi).apply_symm_apply
              (E.disk.boundaryLoop.curve u)).symm
        _ = transportedTorusMap Phi (torusKnotLift p q t) :=
          congrArg (transportedTorusMap Phi) hu
    exact heq ▸ E.boundary_mem_event u
  have hevent := hregion hboundary
  by_cases houter : outerPoint t
  · simpa only [if_pos houter] using houter
  · simpa only [if_neg houter] using hevent.resolve_left houter

/-- Encode a tagged superellipsoid event in the finite sum used by the quantitative count. -/
def CompressionBoundaryEventCover.encode
    {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
    {D : GeneralCompressingDiskWitness Phi} {p q : ℕ}
    (sigma : CircleReparam) (G : CompressionBoundaryEventCover S D p q)
    (t : ℝ) : Sum ℝ (Bool × ℝ) :=
  match G.tag t with
  | Sum.inl _ => Sum.inl (knotFundamentalParameter sigma t)
  | Sum.inr side => Sum.inr (side, knotFundamentalParameter sigma t)

/-- A geometric superellipsoid event cover gives the exact injective finite charging. -/
def CompressionBoundaryEventCover.toCompressionCharging
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q) :
    S.CompressionCharging D p q where
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
          CompressionBoundaryEventCover.encode, htag] using hevent
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
            simpa [cutDisk, coordinateCuttingPlane, compressionParameterPoint] using hpoint.2
        simpa [SuperellipsoidDoubleBubbleSelection.countedEvents,
          CompressionBoundaryEventCover.encode, htag] using hevent
  injOn := by
    intro s hs t ht hst
    have hbridge := knotFundamentalParameter_injOn p q hc K Phi sigma hclass
    apply hbridge hs.1 ht.1
    cases htags : G.tag s with
    | inl us =>
        cases htagt : G.tag t with
        | inl ut =>
            simpa [CompressionBoundaryEventCover.encode, htags, htagt] using hst
        | inr sidet =>
            simp [CompressionBoundaryEventCover.encode, htags, htagt] at hst
    | inr sides =>
        cases htagt : G.tag t with
        | inl ut =>
            simp [CompressionBoundaryEventCover.encode, htags, htagt] at hst
        | inr sidet =>
            have hp := congrArg (fun z : Sum ℝ (Bool × ℝ) ↦
              match z with
              | Sum.inl _ => 0
              | Sum.inr v => v.2) hst
            simpa [CompressionBoundaryEventCover.encode, htags, htagt] using hp

/-- Rotating the disk boundary preserves its geometric superellipsoid event cover. -/
def CompressionBoundaryEventCover.shifted
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (G : CompressionBoundaryEventCover S D p q) (s : ℝ) :
    CompressionBoundaryEventCover S (D.shifted s) p q where
  tag := G.tag
  point_mem_event t ht := by
    apply G.point_mem_event t
    change t ∈ torusLoopIntersectionParameters p q
      (shiftedLoop (transportedLoopCoordinates Phi D.boundaryLoop.curve) s) at ht
    rw [← torusLoopIntersectionParameters_shifted p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve) s]
    exact ht

/-- A shifted transverse certificate and the unchanged event cover give a quantitatively charged
superellipsoid compression. -/
def CompressionBoundaryEventCover.toShiftedChargedCompression
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q) (s : ℝ)
    (C : TransverseIntersectionCertificate p q
      (shiftedLoop (transportedLoopCoordinates Phi D.boundaryLoop.curve) s)
      D.boundaryLoop.lift.first.winding D.boundaryLoop.lift.second.winding) :
    SuperellipsoidChargedCompression (Phi := Phi) p q S where
  disk := D.shifted s
  certificate := C
  charging := ⟨(G.shifted S D p q s).toCompressionCharging
    S (D.shifted s) p q hc sigma hclass⟩

/-- Complete quantitative bridge from an ambiently covered compression and raw regular boundary
data.  The disk is rotated by the canonical non-root phase used by the shifted `SL(2,ℤ)`
certificate; its image and its outer/cut event cover remain unchanged. -/
noncomputable def chargedCompressionOfEventCoveredRawRegular
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    {eventRegion : Set R3}
    (E : EventCoveredCompressingDisk (Phi := Phi) eventRegion)
    (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hregion : eventRegion ⊆
      superellipsoidBoundary frame c S.outer.scale ∪ S.cutDisk)
    (hfirst : ContDiff ℝ 1 E.disk.boundaryLoop.lift.first.angle)
    (hsecond : ContDiff ℝ 1 E.disk.boundaryLoop.lift.second.angle)
    (hregular : ∀ t,
      Circle.exp (transformedSlopeAngle p q E.disk.boundaryLoop.lift t) = 1 →
        deriv (transformedSlopeAngle p q E.disk.boundaryLoop.lift) t ≠ 0)
    (hinjective : Set.InjOn
      (transportedLoopCoordinates Phi E.disk.boundaryLoop.curve)
      (Ico (0 : ℝ) (2 * Real.pi))) :
    SuperellipsoidChargedCompression (Phi := Phi) p q S := by
  let G := CompressionBoundaryEventCover.ofEventRegionSubset S E p q hregion
  let H := transformedRegularPeriodicCircleLift p q E.disk.boundaryLoop.lift
    hfirst hsecond hregular
  exact G.toShiftedChargedCompression S E.disk p q hc sigma hclass H.nonrootPhase
    (shiftedTransverseIntersectionCertificateOfRawRegular p q hc
      E.disk.boundaryLoop.lift hfirst hsecond hregular hinjective)

end SuperellipsoidDoubleBubbleSelection

/-- A concrete essential-sphere surgery, together with raw smooth/transverse data on its retained
stage circle, produces the quantitative superellipsoid compression directly.  The boundary
identity in the surgery contract transports all four analytic hypotheses to the constructed
disk, so no arbitrary charging function is assumed. -/
theorem chargedCompressionOfEssentialSphereCircleRawRegular
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
    {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {stage : FiniteSphereSurgeryIntersectionSystem Phi iota} {i : iota}
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : EssentialSphereCircleSurgeryData stage i)
    (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hregion : stage.eventRegion ⊆
      superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk)
    (hfirst : ContDiff ℝ 1 (stage.circle i).windingLoop.lift.first.angle)
    (hsecond : ContDiff ℝ 1 (stage.circle i).windingLoop.lift.second.angle)
    (hregular : ∀ t,
      Circle.exp
        (transformedSlopeAngle p q (stage.circle i).windingLoop.lift t) = 1 →
      deriv (transformedSlopeAngle p q (stage.circle i).windingLoop.lift) t ≠ 0)
    (hinjective : Set.InjOn
      (transportedLoopCoordinates Phi (stage.circle i).windingLoop.curve)
      (Ico (0 : ℝ) (2 * Real.pi))) :
    Nonempty (SuperellipsoidChargedCompression (Phi := Phi) p q selection) := by
  obtain ⟨disk, hboundary⟩ :=
    D.surgery.exists_generalCompressingDiskWitness_with_boundary i D.innermost
  have hloop : disk.boundaryLoop = (stage.circle i).windingLoop :=
    hboundary.trans D.boundary_eq
  let E : EventCoveredCompressingDisk (Phi := Phi) stage.eventRegion :=
    ⟨disk, fun t ↦ by rw [hloop]; exact stage.circle_mem_event i t⟩
  have hdFirst : ContDiff ℝ 1 disk.boundaryLoop.lift.first.angle := by
    rw [hloop]
    exact hfirst
  have hdSecond : ContDiff ℝ 1 disk.boundaryLoop.lift.second.angle := by
    rw [hloop]
    exact hsecond
  have hdRegular : ∀ t,
      Circle.exp (transformedSlopeAngle p q disk.boundaryLoop.lift t) = 1 →
        deriv (transformedSlopeAngle p q disk.boundaryLoop.lift) t ≠ 0 := by
    rw [hloop]
    exact hregular
  have hdInjective : Set.InjOn
      (transportedLoopCoordinates Phi disk.boundaryLoop.curve)
      (Ico (0 : ℝ) (2 * Real.pi)) := by
    rw [hloop]
    exact hinjective
  exact ⟨SuperellipsoidDoubleBubbleSelection.chargedCompressionOfEventCoveredRawRegular
    selection E p q hc sigma hclass hregion hdFirst hdSecond hdRegular hdInjective⟩

end Submission.PardonDistortion
