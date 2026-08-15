import Submission.ReparamCharging
import Submission.PardonGeometricStep
import Submission.Topology.HalfspaceCut

/-!
# From geometric boundary coverage to finite event charging

The remaining surface construction naturally states that every intersection
point on its compressing boundary lies either on the selected outer box or on
one of the two occurrences of the cutting disk.  This file converts that
ambient statement into the parameter-level assignment used by the finite
`160D` accounting.
-/

open Set

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Torus
open Submission.Topology

noncomputable section

namespace DoubleBubbleSelection

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {Phi : AmbientIsotopy}

/-- An ambient geometric tag for every certified intersection parameter.
The Boolean distinguishes the two uses of the shared cutting disk. -/
structure CompressionBoundaryEventCover
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) where
  tag : ℝ → Sum Unit Bool
  point_mem_event : ∀ t ∈ torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve),
    match tag t with
    | Sum.inl _ => compressionParameterPoint Phi p q t ∈
        orientedBoxBoundary frame c S.outerScale
    | Sum.inr _ => compressionParameterPoint Phi p q t ∈
        closedOrientedBox frame c S.outerScale ∩
          coordinateCuttingPlane frame S.cutHeight

/-- Ambient event coverage induces the exact parameter-level event
assignment after applying the circle reparametrization. -/
def CompressionBoundaryEventCover.toBoundaryEventAssignment
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q) :
    BoundaryEventAssignment S D p q sigma where
  tag := G.tag
  mem_event := by
    intro t ht
    have hpoint := G.point_mem_event t ht
    have hsIco := knotFundamentalParameter_mem_Ico sigma t
    have hcurve := curve_knotFundamentalParameter_eq_transportedTorusKnot
      p q K Phi sigma hclass t
    cases htag : G.tag t with
    | inl u =>
        rw [htag] at hpoint
        change compressionParameterPoint Phi p q t ∈
          orientedBoxBoundary frame c S.outerScale at hpoint
        change knotFundamentalParameter sigma t ∈
          Submission.Coarea.fiberSet (orientedShellParameter K frame c)
            (Ico (0 : ℝ) (2 * Real.pi)) S.outerScale
        change knotFundamentalParameter sigma t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
          orientedShellParameter K frame c
            (knotFundamentalParameter sigma t) = S.outerScale
        refine ⟨hsIco, ?_⟩
        change orientedBoxGauge frame c
          (K.curve (knotFundamentalParameter sigma t)) = S.outerScale
        rw [hcurve]
        simpa [orientedBoxBoundary, compressionParameterPoint] using hpoint
    | inr side =>
        rw [htag] at hpoint
        change compressionParameterPoint Phi p q t ∈
          closedOrientedBox frame c S.outerScale ∩
            coordinateCuttingPlane frame S.cutHeight at hpoint
        change knotFundamentalParameter sigma t ∈
          orientedCutParameterSet K frame c S.outerScale S.cutHeight
        change knotFundamentalParameter sigma t ∈
            closedOrientedBoxParameters K frame c S.outerScale ∧
          longCoordinate K frame (knotFundamentalParameter sigma t) =
            S.cutHeight
        constructor
        · constructor
          · exact ⟨hsIco.1, hsIco.2.le⟩
          · change K.curve (knotFundamentalParameter sigma t) ∈
              closedOrientedBox frame c S.outerScale
            rw [hcurve]
            simpa [compressionParameterPoint] using hpoint.1
        · change (K.curve (knotFundamentalParameter sigma t)).ofLp (frame 2) =
            S.cutHeight
          rw [hcurve]
          simpa [coordinateCuttingPlane, compressionParameterPoint] using hpoint.2

/-- With coprime `(p,q)`, ambient coverage therefore gives the complete
injective finite charging in one step. -/
def CompressionBoundaryEventCover.toCompressionCharging
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q) :
    S.CompressionCharging D p q :=
  (G.toBoundaryEventAssignment S D p q sigma hclass).toCompressionCharging
    S D p q hc sigma hclass

/-- Package ambient coverage and a transverse certificate as the charged
compression branch consumed by the one-step geometric theorem. -/
def CompressionBoundaryEventCover.toChargedCompression
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding)
    (G : CompressionBoundaryEventCover S D p q) :
    ChargedCompression (Phi := Phi) p q S where
  disk := D
  certificate := C
  charging := ⟨G.toCompressionCharging S D p q hc sigma hclass⟩

end DoubleBubbleSelection

end

end Submission.PardonDistortion
