import Submission.Topology.SuperellipsoidCanonicalSeamFlowFourPortTree
import Submission.Topology.SuperellipsoidCanonicalBandPointwiseExactness

/-!
# Relative straightening of the canonical four-port tree

A seam-fixing plane homeomorphism that carries the canonical five-edge tree to the standard
four-port carrier reparametrizes the open tubular strip into an exact paired-band chart.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev BandIndex := Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private def centralOpenBandMap (b : D.BandIndex) : Plane → R3 :=
  fun z ↦ (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip z |>.1.1

universe u

/-- The exact remaining relative planar input for the canonical central bands. -/
structure RelativeFourPortTreeStraighteningData
    (ι : Type u) (tree : ι → Set Plane) (localSet : ι → Set R3)
    (baseMap : ι → Plane → R3) : Type (u + 1) where
  homeomorph : ∀ _b : ι, Plane ≃ₜ Plane
  fixes_seam : ∀ b u, homeomorph b (bandSeamPath u) = bandSeamPath u
  image_tree : ∀ b, homeomorph b '' tree b = standardBandSingularCarrier
  local_carrier_iff : ∀ b z, z ∈ standardBandPatchCarrier →
    (baseMap b ((homeomorph b).symm z) ∈ localSet b ↔
      z ∈ standardBandSingularCarrier)

abbrev CanonicalFourPortTreeStraighteningData :=
  RelativeFourPortTreeStraighteningData D.BandIndex D.centralFourPortTreeCarrier
    (fun _ ↦ D.centralGraph.carrier)
    D.centralOpenBandMap

namespace CanonicalFourPortTreeStraighteningData

variable (X : D.CanonicalFourPortTreeStraighteningData)

private theorem symm_fixes_seam (b : D.BandIndex) (u : unitInterval) :
    (X.homeomorph b).symm (bandSeamPath u) = bandSeamPath u := by
  apply (X.homeomorph b).injective
  rw [(X.homeomorph b).apply_symm_apply, X.fixes_seam]

/-- Reparametrize the open strip by the inverse relative straightener. -/
noncomputable def straightenedBandData (b : D.BandIndex) :
    GlobalBandTubularChartData D.centralCutOrder b := by
  let B := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  let e : Plane ≃ₜ B.surfacePatch := (X.homeomorph b).symm.trans B.strip
  apply GlobalBandTubularChartData.ofStrip B.surfacePatch e
  · rintro _ ⟨z, rfl⟩
    apply B.strip_mem_neighborhood
    exact ⟨(X.homeomorph b).symm z, rfl⟩
  · intro u
    change (((B.strip ((X.homeomorph b).symm (bandSeamPath u)) :
      B.surfacePatch) : transportedTorus Phi) : R3) = _
    rw [X.symm_fixes_seam]
    exact B.core_alignment u

noncomputable def straightenedChartFamily :
    D.centralCutOrder.GlobalBandTubularChartFamily where
  band := X.straightenedBandData

/-- The relative straightener gives the pointwise compact-patch equation in the reparametrized
strip. -/
theorem toPointwiseExactness :
    CanonicalGlobalBandChartPointwiseExactness D.centralGraph D.centralOuterOrder
      D.centralCutOrder X.straightenedChartFamily where
  support_eq := fun _ ↦ rfl
  chart_mem_carrier_iff := fun b z hz ↦ by
    change D.centralOpenBandMap b ((X.homeomorph b).symm z) ∈
        D.centralGraph.carrier ↔ z ∈ standardBandSingularCarrier
    exact X.local_carrier_iff b z hz

/-- A relative straightener produces the exact chart package consumed by the canonical
paired-band construction. -/
noncomputable def toArcExactness : CanonicalCentralBarrierChartData.ArcExactness D where
  charts := X.straightenedChartFamily
  exactness := X.toPointwiseExactness.toCanonicalGlobalBandChartArcExactness
    (hR := D.scale_pos)

end CanonicalFourPortTreeStraighteningData

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
