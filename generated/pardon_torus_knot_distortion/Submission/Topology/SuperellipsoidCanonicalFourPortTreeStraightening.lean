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

def centralOpenBandImage (b : D.BandIndex) (s : Set Plane) : Set R3 :=
  D.centralOpenBandMap b '' s

universe u

/-- The exact remaining relative planar input for the canonical central bands. -/
structure RelativeFourPortTreeStraighteningData
    (ι : Type u) (tree : ι → Set Plane) (localSet : ι → Set R3)
    (baseImage : ι → Set Plane → Set R3) : Type (u + 1) where
  homeomorph : ∀ _b : ι, Plane ≃ₜ Plane
  fixes_seam : ∀ b u, homeomorph b (bandSeamPath u) = bandSeamPath u
  image_tree : ∀ b, homeomorph b '' tree b = standardBandSingularCarrier
  local_carrier : ∀ b, localSet b = baseImage b (tree b)

abbrev CanonicalFourPortTreeStraighteningData :=
  RelativeFourPortTreeStraighteningData D.BandIndex D.centralFourPortTreeCarrier
    (fun b ↦ D.centralGraph.carrier ∩
      D.centralCutOrder.globalBandOpenNeighborhood b)
    D.centralOpenBandImage

namespace CanonicalFourPortTreeStraighteningData

variable (X : D.CanonicalFourPortTreeStraighteningData)

private theorem symm_fixes_seam (b : D.BandIndex) (u : unitInterval) :
    (X.homeomorph b).symm (bandSeamPath u) = bandSeamPath u := by
  apply (X.homeomorph b).injective
  rw [(X.homeomorph b).apply_symm_apply, X.fixes_seam]

private theorem symm_image_standardBandSingularCarrier (b : D.BandIndex) :
    (X.homeomorph b).symm '' standardBandSingularCarrier =
      D.centralFourPortTreeCarrier b := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    rw [← X.image_tree b] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    have huv : (X.homeomorph b).symm u = v := by
      rw [← hvu, (X.homeomorph b).symm_apply_apply]
    exact huv.symm ▸ hv
  · intro z hz
    refine ⟨X.homeomorph b z, ?_, (X.homeomorph b).symm_apply_apply z⟩
    rw [← X.image_tree b]
    exact ⟨z, hz, rfl⟩

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

private theorem singularPatch_straightenedChart_eq_centralOpenBandImage
    (b : D.BandIndex) :
    (X.straightenedChartFamily.chart b).singularPatch =
      D.centralOpenBandImage b (D.centralFourPortTreeCarrier b) := by
  rw [(X.straightenedChartFamily.chart b)
    |>.singularPatch_eq_image_standardBandSingularCarrier]
  change (fun z ↦ D.centralOpenBandMap b ((X.homeomorph b).symm z)) ''
      standardBandSingularCarrier = _
  rw [← Set.image_image, X.symm_image_standardBandSingularCarrier]
  rfl

/-- A relative straightener produces the exact chart package consumed by the canonical
paired-band construction. -/
noncomputable def toArcExactness : CanonicalCentralBarrierChartData.ArcExactness D where
  charts := X.straightenedChartFamily
  exactness := by
    refine ⟨?_⟩
    intro b
    rw [← carrier_inter_globalBandOpenNeighborhood_eq_iUnion
      D.centralGraph D.centralOuterOrder D.centralCutOrder D.scale_pos b,
      X.local_carrier, X.singularPatch_straightenedChart_eq_centralOpenBandImage]

end CanonicalFourPortTreeStraighteningData

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
