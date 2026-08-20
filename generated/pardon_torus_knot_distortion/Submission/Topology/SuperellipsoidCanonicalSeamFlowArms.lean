import Submission.Topology.SuperellipsoidCanonicalEndpointGraphs
import Submission.Topology.SuperellipsoidGlobalBandFlowCollar
import Submission.Topology.SuperellipsoidSeamTangentFlow

/-!
# Canonical moving outer arms from the normalized seam flow

The canonical endpoint package retains a uniformly regular seam band.  Its normalized tangent
flow transports each central seam vertex through that band while preserving the outer
superellipsoid level and translating height exactly.  The resulting left and right curves are
continuous injective lifts of the moving outer arms used by the relative band straightener.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

/-- The complete normalized seam flow at the exact canonical band width. -/
def centralSeamFlowData (D : CanonicalEndpointRegularityData S) :
    SuperellipsoidSeamNormalizedFlowData D.seamRegularBand :=
  Classical.choice (exists_superellipsoidSeamNormalizedFlowData D.seamRegularBand)

private abbrev CanonicalFlowTimes (D : CanonicalEndpointRegularityData S) :=
  globalBandFlowCollarTimes D.heightData.band

private theorem abs_coe_globalBandFlowCollarTimes_le
    (D : CanonicalEndpointRegularityData S)
    (t : CanonicalFlowTimes D) :
    |(t : ℝ)| ≤ D.heightData.band.ε := by
  rw [abs_le]
  exact t.2

variable (D : CanonicalEndpointRegularityData S)

private abbrev CentralBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

/-- The left central seam lift flowed through the canonical regular band. -/
def centralLeftOuterArmLift (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) : Plane :=
  D.centralSeamFlowData.2.flow
    (D.centralCutOrder.globalBandLeftFlowSeamLift b) t

/-- The right central seam lift flowed through the canonical regular band. -/
def centralRightOuterArmLift (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) : Plane :=
  D.centralSeamFlowData.2.flow
    (D.centralCutOrder.globalBandRightFlowSeamLift b) t

private theorem centralLeftFlowSeamLift_level (b : D.CentralBandIndex) :
    superellipsoidPolynomialLift Phi frame c
        (D.centralCutOrder.globalBandLeftFlowSeamLift b) = S.outer.scale ^ 256 := by
  have h := D.centralCutOrder.globalBandLeftFlowSeamLift_mem_seamFiber b D.scale_pos
  change superellipsoidSeamMap Phi frame c
      (D.centralCutOrder.globalBandLeftFlowSeamLift b) =
        (S.outer.scale ^ 256, S.cut.height) at h
  exact congrArg Prod.fst h

private theorem centralRightFlowSeamLift_level (b : D.CentralBandIndex) :
    superellipsoidPolynomialLift Phi frame c
        (D.centralCutOrder.globalBandRightFlowSeamLift b) = S.outer.scale ^ 256 := by
  have h := D.centralCutOrder.globalBandRightFlowSeamLift_mem_seamFiber b D.scale_pos
  change superellipsoidSeamMap Phi frame c
      (D.centralCutOrder.globalBandRightFlowSeamLift b) =
        (S.outer.scale ^ 256, S.cut.height) at h
  exact congrArg Prod.fst h

private theorem centralLeftFlowSeamLift_height (b : D.CentralBandIndex) :
    orientedCoordinateLift Phi frame 2
        (D.centralCutOrder.globalBandLeftFlowSeamLift b) = S.cut.height := by
  have h := D.centralCutOrder.globalBandLeftFlowSeamLift_mem_seamFiber b D.scale_pos
  change superellipsoidSeamMap Phi frame c
      (D.centralCutOrder.globalBandLeftFlowSeamLift b) =
        (S.outer.scale ^ 256, S.cut.height) at h
  exact congrArg Prod.snd h

private theorem centralRightFlowSeamLift_height (b : D.CentralBandIndex) :
    orientedCoordinateLift Phi frame 2
        (D.centralCutOrder.globalBandRightFlowSeamLift b) = S.cut.height := by
  have h := D.centralCutOrder.globalBandRightFlowSeamLift_mem_seamFiber b D.scale_pos
  change superellipsoidSeamMap Phi frame c
      (D.centralCutOrder.globalBandRightFlowSeamLift b) =
        (S.outer.scale ^ 256, S.cut.height) at h
  exact congrArg Prod.snd h

theorem continuous_centralLeftOuterArmLift (b : D.CentralBandIndex) :
    Continuous (D.centralLeftOuterArmLift b) := by
  exact (D.centralSeamFlowData.2.continuous_uncurry
    D.centralSeamFlowData.1.contDiff_completeField
    D.centralSeamFlowData.1.completeField_isPlaneDeckPeriodic).comp
      (continuous_const.prodMk continuous_subtype_val)

theorem continuous_centralRightOuterArmLift (b : D.CentralBandIndex) :
    Continuous (D.centralRightOuterArmLift b) := by
  exact (D.centralSeamFlowData.2.continuous_uncurry
    D.centralSeamFlowData.1.contDiff_completeField
    D.centralSeamFlowData.1.completeField_isPlaneDeckPeriodic).comp
      (continuous_const.prodMk continuous_subtype_val)

theorem centralLeftOuterArmLift_level (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    superellipsoidPolynomialLift Phi frame c (D.centralLeftOuterArmLift b t) =
      S.outer.scale ^ 256 := by
  exact (D.centralSeamFlowData.outer_planeFlow_eq
    (D.centralCutOrder.globalBandLeftFlowSeamLift b) t).trans
      (D.centralLeftFlowSeamLift_level b)

theorem centralRightOuterArmLift_level (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    superellipsoidPolynomialLift Phi frame c (D.centralRightOuterArmLift b t) =
      S.outer.scale ^ 256 := by
  exact (D.centralSeamFlowData.outer_planeFlow_eq
    (D.centralCutOrder.globalBandRightFlowSeamLift b) t).trans
      (D.centralRightFlowSeamLift_level b)

theorem centralLeftOuterArmLift_height (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    orientedCoordinateLift Phi frame 2 (D.centralLeftOuterArmLift b t) =
      S.cut.height + t := by
  exact D.centralSeamFlowData.height_planeFlow_eq_add
    (D.centralCutOrder.globalBandLeftFlowSeamLift b)
    (D.centralLeftFlowSeamLift_level b) (D.centralLeftFlowSeamLift_height b) t
    (abs_coe_globalBandFlowCollarTimes_le D t)

theorem centralRightOuterArmLift_height (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    orientedCoordinateLift Phi frame 2 (D.centralRightOuterArmLift b t) =
      S.cut.height + t := by
  exact D.centralSeamFlowData.height_planeFlow_eq_add
    (D.centralCutOrder.globalBandRightFlowSeamLift b)
    (D.centralRightFlowSeamLift_level b) (D.centralRightFlowSeamLift_height b) t
    (abs_coe_globalBandFlowCollarTimes_le D t)

theorem centralLeftOuterArmLift_injective (b : D.CentralBandIndex) :
    Function.Injective (D.centralLeftOuterArmLift b) := by
  intro s t hst
  apply Subtype.ext
  have hheight := congrArg (orientedCoordinateLift Phi frame 2) hst
  rw [D.centralLeftOuterArmLift_height b s,
    D.centralLeftOuterArmLift_height b t] at hheight
  linarith

theorem centralRightOuterArmLift_injective (b : D.CentralBandIndex) :
    Function.Injective (D.centralRightOuterArmLift b) := by
  intro s t hst
  apply Subtype.ext
  have hheight := congrArg (orientedCoordinateLift Phi frame 2) hst
  rw [D.centralRightOuterArmLift_height b s,
    D.centralRightOuterArmLift_height b t] at hheight
  linarith

theorem centralLeftOuterArmLift_mem_carrier (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    transportedTorusPlaneMap Phi (D.centralLeftOuterArmLift b t) ∈
      D.centralGraph.carrier := by
  rw [transportedTorusPlaneMap_mem_barrier_iff D.centralGraph D.scale_pos]
  exact Or.inl (D.centralLeftOuterArmLift_level b t)

theorem centralRightOuterArmLift_mem_carrier (b : D.CentralBandIndex)
    (t : CanonicalFlowTimes D) :
    transportedTorusPlaneMap Phi (D.centralRightOuterArmLift b t) ∈
      D.centralGraph.carrier := by
  rw [transportedTorusPlaneMap_mem_barrier_iff D.centralGraph D.scale_pos]
  exact Or.inl (D.centralRightOuterArmLift_level b t)

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
