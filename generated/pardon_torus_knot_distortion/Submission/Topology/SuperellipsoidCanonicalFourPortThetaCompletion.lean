import Submission.Topology.StandardFourPortTheta
import Submission.Topology.SuperellipsoidCanonicalFourPortTreeStraightening

/-!
# Theta completion of the canonical four-port tree

Two barrier-avoiding connectors turn the canonical analytic tree into a filled theta graph.
The exact three-path ambient extension then supplies the seam-fixing plane homeomorphism used by
the relative four-port straightener.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

/-- A planar three-path system together with the filled outer-theta decomposition used by the
ambient extension. -/
structure FilledThetaSystemData {a b : Schoenflies.Plane}
    (path : Fin 3 → Path a b) : Type where
  system : ThreePathSystem path
  outer_decomposition :
    closure system.circle12.inside =
      closure system.circle01.inside ∪ closure system.circle02.inside

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev BandIndex := Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

def canonicalBandMap (b : D.BandIndex) : Plane → R3 :=
  fun z ↦ (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip z |>.1.1

theorem canonicalBandMap_centralLeftOuterArmPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralLeftOuterArmPath b u) ∈ D.centralGraph.carrier := by
  have h := D.centralLeftOuterArmLift_mem_carrier b
    (D.openChartNarrowedTime (D.centralOuterArmTime u))
  change D.canonicalBandMap b
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime u)) ∈ D.centralGraph.carrier
  unfold canonicalBandMap centralLeftOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  exact h

theorem canonicalBandMap_centralRightOuterArmPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralRightOuterArmPath b u) ∈ D.centralGraph.carrier := by
  have h := D.centralRightOuterArmLift_mem_carrier b
    (D.openChartNarrowedTime (D.centralOuterArmTime u))
  change D.canonicalBandMap b
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime u)) ∈ D.centralGraph.carrier
  unfold canonicalBandMap centralRightOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  exact h

theorem canonicalBandMap_bandSeamPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (bandSeamPath u) ∈ D.centralGraph.carrier := by
  let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  change ((((T.strip (bandSeamPath u) : T.surfacePatch) : transportedTorus Phi) : R3) ∈
    D.centralGraph.carrier)
  rw [T.core_alignment u]
  exact canonicalBarrierPath_mem_carrier D.centralGraph D.centralOuterOrder
    D.centralCutOrder D.scale_pos
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl (D.centralCutOrder.globalGapOfBand b))))) u

theorem canonicalBandMap_centralLeftLowerBranchPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralLeftLowerBranchPath b u) ∈ D.centralGraph.carrier := by
  obtain ⟨v, hv⟩ := D.centralLeftLowerBranchPath_range_subset_outerArm b ⟨u, rfl⟩
  rw [← hv]
  exact D.canonicalBandMap_centralLeftOuterArmPath_mem_carrier b v

theorem canonicalBandMap_centralRightLowerBranchPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralRightLowerBranchPath b u) ∈ D.centralGraph.carrier := by
  obtain ⟨v, hv⟩ := D.centralRightLowerBranchPath_range_subset_outerArm b ⟨u, rfl⟩
  rw [← hv]
  exact D.canonicalBandMap_centralRightOuterArmPath_mem_carrier b v

theorem canonicalBandMap_centralLeftUpperBranchPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralLeftUpperBranchPath b u) ∈ D.centralGraph.carrier := by
  obtain ⟨v, hv⟩ := D.centralLeftUpperBranchPath_range_subset_outerArm b ⟨u, rfl⟩
  rw [← hv]
  exact D.canonicalBandMap_centralLeftOuterArmPath_mem_carrier b v

theorem canonicalBandMap_centralRightUpperBranchPath_mem_carrier
    (b : D.BandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralRightUpperBranchPath b u) ∈ D.centralGraph.carrier := by
  obtain ⟨v, hv⟩ := D.centralRightUpperBranchPath_range_subset_outerArm b ⟨u, rfl⟩
  rw [← hv]
  exact D.canonicalBandMap_centralRightOuterArmPath_mem_carrier b v

/-- The completed lower route from the left seam vertex to the right seam vertex. -/
def canonicalLowerThetaRoute (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0))) :
    Path bandLeftVertex bandRightVertex :=
  ((D.centralLeftLowerBranchPath b).symm.trans connector).trans
    (D.centralRightLowerBranchPath b)

/-- The completed upper route from the left seam vertex to the right seam vertex. -/
def canonicalUpperThetaRoute (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1))) :
    Path bandLeftVertex bandRightVertex :=
  ((D.centralLeftUpperBranchPath b).trans connector).trans
    (D.centralRightUpperBranchPath b).symm

theorem canonicalLowerThetaRoute_firstCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)))
    (u : unitInterval) :
    D.canonicalLowerThetaRoute b connector (Schoenflies.ThreePiecePath.firstCoordinate u) =
      (D.centralLeftLowerBranchPath b).symm u :=
  Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

theorem canonicalLowerThetaRoute_middleCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)))
    (u : unitInterval) :
    D.canonicalLowerThetaRoute b connector (Schoenflies.ThreePiecePath.middleCoordinate u) =
      connector u :=
  Schoenflies.ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

theorem canonicalLowerThetaRoute_thirdCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)))
    (u : unitInterval) :
    D.canonicalLowerThetaRoute b connector (Schoenflies.ThreePiecePath.thirdCoordinate u) =
      D.centralRightLowerBranchPath b u :=
  Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

theorem canonicalUpperThetaRoute_firstCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)))
    (u : unitInterval) :
    D.canonicalUpperThetaRoute b connector (Schoenflies.ThreePiecePath.firstCoordinate u) =
      D.centralLeftUpperBranchPath b u :=
  Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

theorem canonicalUpperThetaRoute_middleCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)))
    (u : unitInterval) :
    D.canonicalUpperThetaRoute b connector (Schoenflies.ThreePiecePath.middleCoordinate u) =
      connector u :=
  Schoenflies.ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

theorem canonicalUpperThetaRoute_thirdCoordinate (b : D.BandIndex)
    (connector : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)))
    (u : unitInterval) :
    D.canonicalUpperThetaRoute b connector (Schoenflies.ThreePiecePath.thirdCoordinate u) =
      (D.centralRightUpperBranchPath b).symm u :=
  Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

/-- The seam and the two completed return routes in strip coordinates. -/
def canonicalCompletedThetaPath (b : D.BandIndex)
    (lower : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)))
    (upper : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1))) :
    Fin 3 → Path bandLeftVertex bandRightVertex
  | 0 => bandSeamPath
  | 1 => D.canonicalLowerThetaRoute b lower
  | 2 => D.canonicalUpperThetaRoute b upper

/-- The completed source theta transported to the Euclidean Schoenflies plane. -/
def canonicalCompletedPlaneThetaPath (b : D.BandIndex)
    (lower : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)))
    (upper : Path
      (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
      (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1))) :
    Fin 3 → Path (coveringPlaneCoordinates.symm bandLeftVertex)
      (coveringPlaneCoordinates.symm bandRightVertex) :=
  fun i ↦ (D.canonicalCompletedThetaPath b lower upper i).map
    coveringPlaneCoordinates.symm.continuous

/-- The lower connector path type for the completed source theta. -/
abbrev CanonicalLowerConnector (b : D.BandIndex) := Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0))

/-- The upper connector path type for the completed source theta. -/
abbrev CanonicalUpperConnector (b : D.BandIndex) := Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1))

/-- The two connector paths used to complete the source theta. -/
abbrev CanonicalFourPortConnectorData (b : D.BandIndex) :=
  D.CanonicalLowerConnector b × D.CanonicalUpperConnector b

abbrev CanonicalLowerConnectorAvoidsCarrier (b : D.BandIndex)
    (lower : D.CanonicalLowerConnector b) : Prop :=
  ∀ u, D.canonicalBandMap b (lower u) ∈ D.centralGraph.carrier ↔
      u = 0 ∨ u = 1

abbrev CanonicalUpperConnectorAvoidsCarrier (b : D.BandIndex)
    (upper : D.CanonicalUpperConnector b) : Prop :=
  ∀ u, D.canonicalBandMap b (upper u) ∈ D.centralGraph.carrier ↔
      u = 0 ∨ u = 1

/-- The proof package carried by one pair of completed-theta connectors. -/
abbrev CanonicalFourPortThetaCompletionProperty (b : D.BandIndex)
    (E : D.CanonicalFourPortConnectorData b) : Prop :=
  D.CanonicalLowerConnectorAvoidsCarrier b E.1 ∧
    D.CanonicalUpperConnectorAvoidsCarrier b E.2 ∧
      Nonempty (FilledThetaSystemData (D.canonicalCompletedPlaneThetaPath b E.1 E.2))

/-- Exact connector and filled-theta data sufficient for the relative ambient straightening. -/
def CanonicalFourPortThetaCompletionData (b : D.BandIndex) :=
  {E : D.CanonicalFourPortConnectorData b //
    D.CanonicalFourPortThetaCompletionProperty b E}

namespace CanonicalFourPortThetaCompletionData

variable {D} {b : D.BandIndex} (C : D.CanonicalFourPortThetaCompletionData b)

def lowerConnector : Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)) :=
  C.1.1

def upperConnector : Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1))
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)) :=
  C.1.2

theorem lower_mem_carrier_iff (u : unitInterval) :
    D.canonicalBandMap b (C.lowerConnector u) ∈ D.centralGraph.carrier ↔
      u = 0 ∨ u = 1 :=
  C.2.1 u

theorem upper_mem_carrier_iff (u : unitInterval) :
    D.canonicalBandMap b (C.upperConnector u) ∈ D.centralGraph.carrier ↔
      u = 0 ∨ u = 1 :=
  C.2.2.1 u

def filledTheta : FilledThetaSystemData
    (D.canonicalCompletedPlaneThetaPath b C.lowerConnector C.upperConnector) :=
  Classical.choice C.2.2.2

theorem planeSystem : ThreePathSystem
    (D.canonicalCompletedPlaneThetaPath b C.lowerConnector C.upperConnector) :=
  C.filledTheta.system

theorem outer_decomposition :
    closure C.planeSystem.circle12.inside =
      closure C.planeSystem.circle01.inside ∪ closure C.planeSystem.circle02.inside :=
  C.filledTheta.outer_decomposition

/-- Conjugate the exact filled-theta ambient map back to product strip coordinates. -/
noncomputable def homeomorph : Plane ≃ₜ Plane :=
  coveringPlaneCoordinates.symm.trans
    ((C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
      C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition).trans
        coveringPlaneCoordinates)

theorem homeomorph_apply_completedThetaPath (i : Fin 3) (u : unitInterval) :
    C.homeomorph
        (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector i u) =
      standardFourPortThetaPath i u := by
  fin_cases i
  · change coveringPlaneCoordinates
        (C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 0 u))) =
      standardFourPortThetaPath 0 u
    have h := C.planeSystem.outer12AmbientHomeomorph_apply_path0
      standardPlaneFourPortThetaSystem C.outer_decomposition
        standardPlaneFourPortTheta_outer_decomposition u
    change
      C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 0 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 0 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
        congrArg coveringPlaneCoordinates h
  · change coveringPlaneCoordinates
        (C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 1 u))) =
      standardFourPortThetaPath 1 u
    have h := C.planeSystem.outer12AmbientHomeomorph_apply_path1
      standardPlaneFourPortThetaSystem C.outer_decomposition
        standardPlaneFourPortTheta_outer_decomposition u
    change
      C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 1 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 1 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
        congrArg coveringPlaneCoordinates h
  · change coveringPlaneCoordinates
        (C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 2 u))) =
      standardFourPortThetaPath 2 u
    have h := C.planeSystem.outer12AmbientHomeomorph_apply_path2
      standardPlaneFourPortThetaSystem C.outer_decomposition
        standardPlaneFourPortTheta_outer_decomposition u
    change
      C.planeSystem.outer12AmbientHomeomorph standardPlaneFourPortThetaSystem
          C.outer_decomposition standardPlaneFourPortTheta_outer_decomposition
          (coveringPlaneCoordinates.symm
            (D.canonicalCompletedThetaPath b C.lowerConnector C.upperConnector 2 u)) =
        coveringPlaneCoordinates.symm (standardFourPortThetaPath 2 u) at h
    simpa only [coveringPlaneCoordinates.apply_symm_apply] using
        congrArg coveringPlaneCoordinates h

theorem fixes_seam (u : unitInterval) :
    C.homeomorph (bandSeamPath u) = bandSeamPath u := by
  simpa only [canonicalCompletedThetaPath, standardFourPortThetaPath] using
    C.homeomorph_apply_completedThetaPath 0 u

theorem homeomorph_apply_leftLowerBranch (u : unitInterval) :
    C.homeomorph (D.centralLeftLowerBranchPath b u) =
      standardLeftLowerBranchPath (unitInterval.symm u) := by
  have h := C.homeomorph_apply_completedThetaPath 1
    (Schoenflies.ThreePiecePath.firstCoordinate (unitInterval.symm u))
  rw [canonicalCompletedThetaPath, D.canonicalLowerThetaRoute_firstCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_firstCoordinate] at h
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using h

theorem homeomorph_apply_lowerConnector (u : unitInterval) :
    C.homeomorph (C.lowerConnector u) = bandBottomPath u := by
  have h := C.homeomorph_apply_completedThetaPath 1
    (Schoenflies.ThreePiecePath.middleCoordinate u)
  simpa only [canonicalCompletedThetaPath, D.canonicalLowerThetaRoute_middleCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_middleCoordinate] using h

theorem homeomorph_apply_rightLowerBranch (u : unitInterval) :
    C.homeomorph (D.centralRightLowerBranchPath b u) =
      standardRightLowerBranchPath u := by
  have h := C.homeomorph_apply_completedThetaPath 1
    (Schoenflies.ThreePiecePath.thirdCoordinate u)
  simpa only [canonicalCompletedThetaPath, D.canonicalLowerThetaRoute_thirdCoordinate,
    standardFourPortThetaPath_one, standardLowerThetaPath_thirdCoordinate] using h

theorem homeomorph_apply_leftUpperBranch (u : unitInterval) :
    C.homeomorph (D.centralLeftUpperBranchPath b u) =
      standardLeftUpperBranchPath u := by
  have h := C.homeomorph_apply_completedThetaPath 2
    (Schoenflies.ThreePiecePath.firstCoordinate u)
  simpa only [canonicalCompletedThetaPath, D.canonicalUpperThetaRoute_firstCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_firstCoordinate] using h

theorem homeomorph_apply_upperConnector (u : unitInterval) :
    C.homeomorph (C.upperConnector u) = bandTopPath u := by
  have h := C.homeomorph_apply_completedThetaPath 2
    (Schoenflies.ThreePiecePath.middleCoordinate u)
  simpa only [canonicalCompletedThetaPath, D.canonicalUpperThetaRoute_middleCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_middleCoordinate] using h

theorem homeomorph_apply_rightUpperBranch (u : unitInterval) :
    C.homeomorph (D.centralRightUpperBranchPath b u) =
      standardRightUpperBranchPath (unitInterval.symm u) := by
  have h := C.homeomorph_apply_completedThetaPath 2
    (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm u))
  rw [canonicalCompletedThetaPath, D.canonicalUpperThetaRoute_thirdCoordinate,
    standardFourPortThetaPath_two, standardUpperThetaPath_thirdCoordinate] at h
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using h

private theorem symm_apply_leftLowerBranch (u : unitInterval) :
    C.homeomorph.symm (standardLeftLowerBranchPath u) =
      D.centralLeftLowerBranchPath b (unitInterval.symm u) := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  symm
  simpa only [unitInterval.symm_symm] using
    C.homeomorph_apply_leftLowerBranch (unitInterval.symm u)

private theorem symm_apply_lowerConnector (u : unitInterval) :
    C.homeomorph.symm (bandBottomPath u) = C.lowerConnector u := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  exact (C.homeomorph_apply_lowerConnector u).symm

private theorem symm_apply_rightLowerBranch (u : unitInterval) :
    C.homeomorph.symm (standardRightLowerBranchPath u) =
      D.centralRightLowerBranchPath b u := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  exact (C.homeomorph_apply_rightLowerBranch u).symm

private theorem symm_apply_leftUpperBranch (u : unitInterval) :
    C.homeomorph.symm (standardLeftUpperBranchPath u) =
      D.centralLeftUpperBranchPath b u := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  exact (C.homeomorph_apply_leftUpperBranch u).symm

private theorem symm_apply_upperConnector (u : unitInterval) :
    C.homeomorph.symm (bandTopPath u) = C.upperConnector u := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  exact (C.homeomorph_apply_upperConnector u).symm

private theorem symm_apply_rightUpperBranch (u : unitInterval) :
    C.homeomorph.symm (standardRightUpperBranchPath u) =
      D.centralRightUpperBranchPath b (unitInterval.symm u) := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  symm
  simpa only [unitInterval.symm_symm] using
    C.homeomorph_apply_rightUpperBranch (unitInterval.symm u)

private theorem symm_apply_seam (u : unitInterval) :
    C.homeomorph.symm (bandSeamPath u) = bandSeamPath u := by
  apply C.homeomorph.injective
  rw [C.homeomorph.apply_symm_apply]
  exact (C.fixes_seam u).symm

private theorem image_range_leftLowerBranch :
    C.homeomorph '' Set.range (D.centralLeftLowerBranchPath b) =
      Set.range standardLeftLowerBranchPath := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨unitInterval.symm u, (C.homeomorph_apply_leftLowerBranch u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨D.centralLeftLowerBranchPath b (unitInterval.symm u),
      ⟨unitInterval.symm u, rfl⟩, ?_⟩
    simpa only [unitInterval.symm_symm] using
      C.homeomorph_apply_leftLowerBranch (unitInterval.symm u)

private theorem image_range_rightLowerBranch :
    C.homeomorph '' Set.range (D.centralRightLowerBranchPath b) =
      Set.range standardRightLowerBranchPath := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (C.homeomorph_apply_rightLowerBranch u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨D.centralRightLowerBranchPath b u, ⟨u, rfl⟩,
      C.homeomorph_apply_rightLowerBranch u⟩

private theorem image_range_leftUpperBranch :
    C.homeomorph '' Set.range (D.centralLeftUpperBranchPath b) =
      Set.range standardLeftUpperBranchPath := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (C.homeomorph_apply_leftUpperBranch u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨D.centralLeftUpperBranchPath b u, ⟨u, rfl⟩,
      C.homeomorph_apply_leftUpperBranch u⟩

private theorem image_range_rightUpperBranch :
    C.homeomorph '' Set.range (D.centralRightUpperBranchPath b) =
      Set.range standardRightUpperBranchPath := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨unitInterval.symm u, (C.homeomorph_apply_rightUpperBranch u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨D.centralRightUpperBranchPath b (unitInterval.symm u),
      ⟨unitInterval.symm u, rfl⟩, ?_⟩
    simpa only [unitInterval.symm_symm] using
      C.homeomorph_apply_rightUpperBranch (unitInterval.symm u)

private theorem image_range_seam :
    C.homeomorph '' Set.range bandSeamPath = Set.range bandSeamPath := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (C.fixes_seam u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨bandSeamPath u, ⟨u, rfl⟩, C.fixes_seam u⟩

/-- The filled-theta homeomorphism sends the canonical source tree to the standard singular
four-port carrier. -/
theorem image_centralFourPortTreeCarrier :
    C.homeomorph '' D.centralFourPortTreeCarrier b = standardBandSingularCarrier := by
  rw [centralFourPortTreeCarrier, ← D.centralLeftBranchPaths_range_union b,
    ← D.centralRightBranchPaths_range_union b, Set.image_union, Set.image_union,
    Set.image_union, Set.image_union, C.image_range_leftLowerBranch,
    C.image_range_leftUpperBranch, C.image_range_seam,
    C.image_range_rightLowerBranch, C.image_range_rightUpperBranch,
    ← range_bandLeftPath_eq_standardHalves, ← range_bandRightPath_eq_standardHalves]
  ext z
  simp only [standardBandSingularCarrier, Set.mem_union]
  tauto

/-- On the five standard compact edges, the inverse straightener meets the analytic barrier
exactly on the standard singular three-edge carrier. -/
theorem local_carrier_iff (z : Plane) (hz : z ∈ standardBandPatchCarrier) :
    (D.canonicalBandMap b (C.homeomorph.symm z) ∈ D.centralGraph.carrier ↔
      z ∈ standardBandSingularCarrier) := by
  rcases hz with ((((hleft | hright) | hbottom) | htop) | hseam)
  · rw [range_bandLeftPath_eq_standardHalves] at hleft
    rcases hleft with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inl ?_)
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inl ⟨u, rfl⟩
      · intro _
        rw [C.symm_apply_leftLowerBranch]
        exact D.canonicalBandMap_centralLeftLowerBranchPath_mem_carrier b _
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inl ?_)
        rw [range_bandLeftPath_eq_standardHalves]
        exact Or.inr ⟨u, rfl⟩
      · intro _
        rw [C.symm_apply_leftUpperBranch]
        exact D.canonicalBandMap_centralLeftUpperBranchPath_mem_carrier b _
  · rw [range_bandRightPath_eq_standardHalves] at hright
    rcases hright with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inr ?_)
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inl ⟨u, rfl⟩
      · intro _
        rw [C.symm_apply_rightLowerBranch]
        exact D.canonicalBandMap_centralRightLowerBranchPath_mem_carrier b _
    · constructor
      · intro _
        unfold standardBandSingularCarrier
        refine Or.inl (Or.inr ?_)
        rw [range_bandRightPath_eq_standardHalves]
        exact Or.inr ⟨u, rfl⟩
      · intro _
        rw [C.symm_apply_rightUpperBranch]
        exact D.canonicalBandMap_centralRightUpperBranchPath_mem_carrier b _
  · rcases hbottom with ⟨u, rfl⟩
    rw [C.symm_apply_lowerConnector, C.lower_mem_carrier_iff]
    exact (bandBottomPath_mem_standardSingularUnion_iff u).symm
  · rcases htop with ⟨u, rfl⟩
    rw [C.symm_apply_upperConnector, C.upper_mem_carrier_iff]
    exact (bandTopPath_mem_standardSingularUnion_iff u).symm
  · rcases hseam with ⟨u, rfl⟩
    constructor
    · intro _
      unfold standardBandSingularCarrier
      exact Or.inr ⟨u, rfl⟩
    · intro _
      rw [C.symm_apply_seam]
      exact D.canonicalBandMap_bandSeamPath_mem_carrier b u

end CanonicalFourPortThetaCompletionData

/-- A filled-theta completion in every canonical band supplies the relative straightener and
hence the exact compact-patch arc data consumed downstream. -/
noncomputable def canonicalFourPortTreeStraighteningData
    (C : ∀ b : D.BandIndex, D.CanonicalFourPortThetaCompletionData b) :
    D.CanonicalFourPortTreeStraighteningData where
  homeomorph := fun b ↦ (C b).homeomorph
  fixes_seam := fun b u ↦ (C b).fixes_seam u
  image_tree := fun b ↦ (C b).image_centralFourPortTreeCarrier
  local_carrier_iff := fun b z hz ↦ (C b).local_carrier_iff z hz

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
