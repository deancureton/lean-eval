import Submission.Topology.SuperellipsoidCanonicalBooleanOutsidePairing
import Submission.Topology.SuperellipsoidCanonicalHeightFlowFilledSweep
import Submission.Topology.BooleanFourPortLocalPaths

/-!
# Canonical port branches toward the fixed outside paths

The straightened charts give the exact branch from each central seam vertex to either labelled
corner on its outer arm.  Constructing the fixed outside paths still requires trimming these
branches from the full seam-to-seam outer gaps; concatenating with the untrimmed gap would retrace
the branch and fail injectivity.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph
namespace OuterCircleTransverseHeightCyclicOrderFamily

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
  [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

noncomputable def seamToCornerPathOfBandSide
    (T : cutOrder.GlobalBandTubularChartFamily)
    (b : Fin cutOrder.toPairedSeamEnumeration.bandCount) (side level : Fin 2) :
    Path (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, side)).1
      (fourPortChartPoint T.chart (b, side, level)) := by
  refine Fin.cases ?_ (fun side : Fin 1 =>
    Fin.cases ?_ (fun k : Fin 0 => Fin.elim0 k) side) side
  · refine Fin.cases ?_ (fun level : Fin 1 =>
      Fin.cases ?_ (fun k : Fin 0 => Fin.elim0 k) level) level
    · let path := standardLeftLowerBranchPath.map (T.chart b).chartEmbedding.continuous
      have hsource :
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 0)).1 =
            (T.chart b).leftVertex := by
        calc
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 0)).1 =
              (cutOrder.toPairedSeamEnumeration.firstVertex b).1 := rfl
          _ = (T.chart b).leftVertex :=
            (T.band b).toPairedSeamBandChart_leftVertex.symm
      have htarget : fourPortChartPoint T.chart (b, 0, 0) = (T.chart b).leftBottom :=
        fourPortChartPoint_zero_zero T.chart b
      exact path.cast hsource htarget
    · let path := standardLeftUpperBranchPath.map (T.chart b).chartEmbedding.continuous
      have hsource :
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 0)).1 =
            (T.chart b).leftVertex := by
        calc
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 0)).1 =
              (cutOrder.toPairedSeamEnumeration.firstVertex b).1 := rfl
          _ = (T.chart b).leftVertex :=
            (T.band b).toPairedSeamBandChart_leftVertex.symm
      have htarget : fourPortChartPoint T.chart (b, 0, 1) = (T.chart b).leftTop :=
        fourPortChartPoint_zero_one T.chart b
      exact path.cast hsource htarget
  · refine Fin.cases ?_ (fun level : Fin 1 =>
      Fin.cases ?_ (fun k : Fin 0 => Fin.elim0 k) level) level
    · let path := standardRightLowerBranchPath.symm.map
          (T.chart b).chartEmbedding.continuous
      have hsource :
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 1)).1 =
            (T.chart b).rightVertex := by
        calc
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 1)).1 =
              (cutOrder.toPairedSeamEnumeration.secondVertex b).1 := rfl
          _ = (T.chart b).rightVertex :=
            (T.band b).toPairedSeamBandChart_rightVertex.symm
      have htarget : fourPortChartPoint T.chart (b, 1, 0) = (T.chart b).rightBottom :=
        fourPortChartPoint_one_zero T.chart b
      exact path.cast hsource htarget
    · let path := standardRightUpperBranchPath.symm.map
          (T.chart b).chartEmbedding.continuous
      have hsource :
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 1)).1 =
            (T.chart b).rightVertex := by
        calc
          (cutOrder.toPairedSeamEnumeration.endpointEquiv (b, 1)).1 =
              (cutOrder.toPairedSeamEnumeration.secondVertex b).1 := rfl
          _ = (T.chart b).rightVertex :=
            (T.band b).toPairedSeamBandChart_rightVertex.symm
      have htarget : fourPortChartPoint T.chart (b, 1, 1) = (T.chart b).rightTop :=
        fourPortChartPoint_one_one T.chart b
      exact path.cast hsource htarget

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
private theorem chart_mem_transportedTorus
    (T : cutOrder.GlobalBandTubularChartFamily)
    (b : Fin cutOrder.toPairedSeamEnumeration.bandCount) (z : Plane) :
    (T.chart b).chart z ∈ transportedTorus Phi :=
  ((T.band b).strip z).1.2

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
theorem seamToCornerPathOfBandSide_mem_transportedTorus
    (T : cutOrder.GlobalBandTubularChartFamily)
    (b : Fin cutOrder.toPairedSeamEnumeration.bandCount) (side level : Fin 2)
    (t : unitInterval) :
    seamToCornerPathOfBandSide cutOrder T b side level t ∈ transportedTorus Phi := by
  fin_cases side <;> fin_cases level
  all_goals
    change (T.chart b).chart _ ∈ transportedTorus Phi
    exact chart_mem_transportedTorus cutOrder T b _

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
theorem seamToCornerPathOfBandSide_injective
    (T : cutOrder.GlobalBandTubularChartFamily)
    (b : Fin cutOrder.toPairedSeamEnumeration.bandCount) (side level : Fin 2) :
    Function.Injective (seamToCornerPathOfBandSide cutOrder T b side level) := by
  fin_cases side <;> fin_cases level
  · change Function.Injective fun u ↦
      (T.chart b).chart (standardLeftLowerBranchPath u)
    exact (T.chart b).chartEmbedding.injective.comp standardLeftLowerBranchPath_injective
  · change Function.Injective fun u ↦
      (T.chart b).chart (standardLeftUpperBranchPath u)
    exact (T.chart b).chartEmbedding.injective.comp standardLeftUpperBranchPath_injective
  · change Function.Injective fun u ↦
      (T.chart b).chart (standardRightLowerBranchPath (unitInterval.symm u))
    apply (T.chart b).chartEmbedding.injective.comp
      standardRightLowerBranchPath_injective |>.comp
    intro u v huv
    have h := congrArg unitInterval.symm huv
    simpa only [unitInterval.symm_symm] using h
  · change Function.Injective fun u ↦
      (T.chart b).chart (standardRightUpperBranchPath (unitInterval.symm u))
    apply (T.chart b).chartEmbedding.injective.comp
      standardRightUpperBranchPath_injective |>.comp
    intro u v huv
    have h := congrArg unitInterval.symm huv
    simpa only [unitInterval.symm_symm] using h

/-- The canonical chart branch from a seam vertex to its lower or upper corner. -/
noncomputable def seamToFourPortCornerPath
    (T : cutOrder.GlobalBandTubularChartFamily)
    (v : SuperellipsoidSeamVertex Phi frame c R d) (level : Fin 2) :
    Path v.1
      (fourPortChartPoint T.chart
        ((seamBandSide cutOrder v).1, (seamBandSide cutOrder v).2, level)) :=
  (seamToCornerPathOfBandSide cutOrder T (seamBandSide cutOrder v).1
    (seamBandSide cutOrder v).2 level).cast
      (congrArg Subtype.val
        (cutOrder.toPairedSeamEnumeration.endpointEquiv.apply_symm_apply v).symm) rfl

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
theorem seamToFourPortCornerPath_mem_transportedTorus
    (T : cutOrder.GlobalBandTubularChartFamily)
    (v : SuperellipsoidSeamVertex Phi frame c R d) (level : Fin 2)
    (t : unitInterval) :
    seamToFourPortCornerPath cutOrder T v level t ∈ transportedTorus Phi := by
  unfold seamToFourPortCornerPath
  rw [Path.cast_coe]
  exact seamToCornerPathOfBandSide_mem_transportedTorus cutOrder T _ _ _ t

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] in
theorem seamToFourPortCornerPath_injective
    (T : cutOrder.GlobalBandTubularChartFamily)
    (v : SuperellipsoidSeamVertex Phi frame c R d) (level : Fin 2) :
    Function.Injective (seamToFourPortCornerPath cutOrder T v level) := by
  unfold seamToFourPortCornerPath
  exact seamToCornerPathOfBandSide_injective cutOrder T _ _ _

/-! The middle subarc between two corner points is deliberately not defined here.  It must be
obtained by trimming the two chart branches from the corresponding embedded outer gap. -/

end OuterCircleTransverseHeightCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
