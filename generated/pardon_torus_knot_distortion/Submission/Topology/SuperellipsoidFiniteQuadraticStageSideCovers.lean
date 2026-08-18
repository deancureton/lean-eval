import Submission.Topology.FourPortQuadraticLabelChangeContainment
import Submission.Topology.SuperellipsoidCanonicalFiniteStageIntegration

/-!
# Finite stage-sided covers from quadratic four-port moves

This module assembles the validated local quadratic disk-side theorem at every transition of an
already constructed finite regular-stage sequence.  The only per-move inputs retained are the
honest chart-aligned six-edge presentation, its endpoint-circle attachment, and the explicit
quadratic endpoint-label description.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-- All local geometric data for one transition of an all-inessential audited stage sequence. -/
structure QuadraticFourPortStageSideCoverData
    (S : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : S.AllInessential) (k : ℕ) (hk : k < S.length) where
  frame : Equiv.Perm (Fin 3)
  center : R3
  outerScale : ℝ
  cutHeight : ℝ
  outerIndex : Type
  cutIndex : Type
  [outerIndex_fintype : Fintype outerIndex]
  [cutIndex_fintype : Fintype cutIndex]
  barrier : FiniteSuperellipsoidBarrierGraph Phi frame center outerScale cutHeight
    outerIndex cutIndex
  order : barrier.CutCircleTransverseCyclicOrderFamily
  band : Fin order.toPairedSeamEnumeration.bandCount
  chart : order.LiftedGlobalBandTubularChartData band
  raw : FourPortRawEndpointData chart.toGlobalBandTubularChartData.toPairedSeamBandChart
    (S.parityStage k) (S.parityStage (k + 1))
  circles : FourPortRawCircleData raw
  presentation : FourPortRawSixEdgeBandPresentation circles
  endpointAttachment :
    FourPortRawSixEdgeBandPresentation.CanonicalEndpointCircleSideAttachment
      chart presentation (S.system k) (S.system (k + 1))
  endpointLabels :
    FourPortRawSixEdgeBandPresentation.QuadraticEndpointLabelData
      (pre := S.parityStage k) (post := S.parityStage (k + 1)) chart

namespace QuadraticFourPortStageSideCoverData

variable {S : FiniteRegularSphereSurgeryStageSequence Phi}
  {hzero : S.AllInessential} {k : ℕ} {hk : k < S.length}

/-- One quadratic move gives the pre-sided or post-sided elementary cover required by the
heterogeneous parity induction. -/
def toStageSideCover
    (D : QuadraticFourPortStageSideCoverData S hzero k hk) :
    (FiniteElementaryDiskSideCover (S.system k) (hzero k (Nat.le_of_lt hk))
      (S.parityStage k) (S.parityStage (k + 1))) ⊕
    (FiniteElementaryDiskSideCover (S.system (k + 1))
      (hzero (k + 1) hk) (S.parityStage (k + 1)) (S.parityStage k)) :=
  by
    letI := D.outerIndex_fintype
    letI := D.cutIndex_fintype
    exact D.presentation.canonicalEndpointCircleSideAlternative_of_quadraticLabels
      D.chart D.endpointAttachment D.endpointLabels

end QuadraticFourPortStageSideCoverData

/-- A quadratic four-port description at every successive transition. -/
structure FiniteQuadraticFourPortStageSideCoverData
    (S : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : S.AllInessential) where
  move : ∀ k (hk : k < S.length),
    Nonempty (QuadraticFourPortStageSideCoverData S hzero k hk)

namespace FiniteQuadraticFourPortStageSideCoverData

variable {S : FiniteRegularSphereSurgeryStageSequence Phi}
  {hzero : S.AllInessential}

/-- The local quadratic packages construct the exact sided-cover family consumed by the global
all-inessential resolution. -/
def toFiniteStageSideDiskCoverData
    (D : FiniteQuadraticFourPortStageSideCoverData S hzero) :
    FiniteStageSideDiskCoverData S hzero where
  cover k hk := (D.move k hk).some.toStageSideCover

end FiniteQuadraticFourPortStageSideCoverData
end Submission.Topology
