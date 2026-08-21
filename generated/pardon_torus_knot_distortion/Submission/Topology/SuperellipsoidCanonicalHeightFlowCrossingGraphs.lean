import Submission.Topology.SuperellipsoidCanonicalHeightFlowFilledParameters

/-!
# Continuous crossing graphs for the canonical height-flow strip

The two controlled outer-level crossings on every selected height slice are unique.  Their
parameters vary continuously because the moving outer arms lift through the inverse of the
embedded height-flow collar.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev ConnectorBand := D.openChartNarrowedData.heightData.band

private abbrev ConnectorBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private abbrev ConnectorFlowTimes := globalBandFlowCollarTimes D.ConnectorBand

/-- The selected closed interval of flow times, as a parameter space. -/
abbrev CentralConnectorSelectedTime :=
  {t : D.ConnectorFlowTimes // t ∈ D.centralConnectorSelectedTimes}

/-- The unique left outer crossing on a selected height slice. -/
noncomputable def centralConnectorLeftCrossingParameter
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) : unitInterval :=
  Classical.choose (D.existsUnique_centralConnectorLeftCrossing b t.1 t.2)

theorem centralConnectorLeftCrossingParameter_spec
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    D.centralConnectorLeftCrossingParameter b t ∈
        Icc (D.centralConnectorLeftProbe b) (D.centralConnectorLeftInnerProbe b) ∧
      D.centralHeightFlowOuterDefect b t.1
        (D.centralConnectorLeftCrossingParameter b t) = 0 :=
  (Classical.choose_spec (D.existsUnique_centralConnectorLeftCrossing b t.1 t.2)).1

/-- The unique right outer crossing on a selected height slice. -/
noncomputable def centralConnectorRightCrossingParameter
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) : unitInterval :=
  Classical.choose (D.existsUnique_centralConnectorRightCrossing b t.1 t.2)

theorem centralConnectorRightCrossingParameter_spec
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    D.centralConnectorRightCrossingParameter b t ∈
        Icc (D.centralConnectorRightInnerProbe b) (D.centralConnectorRightProbe b) ∧
      D.centralHeightFlowOuterDefect b t.1
        (D.centralConnectorRightCrossingParameter b t) = 0 :=
  (Classical.choose_spec (D.existsUnique_centralConnectorRightCrossing b t.1 t.2)).1

private def centralConnectorFlowHomeomorph (b : D.ConnectorBandIndex) :=
  D.centralCutOrder.globalBandPlaneFlowCollarHomeomorph b D.ConnectorBand
    D.centralHeightFlowData

private def centralConnectorLeftArmFlowRangePoint
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    Set.range (globalBandPlaneFlowCollarMap D.centralCutOrder b D.ConnectorBand
      D.centralHeightFlowData) := by
  refine ⟨D.centralLeftOuterArmLift b (D.openChartNarrowedTime t.1), ?_⟩
  refine ⟨(D.centralConnectorLeftCrossingParameter b t, t.1), ?_⟩
  exact D.centralConnectorLeftCrossing_eq_outerArm b t.1
    (D.abs_lt_uniformCentralConnectorTimeRadius t.2)
    (D.centralConnectorLeftCrossingParameter b t)
    (D.centralConnectorLeftCrossingParameter_spec b t).1
    (D.centralConnectorLeftCrossingParameter_spec b t).2

private theorem continuous_centralConnectorLeftArmFlowRangePoint
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorLeftArmFlowRangePoint b) := by
  apply Continuous.subtype_mk
  exact (D.continuous_centralLeftOuterArmLift b).comp <|
    D.continuous_openChartNarrowedTime.comp continuous_subtype_val

private theorem centralConnectorFlowHomeomorph_symm_leftArm
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    (D.centralConnectorFlowHomeomorph b).symm
        (D.centralConnectorLeftArmFlowRangePoint b t) =
      (D.centralConnectorLeftCrossingParameter b t, t.1) := by
  apply (D.centralConnectorFlowHomeomorph b).injective
  rw [(D.centralConnectorFlowHomeomorph b).apply_symm_apply]
  apply Subtype.ext
  exact (D.centralConnectorLeftCrossing_eq_outerArm b t.1
    (D.abs_lt_uniformCentralConnectorTimeRadius t.2)
    (D.centralConnectorLeftCrossingParameter b t)
    (D.centralConnectorLeftCrossingParameter_spec b t).1
    (D.centralConnectorLeftCrossingParameter_spec b t).2).symm

/-- The left crossing parameter varies continuously with the selected flow time. -/
theorem continuous_centralConnectorLeftCrossingParameter
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorLeftCrossingParameter b) := by
  have hEq : D.centralConnectorLeftCrossingParameter b = fun t ↦
      ((D.centralConnectorFlowHomeomorph b).symm
        (D.centralConnectorLeftArmFlowRangePoint b t)).1 := by
    funext t
    rw [D.centralConnectorFlowHomeomorph_symm_leftArm b t]
  rw [hEq]
  exact continuous_fst.comp <|
    (D.centralConnectorFlowHomeomorph b).symm.continuous.comp
      (D.continuous_centralConnectorLeftArmFlowRangePoint b)

private def centralConnectorRightArmFlowRangePoint
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    Set.range (globalBandPlaneFlowCollarMap D.centralCutOrder b D.ConnectorBand
      D.centralHeightFlowData) := by
  refine ⟨D.centralRightOuterArmLift b (D.openChartNarrowedTime t.1), ?_⟩
  refine ⟨(D.centralConnectorRightCrossingParameter b t, t.1), ?_⟩
  exact D.centralConnectorRightCrossing_eq_outerArm b t.1
    (D.abs_lt_uniformCentralConnectorTimeRadius t.2)
    (D.centralConnectorRightCrossingParameter b t)
    (D.centralConnectorRightCrossingParameter_spec b t).1
    (D.centralConnectorRightCrossingParameter_spec b t).2

private theorem continuous_centralConnectorRightArmFlowRangePoint
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorRightArmFlowRangePoint b) := by
  apply Continuous.subtype_mk
  exact (D.continuous_centralRightOuterArmLift b).comp <|
    D.continuous_openChartNarrowedTime.comp continuous_subtype_val

private theorem centralConnectorFlowHomeomorph_symm_rightArm
    (b : D.ConnectorBandIndex) (t : D.CentralConnectorSelectedTime) :
    (D.centralConnectorFlowHomeomorph b).symm
        (D.centralConnectorRightArmFlowRangePoint b t) =
      (D.centralConnectorRightCrossingParameter b t, t.1) := by
  apply (D.centralConnectorFlowHomeomorph b).injective
  rw [(D.centralConnectorFlowHomeomorph b).apply_symm_apply]
  apply Subtype.ext
  exact (D.centralConnectorRightCrossing_eq_outerArm b t.1
    (D.abs_lt_uniformCentralConnectorTimeRadius t.2)
    (D.centralConnectorRightCrossingParameter b t)
    (D.centralConnectorRightCrossingParameter_spec b t).1
    (D.centralConnectorRightCrossingParameter_spec b t).2).symm

/-- The right crossing parameter varies continuously with the selected flow time. -/
theorem continuous_centralConnectorRightCrossingParameter
    (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorRightCrossingParameter b) := by
  have hEq : D.centralConnectorRightCrossingParameter b = fun t ↦
      ((D.centralConnectorFlowHomeomorph b).symm
        (D.centralConnectorRightArmFlowRangePoint b t)).1 := by
    funext t
    rw [D.centralConnectorFlowHomeomorph_symm_rightArm b t]
  rw [hEq]
  exact continuous_fst.comp <|
    (D.centralConnectorFlowHomeomorph b).symm.continuous.comp
      (D.continuous_centralConnectorRightArmFlowRangePoint b)

/-- The lower endpoint of the selected time interval. -/
def centralLowerSelectedTime : D.CentralConnectorSelectedTime :=
  ⟨D.centralLowerConnectorTime, ⟨le_rfl, by
    apply le_of_lt
    exact D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos⟩⟩

/-- The upper endpoint of the selected time interval. -/
def centralUpperSelectedTime : D.CentralConnectorSelectedTime :=
  ⟨D.centralUpperConnectorTime, ⟨by
    apply le_of_lt
    exact D.centralLowerConnectorTime_neg.trans D.centralUpperConnectorTime_pos, le_rfl⟩⟩

theorem centralConnectorLeftCrossingParameter_lower
    (b : D.ConnectorBandIndex) :
    D.centralConnectorLeftCrossingParameter b D.centralLowerSelectedTime =
      D.centralLowerLeftCrossingParameter b := by
  exact (D.existsUnique_centralConnectorLeftCrossing b D.centralLowerConnectorTime
    D.centralLowerSelectedTime.2).unique
      (D.centralConnectorLeftCrossingParameter_spec b D.centralLowerSelectedTime)
      (D.centralLowerLeftCrossingParameter_mem b)

theorem centralConnectorRightCrossingParameter_lower
    (b : D.ConnectorBandIndex) :
    D.centralConnectorRightCrossingParameter b D.centralLowerSelectedTime =
      D.centralLowerRightCrossingParameter b := by
  exact (D.existsUnique_centralConnectorRightCrossing b D.centralLowerConnectorTime
    D.centralLowerSelectedTime.2).unique
      (D.centralConnectorRightCrossingParameter_spec b D.centralLowerSelectedTime)
      (D.centralLowerRightCrossingParameter_mem b)

theorem centralConnectorLeftCrossingParameter_upper
    (b : D.ConnectorBandIndex) :
    D.centralConnectorLeftCrossingParameter b D.centralUpperSelectedTime =
      D.centralUpperLeftCrossingParameter b := by
  exact (D.existsUnique_centralConnectorLeftCrossing b D.centralUpperConnectorTime
    D.centralUpperSelectedTime.2).unique
      (D.centralConnectorLeftCrossingParameter_spec b D.centralUpperSelectedTime)
      (D.centralUpperLeftCrossingParameter_mem b)

theorem centralConnectorRightCrossingParameter_upper
    (b : D.ConnectorBandIndex) :
    D.centralConnectorRightCrossingParameter b D.centralUpperSelectedTime =
      D.centralUpperRightCrossingParameter b := by
  exact (D.existsUnique_centralConnectorRightCrossing b D.centralUpperConnectorTime
    D.centralUpperSelectedTime.2).unique
      (D.centralConnectorRightCrossingParameter_spec b D.centralUpperSelectedTime)
      (D.centralUpperRightCrossingParameter_mem b)

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
