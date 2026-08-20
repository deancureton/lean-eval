import Submission.Topology.SuperellipsoidCanonicalEndpointRegularity
import Submission.Topology.SuperellipsoidOuterCircleCyclicOrder
import Submission.Topology.SuperellipsoidOuterSmoothCircleSection
import Submission.Topology.SuperellipsoidSeamClosureGluing
import Submission.Topology.SuperellipsoidSmoothCutCircleSection

/-!
# Canonical regular barrier graphs at the two endpoint heights

Simultaneous endpoint regularity canonically supplies smooth outer and cutting circle families.
The regular seam closure theorem turns those families into finite barrier graphs, and their
retained smooth parametrizations construct both cyclic-order packages.  Thus no graph, circle
classification, or smooth-lift choice remains at either endpoint.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

/-- Canonical lower endpoint height. -/
def lowerHeight (D : CanonicalEndpointRegularityData S) : ℝ :=
  S.cut.height - D.heightData.band.ε

/-- Canonical upper endpoint height. -/
def upperHeight (D : CanonicalEndpointRegularityData S) : ℝ :=
  S.cut.height + D.heightData.band.ε

/-- Smooth outer circles at the selected central cut height. -/
def centralOuterFamily (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidOuterTorusSmoothCircleFamily
      Phi frame c S.outer.scale S.cut.height :=
  FiniteSuperellipsoidOuterTorusSmoothCircleFamily.ofRegularValue
    D.scale_pos.le S.outer.surfaceRegular S.cut.seamRegular

/-- Smooth cutting circles at the selected central cut height. -/
def centralCutFamily (_D : CanonicalEndpointRegularityData S) :
    FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame S.cut.height :=
  FiniteCoordinatePlaneTorusSmoothCircleFamily.ofRegularValue
    Phi frame S.cut.surfaceRegular

/-- Smooth outer circles at the lower endpoint height. -/
def lowerOuterFamily (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidOuterTorusSmoothCircleFamily
      Phi frame c S.outer.scale D.lowerHeight :=
  FiniteSuperellipsoidOuterTorusSmoothCircleFamily.ofRegularValue
    D.scale_pos.le S.outer.surfaceRegular D.lowerSeamRegular

/-- Smooth cutting circles at the lower endpoint height. -/
def lowerCutFamily (D : CanonicalEndpointRegularityData S) :
    FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame D.lowerHeight :=
  FiniteCoordinatePlaneTorusSmoothCircleFamily.ofRegularValue
    Phi frame D.lowerSurfaceRegular

/-- Smooth outer circles at the upper endpoint height. -/
def upperOuterFamily (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidOuterTorusSmoothCircleFamily
      Phi frame c S.outer.scale D.upperHeight :=
  FiniteSuperellipsoidOuterTorusSmoothCircleFamily.ofRegularValue
    D.scale_pos.le S.outer.surfaceRegular D.upperSeamRegular

/-- Smooth cutting circles at the upper endpoint height. -/
def upperCutFamily (D : CanonicalEndpointRegularityData S) :
    FiniteCoordinatePlaneTorusSmoothCircleFamily Phi frame D.upperHeight :=
  FiniteCoordinatePlaneTorusSmoothCircleFamily.ofRegularValue
    Phi frame D.upperSurfaceRegular

noncomputable instance centralOuterIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.centralOuterFamily.index := by
  letI := D.centralOuterFamily.finite_index
  exact Fintype.ofFinite _

noncomputable instance centralCutIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.centralCutFamily.index := by
  letI := D.centralCutFamily.finite_index
  exact Fintype.ofFinite _

noncomputable instance lowerOuterIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.lowerOuterFamily.index := by
  letI := D.lowerOuterFamily.finite_index
  exact Fintype.ofFinite _

noncomputable instance lowerCutIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.lowerCutFamily.index := by
  letI := D.lowerCutFamily.finite_index
  exact Fintype.ofFinite _

noncomputable instance upperOuterIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.upperOuterFamily.index := by
  letI := D.upperOuterFamily.finite_index
  exact Fintype.ofFinite _

noncomputable instance upperCutIndexFintype
    (D : CanonicalEndpointRegularityData S) : Fintype D.upperCutFamily.index := by
  letI := D.upperCutFamily.finite_index
  exact Fintype.ofFinite _

/-- The selected central analytic barrier graph. -/
def centralGraph (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph Phi frame c S.outer.scale S.cut.height
      D.centralOuterFamily.index D.centralCutFamily.index :=
  FiniteSuperellipsoidBarrierGraph.ofRegularSectionsAndTransversality
    D.scale_pos.le S.outer.surfaceRegular S.cut.surfaceRegular
    S.cut.seamRegular D.centralOuterFamily.toFiniteEmbeddedTorusCircleSection
    D.centralCutFamily.toFiniteEmbeddedTorusCircleSection
    (hasSuperellipsoidSeamClosureGluing Phi frame c S.outer.scale S.cut.height
      D.scale_pos S.outer.surfaceRegular S.cut.surfaceRegular S.cut.seamRegular)

/-- The lower endpoint analytic barrier graph. -/
def lowerGraph (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph Phi frame c S.outer.scale D.lowerHeight
      D.lowerOuterFamily.index D.lowerCutFamily.index :=
  FiniteSuperellipsoidBarrierGraph.ofRegularSectionsAndTransversality
    D.scale_pos.le S.outer.surfaceRegular D.lowerSurfaceRegular
    D.lowerSeamRegular D.lowerOuterFamily.toFiniteEmbeddedTorusCircleSection
    D.lowerCutFamily.toFiniteEmbeddedTorusCircleSection
    (hasSuperellipsoidSeamClosureGluing Phi frame c S.outer.scale D.lowerHeight
      D.scale_pos S.outer.surfaceRegular D.lowerSurfaceRegular
      D.lowerSeamRegular)

/-- The upper endpoint analytic barrier graph. -/
def upperGraph (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph Phi frame c S.outer.scale D.upperHeight
      D.upperOuterFamily.index D.upperCutFamily.index :=
  FiniteSuperellipsoidBarrierGraph.ofRegularSectionsAndTransversality
    D.scale_pos.le S.outer.surfaceRegular D.upperSurfaceRegular
    D.upperSeamRegular D.upperOuterFamily.toFiniteEmbeddedTorusCircleSection
    D.upperCutFamily.toFiniteEmbeddedTorusCircleSection
    (hasSuperellipsoidSeamClosureGluing Phi frame c S.outer.scale D.upperHeight
      D.scale_pos S.outer.surfaceRegular D.upperSurfaceRegular
      D.upperSeamRegular)

@[instance_reducible]
noncomputable def centralSeamVertexFintype
    (D : CanonicalEndpointRegularityData S) :
    Fintype (SuperellipsoidSeamVertex Phi frame c S.outer.scale S.cut.height) :=
  D.centralGraph.seamVertexFintype

noncomputable instance lowerSeamVertexFintype
    (D : CanonicalEndpointRegularityData S) :
    Fintype (SuperellipsoidSeamVertex Phi frame c S.outer.scale
      (S.cut.height - D.heightData.band.ε)) := by
  simpa only [lowerHeight] using D.lowerGraph.seamVertexFintype

noncomputable instance upperSeamVertexFintype
    (D : CanonicalEndpointRegularityData S) :
    Fintype (SuperellipsoidSeamVertex Phi frame c S.outer.scale
      (S.cut.height + D.heightData.band.ε)) := by
  simpa only [upperHeight] using D.upperGraph.seamVertexFintype

/-- Canonical cyclic height order on the central outer circles. -/
theorem centralOuterOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.OuterCircleTransverseHeightCyclicOrderFamily
      D.centralGraph where
  regular := fun i ↦ D.centralOuterFamily.smoothHeight i

/-- Canonical cyclic inward order on the central cutting circles. -/
theorem centralCutOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily
      D.centralGraph := by
  let _ := D.centralSeamVertexFintype
  exact FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily.ofSmoothLifts
    (fun j ↦ (D.centralCutFamily.smoothLift j.1).toSmoothCutCircleLiftData rfl)
    D.scale_pos S.cut.seamRegular

/-- Canonical cyclic height order on the lower outer circles. -/
theorem lowerOuterOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.OuterCircleTransverseHeightCyclicOrderFamily
      D.lowerGraph where
  regular := by
    intro i
    exact D.lowerOuterFamily.smoothHeight i

/-- Canonical cyclic inward order on the lower cutting circles. -/
theorem lowerCutOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily
      D.lowerGraph :=
  FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily.ofSmoothLifts
    (fun j ↦ (D.lowerCutFamily.smoothLift j.1).toSmoothCutCircleLiftData rfl)
    D.scale_pos D.lowerSeamRegular

/-- Canonical cyclic height order on the upper outer circles. -/
theorem upperOuterOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.OuterCircleTransverseHeightCyclicOrderFamily
      D.upperGraph where
  regular := by
    intro i
    exact D.upperOuterFamily.smoothHeight i

/-- Canonical cyclic inward order on the upper cutting circles. -/
theorem upperCutOrder (D : CanonicalEndpointRegularityData S) :
    FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily
      D.upperGraph :=
  FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily.ofSmoothLifts
    (fun j ↦ (D.upperCutFamily.smoothLift j.1).toSmoothCutCircleLiftData rfl)
    D.scale_pos D.upperSeamRegular

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
