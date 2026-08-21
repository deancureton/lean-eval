import Submission.Topology.BooleanFourPortOutsidePaths
import Submission.Topology.FiniteAlternatingArcCycleCut

/-!
# Cutting a Boolean four-port component at one local edge

Swapping the two colours makes a selected local four-port edge the first edge of its alternating
component.  The specified-edge cut then returns the complete outside route complementary to that
local edge, with embedded-circle data derived from the existing exact incidence package.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ} {F : FinitePairedSeamBandCharts n}

namespace BooleanFourPortOutsidePathData

variable (D : BooleanFourPortOutsidePathData Phi F)

/-- Orient the local matching first and the fixed outside matching second. -/
abbrev localFirstSystem (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem (FourPortVertex n) :=
  (D.system choice).swap

/-- The local paths and fixed outside paths retain exact incidence after exchanging colours. -/
theorem localFirstIncidence (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData
      (D.localFirstSystem choice) (fourPortChartPoint F.band)
        (booleanFourPortLocalEndpointPaths F.band choice) D.paths :=
  (D.incidence choice).swap

/-- The zero endpoint of one selected local edge. -/
def localEdgeStart (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    FourPortVertex n :=
  (fourPortLocalPairing choice).endpointEquiv (e, 0)

/-- The full outside route complementary to one selected local edge. -/
def localEdgeComplementPath (choice : Fin n → Bool) (e : FourPortLocalEdge n) :=
  (FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (A := D.localFirstSystem choice)
      (booleanFourPortLocalEndpointPaths F.band choice) D.paths).complementPathAt
    (localEdgeStart choice e)

/-- The canonically oriented selected local edge. -/
def localEdgePath (choice : Fin n → Bool) (e : FourPortLocalEdge n) :=
  (FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.orientedFamily
      (A := D.localFirstSystem choice)
      (booleanFourPortLocalEndpointPaths F.band choice) D.paths).firstPathAt
    (localEdgeStart choice e)

@[simp] theorem localEdgePath_apply
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) (t : unitInterval) :
    D.localEdgePath choice e t =
      (booleanFourPortLocalEndpointPaths F.band choice).path e t := by
  change (booleanFourPortLocalEndpointPaths F.band choice).orientedPath
      ((fourPortLocalPairing choice).endpointEquiv (e, 0)) t = _
  exact
    FiniteAlternatingEndpointSystem.EndpointPathFamily.orientedPath_endpointEquiv_zero_apply
      (booleanFourPortLocalEndpointPaths F.band choice) e t

theorem range_localEdgePath
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgePath choice e) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) := by
  exact congrArg Set.range (funext (D.localEdgePath_apply choice e))

/-- One local edge glued to its entire outside complement. -/
def localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) : Circle → R3 :=
  TwoArcCircle.circleMap (D.localEdgePath choice e) (D.localEdgeComplementPath choice e)

/-- Exact constituent incidence makes the cut local-edge circle embedded. -/
theorem localEdgeTwoArcData (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    TwoArcCircle.Data (D.localEdgePath choice e) (D.localEdgeComplementPath choice e) := by
  exact (D.localFirstIncidence choice).twoArcDataAt (localEdgeStart choice e)

theorem continuous_localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Continuous (D.localEdgeCircle choice e) :=
  TwoArcCircle.continuous_circleMap _ _

theorem localEdgeCircle_injective (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Function.Injective (D.localEdgeCircle choice e) :=
  (D.localEdgeTwoArcData choice e).injective

/-- The cut circle has exactly the selected local edge and its complementary outside route. -/
theorem range_localEdgeCircle (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) =
      Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) ∪
        Set.range (D.localEdgeComplementPath choice e) := by
  rw [localEdgeCircle, TwoArcCircle.range_circleMap, D.range_localEdgePath]

/-- A specified-edge circle is contained in its quotient-cycle edge carrier. -/
theorem range_localEdgeCircle_subset_cycleEdgeCarrier
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range (D.localEdgeCircle choice e) ⊆
      FiniteAlternatingEndpointSystem.ClosedArcIncidenceData.cycleEdgeCarrier
        (D.localFirstSystem choice) (fourPortChartPoint F.band)
        (booleanFourPortLocalEndpointPaths F.band choice) D.paths
        ((D.localFirstSystem choice).cycleOfVertex (localEdgeStart choice e)) := by
  rw [D.range_localEdgeCircle choice e, ← D.range_localEdgePath choice e]
  exact (D.localFirstIncidence choice)
    |>.range_firstPathAt_union_complementPathAt_subset_cycleEdgeCarrier
      (localEdgeStart choice e)

end BooleanFourPortOutsidePathData
end Submission.Topology
