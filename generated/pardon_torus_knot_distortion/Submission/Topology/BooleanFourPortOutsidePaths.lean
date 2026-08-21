import Submission.Topology.BooleanFourPortLocalIncidence
import Submission.Topology.FiniteAlternatingAmbientTorusCircleSection

/-!
# Fixed outside paths for Boolean four-port resolutions

The paths outside the pairwise-disjoint four-port supports do not depend on the resolution
choice.  This package combines one such fixed matching with the explicit local Boolean paths and
derives the complete alternating incidence data and exact transported-torus circle section.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy} {n : ℕ}

/-- Choice-independent outside arcs and their exact intersections with every local resolution. -/
structure BooleanFourPortOutsidePathData
    (Phi : AmbientIsotopy) (F : FinitePairedSeamBandCharts n) where
  outside : FiniteEndpointPairing (FourPortVertex n)
  paths : FiniteAlternatingEndpointSystem.EndpointPathFamily
    outside (fourPortChartPoint F.band)
  chart_mem_torus : ∀ b z, (F.band b).chart z ∈ transportedTorus Phi
  paths_mem_torus : ∀ e, Set.range (paths.path e) ⊆ transportedTorus Phi
  paths_injective : ∀ e, Function.Injective (paths.path e)
  paths_pairwise : Pairwise fun e f ↦
    Disjoint (Set.range (paths.path e)) (Set.range (paths.path f))
  cross_intersection : ∀ choice e f,
    Set.range (paths.path e) ∩
        Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path f) =
      fourPortChartPoint F.band ''
        (outside.endpointSet e ∩ (fourPortLocalPairing choice).endpointSet f)

namespace BooleanFourPortOutsidePathData

variable {F : FinitePairedSeamBandCharts n}

/-- The fixed outside matching and one chosen local matching. -/
abbrev system (D : BooleanFourPortOutsidePathData Phi F)
    (choice : Fin n → Bool) : FiniteAlternatingEndpointSystem (FourPortVertex n) :=
  booleanFourPortEndpointSystem D.outside choice

/-- Exact closed-arc incidence for every Boolean four-port resolution. -/
theorem incidence (D : BooleanFourPortOutsidePathData Phi F)
    (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem.ClosedArcIncidenceData
      (D.system choice) (fourPortChartPoint F.band) D.paths
        (booleanFourPortLocalEndpointPaths F.band choice) where
  point_injective := F.fourPortChartPoint_injective
  first_injective := D.paths_injective
  second_injective := F.booleanFourPortLocalEndpointPaths_injective choice
  first_pairwise := D.paths_pairwise
  second_pairwise := F.booleanFourPortLocalEndpointPaths_pairwise choice
  cross_intersection := D.cross_intersection choice

/-- Every selected local constituent lies on the transported torus. -/
theorem localPaths_mem_torus (D : BooleanFourPortOutsidePathData Phi F)
    (choice : Fin n → Bool) (e : FourPortLocalEdge n) :
    Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) ⊆
      transportedTorus Phi :=
  F.booleanFourPortLocalEndpointPaths_range_subset_transportedTorus
    D.chart_mem_torus choice e

/-- The exact ambient carrier of all quotient cycles for one Boolean choice. -/
noncomputable def ambientSection (D : BooleanFourPortOutsidePathData Phi F)
    (choice : Fin n → Bool) : Set R3 :=
  (D.incidence choice).ambientCycleCarrierOfAmbient D.paths_mem_torus
    (D.localPaths_mem_torus choice)

/-- The canonical exact finite torus-circle section for one Boolean choice. -/
noncomputable def circleSection (D : BooleanFourPortOutsidePathData Phi F)
    (choice : Fin n → Bool) :
    FiniteEmbeddedTorusCircleSection Phi (D.ambientSection choice)
      (D.system choice).CycleIndex :=
  (D.incidence choice).finiteEmbeddedTorusCircleSectionOfAmbient D.paths_mem_torus
    (D.localPaths_mem_torus choice)

/-- The resolved carrier is exactly the fixed outside arcs plus the selected local arcs. -/
theorem ambientSection_eq_iUnion_ranges
    (D : BooleanFourPortOutsidePathData Phi F) (choice : Fin n → Bool) :
    D.ambientSection choice =
      (⋃ e : D.outside.edge, Set.range (D.paths.path e)) ∪
        ⋃ e : FourPortLocalEdge n,
          Set.range ((booleanFourPortLocalEndpointPaths F.band choice).path e) :=
  (D.incidence choice).ambientCycleCarrierOfAmbient_eq_iUnion_ranges
    D.paths_mem_torus (D.localPaths_mem_torus choice)

end BooleanFourPortOutsidePathData
end Submission.Topology
