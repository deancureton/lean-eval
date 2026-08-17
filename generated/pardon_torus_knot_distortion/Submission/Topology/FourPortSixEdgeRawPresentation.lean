import Submission.Topology.FourPortSixEdgePlanePaths
import Submission.Topology.FourPortEndpointCollarPush
import Submission.Topology.InessentialSliceCircle

/-!
# Attaching the honest six-edge graph to raw four-port circles

The raw parity package stores three embedded endpoint circles but not their decomposition into
the six global edges of the four-port graph.  This file isolates that missing decomposition as
exact carrier equalities.  Equality of parametrizations is neither required nor appropriate.

The carrier equalities transfer zero winding from the raw circles to the canonical circle
parametrizations of the graph.  The coherent lifted planar six-edge system is then unconditional.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

namespace EmbeddedTorusIntersectionCircle

/-- Zero winding depends only on the carrier of an embedded transported-torus circle. -/
theorem windingPair_eq_zero_of_torusCircleCarrier_eq
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hcarrier : torusCircleCarrier C = torusCircleCarrier D)
    (hzero : D.windingLoop.windingPair = (0, 0)) :
    C.windingLoop.windingPair = (0, 0) := by
  apply D.windingPair_eq_zero_of_range_subset_of_windingPair_eq_zero
    C.windingLoop _ hzero
  rintro _ ⟨t, rfl⟩
  have hmem : C.torusCircle (Circle.exp t) ∈ torusCircleCarrier C :=
    ⟨Circle.exp t, rfl⟩
  rw [hcarrier] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  calc
    D.circle z = C.circle (Circle.exp t) := congrArg Subtype.val hz
    _ = C.windingLoop.curve t := C.parametrization t

end EmbeddedTorusIntersectionCircle

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}

/-- Carrier-level identification of one raw move with the honest six-edge graph.

Indices `0`, `1`, and `2` retain their established meanings: the central circle and the lower
and upper child circles.  The split/merge direction only decides which endpoint owns them. -/
structure FourPortRawSixEdgePresentation (R : FourPortRawCircleData raw) where
  graph : FourPortSixEdgePathSystem (transportedTorus Phi)
  centralCarrier_eq :
    torusCircleCarrier graph.centralEmbeddedCircle =
      torusCircleCarrier (R.circle 0)
  bottomCarrier_eq :
    torusCircleCarrier graph.bottomEmbeddedCircle =
      torusCircleCarrier (R.circle 1)
  topCarrier_eq :
    torusCircleCarrier graph.topEmbeddedCircle =
      torusCircleCarrier (R.circle 2)

/-- A raw six-edge presentation aligned with the four local paths of the band chart.

These two carrier equalities are the exact path-level attachment still absent from the raw
endpoint API.  They identify the vertical and horizontal local resolutions without choosing a
parametrization of either outside arc. -/
structure FourPortRawSixEdgeBandPresentation (R : FourPortRawCircleData raw) extends
    FourPortRawSixEdgePresentation R where
  parallelCarrier_eq :
    Set.range graph.left ∪ Set.range graph.right = fourPortParallelPart B
  surgeryCarrier_eq :
    Set.range graph.bottom ∪ Set.range graph.top = fourPortSurgeryPart B

namespace FourPortRawSixEdgePresentation

variable {R : FourPortRawCircleData raw}
  (P : FourPortRawSixEdgePresentation R)

theorem central_zeroWinding :
    P.graph.centralEmbeddedCircle.windingLoop.windingPair = (0, 0) :=
  EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_eq
    P.graph.centralEmbeddedCircle (R.circle 0) P.centralCarrier_eq (R.zeroWinding 0)

theorem bottom_zeroWinding :
    P.graph.bottomEmbeddedCircle.windingLoop.windingPair = (0, 0) :=
  EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_eq
    P.graph.bottomEmbeddedCircle (R.circle 1) P.bottomCarrier_eq (R.zeroWinding 1)

theorem top_zeroWinding :
    P.graph.topEmbeddedCircle.windingLoop.windingPair = (0, 0) :=
  EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_torusCircleCarrier_eq
    P.graph.topEmbeddedCircle (R.circle 2) P.topCarrier_eq (R.zeroWinding 2)

/-- The raw carrier presentation canonically supplies coherent zero-winding circle lifts. -/
theorem zeroWindingData : FourPortSixEdgeZeroWindingData P.graph where
  central := P.central_zeroWinding
  bottom := P.bottom_zeroWinding
  top := P.top_zeroWinding

/-- The raw move therefore has a canonical coherent planar six-edge graph. -/
def planePathSystem : FourPortSixEdgePathSystem TorusCoveringPlane :=
  P.zeroWindingData.planePathSystem

end FourPortRawSixEdgePresentation

namespace FourPortRawSixEdgeBandPresentation

variable {R : FourPortRawCircleData raw}
  (P : FourPortRawSixEdgeBandPresentation R)

/-- Forget the local band alignment while retaining the coherent six-edge lift. -/
def planePathSystem : FourPortSixEdgePathSystem TorusCoveringPlane :=
  P.toFourPortRawSixEdgePresentation.planePathSystem

end FourPortRawSixEdgeBandPresentation
end Submission.Topology
