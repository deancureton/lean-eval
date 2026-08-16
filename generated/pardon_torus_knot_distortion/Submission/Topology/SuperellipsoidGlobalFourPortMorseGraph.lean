import Submission.Topology.FourPortMorseGraphPatch
import Submission.Topology.SuperellipsoidGlobalBandTubularChart

/-!
# Four-port Morse graphs in the global superellipsoid band charts

The universal-cover construction supplies a parameter-preserving torus strip
around every paired seam excursion.  This module uses that strip as the base
of the explicit transported-torus normal tube and inserts the quadratic
four-port Morse graph there.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace CutCircleTransverseCyclicOrderFamily

variable {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

/-- The global torus-strip point underlying one quadratic patch parameter. -/
def globalBandFourPortBase
    (T : GlobalBandTubularChartData F b) (u : FourPortQuadraticDisk) :
    Circle × Circle :=
  (transportedTorusHomeomorph Phi).symm
    ((T.strip u.1 : T.surfacePatch) : transportedTorus Phi)

theorem globalBandFourPortBase_continuous
    (T : GlobalBandTubularChartData F b) :
    Continuous (globalBandFourPortBase T) := by
  exact (transportedTorusHomeomorph Phi).symm.continuous.comp <|
    continuous_subtype_val.comp
      (T.strip.continuous.comp continuous_subtype_val)

theorem globalBandFourPortBase_injective
    (T : GlobalBandTubularChartData F b) :
    Function.Injective (globalBandFourPortBase T) := by
  intro u v huv
  have htorus :
      ((T.strip u.1 : T.surfacePatch) : transportedTorus Phi) =
        ((T.strip v.1 : T.surfacePatch) : transportedTorus Phi) :=
    (transportedTorusHomeomorph Phi).symm.injective huv
  have hpatch : T.strip u.1 = T.strip v.1 :=
    Subtype.ext htorus
  apply Subtype.ext
  exact T.strip.injective hpatch

/-- Normal-tube coordinates of the global four-port graph. -/
def globalBandFourPortTubeCoordinates
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) : StandardTorusNormalTube :=
  (globalBandFourPortBase T u, fourPortNormalCoordinate t u)

theorem globalBandFourPortTubeCoordinates_continuous
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime) :
    Continuous (globalBandFourPortTubeCoordinates T t) := by
  apply (globalBandFourPortBase_continuous T).prodMk
  apply Continuous.subtype_mk
  exact (continuous_const.mul <|
    (continuous_fourPortMorseHeight t).comp continuous_subtype_val)

theorem globalBandFourPortTubeCoordinates_injective
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime) :
    Function.Injective (globalBandFourPortTubeCoordinates T t) := by
  intro u v huv
  apply globalBandFourPortBase_injective T
  exact congrArg Prod.fst huv

/-- The ambient Morse graph in the actual global excursion band. -/
def globalBandFourPortMorseGraph
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) : R3 :=
  transportedTorusNormalTubeMap Phi (globalBandFourPortTubeCoordinates T t u)

theorem globalBandFourPortMorseGraph_isEmbedding
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime) :
    IsEmbedding (globalBandFourPortMorseGraph T t) := by
  apply (transportedTorusNormalTubeMap_isEmbedding Phi).comp
  exact (globalBandFourPortTubeCoordinates_continuous T t).isClosedEmbedding
    (globalBandFourPortTubeCoordinates_injective T t) |>.isEmbedding

/-- The graph meets the transported torus precisely on the quadratic zero carrier. -/
theorem globalBandFourPortMorseGraph_mem_transportedTorus_iff
    (T : GlobalBandTubularChartData F b) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) :
    globalBandFourPortMorseGraph T t u ∈ transportedTorus Phi ↔
      fourPortMorseHeight t u.1 = 0 := by
  rw [globalBandFourPortMorseGraph,
    transportedTorusNormalTubeMap_mem_transportedTorus_iff]
  rw [Subtype.ext_iff]
  change ((1 / 4 : ℝ) * fourPortMorseHeight t u.1 : ℝ) = 0 ↔ _
  norm_num

/-- The initial global graph has exactly the vertical four-port carrier. -/
theorem globalBandFourPortMorseGraph_zero_mem_transportedTorus_iff
    (T : GlobalBandTubularChartData F b) (u : FourPortQuadraticDisk) :
    globalBandFourPortMorseGraph T ⟨0, by norm_num⟩ u ∈ transportedTorus Phi ↔
      u.1 ∈ fourPortVerticalCarrier := by
  rw [globalBandFourPortMorseGraph_mem_transportedTorus_iff,
    fourPortMorseHeight_zero]
  constructor
  · intro h
    exact (mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u.1).mp
      ⟨u.property, h⟩
  · intro h
    exact ((mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u.1).mpr h).2

/-- The final global graph has exactly the horizontal four-port carrier. -/
theorem globalBandFourPortMorseGraph_one_mem_transportedTorus_iff
    (T : GlobalBandTubularChartData F b) (u : FourPortQuadraticDisk) :
    globalBandFourPortMorseGraph T ⟨1, by norm_num⟩ u ∈ transportedTorus Phi ↔
      u.1 ∈ fourPortHorizontalCarrier := by
  rw [globalBandFourPortMorseGraph_mem_transportedTorus_iff,
    fourPortMorseHeight_one]
  constructor
  · intro h
    exact (mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u.1).mp
      ⟨u.property, h⟩
  · intro h
    exact ((mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u.1).mpr h).2

end CutCircleTransverseCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
