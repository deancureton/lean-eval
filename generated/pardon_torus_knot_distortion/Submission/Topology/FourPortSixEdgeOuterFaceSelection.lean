import Submission.Topology.FourPortSixEdgeRawPresentation
import Submission.Topology.FourPortSixEdgeThetaDecompositions
import Submission.Topology.RawFourPortTopologicalDiskSide

/-!
# Selecting the outer raw face of the six-edge four-port graph

The honest four-port graph has three raw cycles and one rectangular face.  The planar face theorem
selects one raw cycle whose closed disk is the union of the rectangle and the other two raw closed
disks.  This module packages that choice with the established raw index order: central is `0`,
lower child is `1`, and upper child is `2`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

namespace EmbeddedTorusIntersectionCircle

/-- The carrier of the lifted Jordan circle is the range of its circle-parametrized lift. -/
@[simp] theorem carrier_zeroWindingJordanCircle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    (C.zeroWindingJordanCircle hzero).carrier =
      Set.range (C.zeroWindingPlaneCircle hzero) := by
  change Set.range
      (C.zeroWindingPlaneCircle hzero ∘ JordanCurve.Arcs.spherePlaneHomeoCircle) = _
  rw [Set.range_comp, JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq,
    Set.image_univ]

/-- Deck translation does not change the projected image of a plane set. -/
theorem image_add_lattice
    (s : Set TorusCoveringPlane) (k : Fin 2 → ℤ) :
    torusCoveringProjectionToTorus Phi ''
        ((fun x ↦ x + torusLatticeVector k) '' s) =
      torusCoveringProjectionToTorus Phi '' s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact (torusCoveringProjectionToTorus_add_lattice x k).symm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x + torusLatticeVector k, ⟨x, hx, rfl⟩, ?_⟩
    exact torusCoveringProjectionToTorus_add_lattice x k

/-- Every zero-winding circle lies on the boundary of its projected closed Jordan disk. -/
theorem torusCircleCarrier_subset_projectedClosedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    torusCircleCarrier C ⊆ C.zeroWindingProjectedClosedJordanDisk hzero := by
  change Set.range C.torusCircle ⊆ _
  rw [← C.image_zeroWindingJordanCarrier hzero]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [zeroWindingClosedJordanDisk, (C.zeroWindingJordanCircle hzero).closure_inside]
  exact Or.inr hx

end EmbeddedTorusIntersectionCircle

namespace FourPortSixEdgePathSystem

variable (G : FourPortSixEdgePathSystem Schoenflies.Plane)

/-- The three raw planar Jordan circles in raw endpoint index order. -/
def rawPlaneJordanCircle : Fin 3 → Schoenflies.JordanCircle
  | 0 => G.centralJordanCircle
  | 1 => G.bottomJordanCircle
  | 2 => G.topJordanCircle

@[simp] theorem rawPlaneJordanCircle_zero :
    G.rawPlaneJordanCircle 0 = G.centralJordanCircle := rfl

@[simp] theorem rawPlaneJordanCircle_one :
    G.rawPlaneJordanCircle 1 = G.bottomJordanCircle := rfl

@[simp] theorem rawPlaneJordanCircle_two :
    G.rawPlaneJordanCircle 2 = G.topJordanCircle := rfl

/-- The exact output of selecting the outer raw face. -/
structure OuterRawFaceData (D : G.RectangleRotationData) where
  outerIndex : Fin 3
  childOneIndex : Fin 3
  childTwoIndex : Fin 3
  indices_exhaust : ∀ i,
    i = outerIndex ∨ i = childOneIndex ∨ i = childTwoIndex
  outerClosed_eq :
    closure (G.rawPlaneJordanCircle outerIndex).inside =
      closure (G.localRectangleJordanCircle D.rectangle).inside ∪
        closure (G.rawPlaneJordanCircle childOneIndex).inside ∪
          closure (G.rawPlaneJordanCircle childTwoIndex).inside

namespace OuterRawFaceData

variable {G : FourPortSixEdgePathSystem Schoenflies.Plane}
  {D : G.RectangleRotationData}

/-- Every raw closed disk lies in the selected outer raw disk. -/
theorem rawClosed_subset_outerClosed (F : G.OuterRawFaceData D) (i : Fin 3) :
    closure (G.rawPlaneJordanCircle i).inside ⊆
      closure (G.rawPlaneJordanCircle F.outerIndex).inside := by
  rcases F.indices_exhaust i with hi | hi | hi
  · subst i
    exact Set.Subset.rfl
  · subst i
    rw [F.outerClosed_eq]
    exact Set.subset_union_right.trans Set.subset_union_left
  · subst i
    rw [F.outerClosed_eq]
    exact Set.subset_union_right

end OuterRawFaceData

/-- The rotation data canonically selects and orders the outer raw face. -/
theorem nonempty_outerRawFaceData (D : G.RectangleRotationData) :
    Nonempty (G.OuterRawFaceData D) := by
  rcases G.rawFace_exists_outer_cycle_decomposition D with
    hbottom | htop | hcentral
  · refine ⟨{
      outerIndex := 1
      childOneIndex := 2
      childTwoIndex := 0
      indices_exhaust := ?_
      outerClosed_eq := ?_ }⟩
    · intro i
      fin_cases i
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · simpa only [rawPlaneJordanCircle_zero, rawPlaneJordanCircle_one,
        rawPlaneJordanCircle_two] using hbottom
  · refine ⟨{
      outerIndex := 2
      childOneIndex := 1
      childTwoIndex := 0
      indices_exhaust := ?_
      outerClosed_eq := ?_ }⟩
    · intro i
      fin_cases i
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · simpa only [rawPlaneJordanCircle_zero, rawPlaneJordanCircle_one,
        rawPlaneJordanCircle_two] using htop
  · refine ⟨{
      outerIndex := 0
      childOneIndex := 1
      childTwoIndex := 2
      indices_exhaust := ?_
      outerClosed_eq := ?_ }⟩
    · intro i
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · simpa only [rawPlaneJordanCircle_zero, rawPlaneJordanCircle_one,
        rawPlaneJordanCircle_two] using hcentral

/-- A canonical choice of the outer raw face for downstream constructions. -/
noncomputable def selectedOuterRawFaceData (D : G.RectangleRotationData) :
    G.OuterRawFaceData D :=
  Classical.choice (G.nonempty_outerRawFaceData D)

end FourPortSixEdgePathSystem

namespace FourPortSixEdgeZeroWindingData

variable {G : FourPortSixEdgePathSystem (transportedTorus Phi)}
  (Z : FourPortSixEdgeZeroWindingData G)

/-- The three canonical graph circles in raw index order. -/
def rawEmbeddedCircle (_Z : FourPortSixEdgeZeroWindingData G) :
    Fin 3 → EmbeddedTorusIntersectionCircle Phi
  | 0 => G.centralEmbeddedCircle
  | 1 => G.bottomEmbeddedCircle
  | 2 => G.topEmbeddedCircle

/-- Their zero-winding proofs in the same order. -/
theorem rawZeroWinding (Z : FourPortSixEdgeZeroWindingData G) (i : Fin 3) :
    (Z.rawEmbeddedCircle i).windingLoop.windingPair = (0, 0) := by
  fin_cases i
  · exact Z.central
  · exact Z.bottom
  · exact Z.top

/-- The deck translations used to make all shared outside arcs agree. -/
def rawAlignmentIndex : Fin 3 → (Fin 2 → ℤ)
  | 0 => 0
  | 1 => Z.bottomAlignmentIndex
  | 2 => Z.topAlignmentIndex

@[simp] theorem rawEmbeddedCircle_zero :
    Z.rawEmbeddedCircle 0 = G.centralEmbeddedCircle := rfl

@[simp] theorem rawEmbeddedCircle_one :
    Z.rawEmbeddedCircle 1 = G.bottomEmbeddedCircle := rfl

@[simp] theorem rawEmbeddedCircle_two :
    Z.rawEmbeddedCircle 2 = G.topEmbeddedCircle := rfl

@[simp] theorem rawAlignmentIndex_zero : Z.rawAlignmentIndex 0 = 0 := rfl

@[simp] theorem rawAlignmentIndex_one :
    Z.rawAlignmentIndex 1 = Z.bottomAlignmentIndex := rfl

@[simp] theorem rawAlignmentIndex_two :
    Z.rawAlignmentIndex 2 = Z.topAlignmentIndex := rfl

private theorem range_alignedBottomPlaneCircle :
    Set.range Z.alignedBottomPlaneCircle =
      (fun x ↦ x + EmbeddedTorusIntersectionCircle.torusLatticeVector
        Z.bottomAlignmentIndex) '' Set.range Z.bottomPlaneCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨Z.bottomPlaneCircle z, ⟨z, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

private theorem range_alignedTopPlaneCircle :
    Set.range Z.alignedTopPlaneCircle =
      (fun x ↦ x + EmbeddedTorusIntersectionCircle.torusLatticeVector
        Z.topAlignmentIndex) '' Set.range Z.topPlaneCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨Z.topPlaneCircle z, ⟨z, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

/-- Each raw circle of the coherent path system is the appropriate deck translate of the
canonical lifted graph circle. -/
theorem rawPlaneJordanCircle_carrier_eq_translate (i : Fin 3) :
    (Z.planePathSystem.rawPlaneJordanCircle i).carrier =
      (((Z.rawEmbeddedCircle i).zeroWindingJordanCircle
          (Z.rawZeroWinding i)).translate
            (EmbeddedTorusIntersectionCircle.torusLatticeVector
              (Z.rawAlignmentIndex i))).carrier := by
  fin_cases i
  · simp only [FourPortSixEdgePathSystem.rawPlaneJordanCircle, rawEmbeddedCircle,
      rawAlignmentIndex]
    apply Schoenflies.JordanCircle.carrier_eq_of_subset_carrier
    rw [FourPortSixEdgePathSystem.carrier_centralJordanCircle,
      Schoenflies.JordanCircle.carrier_translate,
      EmbeddedTorusIntersectionCircle.carrier_zeroWindingJordanCircle,
      EmbeddedTorusIntersectionCircle.torusLatticeVector_zero]
    change Set.range (fourPortCentralUpperPath Z.leftPlanePath Z.topOutsidePlanePath
        Z.rightPlanePath) ∪ Set.range Z.bottomOutsidePlanePath ⊆
      (fun x ↦ x + 0) '' Set.range Z.centralPlaneCircle
    simpa only [add_zero, Set.image_id'] using
      Z.centralPlaneCarrier_subset_centralPlaneCircle
  · simp only [FourPortSixEdgePathSystem.rawPlaneJordanCircle, rawEmbeddedCircle,
      rawAlignmentIndex]
    apply Schoenflies.JordanCircle.carrier_eq_of_subset_carrier
    rw [FourPortSixEdgePathSystem.carrier_bottomJordanCircle,
      Schoenflies.JordanCircle.carrier_translate,
      EmbeddedTorusIntersectionCircle.carrier_zeroWindingJordanCircle]
    change Set.range Z.bottomPlanePath ∪ Set.range Z.bottomOutsidePlanePath ⊆
      (fun x ↦ x + EmbeddedTorusIntersectionCircle.torusLatticeVector
        Z.bottomAlignmentIndex) '' Set.range Z.bottomPlaneCircle
    rw [← Z.range_alignedBottomPlaneCircle]
    exact Z.bottomPlaneCarrier_subset_alignedBottomPlaneCircle
  · simp only [FourPortSixEdgePathSystem.rawPlaneJordanCircle, rawEmbeddedCircle,
      rawAlignmentIndex]
    apply Schoenflies.JordanCircle.carrier_eq_of_subset_carrier
    rw [FourPortSixEdgePathSystem.carrier_topJordanCircle,
      Schoenflies.JordanCircle.carrier_translate,
      EmbeddedTorusIntersectionCircle.carrier_zeroWindingJordanCircle]
    change Set.range Z.topPlanePath ∪ Set.range Z.topOutsidePlanePath ⊆
      (fun x ↦ x + EmbeddedTorusIntersectionCircle.torusLatticeVector
        Z.topAlignmentIndex) '' Set.range Z.topPlaneCircle
    rw [← Z.range_alignedTopPlaneCircle]
    exact Z.topPlaneCarrier_subset_alignedTopPlaneCircle

/-- The selected plane closed disk projects to the canonical disk of the same graph circle. -/
theorem image_rawPlaneJordanClosedDisk (i : Fin 3) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure (Z.planePathSystem.rawPlaneJordanCircle i).inside =
      (Z.rawEmbeddedCircle i).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding i) := by
  have hinside := Schoenflies.JordanCircle.inside_eq_of_carrier_eq
    (Z.planePathSystem.rawPlaneJordanCircle i)
    (((Z.rawEmbeddedCircle i).zeroWindingJordanCircle
      (Z.rawZeroWinding i)).translate
        (EmbeddedTorusIntersectionCircle.torusLatticeVector
          (Z.rawAlignmentIndex i)))
    (Z.rawPlaneJordanCircle_carrier_eq_translate i)
  rw [hinside, Schoenflies.JordanCircle.closure_inside_translate,
    EmbeddedTorusIntersectionCircle.zeroWindingProjectedClosedJordanDisk,
    EmbeddedTorusIntersectionCircle.zeroWindingClosedJordanDisk,
    EmbeddedTorusIntersectionCircle.image_add_lattice]

namespace OuterRawFaceData

variable {D : Z.planePathSystem.RectangleRotationData}

/-- Every graph-circle carrier lies in the projected disk selected by the planar face theorem. -/
theorem rawCircleCarrier_subset_selectedDisk
    (F : Z.planePathSystem.OuterRawFaceData D) (i : Fin 3) :
    torusCircleCarrier (Z.rawEmbeddedCircle i) ⊆
      (Z.rawEmbeddedCircle F.outerIndex).zeroWindingProjectedClosedJordanDisk
        (Z.rawZeroWinding F.outerIndex) := by
  rw [← Z.image_rawPlaneJordanClosedDisk F.outerIndex]
  intro x hx
  have hxOwn :=
    EmbeddedTorusIntersectionCircle.torusCircleCarrier_subset_projectedClosedJordanDisk
      (Z.rawEmbeddedCircle i) (Z.rawZeroWinding i) hx
  rw [← Z.image_rawPlaneJordanClosedDisk i] at hxOwn
  obtain ⟨y, hy, rfl⟩ := hxOwn
  exact ⟨y, F.rawClosed_subset_outerClosed i hy, rfl⟩

end OuterRawFaceData
end FourPortSixEdgeZeroWindingData

namespace FourPortRawSixEdgePresentation

variable (P : FourPortRawSixEdgePresentation R)

/-- The three canonical graph circles in raw endpoint index order. -/
def rawEmbeddedCircle : Fin 3 → EmbeddedTorusIntersectionCircle Phi
  | 0 => P.graph.centralEmbeddedCircle
  | 1 => P.graph.bottomEmbeddedCircle
  | 2 => P.graph.topEmbeddedCircle

@[simp] theorem rawEmbeddedCircle_zero :
    P.rawEmbeddedCircle 0 = P.graph.centralEmbeddedCircle := rfl

@[simp] theorem rawEmbeddedCircle_one :
    P.rawEmbeddedCircle 1 = P.graph.bottomEmbeddedCircle := rfl

@[simp] theorem rawEmbeddedCircle_two :
    P.rawEmbeddedCircle 2 = P.graph.topEmbeddedCircle := rfl

/-- The graph and raw endpoint circles have the same carriers at every raw index. -/
theorem rawEmbeddedCircle_carrier_eq (i : Fin 3) :
    torusCircleCarrier (P.rawEmbeddedCircle i) = torusCircleCarrier (R.circle i) := by
  fin_cases i
  · exact P.centralCarrier_eq
  · exact P.bottomCarrier_eq
  · exact P.topCarrier_eq

end FourPortRawSixEdgePresentation

end Submission.Topology
