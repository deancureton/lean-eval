import Submission.Topology.FinitePlanarJordanDiskPushout
import Submission.Topology.SphereCirclePlanarNesting

/-!
# Connectivity of the canonical planar sphere-circle core

The inclusion-maximal inner circle disks are pairwise disjoint and lie strictly inside the
selected outer Jordan circle.  The finite planar pushout therefore proves that the canonical
open core between them is connected.  An explicit subtype homeomorphism transfers this result
to the canonical core of the closed punctured remainder.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {S : EmbeddedTopologicalSphereInR3}
  {ι : Type*} [Fintype ι] {circle : ι → EmbeddedTorusIntersectionCircle Phi}

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable (D : FiniteEmbeddedSphereCircleCommonPoleData S circle)
  (hpairwise : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle))
  (outer : ι)

/-- The subtype of circle indices representing the selected maximal inner disks. -/
def maximalInnerDiskIndex :=
  {i // i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer}

noncomputable instance : Fintype (D.maximalInnerDiskIndex outer) :=
  Finset.fintypeCoeSort (D.inclusionMaximalInnerClosedPlaneDiskIndices outer)

/-- The planar Jordan circle indexed by a selected maximal inner disk. -/
def maximalInnerJordanCircle (i : D.maximalInnerDiskIndex outer) :
    Schoenflies.JordanCircle :=
  (D.circleData i.1).planeJordanCircle

/-- The canonical maximal inner disks have separated radial supports inside the outer disk. -/
def maximalInnerSeparatedSupports :
    Schoenflies.JordanCircle.SeparatedPlanarJordanDiskSupports
      (D.circleData outer).planeJordanCircle (D.maximalInnerJordanCircle outer) := by
  classical
  apply Classical.choice
  apply Schoenflies.JordanCircle.exists_separatedPlanarJordanDiskSupports
  · intro i
    exact D.inclusionMaximalInnerClosedPlaneDisk_inside outer i.2
  · intro i j hij
    apply D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint hpairwise outer
      i.2 j.2
    intro hijVal
    exact hij (Subtype.ext hijVal)

/-- The generic finite-pushout core is exactly the canonical maximal-inner-disk core. -/
theorem maximalInnerSeparatedSupports_outerDiskCore_eq :
    (D.maximalInnerSeparatedSupports hpairwise outer).outerDiskCore =
      D.outerDiskOpenCore outer := by
  apply Set.ext
  intro x
  simp only [Schoenflies.JordanCircle.SeparatedPlanarJordanDiskSupports.outerDiskCore,
    Schoenflies.JordanCircle.SeparatedPlanarJordanDiskSupports.closedInnerDiskUnion,
    outerDiskOpenCore, maximalInnerClosedUnion, mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨hxOuter, hxInner⟩
    refine ⟨hxOuter, ?_⟩
    rintro ⟨i, hi, hxi⟩
    apply hxInner
    exact ⟨⟨i, hi⟩, hxi⟩
  · rintro ⟨hxOuter, hxInner⟩
    refine ⟨hxOuter, ?_⟩
    rintro ⟨i, hxi⟩
    exact hxInner ⟨i.1, i.2, hxi⟩

include hpairwise in
/-- The canonical open core between the outer disk and all maximal inner disks is connected. -/
theorem isConnected_outerDiskOpenCore : IsConnected (D.outerDiskOpenCore outer) := by
  rw [← D.maximalInnerSeparatedSupports_outerDiskCore_eq hpairwise outer]
  exact (D.maximalInnerSeparatedSupports hpairwise outer).isConnected_outerDiskCore

/-- The open core and its copy inside the closed punctured remainder are homeomorphic. -/
def outerDiskOpenCoreHomeomorphRemainderCore :
    D.outerDiskOpenCore outer ≃ₜ D.outerDiskRemainderCore outer where
  toFun x :=
    ⟨⟨x, D.outerDiskOpenCore_subset_outerDiskRemainder outer x.2⟩, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

include hpairwise in
/-- The canonical core of the closed punctured remainder is connected. -/
theorem isConnected_outerDiskRemainderCore :
    IsConnected (D.outerDiskRemainderCore outer) := by
  let _ : ConnectedSpace (D.outerDiskOpenCore outer) :=
    isConnected_iff_connectedSpace.mp (D.isConnected_outerDiskOpenCore hpairwise outer)
  have _ : ConnectedSpace (D.outerDiskRemainderCore outer) :=
    (D.outerDiskOpenCoreHomeomorphRemainderCore outer).connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
