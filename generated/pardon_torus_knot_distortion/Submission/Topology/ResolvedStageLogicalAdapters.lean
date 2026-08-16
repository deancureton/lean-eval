import Submission.Topology.FiniteSequentialTorusPushout
import Submission.Topology.SuperellipsoidBarrierGraph

/-!
# Logical adapters for resolved regular sphere stages

This module connects two already proved pieces of the regular-stage argument.  First, the
essential-circle surgery data recorded by a resolved barrier is repackaged in the interface used
by the surgery dichotomy.  Second, separated canonical Schoenflies supports give the connected
pushout required for a maximal family of inessential torus disks.

No moving-sphere or cell geometry is assumed or constructed here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-! ## Essential resolved circles -/

namespace EssentialResolvedBarrierCircleSurgeryData

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι} {i : ι}

/-- The resolved-barrier surgery record has exactly the data required by the generic regular-stage
essential-circle interface. -/
def toEssentialSphereCircleSurgeryData
    (D : EssentialResolvedBarrierCircleSurgeryData S i) :
    EssentialSphereCircleSurgeryData S i where
  system := D.system
  innermost := D.innermost
  boundary_eq := D.boundary_eq
  surgery := D.surgery

end EssentialResolvedBarrierCircleSurgeryData

namespace FiniteBarrierTwoSurgeryResolution

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge resolvedIndex : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  [Fintype resolvedIndex] [DecidableEq resolvedIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}

/-- Essential surgery inputs attached to a resolved barrier supply the generic essential branch
at its regular stage. -/
theorem essentialSurgery_of_inputs
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex)
    (hinputs : Q.HasEssentialSurgeryInputs) :
    ∀ i, (Q.stage.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData Q.stage i) := by
  intro i hi
  obtain ⟨D⟩ := hinputs i hi
  exact ⟨D.toEssentialSphereCircleSurgeryData⟩

end FiniteBarrierTwoSurgeryResolution

/-! ## The canonical finite pushout for maximal inessential disks -/

namespace FiniteSphereSurgeryIntersectionSystem

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]

/-- The torus disk used by a regular stage is the canonical projected Schoenflies disk used by
the finite sequential pushout. -/
theorem range_torusDiskMap_eq_zeroWindingProjectedClosedJordanDisk
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    Set.range (S.torusDiskMap hzero i) =
      (S.circle i).zeroWindingProjectedClosedJordanDisk (hzero i) := by
  rw [(S.circle i).zeroWindingProjectedClosedJordanDisk_eq_range (hzero i)]
  rfl

end FiniteSphereSurgeryIntersectionSystem

namespace MaximalInessentialTorusDiskFamily

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}

/-- The canonical centers of the selected maximal circles are exactly the centers named by the
maximal-disk family. -/
theorem finiteZeroWindingDiskCenters_eq_centers
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskCenters
        (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1) =
      M.centers := by
  funext i
  apply (transportedTorusHomeomorph Phi).injective
  rw [EmbeddedTorusIntersectionCircle.transported_zeroWindingDiskCenterCoordinates,
    (transportedTorusHomeomorph Phi).apply_symm_apply]

/-- Removing the canonical disks of the selected maximal circles gives precisely the complement
of the maximal disk union. -/
theorem finiteZeroWindingDiskComplement_eq_diskComplement
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskComplement
        (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1) =
      M.diskComplement := by
  ext x
  change (∀ i : M.maximal,
      x ∉ (S.circle i.1).zeroWindingProjectedClosedJordanDisk (hzero i.1)) ↔
    x ∉ M.diskUnion
  constructor
  · intro hx hxUnion
    simp only [diskUnion, Set.mem_iUnion] at hxUnion
    obtain ⟨i, hi, hxi⟩ := hxUnion
    rw [S.range_torusDiskMap_eq_zeroWindingProjectedClosedJordanDisk hzero i] at hxi
    exact hx ⟨i, hi⟩ hxi
  · intro hx i hxi
    apply hx
    simp only [diskUnion, Set.mem_iUnion]
    refine ⟨i.1, i.2, ?_⟩
    rw [S.range_torusDiskMap_eq_zeroWindingProjectedClosedJordanDisk hzero i.1]
    exact hxi

/-- Pairwise-separated canonical supports supply the connected finite pushout for a maximal
inessential disk family.  The target and center identifications are derived above rather than
being assumed as additional compatibility data. -/
def connectedPushoutData_of_separatedSupports
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (D : EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports
      (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1)) :
    M.ConnectedPushoutData := by
  let P := D.toFinitePuncturePushoutData
  have hsurjective :
      ∀ y : EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskComplement
          (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1),
        ∃ x, P.push x = y.1 := by
    intro y
    exact (D.mem_finiteZeroWindingDiskComplement_iff_exists_preimage y.1).mp y.2
  rw [M.finiteZeroWindingDiskCenters_eq_centers,
    M.finiteZeroWindingDiskComplement_eq_diskComplement] at P hsurjective
  exact ⟨P, hsurjective⟩

end MaximalInessentialTorusDiskFamily

namespace FiniteSphereSurgeryIntersectionSystem

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A maximal-family construction with separated canonical supports supplies exactly the
all-inessential input expected by downstream regular-stage arguments. -/
theorem inessentialData_of_maximalSeparatedSupports
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hdata : ∀ hzero : S.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily S hzero,
        Nonempty (EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports
          (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1))) :
    ∀ hzero : S.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily S hzero,
        Nonempty M.ConnectedPushoutData := by
  intro hzero
  obtain ⟨M, ⟨D⟩⟩ := hdata hzero
  exact ⟨M, ⟨M.connectedPushoutData_of_separatedSupports D⟩⟩

end FiniteSphereSurgeryIntersectionSystem

end Submission.Topology
