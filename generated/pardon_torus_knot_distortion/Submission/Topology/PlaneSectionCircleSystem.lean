import Submission.Topology.CoordinatePlaneDisk

/-!
# From a regular plane section to the finite disk-circle surgery interface

This module separates the differential-topology task of decomposing a regular torus section into
embedded circles from the elementary task of placing that compact section in an explicit planar
disk.  Once the circle decomposition and its finite nesting order are supplied, the conversion to
`FinitePlaneDiskTorusCircleSystem` is unconditional.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- Exact finite embedded-circle data for one coordinate-plane section of the transported torus.
The `inside` relation and its depth function are the finite Jordan nesting data later consumed by
the innermost-circle argument. -/
structure FinitePlaneTorusCircleDecomposition
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ)
    (ι : Type*) [DecidableEq ι] where
  circles : Finset ι
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  circle_mem_section : ∀ i ∈ circles, Set.range (circle i).circle ⊆
    coordinateCuttingPlane frame d ∩ transportedTorus Phi
  pairwise_disjoint : ∀ {i}, i ∈ circles → ∀ {j}, j ∈ circles → i ≠ j →
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  section_exact : coordinateCuttingPlane frame d ∩ transportedTorus Phi =
    ⋃ i ∈ circles, Set.range (circle i).circle
  has_essential : ∃ i ∈ circles, (circle i).Essential
  inside : ι → ι → Prop
  depth : ι → ℕ
  inside_depth_lt : ∀ {i j}, i ∈ circles → j ∈ circles →
    inside i j → depth i < depth j

namespace FinitePlaneTorusCircleDecomposition

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {ι : Type*} [DecidableEq ι]

/-- Convert a plane-section decomposition to the disk-based surgery interface after choosing any
positive round disk that contains the whole torus section. -/
def toFinitePlaneDiskTorusCircleSystem
    (S : FinitePlaneTorusCircleDecomposition Phi frame d ι)
    (scale : ℝ) (hscale : 0 < scale)
    (hcontain : transportedTorus Phi ∩ coordinateCuttingPlane frame d ⊆
      Set.range (coordinatePlaneDiskPoint frame d 0 scale)) :
    FinitePlaneDiskTorusCircleSystem Phi ι where
  plane := coordinateCuttingPlane frame d
  planeDisk := coordinatePlaneEmbeddedDisk frame d 0 scale hscale.ne'
  disk_mem_plane := coordinatePlaneEmbeddedDisk_range_subset_plane
    frame d 0 scale hscale.ne'
  circles := S.circles
  circle := S.circle
  circle_mem_disk := by
    intro i hi x hx
    exact hcontain ⟨(S.circle_mem_section i hi hx).2, (S.circle_mem_section i hi hx).1⟩
  pairwise_disjoint := S.pairwise_disjoint
  intersection_exact := by
    rw [← S.section_exact]
    ext x
    constructor
    · rintro ⟨hdisk, htorus⟩
      exact ⟨coordinatePlaneEmbeddedDisk_range_subset_plane
        frame d 0 scale hscale.ne' hdisk, htorus⟩
    · rintro ⟨hplane, htorus⟩
      exact ⟨hcontain ⟨htorus, hplane⟩, htorus⟩
  has_essential := S.has_essential
  inside := S.inside
  depth := S.depth
  inside_depth_lt := S.inside_depth_lt

/-- Every exact plane-section decomposition can be placed in some explicit round disk. -/
theorem exists_finitePlaneDiskTorusCircleSystem
    (S : FinitePlaneTorusCircleDecomposition Phi frame d ι) :
    Nonempty (FinitePlaneDiskTorusCircleSystem Phi ι) := by
  obtain ⟨scale, hscale, hcontain⟩ :=
    exists_coordinatePlaneDisk_containing_transportedTorus_section Phi frame d
  exact ⟨S.toFinitePlaneDiskTorusCircleSystem scale hscale hcontain⟩

end FinitePlaneTorusCircleDecomposition

end Submission.Topology
