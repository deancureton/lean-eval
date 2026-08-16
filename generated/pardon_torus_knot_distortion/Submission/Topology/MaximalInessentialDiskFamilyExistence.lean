import Mathlib.Order.Preorder.Finite
import Submission.Topology.MaximalDiskSeparatedSupports

/-!
# Existence of maximal inessential torus disk families

Disjoint zero-winding torus circles bound a laminar family of canonical disks.  To see this in
the covering plane, compare one lifted Jordan disk with the deck translate of the other that
meets it.  Their carriers are disjoint, so the planar Jordan trichotomy says that the closed
disks are disjoint or nested.  Projection preserves both nesting alternatives.

The resulting finite laminar family has inclusion-maximal members.  We select maximal disk
images first and then one index representing each image; this also handles repeated disk
parametrizations without introducing an order on the original finite index type.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*}

namespace EmbeddedTorusIntersectionCircle

/-- Equal points under the torus covering projection differ by an integral deck vector. -/
theorem exists_latticeVector_of_torusCoveringProjection_eq
    {x y : TorusCoveringPlane}
    (hxy : torusCoveringProjection Phi x = torusCoveringProjection Phi y) :
    ∃ k : Fin 2 → ℤ, x = y + torusLatticeVector k := by
  have hpair : (Circle.exp (x 0), Circle.exp (x 1)) =
      (Circle.exp (y 0), Circle.exp (y 1)) := by
    apply transportedTorusMap_injective Phi
    exact hxy
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hpair)
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hpair)
  let k : Fin 2 → ℤ := ![m, n]
  refine ⟨k, ?_⟩
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · simpa [k, torusLatticeVector] using hm
  · simpa [k, torusLatticeVector] using hn

/-- The transported-torus-valued covering projection is invariant under deck translation. -/
theorem torusCoveringProjectionToTorus_add_lattice
    (x : TorusCoveringPlane) (k : Fin 2 → ℤ) :
    torusCoveringProjectionToTorus Phi (x + torusLatticeVector k) =
      torusCoveringProjectionToTorus Phi x := by
  apply Subtype.ext
  exact torusCoveringProjection_add_lattice Phi x k

/-- Projecting a point of the lifted Jordan carrier lands on the original torus circle. -/
theorem torusCoveringProjection_mem_circle_range_of_mem_zeroWindingJordanCarrier
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0))
    {x : TorusCoveringPlane} (hx : x ∈ (C.zeroWindingJordanCircle hzero).carrier) :
    torusCoveringProjection Phi x ∈ Set.range C.circle := by
  obtain ⟨q, rfl⟩ := hx
  let z := JordanCurve.Arcs.spherePlaneHomeoCircle q
  exact ⟨z, (C.torusCoveringProjection_zeroWindingPlaneCircle hzero z).symm⟩

/-- Disjoint torus circles have disjoint lifted carriers after every deck translation. -/
theorem disjoint_zeroWindingJordanCarriers_lattice_of_disjoint_circle_ranges
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0))
    (hdisjoint : Disjoint (Set.range C.circle) (Set.range D.circle))
    (k : Fin 2 → ℤ) :
    Disjoint (C.zeroWindingJordanCircle hC).carrier
      ((fun x ↦ x + torusLatticeVector k) ''
        (D.zeroWindingJordanCircle hD).carrier) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨y, hy, hxy⟩
  have hxrange :=
    C.torusCoveringProjection_mem_circle_range_of_mem_zeroWindingJordanCarrier hC hx
  have hyrange :=
    D.torusCoveringProjection_mem_circle_range_of_mem_zeroWindingJordanCarrier hD hy
  have hprojection : torusCoveringProjection Phi x = torusCoveringProjection Phi y := by
    rw [← hxy, torusCoveringProjection_add_lattice]
  exact Set.disjoint_left.mp hdisjoint (hprojection ▸ hxrange) hyrange

/-- In the covering plane, two lifted disks with disjoint projected boundary circles are
disjoint or nested after any deck translation. -/
theorem disjoint_or_nested_zeroWindingClosedJordanDisks_lattice
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0))
    (hdisjoint : Disjoint (Set.range C.circle) (Set.range D.circle))
    (k : Fin 2 → ℤ) :
    Disjoint (C.zeroWindingClosedJordanDisk hC)
        ((fun x ↦ x + torusLatticeVector k) '' D.zeroWindingClosedJordanDisk hD) ∨
      C.zeroWindingClosedJordanDisk hC ⊆
        (fun x ↦ x + torusLatticeVector k) '' D.zeroWindingClosedJordanDisk hD ∨
      (fun x ↦ x + torusLatticeVector k) '' D.zeroWindingClosedJordanDisk hD ⊆
        C.zeroWindingClosedJordanDisk hC := by
  let J := C.zeroWindingJordanCircle hC
  let K := D.zeroWindingJordanCircle hD
  let v := torusLatticeVector k
  have hcarriers : Disjoint J.carrier (K.translate v).carrier := by
    simpa only [J, K, v, Schoenflies.JordanCircle.carrier_translate] using
      C.disjoint_zeroWindingJordanCarriers_lattice_of_disjoint_circle_ranges
        D hC hD hdisjoint k
  rcases J.disjoint_or_nested_closure_inside (K.translate v) hcarriers with
      hseparate | hJK | hKJ
  · left
    simpa only [J, K, v, zeroWindingClosedJordanDisk,
      Schoenflies.JordanCircle.closure_inside_translate] using hseparate
  · right; left
    have hsub : closure J.inside ⊆ closure (K.translate v).inside :=
      hJK.trans subset_closure
    simpa only [J, K, v, zeroWindingClosedJordanDisk,
      Schoenflies.JordanCircle.closure_inside_translate] using hsub
  · right; right
    have hsub : closure (K.translate v).inside ⊆ closure J.inside :=
      hKJ.trans subset_closure
    simpa only [J, K, v, zeroWindingClosedJordanDisk,
      Schoenflies.JordanCircle.closure_inside_translate] using hsub

/-- Lifted nesting into a deck translate descends to nesting of projected closed disks. -/
theorem projectedClosedJordanDisk_subset_of_lifted_subset_translate
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0))
    (k : Fin 2 → ℤ)
    (hsub : C.zeroWindingClosedJordanDisk hC ⊆
      (fun x ↦ x + torusLatticeVector k) '' D.zeroWindingClosedJordanDisk hD) :
    C.zeroWindingProjectedClosedJordanDisk hC ⊆
      D.zeroWindingProjectedClosedJordanDisk hD := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hsub hx
  refine ⟨y, hy, ?_⟩
  calc
    torusCoveringProjectionToTorus Phi y =
        torusCoveringProjectionToTorus Phi (y + torusLatticeVector k) :=
      (torusCoveringProjectionToTorus_add_lattice y k).symm
    _ = torusCoveringProjectionToTorus Phi x := congrArg _ hxy

/-- Reverse lifted nesting also descends after adding the same deck translate. -/
theorem projectedClosedJordanDisk_subset_of_translate_subset_lifted
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0))
    (k : Fin 2 → ℤ)
    (hsub : (fun x ↦ x + torusLatticeVector k) '' D.zeroWindingClosedJordanDisk hD ⊆
      C.zeroWindingClosedJordanDisk hC) :
    D.zeroWindingProjectedClosedJordanDisk hD ⊆
      C.zeroWindingProjectedClosedJordanDisk hC := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y + torusLatticeVector k, hsub ⟨y, hy, rfl⟩, ?_⟩
  exact torusCoveringProjectionToTorus_add_lattice y k

/-- Canonical disks bounded by disjoint zero-winding torus circles are disjoint or nested. -/
theorem disjoint_or_nested_zeroWindingProjectedClosedJordanDisks
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0))
    (hdisjoint : Disjoint (Set.range C.circle) (Set.range D.circle)) :
    Disjoint (C.zeroWindingProjectedClosedJordanDisk hC)
        (D.zeroWindingProjectedClosedJordanDisk hD) ∨
      C.zeroWindingProjectedClosedJordanDisk hC ⊆
        D.zeroWindingProjectedClosedJordanDisk hD ∨
      D.zeroWindingProjectedClosedJordanDisk hD ⊆
        C.zeroWindingProjectedClosedJordanDisk hC := by
  by_cases hprojected : Disjoint (C.zeroWindingProjectedClosedJordanDisk hC)
      (D.zeroWindingProjectedClosedJordanDisk hD)
  · exact Or.inl hprojected
  obtain ⟨p, hpC, hpD⟩ := Set.not_disjoint_iff.mp hprojected
  obtain ⟨x, hx, hxp⟩ := hpC
  obtain ⟨y, hy, hyp⟩ := hpD
  have hprojection : torusCoveringProjection Phi x = torusCoveringProjection Phi y :=
    congrArg Subtype.val (hxp.trans hyp.symm)
  obtain ⟨k, hxy⟩ := exists_latticeVector_of_torusCoveringProjection_eq hprojection
  rcases C.disjoint_or_nested_zeroWindingClosedJordanDisks_lattice
      D hC hD hdisjoint k with hlift | hCD | hDC
  · exfalso
    exact Set.disjoint_left.mp hlift hx ⟨y, hy, hxy.symm⟩
  · exact Or.inr <| Or.inl <|
      C.projectedClosedJordanDisk_subset_of_lifted_subset_translate D hC hD k hCD
  · exact Or.inr <| Or.inr <|
      C.projectedClosedJordanDisk_subset_of_translate_subset_lifted D hC hD k hDC

end EmbeddedTorusIntersectionCircle

namespace FiniteSphereSurgeryIntersectionSystem

variable [Fintype ι] [DecidableEq ι]

/-- The canonical projected torus-side disk of one inessential stage circle. -/
def projectedClosedJordanDisk (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) : Set (transportedTorus Phi) :=
  (S.circle i).zeroWindingProjectedClosedJordanDisk (hzero i)

omit [DecidableEq ι] in
/-- The geometric disjoint-or-nested alternative for two distinct stage disks. -/
theorem projectedClosedJordanDisks_disjoint_or_nested
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) {i j : ι} (hij : i ≠ j) :
    Disjoint (S.projectedClosedJordanDisk hzero i) (S.projectedClosedJordanDisk hzero j) ∨
      S.projectedClosedJordanDisk hzero i ⊆ S.projectedClosedJordanDisk hzero j ∨
      S.projectedClosedJordanDisk hzero j ⊆ S.projectedClosedJordanDisk hzero i :=
  (S.circle i).disjoint_or_nested_zeroWindingProjectedClosedJordanDisks
    (S.circle j) (hzero i) (hzero j) (S.pairwise_disjoint hij)

/-- The finite set of canonical projected disk images, with repeated images removed. -/
def projectedClosedJordanDiskFinset (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) : Finset (Set (transportedTorus Phi)) := by
  classical
  exact Finset.univ.image (S.projectedClosedJordanDisk hzero)

/-- One representative index for a disk image occurring in the finite family. -/
def projectedClosedJordanDiskIndex (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (D : {D // D ∈ S.projectedClosedJordanDiskFinset hzero}) : ι := by
  classical
  exact Classical.choose (Finset.mem_image.mp D.2)

omit [DecidableEq ι] in
theorem projectedClosedJordanDiskIndex_spec
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (D : {D // D ∈ S.projectedClosedJordanDiskFinset hzero}) :
    S.projectedClosedJordanDisk hzero (S.projectedClosedJordanDiskIndex hzero D) = D.1 := by
  classical
  exact (Finset.mem_image.mp D.2).choose_spec.2

/-- Inclusion-maximal disk images in the finite canonical family. -/
def inclusionMaximalProjectedDiskSets (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) : Finset (Set (transportedTorus Phi)) := by
  classical
  exact (S.projectedClosedJordanDiskFinset hzero).filter fun D ↦
    ∀ E ∈ S.projectedClosedJordanDiskFinset hzero, D ⊆ E → E ⊆ D

/-- A representative circle index for each maximal disk image. -/
def inclusionMaximalProjectedDiskIndex (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (D : {D // D ∈ S.inclusionMaximalProjectedDiskSets hzero}) : ι := by
  classical
  exact S.projectedClosedJordanDiskIndex hzero
    ⟨D.1, (Finset.mem_filter.mp D.2).1⟩

omit [DecidableEq ι] in
theorem inclusionMaximalProjectedDiskIndex_spec
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (D : {D // D ∈ S.inclusionMaximalProjectedDiskSets hzero}) :
    S.projectedClosedJordanDisk hzero
        (S.inclusionMaximalProjectedDiskIndex hzero D) = D.1 := by
  classical
  exact S.projectedClosedJordanDiskIndex_spec hzero
    ⟨D.1, (Finset.mem_filter.mp D.2).1⟩

/-- One index for each distinct inclusion-maximal canonical disk image. -/
def inclusionMaximalDiskIndices (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) : Finset ι := by
  classical
  exact (S.inclusionMaximalProjectedDiskSets hzero).attach.image
    (S.inclusionMaximalProjectedDiskIndex hzero)

theorem inclusionMaximalProjectedDiskIndex_mem
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential)
    (D : {D // D ∈ S.inclusionMaximalProjectedDiskSets hzero}) :
    S.inclusionMaximalProjectedDiskIndex hzero D ∈ S.inclusionMaximalDiskIndices hzero := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨D, by simp, rfl⟩

/-- Every canonical disk lies in a selected inclusion-maximal disk. -/
theorem exists_inclusionMaximalDisk_superset
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    ∃ j ∈ S.inclusionMaximalDiskIndices hzero,
      S.projectedClosedJordanDisk hzero i ⊆ S.projectedClosedJordanDisk hzero j := by
  classical
  let F := S.projectedClosedJordanDiskFinset hzero
  have hi : S.projectedClosedJordanDisk hzero i ∈ F := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨D, hiD, hDmax⟩ := F.exists_le_maximal hi
  have hDselected : D ∈ S.inclusionMaximalProjectedDiskSets hzero := by
    apply Finset.mem_filter.mpr
    refine ⟨hDmax.1, ?_⟩
    intro E hEF hDE
    exact hDmax.2 hEF hDE
  let Ds : {D // D ∈ S.inclusionMaximalProjectedDiskSets hzero} := ⟨D, hDselected⟩
  refine ⟨S.inclusionMaximalProjectedDiskIndex hzero Ds,
    S.inclusionMaximalProjectedDiskIndex_mem hzero Ds, ?_⟩
  rw [S.inclusionMaximalProjectedDiskIndex_spec hzero Ds]
  exact hiD

/-- Distinct selected maximal representatives have disjoint projected disks. -/
theorem inclusionMaximalDiskIndices_pairwise_disjoint
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) :
    ∀ {i}, i ∈ S.inclusionMaximalDiskIndices hzero →
      ∀ {j}, j ∈ S.inclusionMaximalDiskIndices hzero → i ≠ j →
      Disjoint (S.projectedClosedJordanDisk hzero i)
        (S.projectedClosedJordanDisk hzero j) := by
  classical
  intro i hi j hj hij
  obtain ⟨Di, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨Dj, _, rfl⟩ := Finset.mem_image.mp hj
  have hDiDj : Di.1 ≠ Dj.1 := by
    intro heq
    apply hij
    exact congrArg (S.inclusionMaximalProjectedDiskIndex hzero) (Subtype.ext heq)
  have hDi := S.inclusionMaximalProjectedDiskIndex_spec hzero Di
  have hDj := S.inclusionMaximalProjectedDiskIndex_spec hzero Dj
  have hcases := S.projectedClosedJordanDisks_disjoint_or_nested hzero hij
  rw [hDi, hDj] at hcases ⊢
  rcases hcases with hdisjoint | hsub | hsub
  · exact hdisjoint
  · exfalso
    apply hDiDj
    apply Set.Subset.antisymm
    · exact hsub
    · exact (Finset.mem_filter.mp Di.2).2 Dj.1 (Finset.mem_filter.mp Dj.2).1 hsub
  · exfalso
    apply hDiDj
    apply Set.Subset.antisymm
    · exact (Finset.mem_filter.mp Dj.2).2 Di.1 (Finset.mem_filter.mp Di.2).1 hsub
    · exact hsub

/-- The inclusion-maximal canonical disks form the maximal family required by surgery. -/
def canonicalMaximalInessentialTorusDiskFamily
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) : MaximalInessentialTorusDiskFamily S hzero where
  maximal := S.inclusionMaximalDiskIndices hzero
  disks_pairwise_disjoint := by
    intro i hi j hj hij
    rw [S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i,
      S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero j]
    exact S.inclusionMaximalDiskIndices_pairwise_disjoint hzero hi hj hij
  every_disk_nested := by
    intro i
    obtain ⟨j, hj, hij⟩ := S.exists_inclusionMaximalDisk_superset hzero i
    refine ⟨j, hj, ?_⟩
    rw [S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i,
      S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero j]
    exact hij

end FiniteSphereSurgeryIntersectionSystem

end Submission.Topology
