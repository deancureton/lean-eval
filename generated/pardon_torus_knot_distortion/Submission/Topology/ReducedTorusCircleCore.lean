import Submission.Topology.ReducedTorusCircleStages
import Submission.Topology.MaximalInessentialDiskFamilyExistence
import Submission.Topology.ResolvedStageLogicalAdapters

/-!
# Canonical disk cores from finite torus-circle families

The all-inessential reduced axis uses only canonical torus-side disks.  This module constructs
their maximal laminar family and finite-puncture pushout directly from pairwise-disjoint torus
circles, without introducing an ambient sphere family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]

namespace FiniteDisjointTorusCircleFamily

/-- The canonical torus-side disk map of an inessential circle. -/
def torusDiskMap (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) (z : ClosedUnitDisk) :
    transportedTorus Phi :=
  let D := (F.circle i).inessentialTorusCircleDisk (hzero i)
  ⟨D.disk z, D.range_subset ⟨z, rfl⟩⟩

theorem continuous_torusDiskMap (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    Continuous (F.torusDiskMap hzero i) :=
  ((F.circle i).inessentialTorusCircleDisk (hzero i)).isEmbedding.continuous.subtype_mk _

theorem injective_torusDiskMap (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    Function.Injective (F.torusDiskMap hzero i) := by
  intro z w hzw
  exact ((F.circle i).inessentialTorusCircleDisk (hzero i)).isEmbedding.injective
    (congrArg Subtype.val hzw)

theorem isEmbedding_torusDiskMap (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    IsEmbedding (F.torusDiskMap hzero i) :=
  ((F.continuous_torusDiskMap hzero i).isClosedEmbedding
    (F.injective_torusDiskMap hzero i)).isEmbedding

/-- The canonical disk map has exactly the projected closed Jordan disk as its range. -/
theorem range_torusDiskMap_eq_projectedClosedJordanDisk
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    Set.range (F.torusDiskMap hzero i) =
      (F.circle i).zeroWindingProjectedClosedJordanDisk (hzero i) := by
  rw [(F.circle i).zeroWindingProjectedClosedJordanDisk_eq_range (hzero i)]
  rfl

/-- The circle itself lies in its canonical torus-side disk. -/
theorem circle_range_subset_torusDiskMap_range
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    Set.range (F.circle i).windingLoop.curve ⊆
      Set.range (F.torusDiskMap hzero i) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨unitDiskBoundary t, ?_⟩
  apply Subtype.ext
  exact ((F.circle i).inessentialTorusCircleDisk (hzero i)).boundary t

private def torusDiskRangeCurve (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    ℝ → Set.range (F.torusDiskMap hzero i) :=
  fun t ↦ ⟨L.curve t, hsub ⟨t, rfl⟩⟩

private theorem continuous_torusDiskRangeCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Continuous (F.torusDiskRangeCurve hzero i L hsub) :=
  L.continuous_curve.subtype_mk _

private theorem periodic_torusDiskRangeCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Function.Periodic (F.torusDiskRangeCurve hzero i L hsub) (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  exact L.periodic_curve t

private def torusDiskFactorCurve (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    ℝ → ClosedUnitDisk :=
  fun t ↦ (F.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm
    (F.torusDiskRangeCurve hzero i L hsub t)

private theorem continuous_torusDiskFactorCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Continuous (F.torusDiskFactorCurve hzero i L hsub) :=
  (F.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm.continuous.comp
    (F.continuous_torusDiskRangeCurve hzero i L hsub)

private theorem periodic_torusDiskFactorCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Function.Periodic (F.torusDiskFactorCurve hzero i L hsub) (2 * Real.pi) := by
  intro t
  exact congrArg (F.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm
    (F.periodic_torusDiskRangeCurve hzero i L hsub t)

private theorem torusDiskMap_factorCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) (t : ℝ) :
    F.torusDiskMap hzero i (F.torusDiskFactorCurve hzero i L hsub t) = L.curve t :=
  congrArg Subtype.val <|
    (F.isEmbedding_torusDiskMap hzero i).toHomeomorph.apply_symm_apply
      (F.torusDiskRangeCurve hzero i L hsub t)

private def contractedDiskPoint (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i))
    (a t : ℝ) : ClosedUnitDisk := by
  let r : ℝ := FiniteSphereSurgeryIntersectionSystem.diskContractionParameter a
  let z : ℂ := (1 - r) • (F.torusDiskFactorCurve hzero i L hsub t : ℂ)
  refine ⟨z, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hr0 : 0 ≤ 1 - r := by
    exact sub_nonneg.mpr
      (FiniteSphereSurgeryIntersectionSystem.diskContractionParameter a).property.2
  have hr1 : 1 - r ≤ 1 := by
    linarith [(FiniteSphereSurgeryIntersectionSystem.diskContractionParameter a).property.1]
  have hz := (F.torusDiskFactorCurve hzero i L hsub t).property
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  change ‖(1 - r) • (F.torusDiskFactorCurve hzero i L hsub t : ℂ)‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left hz hr0).trans <| by simpa using hr1

private theorem continuous_contractedDiskPoint
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Continuous (Function.uncurry (F.contractedDiskPoint hzero i L hsub)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub
      (continuous_subtype_val.comp
        (continuous_projIcc.comp continuous_fst))).smul
    ((continuous_subtype_val.comp
      (F.continuous_torusDiskFactorCurve hzero i L hsub)).comp continuous_snd))

private def contractedTorusDiskCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i))
    (a t : ℝ) : transportedTorus Phi :=
  F.torusDiskMap hzero i (F.contractedDiskPoint hzero i L hsub a t)

private theorem continuous_contractedTorusDiskCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    Continuous (Function.uncurry (F.contractedTorusDiskCurve hzero i L hsub)) :=
  (F.continuous_torusDiskMap hzero i).comp
    (F.continuous_contractedDiskPoint hzero i L hsub)

private theorem periodic_contractedTorusDiskCurve
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) (a : ℝ) :
    Function.Periodic (F.contractedTorusDiskCurve hzero i L hsub a) (2 * Real.pi) := by
  intro t
  apply congrArg (F.torusDiskMap hzero i)
  apply Subtype.ext
  exact congrArg (fun z : ClosedUnitDisk ↦
    (1 - (FiniteSphereSurgeryIntersectionSystem.diskContractionParameter a : ℝ)) •
      (z : ℂ)) (F.periodic_torusDiskFactorCurve hzero i L hsub t)

private theorem contractedTorusDiskCurve_zero
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) (t : ℝ) :
    F.contractedTorusDiskCurve hzero i L hsub 0 t = L.curve t := by
  rw [contractedTorusDiskCurve]
  have hpoint : F.contractedDiskPoint hzero i L hsub 0 t =
      F.torusDiskFactorCurve hzero i L hsub t := by
    apply Subtype.ext
    simp [contractedDiskPoint, FiniteSphereSurgeryIntersectionSystem.diskContractionParameter]
  rw [hpoint]
  exact F.torusDiskMap_factorCurve hzero i L hsub t

private theorem contractedTorusDiskCurve_one
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) (t : ℝ) :
    F.contractedTorusDiskCurve hzero i L hsub 1 t = F.torusDiskMap hzero i 0 := by
  rw [contractedTorusDiskCurve]
  have hpoint : F.contractedDiskPoint hzero i L hsub 1 t = 0 := by
    apply Subtype.ext
    simp [contractedDiskPoint, FiniteSphereSurgeryIntersectionSystem.diskContractionParameter]
  rw [hpoint]

/-- Every loop contained in one canonical circle disk has zero winding. -/
theorem windingPair_eq_zero_of_range_subset_torusDiskMap
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (F.torusDiskMap hzero i)) :
    L.windingPair = (0, 0) := by
  let x := F.torusDiskMap hzero i 0
  have hhomotopy : PeriodicTorusLoopHomotopy
      (transportedLoopCoordinates Phi L.curve)
      (transportedLoopCoordinates Phi (fun _ ↦ x)) := {
    homotopy := fun a t ↦ transportedLoopCoordinates Phi
      (F.contractedTorusDiskCurve hzero i L hsub a) t
    continuous_homotopy :=
      (transportedTorusHomeomorph Phi).symm.continuous.comp
        (F.continuous_contractedTorusDiskCurve hzero i L hsub)
    periodic_homotopy := fun a t ↦ congrArg
      (transportedTorusHomeomorph Phi).symm
      (F.periodic_contractedTorusDiskCurve hzero i L hsub a t)
    homotopy_zero := by
      funext t
      exact congrArg (transportedTorusHomeomorph Phi).symm
        (F.contractedTorusDiskCurve_zero hzero i L hsub t)
    homotopy_one := by
      funext t
      exact congrArg (transportedTorusHomeomorph Phi).symm
        (F.contractedTorusDiskCurve_one hzero i L hsub t)
  }
  have heq := TorusLoopLift.windingPair_eq_of_periodicHomotopy hhomotopy L.lift
    (FiniteSphereSurgeryIntersectionSystem.constantTransportedTorusLoopLift x)
  simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair,
    FiniteSphereSurgeryIntersectionSystem.constantTransportedTorusLoopLift] using heq

end FiniteDisjointTorusCircleFamily

private theorem IsPreconnected.subset_or_subset_closed
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v)
    (huv : Disjoint u v) (hsub : s ⊆ u ∪ v) :
    s ⊆ u ∨ s ⊆ v := by
  by_contra h
  have hsu : ¬ s ⊆ u := fun hsu ↦ h (Or.inl hsu)
  have hsv : ¬ s ⊆ v := fun hsv ↦ h (Or.inr hsv)
  obtain ⟨x, hxs, hxu⟩ := Set.not_subset.mp hsu
  obtain ⟨y, hys, hyv⟩ := Set.not_subset.mp hsv
  have hxv : x ∈ v := (hsub hxs).resolve_left hxu
  have hyu : y ∈ u := (hsub hys).resolve_right hyv
  obtain ⟨z, _hzs, hzu, hzv⟩ :=
    isPreconnected_closed_iff.mp hs u v hu hv hsub
      ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  exact Set.disjoint_left.mp huv hzu hzv

private theorem IsConnected.subset_one_of_subset_biUnion_pairwise_disjoint_closed
    {X κ : Type*} [TopologicalSpace X] [DecidableEq κ]
    {s : Set X} (hs : IsConnected s) (I : Finset κ) (u : κ → Set X)
    (hclosed : ∀ i ∈ I, IsClosed (u i))
    (hdisjoint : ∀ {i}, i ∈ I → ∀ {j}, j ∈ I → i ≠ j →
      Disjoint (u i) (u j))
    (hsub : s ⊆ ⋃ i ∈ I, u i) :
    ∃ i ∈ I, s ⊆ u i := by
  induction I using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hs.nonempty
      simpa using hsub hx
  | @insert i I hi ih =>
      let rest : Set X := ⋃ j ∈ I, u j
      have hrestClosed : IsClosed rest :=
        isClosed_biUnion_finset fun j hj ↦ hclosed j (Finset.mem_insert_of_mem hj)
      have hiClosed : IsClosed (u i) := hclosed i (Finset.mem_insert_self i I)
      have hiRest : Disjoint (u i) rest := by
        rw [Set.disjoint_left]
        intro x hxi hxrest
        simp only [rest, Set.mem_iUnion] at hxrest
        obtain ⟨j, hj, hxj⟩ := hxrest
        exact Set.disjoint_left.mp
          (hdisjoint (Finset.mem_insert_self i I) (Finset.mem_insert_of_mem hj)
            (Ne.symm <| fun hji ↦ hi (hji ▸ hj))) hxi hxj
      have hcover : s ⊆ u i ∪ rest := by
        simpa only [Finset.set_biUnion_insert] using hsub
      rcases IsPreconnected.subset_or_subset_closed hs.isPreconnected
          hiClosed hrestClosed hiRest hcover with hsi | hsrest
      · exact ⟨i, Finset.mem_insert_self i I, hsi⟩
      · obtain ⟨j, hj, hsj⟩ := ih
          (fun j hj ↦ hclosed j (Finset.mem_insert_of_mem hj))
          (fun {j} hj {k} hk hjk ↦ hdisjoint
            (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk)
          hsrest
        exact ⟨j, Finset.mem_insert_of_mem hj, hsj⟩

namespace FiniteDisjointTorusCircleFamily

variable [DecidableEq ι]

/-- The canonical torus-side disk range of one circle. -/
def torusDiskRange (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) : Set (transportedTorus Phi) :=
  Set.range (F.torusDiskMap hzero i)

omit [DecidableEq ι] in
theorem torusDiskRanges_disjoint_or_nested
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {i j : ι} (hij : i ≠ j) :
    Disjoint (F.torusDiskRange hzero i) (F.torusDiskRange hzero j) ∨
      F.torusDiskRange hzero i ⊆ F.torusDiskRange hzero j ∨
      F.torusDiskRange hzero j ⊆ F.torusDiskRange hzero i := by
  rw [torusDiskRange, torusDiskRange,
    F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i,
    F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero j]
  exact (F.circle i).disjoint_or_nested_zeroWindingProjectedClosedJordanDisks
    (F.circle j) (hzero i) (hzero j) (F.pairwise_disjoint hij)

/-- The finite set of canonical disk images. -/
def torusDiskRangeFinset (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) : Finset (Set (transportedTorus Phi)) := by
  classical
  exact Finset.univ.image (F.torusDiskRange hzero)

/-- One circle index representing a canonical disk image. -/
def torusDiskRangeIndex (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (D : {D // D ∈ F.torusDiskRangeFinset hzero}) : ι := by
  classical
  exact Classical.choose (Finset.mem_image.mp D.2)

omit [DecidableEq ι] in
theorem torusDiskRangeIndex_spec (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (D : {D // D ∈ F.torusDiskRangeFinset hzero}) :
    F.torusDiskRange hzero (F.torusDiskRangeIndex hzero D) = D.1 := by
  classical
  exact (Finset.mem_image.mp D.2).choose_spec.2

/-- Inclusion-maximal disk images in the finite laminar family. -/
def inclusionMaximalTorusDiskSets
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) : Finset (Set (transportedTorus Phi)) := by
  classical
  exact (F.torusDiskRangeFinset hzero).filter fun D ↦
    ∀ E ∈ F.torusDiskRangeFinset hzero, D ⊆ E → E ⊆ D

/-- A representative circle index for each maximal disk image. -/
def inclusionMaximalTorusDiskIndex
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (D : {D // D ∈ F.inclusionMaximalTorusDiskSets hzero}) : ι := by
  classical
  exact F.torusDiskRangeIndex hzero
    ⟨D.1, (Finset.mem_filter.mp D.2).1⟩

omit [DecidableEq ι] in
theorem inclusionMaximalTorusDiskIndex_spec
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (D : {D // D ∈ F.inclusionMaximalTorusDiskSets hzero}) :
    F.torusDiskRange hzero (F.inclusionMaximalTorusDiskIndex hzero D) = D.1 := by
  classical
  exact F.torusDiskRangeIndex_spec hzero
    ⟨D.1, (Finset.mem_filter.mp D.2).1⟩

/-- One representative index for every maximal canonical disk image. -/
def inclusionMaximalTorusDiskIndices
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) : Finset ι := by
  classical
  exact (F.inclusionMaximalTorusDiskSets hzero).attach.image
    (F.inclusionMaximalTorusDiskIndex hzero)

theorem inclusionMaximalTorusDiskIndex_mem
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (D : {D // D ∈ F.inclusionMaximalTorusDiskSets hzero}) :
    F.inclusionMaximalTorusDiskIndex hzero D ∈
      F.inclusionMaximalTorusDiskIndices hzero := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨D, by simp, rfl⟩

/-- Every canonical disk lies in one selected maximal disk. -/
theorem exists_inclusionMaximalTorusDisk_superset
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    ∃ j ∈ F.inclusionMaximalTorusDiskIndices hzero,
      F.torusDiskRange hzero i ⊆ F.torusDiskRange hzero j := by
  classical
  let D := F.torusDiskRangeFinset hzero
  have hi : F.torusDiskRange hzero i ∈ D :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨E, hiE, hEmax⟩ := D.exists_le_maximal hi
  have hEselected : E ∈ F.inclusionMaximalTorusDiskSets hzero := by
    apply Finset.mem_filter.mpr
    refine ⟨hEmax.1, ?_⟩
    intro A hAD hEA
    exact hEmax.2 hAD hEA
  let Es : {E // E ∈ F.inclusionMaximalTorusDiskSets hzero} := ⟨E, hEselected⟩
  refine ⟨F.inclusionMaximalTorusDiskIndex hzero Es,
    F.inclusionMaximalTorusDiskIndex_mem hzero Es, ?_⟩
  rw [F.inclusionMaximalTorusDiskIndex_spec hzero Es]
  exact hiE

/-- Distinct selected maximal disk images are disjoint. -/
theorem inclusionMaximalTorusDiskIndices_pairwise_disjoint
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) :
    ∀ {i}, i ∈ F.inclusionMaximalTorusDiskIndices hzero →
      ∀ {j}, j ∈ F.inclusionMaximalTorusDiskIndices hzero → i ≠ j →
      Disjoint (F.torusDiskRange hzero i) (F.torusDiskRange hzero j) := by
  classical
  intro i hi j hj hij
  obtain ⟨Di, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨Dj, _, rfl⟩ := Finset.mem_image.mp hj
  have hDiDj : Di.1 ≠ Dj.1 := by
    intro heq
    apply hij
    exact congrArg (F.inclusionMaximalTorusDiskIndex hzero) (Subtype.ext heq)
  have hDi := F.inclusionMaximalTorusDiskIndex_spec hzero Di
  have hDj := F.inclusionMaximalTorusDiskIndex_spec hzero Dj
  have hcases := F.torusDiskRanges_disjoint_or_nested hzero hij
  rw [hDi, hDj] at hcases ⊢
  rcases hcases with hdisjoint | hsub | hsub
  · exact hdisjoint
  · exfalso
    apply hDiDj
    apply Set.Subset.antisymm
    · exact hsub
    · exact (Finset.mem_filter.mp Di.2).2 Dj.1
        (Finset.mem_filter.mp Dj.2).1 hsub
  · exfalso
    apply hDiDj
    apply Set.Subset.antisymm
    · exact (Finset.mem_filter.mp Dj.2).2 Di.1
        (Finset.mem_filter.mp Di.2).1 hsub
    · exact hsub

/-- Union of the selected maximal canonical disks. -/
def canonicalDiskUnion (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) : Set (transportedTorus Phi) :=
  ⋃ i ∈ F.inclusionMaximalTorusDiskIndices hzero, F.torusDiskRange hzero i

/-- Every canonical disk is contained in the selected maximal disk union. -/
theorem torusDiskRange_subset_canonicalDiskUnion
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    F.torusDiskRange hzero i ⊆ F.canonicalDiskUnion hzero := by
  obtain ⟨j, hj, hij⟩ := F.exists_inclusionMaximalTorusDisk_superset hzero i
  exact hij.trans <| Set.subset_iUnion_of_subset j <|
    Set.subset_iUnion_of_subset hj Subset.rfl

/-- Every circle in the family lies in the selected maximal disk union. -/
theorem circle_range_subset_canonicalDiskUnion
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) (i : ι) :
    Set.range (F.circle i).windingLoop.curve ⊆ F.canonicalDiskUnion hzero :=
  (F.circle_range_subset_torusDiskMap_range hzero i).trans
    (F.torusDiskRange_subset_canonicalDiskUnion hzero i)

/-- The selected maximal circles, indexed without duplicates. -/
def selectedCircle (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (i : F.inclusionMaximalTorusDiskIndices hzero) :
    EmbeddedTorusIntersectionCircle Phi :=
  F.circle i.1

theorem selectedCircle_zeroWinding (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential)
    (i : F.inclusionMaximalTorusDiskIndices hzero) :
    (F.selectedCircle hzero i).windingLoop.windingPair = (0, 0) :=
  hzero i.1

theorem selectedCircle_disks_pairwise_disjoint
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) :
    Pairwise fun i j : F.inclusionMaximalTorusDiskIndices hzero ↦
      Disjoint
        ((F.selectedCircle hzero i).zeroWindingProjectedClosedJordanDisk
          (F.selectedCircle_zeroWinding hzero i))
        ((F.selectedCircle hzero j).zeroWindingProjectedClosedJordanDisk
          (F.selectedCircle_zeroWinding hzero j)) := by
  intro i j hij
  change Disjoint
    ((F.circle i.1).zeroWindingProjectedClosedJordanDisk (hzero i.1))
    ((F.circle j.1).zeroWindingProjectedClosedJordanDisk (hzero j.1))
  rw [← F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i.1,
    ← F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero j.1]
  exact F.inclusionMaximalTorusDiskIndices_pairwise_disjoint hzero i.2 j.2
    (fun hval ↦ hij (Subtype.ext hval))

/-- Canonical separated supports for the selected maximal circles. -/
def selectedCircleSeparatedSupports
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) :
    EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports
      (F.selectedCircle hzero) (F.selectedCircle_zeroWinding hzero) :=
  Classical.choice <|
    EmbeddedTorusIntersectionCircle.exists_separatedZeroWindingDiskSupports_of_pairwise_disjoint
      (F.selectedCircle hzero) (F.selectedCircle_zeroWinding hzero)
      (F.selectedCircle_disks_pairwise_disjoint hzero)

/-- The complement of the selected disk union is the standard simultaneous disk complement. -/
theorem canonicalDiskUnion_compl_eq_finiteZeroWindingDiskComplement
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) :
    (F.canonicalDiskUnion hzero)ᶜ =
      EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskComplement
        (F.selectedCircle hzero) (F.selectedCircle_zeroWinding hzero) := by
  ext x
  constructor
  · intro hx i hxi
    apply hx
    have hiRange : x ∈ F.torusDiskRange hzero i.1 := by
      rw [torusDiskRange,
        F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i.1]
      simpa only [selectedCircle] using hxi
    have hiSelected : x ∈ ⋃ (_h : i.1 ∈ F.inclusionMaximalTorusDiskIndices hzero),
        F.torusDiskRange hzero i.1 :=
      Set.mem_iUnion.mpr ⟨i.2, hiRange⟩
    exact Set.mem_iUnion.mpr ⟨i.1, hiSelected⟩
  · intro hx hxi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxi
    obtain ⟨hiMax, hxi⟩ := Set.mem_iUnion.mp hi
    have hselected := hx ⟨i, hiMax⟩
    apply hselected
    change x ∈ (F.circle i).zeroWindingProjectedClosedJordanDisk (hzero i)
    rw [← F.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i]
    exact hxi

/-- A connected loop covered by the maximal disks lies in one selected disk. -/
theorem connected_range_subset_one_canonicalDisk
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) {s : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ F.canonicalDiskUnion hzero) :
    ∃ i ∈ F.inclusionMaximalTorusDiskIndices hzero,
      Set.range L.curve ⊆ F.torusDiskRange hzero i := by
  exact IsConnected.subset_one_of_subset_biUnion_pairwise_disjoint_closed
    (isConnected_range L.continuous_curve)
    (F.inclusionMaximalTorusDiskIndices hzero) (F.torusDiskRange hzero)
    (fun i _ ↦ (isCompact_range (F.continuous_torusDiskMap hzero i)).isClosed)
    (F.inclusionMaximalTorusDiskIndices_pairwise_disjoint hzero) hsub

/-- A finite all-inessential torus-circle family canonically supplies the reduced disk core. -/
def toReducedInessentialTorusCoreData
    (F : FiniteDisjointTorusCircleFamily Phi ι)
    (hzero : F.AllInessential) : ReducedInessentialTorusCoreData Phi where
  diskUnion := F.canonicalDiskUnion hzero
  diskComplement := (F.canonicalDiskUnion hzero)ᶜ
  diskComplement_eq := rfl
  complement_isConnected := by
    let D := F.selectedCircleSeparatedSupports hzero
    rw [F.canonicalDiskUnion_compl_eq_finiteZeroWindingDiskComplement hzero,
      ← D.range_finitePush, ← Set.image_univ]
    exact (transportedFinitePointComplement_isConnected
        (EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskCenters
          (F.selectedCircle hzero) (F.selectedCircle_zeroWinding hzero))).image
      D.finitePush
      (D.toFiniteSupportedDiskReplacements.toFiniteSequentialPunctureStages.continuous_push
        |>.continuousOn)
  complement_carries := by
    rw [F.canonicalDiskUnion_compl_eq_finiteZeroWindingDiskComplement hzero]
    exact carriesBasedLoopTorusGenus_of_finitePuncturePushout
      (F.selectedCircleSeparatedSupports hzero).toFinitePuncturePushoutData
  loop_zero_of_range_subset_diskUnion := by
    intro s L hsub
    obtain ⟨i, _hi, hi⟩ := F.connected_range_subset_one_canonicalDisk hzero L hsub
    exact F.windingPair_eq_zero_of_range_subset_torusDiskMap hzero i L hi

end FiniteDisjointTorusCircleFamily

end Submission.Topology
