import Submission.Topology.FourPortSixEdgeRawPresentation
import Submission.Topology.ReducedTorusCircleStages
import Submission.Topology.ThreeBoundaryCanonicalDiskSides

/-!
# Carrier invariance of canonical inessential torus disks

The canonical disk attached to a zero-winding embedded torus circle depends only on its carrier,
not on the chosen circle parametrization.  The proof aligns the two lifted plane circles by one
deck translation, uses covering-lift uniqueness on the connected parameter circle, and then
applies planar Jordan carrier invariance before projecting back to the torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

namespace EmbeddedTorusIntersectionCircle

private theorem isEmbedding_torusCircle'
    (C : EmbeddedTorusIntersectionCircle Phi) :
    IsEmbedding C.torusCircle := by
  have h := C.isEmbedding.codRestrict (transportedTorus Phi) fun z ↦
    C.range_subset_transportedTorus ⟨z, rfl⟩
  convert h using 1
  funext z
  apply Subtype.ext
  rfl

theorem continuous_torusCircle (C : EmbeddedTorusIntersectionCircle Phi) :
    Continuous C.torusCircle :=
  (isEmbedding_torusCircle' C).continuous

/-- The circle and real-periodic parametrizations have the same transported-torus carrier. -/
theorem range_torusCircle_eq_range_windingLoop_curve
    (C : EmbeddedTorusIntersectionCircle Phi) :
    Set.range C.torusCircle = Set.range C.windingLoop.curve := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    refine ⟨t, Subtype.ext ?_⟩
    exact (C.parametrization t).symm
  · rintro _ ⟨t, rfl⟩
    refine ⟨Circle.exp t, Subtype.ext ?_⟩
    exact C.parametrization t

/-- Ambient range inclusion is the same inclusion after bundling both circles in the torus. -/
theorem torusCircleCarrier_subset_of_range_subset
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : Set.range C.circle ⊆ Set.range D.circle) :
    torusCircleCarrier C ⊆ torusCircleCarrier D := by
  rintro x ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := hsubset ⟨z, rfl⟩
  exact ⟨w, Subtype.ext hw⟩

/-- Zero winding descends along carrier inclusion between embedded torus circles. -/
theorem windingPair_eq_zero_of_torusCircleCarrier_subset
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D)
    (hzero : D.windingLoop.windingPair = (0, 0)) :
    C.windingLoop.windingPair = (0, 0) := by
  apply D.windingPair_eq_zero_of_range_subset_of_windingPair_eq_zero
    C.windingLoop _ hzero
  rintro _ ⟨t, rfl⟩
  have hmem : C.torusCircle (Circle.exp t) ∈ torusCircleCarrier C := ⟨Circle.exp t, rfl⟩
  obtain ⟨z, hz⟩ := hsubset hmem
  refine ⟨z, ?_⟩
  calc
    D.circle z = C.circle (Circle.exp t) := congrArg Subtype.val hz
    _ = C.windingLoop.curve t := C.parametrization t

/-- The unique reparametrization between two embedded torus circles with the same carrier. -/
def carrierHomeomorph
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hcarrier : torusCircleCarrier C = torusCircleCarrier D) : Circle ≃ₜ Circle :=
  (isEmbedding_torusCircle' C).toHomeomorph |>.trans <|
    (Homeomorph.setCongr hcarrier).trans (isEmbedding_torusCircle' D).toHomeomorph.symm

@[simp]
theorem torusCircle_carrierHomeomorph
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hcarrier : torusCircleCarrier C = torusCircleCarrier D) (z : Circle) :
    D.torusCircle (carrierHomeomorph C D hcarrier z) = C.torusCircle z := by
  apply Subtype.ext
  have happly := (isEmbedding_torusCircle' D).toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr hcarrier) ((isEmbedding_torusCircle' C).toHomeomorph z))
  exact congrArg (fun x : Set.range D.torusCircle ↦ (x.1 : R3)) happly

private theorem exp_apply_eq_of_projection_eq
    {x y : TorusCoveringPlane}
    (h : torusCoveringProjectionToTorus Phi x =
      torusCoveringProjectionToTorus Phi y) (i : Fin 2) :
    Circle.exp (x i) = Circle.exp (y i) := by
  have hval : torusCoveringProjection Phi x = torusCoveringProjection Phi y := by
    exact congrArg Subtype.val h
  change transportedTorusMap Phi
      (Circle.exp (x 0), Circle.exp (x 1)) =
    transportedTorusMap Phi
      (Circle.exp (y 0), Circle.exp (y 1)) at hval
  have hpair := transportedTorusMap_injective Phi hval
  fin_cases i
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- Factor one embedded torus circle continuously through another carrier containing it. -/
def carrierFactor
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D) : Circle → Circle :=
  fun z ↦ (isEmbedding_torusCircle' D).toHomeomorph.symm
    ⟨C.torusCircle z, hsubset ⟨z, rfl⟩⟩

theorem continuous_carrierFactor
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D) :
    Continuous (carrierFactor C D hsubset) :=
  (isEmbedding_torusCircle' D).toHomeomorph.symm.continuous.comp <|
    ((isEmbedding_torusCircle' C).continuous.subtype_mk _)

@[simp]
theorem torusCircle_carrierFactor
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D) (z : Circle) :
    D.torusCircle (carrierFactor C D hsubset z) = C.torusCircle z := by
  apply Subtype.ext
  exact congrArg (fun x : Set.range D.torusCircle ↦ (x.1 : R3)) <|
    (isEmbedding_torusCircle' D).toHomeomorph.apply_symm_apply
      ⟨C.torusCircle z, hsubset ⟨z, rfl⟩⟩

/-- A lifted circle contained in another lifted carrier differs from its factor lift by one deck
translation. -/
theorem exists_planeCircle_eq_factor_add_lattice
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    ∃ k : Fin 2 → ℤ, ∀ z,
      C.zeroWindingPlaneCircle hC z =
        D.zeroWindingPlaneCircle hD (carrierFactor C D hsubset z) +
          torusLatticeVector k := by
  let f := carrierFactor C D hsubset
  let z₀ : Circle := 1
  have hprojection₀ : torusCoveringProjection Phi (C.zeroWindingPlaneCircle hC z₀) =
      torusCoveringProjection Phi (D.zeroWindingPlaneCircle hD (f z₀)) := by
    rw [C.torusCoveringProjection_zeroWindingPlaneCircle hC,
      D.torusCoveringProjection_zeroWindingPlaneCircle hD]
    exact congrArg Subtype.val (torusCircle_carrierFactor C D hsubset z₀).symm
  obtain ⟨k, hk⟩ := exists_latticeVector_of_torusCoveringProjection_eq hprojection₀
  refine ⟨k, ?_⟩
  intro z
  rw [WithLp.ext_iff]
  funext i
  let p : Circle → ℝ := fun w ↦ C.zeroWindingPlaneCircle hC w i
  let q : Circle → ℝ := fun w ↦
    (D.zeroWindingPlaneCircle hD (f w) + torusLatticeVector k) i
  have hp : Continuous p :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp
      (C.continuous_zeroWindingPlaneCircle hC)
  have hq : Continuous q :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp <|
      (D.continuous_zeroWindingPlaneCircle hD).comp
        (C.continuous_carrierFactor D hsubset) |>.add continuous_const
  have hcomp : Circle.exp ∘ p = Circle.exp ∘ q := by
    funext w
    apply exp_apply_eq_of_projection_eq (Phi := Phi)
    rw [torusCoveringProjectionToTorus_add_lattice]
    apply Subtype.ext
    change torusCoveringProjection Phi (C.zeroWindingPlaneCircle hC w) =
      torusCoveringProjection Phi (D.zeroWindingPlaneCircle hD (f w))
    rw [C.torusCoveringProjection_zeroWindingPlaneCircle hC,
      D.torusCoveringProjection_zeroWindingPlaneCircle hD]
    exact congrArg Subtype.val (torusCircle_carrierFactor C D hsubset w).symm
  have hbase : p z₀ = q z₀ :=
    congrArg (fun x : TorusCoveringPlane ↦ x i) hk
  have hpq : p = q :=
    Circle.isCoveringMap_exp.eq_of_comp_eq hp hq hcomp z₀ hbase
  exact congrFun hpq z

/-- Equal carrier parametrizations have plane lifts that differ by one fixed deck translation. -/
theorem exists_planeCircle_eq_comp_add_lattice
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hcarrier : torusCircleCarrier C = torusCircleCarrier D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    ∃ k : Fin 2 → ℤ, ∀ z,
      C.zeroWindingPlaneCircle hC z =
        D.zeroWindingPlaneCircle hD (carrierHomeomorph C D hcarrier z) +
          torusLatticeVector k := by
  let e := carrierHomeomorph C D hcarrier
  let z₀ : Circle := 1
  have hprojection₀ : torusCoveringProjection Phi (C.zeroWindingPlaneCircle hC z₀) =
      torusCoveringProjection Phi (D.zeroWindingPlaneCircle hD (e z₀)) := by
    rw [C.torusCoveringProjection_zeroWindingPlaneCircle hC,
      D.torusCoveringProjection_zeroWindingPlaneCircle hD]
    exact congrArg Subtype.val (torusCircle_carrierHomeomorph C D hcarrier z₀).symm
  obtain ⟨k, hk⟩ := exists_latticeVector_of_torusCoveringProjection_eq hprojection₀
  refine ⟨k, ?_⟩
  intro z
  rw [WithLp.ext_iff]
  funext i
  let p : Circle → ℝ := fun w ↦ C.zeroWindingPlaneCircle hC w i
  let q : Circle → ℝ := fun w ↦
    (D.zeroWindingPlaneCircle hD (e w) + torusLatticeVector k) i
  have hp : Continuous p :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp
      (C.continuous_zeroWindingPlaneCircle hC)
  have hq : Continuous q :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) i).comp <|
      (D.continuous_zeroWindingPlaneCircle hD).comp e.continuous |>.add continuous_const
  have hcomp : Circle.exp ∘ p = Circle.exp ∘ q := by
    funext w
    apply exp_apply_eq_of_projection_eq (Phi := Phi)
    rw [torusCoveringProjectionToTorus_add_lattice]
    apply Subtype.ext
    change torusCoveringProjection Phi (C.zeroWindingPlaneCircle hC w) =
      torusCoveringProjection Phi (D.zeroWindingPlaneCircle hD (e w))
    rw [C.torusCoveringProjection_zeroWindingPlaneCircle hC,
      D.torusCoveringProjection_zeroWindingPlaneCircle hD]
    exact congrArg Subtype.val (torusCircle_carrierHomeomorph C D hcarrier w).symm
  have hbase : p z₀ = q z₀ := by
    exact congrArg (fun x : TorusCoveringPlane ↦ x i) hk
  have hpq : p = q :=
    Circle.isCoveringMap_exp.eq_of_comp_eq hp hq hcomp z₀ hbase
  exact congrFun hpq z

private theorem carrier_zeroWindingJordanCircle'
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    (C.zeroWindingJordanCircle hzero).carrier =
      Set.range (C.zeroWindingPlaneCircle hzero) := by
  change Set.range
      (C.zeroWindingPlaneCircle hzero ∘ JordanCurve.Arcs.spherePlaneHomeoCircle) = _
  rw [Set.range_comp, JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq,
    Set.image_univ]

/-- Carrier inclusion is enough to identify the canonical projected closed disks. -/
theorem zeroWindingProjectedClosedJordanDisk_eq_of_torusCircleCarrier_subset
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hsubset : torusCircleCarrier C ⊆ torusCircleCarrier D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      D.zeroWindingProjectedClosedJordanDisk hD := by
  obtain ⟨k, hk⟩ := C.exists_planeCircle_eq_factor_add_lattice D hsubset hC hD
  have hcarrierPlane :
      (C.zeroWindingJordanCircle hC).carrier =
        ((D.zeroWindingJordanCircle hD).translate (torusLatticeVector k)).carrier := by
    apply Schoenflies.JordanCircle.carrier_eq_of_subset_carrier
    rw [C.carrier_zeroWindingJordanCircle' hC,
      Schoenflies.JordanCircle.carrier_translate,
      D.carrier_zeroWindingJordanCircle' hD]
    rintro _ ⟨z, rfl⟩
    refine ⟨D.zeroWindingPlaneCircle hD (carrierFactor C D hsubset z),
      ⟨carrierFactor C D hsubset z, rfl⟩, ?_⟩
    exact (hk z).symm
  have hinside := Schoenflies.JordanCircle.inside_eq_of_carrier_eq
    (C.zeroWindingJordanCircle hC)
    ((D.zeroWindingJordanCircle hD).translate (torusLatticeVector k)) hcarrierPlane
  rw [zeroWindingProjectedClosedJordanDisk, zeroWindingClosedJordanDisk,
    hinside, Schoenflies.JordanCircle.closure_inside_translate]
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (torusCoveringProjectionToTorus_add_lattice x k).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x + torusLatticeVector k, ⟨x, hx, rfl⟩, ?_⟩
    exact torusCoveringProjectionToTorus_add_lattice x k

/-- The canonical projected closed disk depends only on the torus-circle carrier. -/
theorem zeroWindingProjectedClosedJordanDisk_eq_of_torusCircleCarrier_eq
    (C D : EmbeddedTorusIntersectionCircle Phi)
    (hcarrier : torusCircleCarrier C = torusCircleCarrier D)
    (hC : C.windingLoop.windingPair = (0, 0))
    (hD : D.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hC =
      D.zeroWindingProjectedClosedJordanDisk hD := by
  exact C.zeroWindingProjectedClosedJordanDisk_eq_of_torusCircleCarrier_subset D
    hcarrier.le hC hD

end EmbeddedTorusIntersectionCircle

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
  obtain ⟨_, _, hzu, hzv⟩ :=
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

variable {iota : Type*} [Fintype iota]

/-- A connected nonempty subset of a finite disjoint circle carrier lies in one circle. -/
theorem exists_circleCarrier_of_isConnected_subset_carrier
    (F : FiniteDisjointTorusCircleFamily Phi iota)
    {s : Set (transportedTorus Phi)} (hs : IsConnected s)
    (hsub : s ⊆ F.carrier) :
    ∃ i, s ⊆ torusCircleCarrier (F.circle i) := by
  classical
  obtain ⟨i, _, hi⟩ :=
    IsConnected.subset_one_of_subset_biUnion_pairwise_disjoint_closed hs
      Finset.univ (fun i ↦ torusCircleCarrier (F.circle i))
      (fun i _ ↦ (isCompact_range
        (EmbeddedTorusIntersectionCircle.isEmbedding_torusCircle' (F.circle i)).continuous).isClosed)
      (fun {i} _ {j} _ hij ↦ by
        rw [Set.disjoint_left]
        rintro x ⟨z, rfl⟩ ⟨w, hw⟩
        exact Set.disjoint_left.mp (F.pairwise_disjoint hij)
          ⟨z, rfl⟩ ⟨w, congrArg Subtype.val hw⟩)
      (by
        intro x hx
        have hx' := hsub hx
        simp only [FiniteDisjointTorusCircleFamily.carrier, Set.mem_iUnion] at hx' ⊢
        obtain ⟨i, hi⟩ := hx'
        refine ⟨i, Finset.mem_univ i, ?_⟩
        change x ∈ Set.range (F.circle i).torusCircle
        rw [(F.circle i).range_torusCircle_eq_range_windingLoop_curve]
        exact hi)
  exact ⟨i, hi⟩

end FiniteDisjointTorusCircleFamily

end Submission.Topology
