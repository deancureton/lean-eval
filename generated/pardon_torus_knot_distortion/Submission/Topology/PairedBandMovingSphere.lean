import Submission.Topology.PairedSeamBandSmoothing

/-!
# Embedded moving spheres from paired-band replacements

This file isolates the primitive collar input for one regular stage of the two-surgery and derives
the global object that was previously missing.  A source parametrization is allowed to be singular
inside a closed parameter region.  On that region it is replaced by the regular sheet supplied by
an ambient band/collar chart.  Agreement on the frontier gives continuity; three elementary
injectivity conditions give an embedded sphere.

The construction is componentwise, so the output is a finite pairwise-disjoint family of spheres.
This is necessary after a two-surgery, when a regular stage can have more than one sphere
component.  The final section proves the exact transported-torus intersection from pointwise
outside-collar and replacement-chart facts; it is not stored as a conclusion field.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- The fixed parameter sphere used for every component of a regular moving-sphere stage. -/
abbrev MovingSphereDomain := Metric.sphere (0 : R3) 1

/-! ## One relative sphere replacement -/

/-- Primitive relative patching data in a sphere collar.

`source` need only be an injective sheet off `region`; it may describe the singular double-bubble
inside the region.  The replacement is the regular sheet.  The last condition is the geometric
separation supplied by an ambient collar. -/
structure RelativeSphereBandPatchData where
  source : MovingSphereDomain → R3
  region : Set MovingSphereDomain
  isClosed_region : IsClosed region
  replacement : MovingSphereDomain → R3
  continuous_source : Continuous source
  continuousOn_replacement : ContinuousOn replacement region
  frontier_eq : Set.EqOn replacement source (frontier region)
  replacement_injOn : Set.InjOn replacement region
  source_injOn_compl : Set.InjOn source regionᶜ
  replacement_ne_source_compl :
    ∀ x ∈ region, ∀ y ∉ region, replacement x ≠ source y

namespace RelativeSphereBandPatchData

/-- Use the regular sheet on the surgery region and the old sheet elsewhere. -/
def patchedParametrization (P : RelativeSphereBandPatchData) : MovingSphereDomain → R3 :=
  by
    classical
    exact P.region.piecewise P.replacement P.source

theorem continuous_patchedParametrization (P : RelativeSphereBandPatchData) :
    Continuous P.patchedParametrization := by
  classical
  rw [patchedParametrization]
  apply continuous_piecewise
  · exact P.frontier_eq
  · simpa [P.isClosed_region.closure_eq] using P.continuousOn_replacement
  · exact P.continuous_source.continuousOn

theorem injective_patchedParametrization (P : RelativeSphereBandPatchData) :
    Function.Injective P.patchedParametrization := by
  classical
  rw [patchedParametrization, Set.injective_piecewise_iff]
  exact ⟨P.replacement_injOn, P.source_injOn_compl,
    P.replacement_ne_source_compl⟩

/-- The relative replacement is an actual embedded sphere. -/
def patchedSphere (P : RelativeSphereBandPatchData) : EmbeddedTopologicalSphereInR3 where
  parametrization := P.patchedParametrization
  isEmbedding :=
    (P.continuous_patchedParametrization.isClosedEmbedding
      P.injective_patchedParametrization).isEmbedding

/-- Exact image formula for the glued sphere. -/
theorem patchedSphere_carrier (P : RelativeSphereBandPatchData) :
    P.patchedSphere.carrier =
      P.replacement '' P.region ∪ P.source '' P.regionᶜ := by
  classical
  change Set.range P.patchedParametrization =
    P.replacement '' P.region ∪ P.source '' P.regionᶜ
  unfold patchedParametrization
  exact Set.range_piecewise P.region P.replacement P.source

end RelativeSphereBandPatchData

/-! ## Simultaneous finite sphere-family replacement -/

/-- Primitive input for simultaneous replacement on finitely many sphere components.  Distinct
components are assigned pairwise-disjoint ambient collar neighborhoods; disjointness of the
completed components is derived below. -/
structure FiniteRelativeSphereBandPatchData where
  count : ℕ
  patch : Fin count → RelativeSphereBandPatchData
  componentNeighborhood : Fin count → Set R3
  neighborhood_pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (componentNeighborhood i) (componentNeighborhood j)
  source_compl_mem_neighborhood : ∀ i x, x ∉ (patch i).region →
    (patch i).source x ∈ componentNeighborhood i
  replacement_mem_neighborhood : ∀ i x, x ∈ (patch i).region →
    (patch i).replacement x ∈ componentNeighborhood i

namespace FiniteRelativeSphereBandPatchData

theorem patchedSphere_carrier_subset_componentNeighborhood
    (F : FiniteRelativeSphereBandPatchData) (i : Fin F.count) :
    (F.patch i).patchedSphere.carrier ⊆ F.componentNeighborhood i := by
  rw [(F.patch i).patchedSphere_carrier]
  apply Set.union_subset
  · rintro _ ⟨x, hx, rfl⟩
    exact F.replacement_mem_neighborhood i x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact F.source_compl_mem_neighborhood i x hx

/-- The finite family of embedded regular-stage spheres produced by all relative replacements. -/
def patchedFamily (F : FiniteRelativeSphereBandPatchData) :
    FiniteEmbeddedTopologicalSphereFamilyInR3 where
  count := F.count
  sphere := fun i ↦ (F.patch i).patchedSphere
  pairwise_disjoint := by
    intro i j hij
    exact (F.neighborhood_pairwise_disjoint hij).mono
      (F.patchedSphere_carrier_subset_componentNeighborhood i)
      (F.patchedSphere_carrier_subset_componentNeighborhood j)

/-- Images of all newly inserted sheets. -/
def replacementImage (F : FiniteRelativeSphereBandPatchData) : Set R3 :=
  ⋃ i, (F.patch i).replacement '' (F.patch i).region

/-- Images of all unchanged source sheets outside the collar regions. -/
def sourceOutsideImage (F : FiniteRelativeSphereBandPatchData) : Set R3 :=
  ⋃ i, (F.patch i).source '' (F.patch i).regionᶜ

/-- The full source carrier before replacement; it may be singular inside the collar regions. -/
def sourceImage (F : FiniteRelativeSphereBandPatchData) : Set R3 :=
  ⋃ i, Set.range (F.patch i).source

/-- The carrier of the constructed sphere family is exactly the inserted sheets together with
the untouched outside sheets. -/
theorem patchedFamily_carrier (F : FiniteRelativeSphereBandPatchData) :
    F.patchedFamily.carrier = F.replacementImage ∪ F.sourceOutsideImage := by
  ext x
  simp only [patchedFamily, FiniteEmbeddedTopologicalSphereFamilyInR3.carrier,
    Set.mem_iUnion, RelativeSphereBandPatchData.patchedSphere_carrier,
    Set.mem_union, replacementImage, sourceOutsideImage]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr hi⟩

/-- Exact transported-torus intersection formula for the completed moving-sphere family. -/
theorem patchedFamily_inter_transportedTorus
    (F : FiniteRelativeSphereBandPatchData) (Phi : AmbientIsotopy) :
    F.patchedFamily.carrier ∩ transportedTorus Phi =
      (F.replacementImage ∩ transportedTorus Phi) ∪
        (F.sourceOutsideImage ∩ transportedTorus Phi) := by
  rw [F.patchedFamily_carrier, Set.union_inter_distrib_right]

end FiniteRelativeSphereBandPatchData

/-! ## The paired-band collar contract and its derived exact stage intersection -/

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]

/-- Every point of the analytic barrier graph lies on the transported torus. -/
theorem carrier_subset_transportedTorus
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    G.carrier ⊆ transportedTorus Phi := by
  rw [G.carrier_eq_ambientBarrier]
  intro x hx
  exact hx.1

end FiniteSuperellipsoidBarrierGraph

/-- Primitive collar facts for realizing a chosen paired-band smoothing by a finite family of
embedded spheres.

The four pointwise fields are deliberately local image/preimage statements.  They are what an
ambient collar computation proves.  Neither the completed family nor its exact global torus
intersection is a field. -/
structure PairedBandMovingSphereCollarData
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    {P : FiniteBarrierExcursionPairing A}
    (C : BarrierExcursionBandChartRealization P)
    (choice : Fin P.bandCount → Bool) where
  family : FiniteRelativeSphereBandPatchData
  sourceOutside_torus_mem : ∀ k x, x ∉ (family.patch k).region →
    (family.patch k).source x ∈ transportedTorus Phi →
      (family.patch k).source x ∈
        G.carrier \ C.toFinitePairedSeamBandCharts.supportUnion
  oldOutside_has_source : ∀ y,
    y ∈ G.carrier \ C.toFinitePairedSeamBandCharts.supportUnion →
      ∃ k x, x ∉ (family.patch k).region ∧ (family.patch k).source x = y
  source_mem_support_iff : ∀ k x,
    (family.patch k).source x ∈ C.toFinitePairedSeamBandCharts.supportUnion ↔
      x ∈ (family.patch k).region
  replacement_region_mem_support : ∀ k x, x ∈ (family.patch k).region →
    (family.patch k).replacement x ∈
      C.toFinitePairedSeamBandCharts.supportUnion
  replacement_torus_mem : ∀ k x, x ∈ (family.patch k).region →
    (family.patch k).replacement x ∈ transportedTorus Phi →
      (family.patch k).replacement x ∈
        C.toFinitePairedSeamBandCharts.patchUnion choice
  patch_has_replacement : ∀ y,
    y ∈ C.toFinitePairedSeamBandCharts.patchUnion choice →
      ∃ k x, x ∈ (family.patch k).region ∧ (family.patch k).replacement x = y

namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}
  {choice : Fin P.bandCount → Bool}

theorem replacementImage_inter_torus_eq
    (D : PairedBandMovingSphereCollarData C choice) :
    D.family.replacementImage ∩ transportedTorus Phi =
      C.toFinitePairedSeamBandCharts.patchUnion choice := by
  ext y
  constructor
  · rintro ⟨hy, hyTorus⟩
    simp only [FiniteRelativeSphereBandPatchData.replacementImage,
      Set.mem_iUnion] at hy
    obtain ⟨k, x, hx, rfl⟩ := hy
    exact D.replacement_torus_mem k x hx hyTorus
  · intro hy
    obtain ⟨k, x, hx, hxy⟩ := D.patch_has_replacement y hy
    refine ⟨?_, C.patchUnion_subset_transportedTorus choice hy⟩
    simp only [FiniteRelativeSphereBandPatchData.replacementImage,
      Set.mem_iUnion]
    exact ⟨k, x, hx, hxy⟩

/-- The constructed sphere family agrees exactly with the source surface away from the ambient
union of band supports.  This is derived from support control of the primitive collar sheets. -/
theorem patchedFamily_sdiff_support_eq_source
    (D : PairedBandMovingSphereCollarData C choice) :
    D.family.patchedFamily.carrier \
        C.toFinitePairedSeamBandCharts.supportUnion =
      D.family.sourceImage \ C.toFinitePairedSeamBandCharts.supportUnion := by
  rw [D.family.patchedFamily_carrier]
  ext y
  constructor
  · rintro ⟨hy, hySupport⟩
    rcases hy with hyReplacement | hySource
    · simp only [FiniteRelativeSphereBandPatchData.replacementImage,
        Set.mem_iUnion] at hyReplacement
      obtain ⟨k, x, hx, rfl⟩ := hyReplacement
      exact False.elim (hySupport (D.replacement_region_mem_support k x hx))
    · refine ⟨?_, hySupport⟩
      simp only [FiniteRelativeSphereBandPatchData.sourceOutsideImage,
        FiniteRelativeSphereBandPatchData.sourceImage, Set.mem_iUnion] at hySource ⊢
      obtain ⟨k, x, hx, hxy⟩ := hySource
      exact ⟨k, x, hxy⟩
  · rintro ⟨hy, hySupport⟩
    simp only [FiniteRelativeSphereBandPatchData.sourceImage,
      Set.mem_iUnion] at hy
    obtain ⟨k, x, hxy⟩ := hy
    have hx : x ∉ (D.family.patch k).region := by
      intro hx
      have hsource := (D.source_mem_support_iff k x).2 hx
      exact hySupport (hxy ▸ hsource)
    refine ⟨Or.inr ?_, hySupport⟩
    simp only [FiniteRelativeSphereBandPatchData.sourceOutsideImage,
      Set.mem_iUnion]
    exact ⟨k, x, hx, hxy⟩

/-- Agreement off compact replacement support implies agreement off the larger open isolation
neighborhoods. -/
theorem patchedFamily_sdiff_bandNeighborhoods_eq_source
    (D : PairedBandMovingSphereCollarData C choice) :
    D.family.patchedFamily.carrier \ (⋃ b, P.bandNeighborhood b) =
      D.family.sourceImage \ (⋃ b, P.bandNeighborhood b) := by
  have hsupport := C.supportUnion_subset_bandNeighborhoods
  have hoff := Set.ext_iff.mp D.patchedFamily_sdiff_support_eq_source
  ext y
  constructor
  · rintro ⟨hy, hyBand⟩
    have hySupport : y ∉ C.toFinitePairedSeamBandCharts.supportUnion :=
      fun hy ↦ hyBand (hsupport hy)
    exact ⟨((hoff y).mp ⟨hy, hySupport⟩).1, hyBand⟩
  · rintro ⟨hy, hyBand⟩
    have hySupport : y ∉ C.toFinitePairedSeamBandCharts.supportUnion :=
      fun hy ↦ hyBand (hsupport hy)
    exact ⟨((hoff y).mpr ⟨hy, hySupport⟩).1, hyBand⟩

theorem sourceOutsideImage_inter_torus_eq
    (D : PairedBandMovingSphereCollarData C choice) :
    D.family.sourceOutsideImage ∩ transportedTorus Phi =
      G.carrier \ C.toFinitePairedSeamBandCharts.supportUnion := by
  ext y
  constructor
  · rintro ⟨hy, hyTorus⟩
    simp only [FiniteRelativeSphereBandPatchData.sourceOutsideImage,
      Set.mem_iUnion] at hy
    obtain ⟨k, x, hx, rfl⟩ := hy
    exact D.sourceOutside_torus_mem k x hx hyTorus
  · intro hy
    obtain ⟨k, x, hx, hxy⟩ := D.oldOutside_has_source y hy
    refine ⟨?_, G.carrier_subset_transportedTorus hy.1⟩
    simp only [FiniteRelativeSphereBandPatchData.sourceOutsideImage,
      Set.mem_iUnion]
    exact ⟨k, x, hx, hxy⟩

/-- The actual finite embedded moving-sphere stage has exactly the chosen resolved graph as its
transported-torus intersection. -/
theorem patchedFamily_inter_torus_eq_resolvedGraphCarrier
    (D : PairedBandMovingSphereCollarData C choice) :
    D.family.patchedFamily.carrier ∩ transportedTorus Phi =
      C.resolvedGraphCarrier choice := by
  rw [D.family.patchedFamily_inter_transportedTorus,
    D.replacementImage_inter_torus_eq, D.sourceOutsideImage_inter_torus_eq,
    BarrierExcursionBandChartRealization.resolvedGraphCarrier,
    FinitePairedSeamBandCharts.resolvedCarrier]
  exact Set.union_comm _ _

/-- Circle and parity-side data attached to the already constructed moving-sphere family.  The
only global topological input left here is that the finitely glued smoothing arcs form the stated
circle family.  In particular, no sphere or sphere-intersection equality is a field. -/
structure RegularStageDecoration
    (D : PairedBandMovingSphereCollarData C choice)
    (ι : Type*) [Fintype ι] where
  insideCell : Set R3
  family_is_boundary : D.family.patchedFamily.carrier = frontier insideCell
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  resolvedCarrier_eq_circleUnion : C.resolvedGraphCarrier choice =
    ⋃ i, Set.range (circle i).circle
  sphereDisk : ι → BoundaryParametrizedEmbeddedDiskInR3
  sphereDisk_mem : ∀ i,
    Set.range (sphereDisk i).disk ⊆ D.family.patchedFamily.carrier
  sphereDisk_boundary : ∀ i t,
    (sphereDisk i).disk (unitDiskBoundary t) = (circle i).windingLoop.curve t
  eventRegion : Set R3
  circle_mem_event : ∀ i t, ((circle i).windingLoop.curve t : R3) ∈ eventRegion

/-- The finite regular stage consumed by the Pardon surgery dichotomy.  Its embedded sphere
family and its exact transported-torus intersection are supplied by the relative collar
construction above. -/
def RegularStageDecoration.toFiniteSphereSurgeryIntersectionSystem
    {D : PairedBandMovingSphereCollarData C choice}
    {ι : Type*} [Fintype ι] (E : RegularStageDecoration D ι) :
    FiniteSphereSurgeryIntersectionSystem Phi ι where
  sphereFamily := D.family.patchedFamily
  insideCell := E.insideCell
  sphereFamily_is_boundary := E.family_is_boundary
  circle := E.circle
  pairwise_disjoint := E.pairwise_disjoint
  intersection_exact := by
    rw [D.patchedFamily_inter_torus_eq_resolvedGraphCarrier,
      E.resolvedCarrier_eq_circleUnion]
  sphereDisk := E.sphereDisk
  sphereDisk_mem := E.sphereDisk_mem
  sphereDisk_boundary := E.sphereDisk_boundary
  eventRegion := E.eventRegion
  circle_mem_event := E.circle_mem_event

/-! ## Rank-two core invariance across inessential band moves -/

/-- Local disk cover of the part of the transported torus changed by a finite band move.  Each
changed patch is placed in one selected maximal inessential torus disk. -/
structure InessentialBandDiskCover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (support : Set R3) where
  bandCount : ℕ
  changedPatch : Fin bandCount → Set (transportedTorus Phi)
  supportPart_eq : transportedTorusPart Phi support = ⋃ b, changedPatch b
  diskIndex : Fin bandCount → ι
  diskIndex_mem : ∀ b, diskIndex b ∈ M.maximal
  patch_subset_disk : ∀ b, changedPatch b ⊆
    Set.range (S.torusDiskMap hzero (diskIndex b))

namespace InessentialBandDiskCover

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}
  {M : MaximalInessentialTorusDiskFamily S hzero}
  {support : Set R3}

/-- The entire changed torus patch lies in the finite union of maximal inessential disks. -/
theorem supportPart_subset_diskUnion (B : InessentialBandDiskCover M support) :
    transportedTorusPart Phi support ⊆ M.diskUnion := by
  rw [B.supportPart_eq]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨b, hb⟩ := hx
  exact Set.mem_iUnion.mpr ⟨B.diskIndex b,
    Set.mem_iUnion.mpr ⟨B.diskIndex_mem b, B.patch_subset_disk b hb⟩⟩

/-- Any explicitly proved finite-disk cover can be reindexed by `Fin`; no additional geometric
content is hidden in the bookkeeping structure. -/
def ofSubsetDiskUnion
    (h : transportedTorusPart Phi support ⊆ M.diskUnion) :
    InessentialBandDiskCover M support := by
  let e : M.maximal ≃ Fin (Fintype.card M.maximal) := Fintype.equivFin M.maximal
  refine {
    bandCount := Fintype.card M.maximal
    changedPatch := fun b ↦ transportedTorusPart Phi support ∩
      Set.range (S.torusDiskMap hzero (e.symm b).1)
    supportPart_eq := ?_
    diskIndex := fun b ↦ (e.symm b).1
    diskIndex_mem := fun b ↦ (e.symm b).2
    patch_subset_disk := fun b ↦ Set.inter_subset_right }
  ext x
  constructor
  · intro hx
    have hxDisk := h hx
    simp only [MaximalInessentialTorusDiskFamily.diskUnion, Set.mem_iUnion] at hxDisk
    obtain ⟨i, hi, hxi⟩ := hxDisk
    let q : M.maximal := ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨e q, hx, ?_⟩
    simpa [q] using hxi
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨b, hx, -⟩ := hx
    exact hx

end InessentialBandDiskCover

/-- Parity-side data for one inessential band move.  Agreement is required only away from the
ambient support, where the pre- and post-surgery sphere families literally coincide. -/
structure InessentialBandCoreParityData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (support : Set R3) where
  diskCover : InessentialBandDiskCover M support
  beforeInside : Set (transportedTorus Phi)
  afterInside : Set (transportedTorus Phi)
  inside_agree_off_support : ∀ x,
    x ∉ transportedTorusPart Phi support →
      (x ∈ beforeInside ↔ x ∈ afterInside)

namespace InessentialBandCoreParityData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}
  {M : MaximalInessentialTorusDiskFamily S hzero}
  {support : Set R3}

/-- The connected rank-two core misses every band support. -/
theorem diskComplement_disjoint_support
    (I : InessentialBandCoreParityData M support) :
    Disjoint M.diskComplement (transportedTorusPart Phi support) := by
  rw [Set.disjoint_left]
  intro x hxCore hxSupport
  exact hxCore (I.diskCover.supportPart_subset_diskUnion hxSupport)

/-- The parity-inside label of the entire rank-two core is invariant across the band move. -/
theorem diskComplement_subset_after_iff_before
    (I : InessentialBandCoreParityData M support) :
    M.diskComplement ⊆ I.afterInside ↔ M.diskComplement ⊆ I.beforeInside := by
  constructor
  · intro hAfter x hxCore
    exact (I.inside_agree_off_support x fun hxSupport ↦
      Set.disjoint_left.mp I.diskComplement_disjoint_support hxCore hxSupport).mpr
      (hAfter hxCore)
  · intro hBefore x hxCore
    exact (I.inside_agree_off_support x fun hxSupport ↦
      Set.disjoint_left.mp I.diskComplement_disjoint_support hxCore hxSupport).mp
      (hBefore hxCore)

end InessentialBandCoreParityData

/-- One honest regular sphere-family stage, with its two open parity cells and exact boundary
partition on the transported torus. -/
structure RegularSphereFamilyParityStage (Phi : AmbientIsotopy) where
  sphereFamily : FiniteEmbeddedTopologicalSphereFamilyInR3
  ambientInside : Set R3
  family_is_boundary : sphereFamily.carrier = frontier ambientInside
  inside : Set (transportedTorus Phi)
  outside : Set (transportedTorus Phi)
  isOpen_inside : IsOpen inside
  isOpen_outside : IsOpen outside
  inside_disjoint_outside : Disjoint inside outside
  surface_partition : Set.univ =
    inside ∪ outside ∪ transportedTorusPart Phi sphereFamily.carrier

/-- One all-inessential transition with its own finite disk family and rank-two core.  Different
transitions may use overlapping disk families; no global common-core premise is imposed. -/
structure InessentialParityTransition
    (pre post : RegularSphereFamilyParityStage Phi) where
  coreCircleCount : ℕ
  coreSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin coreCircleCount)
  coreAllInessential : coreSystem.AllInessential
  maximal : MaximalInessentialTorusDiskFamily coreSystem coreAllInessential
  pushout : maximal.ConnectedPushoutData
  support : Set R3
  diskCover : InessentialBandDiskCover maximal support
  boundaries_subset_support :
    transportedTorusPart Phi pre.sphereFamily.carrier ∪
        transportedTorusPart Phi post.sphereFamily.carrier ⊆
      transportedTorusPart Phi support
  labelChange_subset_support :
    {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)} ⊆
      transportedTorusPart Phi support

namespace InessentialParityTransition

variable {pre post : RegularSphereFamilyParityStage Phi}

theorem core_disjoint_support (T : InessentialParityTransition pre post) :
    Disjoint T.maximal.diskComplement (transportedTorusPart Phi T.support) := by
  rw [Set.disjoint_left]
  intro x hxCore hxSupport
  exact hxCore (T.diskCover.supportPart_subset_diskUnion hxSupport)

theorem preBoundary_subset_diskUnion (T : InessentialParityTransition pre post) :
    transportedTorusPart Phi pre.sphereFamily.carrier ⊆ T.maximal.diskUnion := by
  intro x hx
  exact T.diskCover.supportPart_subset_diskUnion
    (T.boundaries_subset_support (Or.inl hx))

theorem core_subset_preInside_or_outside (T : InessentialParityTransition pre post) :
    T.maximal.diskComplement ⊆ pre.inside ∨
      T.maximal.diskComplement ⊆ pre.outside := by
  have hsubset : T.maximal.diskComplement ⊆ pre.inside ∪ pre.outside := by
    intro x hxCore
    have hxUniv : x ∈ (Set.univ : Set (transportedTorus Phi)) := Set.mem_univ x
    rw [pre.surface_partition] at hxUniv
    rcases hxUniv with hxCell | hxBoundary
    · exact hxCell
    · exact False.elim (hxCore (T.preBoundary_subset_diskUnion hxBoundary))
  exact (MaximalInessentialTorusDiskFamily.ConnectedPushoutData.complement_isConnected
      T.maximal T.pushout).isPreconnected
    |>.subset_or_subset pre.isOpen_inside pre.isOpen_outside
      pre.inside_disjoint_outside hsubset

theorem not_core_subset_preOutside_of_carrier
    (T : InessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    ¬ T.maximal.diskComplement ⊆ pre.outside := by
  intro hOutside
  have hInsideDisk : pre.inside ⊆ T.maximal.diskUnion := by
    intro x hxInside
    by_contra hxDisk
    exact Set.disjoint_left.mp pre.inside_disjoint_outside hxInside (hOutside hxDisk)
  obtain ⟨W⟩ := hpre
  have hFirstRange : Set.range W.first.curve ⊆ T.maximal.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hInsideDisk (W.first.curve_mem t)
  have hSecondRange : Set.range W.second.curve ⊆ T.maximal.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hInsideDisk (W.second.curve_mem t)
  obtain ⟨i, -, hFirstDisk⟩ :=
    T.maximal.connected_range_subset_one_maximalDisk W.first hFirstRange
  obtain ⟨j, -, hSecondDisk⟩ :=
    T.maximal.connected_range_subset_one_maximalDisk W.second hSecondRange
  have hFirstZero := T.coreSystem.windingPair_eq_zero_of_range_subset_torusDisk
    i W.first hFirstDisk
  have hSecondZero := T.coreSystem.windingPair_eq_zero_of_range_subset_torusDisk
    j W.second hSecondDisk
  have hindependent := W.independent
  rw [hFirstZero, hSecondZero] at hindependent
  exact hindependent (by simp [windingDet])

theorem core_subset_preInside
    (T : InessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    T.maximal.diskComplement ⊆ pre.inside := by
  rcases T.core_subset_preInside_or_outside with hInside | hOutside
  · exact hInside
  · exact False.elim (T.not_core_subset_preOutside_of_carrier hpre hOutside)

theorem core_inside_agree (T : InessentialParityTransition pre post)
    (x : transportedTorus Phi) (hxCore : x ∈ T.maximal.diskComplement) :
    x ∈ pre.inside ↔ x ∈ post.inside := by
  by_cases hpre : x ∈ pre.inside <;> by_cases hpost : x ∈ post.inside
  · exact iff_of_true hpre hpost
  · exact False.elim <| Set.disjoint_left.mp T.core_disjoint_support hxCore
      (T.labelChange_subset_support (by simp [hpre, hpost]))
  · exact False.elim <| Set.disjoint_left.mp T.core_disjoint_support hxCore
      (T.labelChange_subset_support (by simp [hpre, hpost]))
  · exact iff_of_false hpre hpost

/-- A local all-inessential transition preserves based torus genus. -/
theorem carries_post (T : InessentialParityTransition pre post)
    (hpre : CarriesBasedLoopTorusGenus Phi pre.inside) :
    CarriesBasedLoopTorusGenus Phi post.inside := by
  have hCoreCarrier : CarriesBasedLoopTorusGenus Phi T.maximal.diskComplement :=
    carriesBasedLoopTorusGenus_of_finitePuncturePushout T.pushout.pushout
  apply hCoreCarrier.mono
  intro x hxCore
  exact (T.core_inside_agree x hxCore).mp (T.core_subset_preInside hpre hxCore)

end InessentialParityTransition

/-- A finite heterogeneous list of local inessential transitions. -/
structure FiniteInessentialParityTransitionSequence (Phi : AmbientIsotopy) where
  length : ℕ
  stage : ℕ → RegularSphereFamilyParityStage Phi
  transition : ∀ k, k < length → InessentialParityTransition (stage k) (stage (k + 1))

namespace FiniteInessentialParityTransitionSequence

/-- Ordinary finite induction propagates genus even though each transition uses a different
disk-complement core. -/
theorem carries_stage_of_le (Q : FiniteInessentialParityTransitionSequence Phi)
    (hInitial : CarriesBasedLoopTorusGenus Phi (Q.stage 0).inside) :
    ∀ k, k ≤ Q.length → CarriesBasedLoopTorusGenus Phi (Q.stage k).inside := by
  intro k
  induction k with
  | zero =>
      intro _
      exact hInitial
  | succ k ih =>
      intro hk
      have hklt : k < Q.length := Nat.lt_of_succ_le hk
      have hkPrev : k ≤ Q.length := Nat.le_trans (Nat.le_succ k) hk
      simpa [Nat.succ_eq_add_one] using (Q.transition k hklt).carries_post (ih hkPrev)

theorem carries_terminal (Q : FiniteInessentialParityTransitionSequence Phi)
    (hInitial : CarriesBasedLoopTorusGenus Phi (Q.stage 0).inside) :
    CarriesBasedLoopTorusGenus Phi (Q.stage Q.length).inside :=
  Q.carries_stage_of_le hInitial Q.length le_rfl

end FiniteInessentialParityTransitionSequence

/-! ## A concrete local inessential transition from two paired-band collars -/

/-- Data shared by the two regular smoothings of one paired excursion move.  The only remaining
local geometric disk input says that the torus part of the bands and the pre-stage boundary fit
inside one finite pairwise-disjoint inessential disk family. -/
structure PairedBandInessentialTransitionData
    (preChoice postChoice : Fin P.bandCount → Bool)
    (preCollar : PairedBandMovingSphereCollarData C preChoice)
    (postCollar : PairedBandMovingSphereCollarData C postChoice)
    (pre post : RegularSphereFamilyParityStage Phi) where
  preCarrier_eq : pre.sphereFamily.carrier = preCollar.family.patchedFamily.carrier
  postCarrier_eq : post.sphereFamily.carrier = postCollar.family.patchedFamily.carrier
  sourceImage_eq : preCollar.family.sourceImage = postCollar.family.sourceImage
  inside_agree_off_bands : ∀ (x : transportedTorus Phi),
    (x : R3) ∉ ⋃ b, P.bandNeighborhood b →
      (x ∈ pre.inside ↔ x ∈ post.inside)
  coreCircleCount : ℕ
  coreSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin coreCircleCount)
  coreAllInessential : coreSystem.AllInessential
  maximal : MaximalInessentialTorusDiskFamily coreSystem coreAllInessential
  pushout : maximal.ConnectedPushoutData
  bandPart_subset_diskUnion : transportedTorusPart Phi (⋃ b, P.bandNeighborhood b) ⊆
    maximal.diskUnion
  preBoundary_subset_diskUnion : transportedTorusPart Phi pre.sphereFamily.carrier ⊆
    maximal.diskUnion

namespace PairedBandInessentialTransitionData

variable {preChoice postChoice : Fin P.bandCount → Bool}
  {preCollar : PairedBandMovingSphereCollarData C preChoice}
  {postCollar : PairedBandMovingSphereCollarData C postChoice}
  {pre post : RegularSphereFamilyParityStage Phi}

/-- The ambient support used for the local transition: changed bands together with the old
boundary.  The latter is included so the local core misses every pre/post boundary circle. -/
def transitionSupport
    (_D : PairedBandInessentialTransitionData preChoice postChoice
      preCollar postCollar pre post) : Set R3 :=
  (⋃ b, P.bandNeighborhood b) ∪ pre.sphereFamily.carrier

theorem supportPart_subset_diskUnion
    (D : PairedBandInessentialTransitionData preChoice postChoice
      preCollar postCollar pre post) :
    transportedTorusPart Phi D.transitionSupport ⊆ D.maximal.diskUnion := by
  intro x hx
  rcases hx with hxBand | hxBoundary
  · exact D.bandPart_subset_diskUnion hxBand
  · exact D.preBoundary_subset_diskUnion hxBoundary

theorem postBoundary_subset_support
    (D : PairedBandInessentialTransitionData preChoice postChoice
      preCollar postCollar pre post) :
    transportedTorusPart Phi post.sphereFamily.carrier ⊆
      transportedTorusPart Phi D.transitionSupport := by
  intro x hxPost
  by_cases hxBand : (x : R3) ∈ ⋃ b, P.bandNeighborhood b
  · exact Or.inl hxBand
  · right
    have hxPostPatched : (x : R3) ∈
        postCollar.family.patchedFamily.carrier \ (⋃ b, P.bandNeighborhood b) := by
      exact ⟨D.postCarrier_eq ▸ hxPost, hxBand⟩
    have hxPostSource : (x : R3) ∈
        postCollar.family.sourceImage \ (⋃ b, P.bandNeighborhood b) := by
      rw [← postCollar.patchedFamily_sdiff_bandNeighborhoods_eq_source]
      exact hxPostPatched
    have hxPreSource : (x : R3) ∈
        preCollar.family.sourceImage \ (⋃ b, P.bandNeighborhood b) := by
      rw [D.sourceImage_eq]
      exact hxPostSource
    have hxPrePatched : (x : R3) ∈
        preCollar.family.patchedFamily.carrier \ (⋃ b, P.bandNeighborhood b) := by
      rw [preCollar.patchedFamily_sdiff_bandNeighborhoods_eq_source]
      exact hxPreSource
    exact D.preCarrier_eq.symm ▸ hxPrePatched.1

/-- The concrete two-collar data constructs the abstract local transition used by parity
induction. -/
def toInessentialParityTransition
    (D : PairedBandInessentialTransitionData preChoice postChoice
      preCollar postCollar pre post) :
    InessentialParityTransition pre post where
  coreCircleCount := D.coreCircleCount
  coreSystem := D.coreSystem
  coreAllInessential := D.coreAllInessential
  maximal := D.maximal
  pushout := D.pushout
  support := D.transitionSupport
  diskCover := InessentialBandDiskCover.ofSubsetDiskUnion
    D.supportPart_subset_diskUnion
  boundaries_subset_support := by
    intro x hx
    rcases hx with hxPre | hxPost
    · exact Or.inr hxPre
    · exact D.postBoundary_subset_support hxPost
  labelChange_subset_support := by
    intro x hxChange
    have hxBand : (x : R3) ∈ ⋃ b, P.bandNeighborhood b := by
      by_contra hxOff
      exact hxChange (propext (D.inside_agree_off_bands x hxOff))
    exact Or.inl hxBand

end PairedBandInessentialTransitionData

/-- At a terminal regular stage the parity-inside part is the disjoint union of the two child
cells.  This is required only at the terminal stage, not at every singular graph. -/
structure TerminalTwoSphereCoreCells
    (inside : Set (transportedTorus Phi)) where
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  isOpen_lower : IsOpen lower
  isOpen_upper : IsOpen upper
  lower_disjoint_upper : Disjoint lower upper
  inside_eq : inside = lower ∪ upper

/-- Terminal geometry tied to an actual two-component embedded sphere family. -/
structure TerminalTwoComponentSphereStage
    (stage : RegularSphereFamilyParityStage Phi)
    extends TerminalTwoSphereCoreCells stage.inside where
  sphere_count : stage.sphereFamily.count = 2

namespace TerminalTwoSphereCoreCells

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}
  {M : MaximalInessentialTorusDiskFamily S hzero}
  {support : Set R3}

private def restrictLoopToRange
    {s t : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s)
    (h : Set.range L.curve ⊆ t) : TransportedWindingLoop Phi t where
  curve := L.curve
  continuous_curve := L.continuous_curve
  periodic_curve := L.periodic_curve
  curve_mem u := h ⟨u, rfl⟩
  lift := L.lift

/-- A based carrier in the disjoint union of two open terminal cells lies wholly in one child.
The common basepoint forces both connected loop ranges to choose the same child. -/
theorem carries_lower_or_upper_of_carries_inside
    {inside : Set (transportedTorus Phi)}
    (T : TerminalTwoSphereCoreCells inside)
    (hinside : CarriesBasedLoopTorusGenus Phi inside) :
    CarriesBasedLoopTorusGenus Phi T.lower ∨
      CarriesBasedLoopTorusGenus Phi T.upper := by
  obtain ⟨W⟩ := hinside
  have hFirstUnion : Set.range W.first.curve ⊆ T.lower ∪ T.upper := by
    intro x hx
    rw [← T.inside_eq]
    obtain ⟨t, rfl⟩ := hx
    exact W.first.curve_mem t
  have hSecondUnion : Set.range W.second.curve ⊆ T.lower ∪ T.upper := by
    intro x hx
    rw [← T.inside_eq]
    obtain ⟨t, rfl⟩ := hx
    exact W.second.curve_mem t
  have hFirst := (isConnected_range W.first.continuous_curve).isPreconnected
    |>.subset_or_subset T.isOpen_lower T.isOpen_upper T.lower_disjoint_upper hFirstUnion
  have hSecond := (isConnected_range W.second.continuous_curve).isPreconnected
    |>.subset_or_subset T.isOpen_lower T.isOpen_upper T.lower_disjoint_upper hSecondUnion
  rcases hFirst with hFirstLower | hFirstUpper <;>
      rcases hSecond with hSecondLower | hSecondUpper
  · exact Or.inl ⟨{
      basepoint := W.basepoint
      first := restrictLoopToRange W.first hFirstLower
      second := restrictLoopToRange W.second hSecondLower
      first_zero := W.first_zero
      second_zero := W.second_zero
      independent := W.independent }⟩
  · exact False.elim <| Set.disjoint_left.mp T.lower_disjoint_upper
      (hFirstLower ⟨0, rfl⟩) (by rw [W.curves_zero_eq]; exact hSecondUpper ⟨0, rfl⟩)
  · exact False.elim <| Set.disjoint_left.mp T.lower_disjoint_upper
      (hSecondLower ⟨0, rfl⟩) (by rw [← W.curves_zero_eq]; exact hFirstUpper ⟨0, rfl⟩)
  · exact Or.inr ⟨{
      basepoint := W.basepoint
      first := restrictLoopToRange W.first hFirstUpper
      second := restrictLoopToRange W.second hSecondUpper
      first_zero := W.first_zero
      second_zero := W.second_zero
      independent := W.independent }⟩

/-- Invariance plus connectedness places the rank-two core in one terminal child. -/
theorem diskComplement_subset_lower_or_upper
    (I : InessentialBandCoreParityData M support)
    (T : TerminalTwoSphereCoreCells I.afterInside)
    (hconnected : IsConnected M.diskComplement)
    (hBefore : M.diskComplement ⊆ I.beforeInside) :
    M.diskComplement ⊆ T.lower ∨ M.diskComplement ⊆ T.upper := by
  have hAfter : M.diskComplement ⊆ I.afterInside :=
    I.diskComplement_subset_after_iff_before.mpr hBefore
  have hUnion : M.diskComplement ⊆ T.lower ∪ T.upper := by
    rw [← T.inside_eq]
    exact hAfter
  exact hconnected.isPreconnected.subset_or_subset T.isOpen_lower T.isOpen_upper
    T.lower_disjoint_upper hUnion

/-- The finite-pushout rank-two carrier propagates to one terminal child without an intermediate
three-cell partition. -/
theorem carriesBasedLoopGenus_lower_or_upper
    (I : InessentialBandCoreParityData M support)
    (T : TerminalTwoSphereCoreCells I.afterInside)
    (P : M.ConnectedPushoutData)
    (hBefore : M.diskComplement ⊆ I.beforeInside) :
    CarriesBasedLoopTorusGenus Phi T.lower ∨
      CarriesBasedLoopTorusGenus Phi T.upper := by
  have hCore : CarriesBasedLoopTorusGenus Phi M.diskComplement :=
    carriesBasedLoopTorusGenus_of_finitePuncturePushout P.pushout
  rcases T.diskComplement_subset_lower_or_upper I
      (MaximalInessentialTorusDiskFamily.ConnectedPushoutData.complement_isConnected M P)
      hBefore with hLower | hUpper
  · exact Or.inl (hCore.mono hLower)
  · exact Or.inr (hCore.mono hUpper)

end TerminalTwoSphereCoreCells

/-! ## Essential boundary or finite all-inessential sequence -/

namespace EventCoveredCompressingDisk

/-- Enlarge the event region retaining a compressing disk's boundary coverage. -/
def mono {a b : Set R3} (h : a ⊆ b)
    (D : EventCoveredCompressingDisk (Phi := Phi) a) :
    EventCoveredCompressingDisk (Phi := Phi) b where
  disk := D.disk
  boundary_mem_event := fun t ↦ h (D.boundary_mem_event t)

end EventCoveredCompressingDisk

/-- The finite list of honest regular stages whose boundary circles are audited for essentiality.
All stage event regions map into one common charged event region. -/
structure FiniteRegularSphereSurgeryStageSequence (Phi : AmbientIsotopy) where
  length : ℕ
  circleCount : ℕ → ℕ
  system : ∀ k, FiniteSphereSurgeryIntersectionSystem Phi (Fin (circleCount k))
  parityStage : ℕ → RegularSphereFamilyParityStage Phi
  sphereFamily_eq : ∀ k, (system k).sphereFamily = (parityStage k).sphereFamily
  commonEventRegion : Set R3
  stage_event_subset : ∀ k, k ≤ length →
    (system k).eventRegion ⊆ commonEventRegion

namespace FiniteRegularSphereSurgeryStageSequence

def AllInessential (F : FiniteRegularSphereSurgeryStageSequence Phi) : Prop :=
  ∀ k, k ≤ F.length → (F.system k).AllInessential

end FiniteRegularSphereSurgeryStageSequence

/-- Explicit data for the globally all-inessential branch.  Each transition supplies its own
local disk family and core, so circles and disk neighborhoods from different times may overlap. -/
structure AllInessentialFiniteBandResolution
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi)) where
  paritySequence : FiniteInessentialParityTransitionSequence Phi
  length_eq : paritySequence.length = F.length
  stage_eq : ∀ k, k ≤ F.length → paritySequence.stage k = F.parityStage k
  terminal : TerminalTwoComponentSphereStage
    (paritySequence.stage paritySequence.length)
  terminal_lower_eq : terminal.lower = lower
  terminal_upper_eq : terminal.upper = upper

namespace FiniteRegularSphereSurgeryStageSequence

/-- The finite regular-stage alternative.  The essential branch uses the existing resolved
innermost-circle surgery.  If no audited boundary is essential, the supplied common disk-covered
parity sequence propagates the incoming rank-two carrier to a terminal child. -/
theorem eventCoveredCompression_or_carries_terminalChild
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (hparent : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside) :
    Nonempty (EventCoveredCompressingDisk (Phi := Phi) F.commonEventRegion) ∨
      CarriesBasedLoopTorusGenus Phi lower ∨
        CarriesBasedLoopTorusGenus Phi upper := by
  classical
  by_cases hessential : ∃ k, k ≤ F.length ∧
      ∃ i, ((F.system k).circle i).Essential
  · obtain ⟨k, hk, i, hi⟩ := hessential
    obtain ⟨G⟩ := essentialSurgery k hk i hi
    obtain ⟨D⟩ := G.exists_eventCoveredCompressingDisk
    exact Or.inl ⟨EventCoveredCompressingDisk.mono (F.stage_event_subset k hk) D⟩
  · have hzero : F.AllInessential := by
      intro k hk i
      have hi : ¬ ((F.system k).circle i).Essential := fun hi ↦
        hessential ⟨k, hk, i, hi⟩
      exact not_ne_iff.mp (show
        ¬ ((F.system k).circle i).windingLoop.windingPair ≠ (0, 0) from hi)
    obtain ⟨D⟩ := inessentialResolution hzero
    have hInitial : CarriesBasedLoopTorusGenus Phi
        (D.paritySequence.stage 0).inside := by
      rw [D.stage_eq 0 (Nat.zero_le F.length)]
      exact hparent
    have hterminal := D.paritySequence.carries_terminal hInitial
    have hchildren := D.terminal.toTerminalTwoSphereCoreCells
      |>.carries_lower_or_upper_of_carries_inside hterminal
    rw [D.terminal_lower_eq, D.terminal_upper_eq] at hchildren
    exact Or.inr hchildren

end FiniteRegularSphereSurgeryStageSequence

end PairedBandMovingSphereCollarData

end Submission.Topology
