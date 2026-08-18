import Submission.Topology.SphereCircleAxisFilling
import Submission.Topology.JordanTranslate
import Mathlib.Topology.Baire.Lemmas

/-!
# Planar nesting of circles on one embedded sphere

A pole chosen off one sphere circle gives a stereographic plane chart.  Any second circle on the
same sphere which also avoids that pole becomes a Jordan circle in the same plane.  Disjoint
ambient circles have disjoint planar carriers, so Jordan separation places the second carrier
wholly inside or wholly outside the first.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Schoenflies.JordanCircle

/-- A planar Jordan carrier is nowhere dense. -/
theorem isNowhereDense_carrier (J : JordanCircle) : IsNowhereDense J.carrier := by
  have hclosed : IsClosed J.carrier := by
    change IsClosed (Set.range J.parametrization)
    exact (isCompact_range J.continuous).isClosed
  rw [hclosed.isNowhereDense_iff, ← J.frontier_inside, ← frontier_compl]
  exact interior_frontier J.inside_isOpen.isClosed_compl

end Schoenflies.JordanCircle

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {S : EmbeddedTopologicalSphereInR3}
  {C K : EmbeddedTorusIntersectionCircle Phi}

namespace EmbeddedSphereCirclePoleData

/-- Pull a second circle through the stereographic chart selected by the first circle's pole. -/
def relativePlaneCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (z : Circle) : JordanCurve.Arcs.Plane :=
  stereographic' 2 D.pole (embeddedSphereCirclePullback S K hmem z)

theorem relativeSphereCircle_mem_stereographicSource
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle)
    (z : Circle) :
    embeddedSphereCirclePullback S K hmem z ∈ (stereographic' 2 D.pole).source := by
  rw [stereographic'_source]
  intro hz
  apply hpole
  refine ⟨z, ?_⟩
  rw [← embeddedSphereCirclePullback_parametrization S K hmem z, hz]

theorem continuous_relativePlaneCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle) :
    Continuous (D.relativePlaneCircle hmem) := by
  change Continuous ((stereographic' 2 D.pole) ∘ embeddedSphereCirclePullback S K hmem)
  rw [← continuousOn_univ]
  exact (stereographic' 2 D.pole).continuousOn.comp
    (continuous_embeddedSphereCirclePullback S K hmem).continuousOn fun z _ ↦
      D.relativeSphereCircle_mem_stereographicSource hmem hpole z

theorem injective_relativePlaneCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle) :
    Function.Injective (D.relativePlaneCircle hmem) := by
  intro z w hzw
  apply injective_embeddedSphereCirclePullback S K hmem
  exact (stereographic' 2 D.pole).injOn
    (D.relativeSphereCircle_mem_stereographicSource hmem hpole z)
    (D.relativeSphereCircle_mem_stereographicSource hmem hpole w) hzw

/-- The second sphere circle, represented as a Jordan circle in the first circle's plane chart. -/
def relativePlaneJordanCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle) :
    Schoenflies.JordanCircle where
  parametrization := D.relativePlaneCircle hmem ∘
    JordanCurve.Arcs.spherePlaneHomeoCircle
  continuous := (D.continuous_relativePlaneCircle hmem hpole).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  injective := (D.injective_relativePlaneCircle hmem hpole).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

theorem carrier_planeJordanCircle (D : EmbeddedSphereCirclePoleData S C) :
    D.planeJordanCircle.carrier = Set.range D.planeCircle := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨JordanCurve.Arcs.spherePlaneHomeoCircle z, rfl⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨JordanCurve.Arcs.spherePlaneHomeoCircle.symm z, ?_⟩
    exact congrArg D.planeCircle <|
      JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply z

/-- The pulled-back sphere circle is the inverse stereographic image of its planar carrier. -/
theorem range_sphereCircle_eq_symm_image_carrier
    (D : EmbeddedSphereCirclePoleData S C) :
    Set.range D.sphereCircle =
      (stereographic' 2 D.pole).symm '' D.planeJordanCircle.carrier := by
  rw [D.carrier_planeJordanCircle]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    refine ⟨D.planeCircle z, ⟨z, rfl⟩, ?_⟩
    exact (stereographic' 2 D.pole).left_inv
      (D.sphereCircle_mem_stereographicSource z)
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨z, ?_⟩
    exact ((stereographic' 2 D.pole).left_inv
      (D.sphereCircle_mem_stereographicSource z)).symm

/-- The pullback of one embedded circle to the standard sphere is nowhere dense. -/
theorem isNowhereDense_range_sphereCircle
    (D : EmbeddedSphereCirclePoleData S C) :
    IsNowhereDense (Set.range D.sphereCircle) := by
  rw [D.range_sphereCircle_eq_symm_image_carrier]
  apply ((stereographic' 2 D.pole).symm.isOpenEmbedding ?_).isInducing.isNowhereDense_image
  · exact D.planeJordanCircle.isNowhereDense_carrier
  · rw [OpenPartialHomeomorph.symm_source, stereographic'_target]

theorem carrier_relativePlaneJordanCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle) :
    (D.relativePlaneJordanCircle hmem hpole).carrier =
      Set.range (D.relativePlaneCircle hmem) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨JordanCurve.Arcs.spherePlaneHomeoCircle z, rfl⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨JordanCurve.Arcs.spherePlaneHomeoCircle.symm z, ?_⟩
    exact congrArg (D.relativePlaneCircle hmem) <|
      JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply z

/-- Disjoint ambient circles remain disjoint in a common stereographic chart. -/
theorem planeJordanCircle_disjoint_relativePlaneJordanCircle
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle)
    (hdisjoint : Disjoint (Set.range C.circle) (Set.range K.circle)) :
    Disjoint D.planeJordanCircle.carrier
      (D.relativePlaneJordanCircle hmem hpole).carrier := by
  rw [D.carrier_planeJordanCircle,
    D.carrier_relativePlaneJordanCircle hmem hpole, Set.disjoint_left]
  rintro x ⟨z, hz⟩ ⟨w, hw⟩
  have hpullback : D.sphereCircle z = embeddedSphereCirclePullback S K hmem w := by
    apply (stereographic' 2 D.pole).injOn
    · exact D.sphereCircle_mem_stereographicSource z
    · exact D.relativeSphereCircle_mem_stereographicSource hmem hpole w
    exact hz.trans hw.symm
  exact Set.disjoint_left.mp hdisjoint ⟨z, rfl⟩ ⟨w, by
    rw [← D.sphere_parametrization_sphereCircle z,
      ← embeddedSphereCirclePullback_parametrization S K hmem w, hpullback]⟩

/-- A disjoint second circle in the same sphere chart lies wholly inside or wholly outside the
selected first circle. -/
theorem relativePlaneCarrier_subset_inside_or_outside
    (D : EmbeddedSphereCirclePoleData S C)
    (hmem : Set.range K.circle ⊆ S.carrier)
    (hpole : S.parametrization D.pole ∉ Set.range K.circle)
    (hdisjoint : Disjoint (Set.range C.circle) (Set.range K.circle)) :
    (D.relativePlaneJordanCircle hmem hpole).carrier ⊆ D.planeJordanCircle.inside ∨
      (D.relativePlaneJordanCircle hmem hpole).carrier ⊆
        D.planeJordanCircle.outside :=
  by
    let J := D.planeJordanCircle
    let L := D.relativePlaneJordanCircle hmem hpole
    have hdisjointPlanar : Disjoint J.carrier L.carrier :=
      D.planeJordanCircle_disjoint_relativePlaneJordanCircle hmem hpole hdisjoint
    have hcomplement : L.carrier ⊆ J.carrierᶜ := by
      intro x hxL hxJ
      exact Set.disjoint_left.mp hdisjointPlanar hxJ hxL
    have hsides : L.carrier ⊆ J.inside ∪ J.outside := by
      rw [J.inside_union_outside]
      exact hcomplement
    exact L.isConnected_carrier.isPreconnected.subset_or_subset
      J.inside_isOpen J.outside_isOpen J.inside_disjoint_outside hsides

end EmbeddedSphereCirclePoleData

/-- Any embedded circle pulled back to the standard sphere is nowhere dense. -/
theorem isNowhereDense_range_embeddedSphereCirclePullback
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    IsNowhereDense (Set.range (embeddedSphereCirclePullback S C hmem)) := by
  let D := (nonempty_embeddedSphereCirclePoleData S C hmem).some
  change IsNowhereDense (Set.range D.sphereCircle)
  exact D.isNowhereDense_range_sphereCircle

/-- A finite family of embedded circles on one sphere misses a common sphere point. -/
theorem exists_sphere_point_avoiding_finite_circle_family
    {iota : Type*} [Fintype iota]
    (S : EmbeddedTopologicalSphereInR3)
    (circle : iota → EmbeddedTorusIntersectionCircle Phi)
    (hmem : ∀ i, Set.range (circle i).circle ⊆ S.carrier) :
    ∃ p : Metric.sphere (0 : R3) 1,
      ∀ i, S.parametrization p ∉ Set.range (circle i).circle := by
  classical
  by_contra havoid
  push Not at havoid
  let pullbackCarrier : iota → Set (Metric.sphere (0 : R3) 1) :=
    fun i ↦ Set.range (embeddedSphereCirclePullback S (circle i) (hmem i))
  have hmeagre : IsMeagre (⋃ i, pullbackCarrier i) :=
    isMeagre_iUnion fun i ↦
      (isNowhereDense_range_embeddedSphereCirclePullback S (circle i) (hmem i)).isMeagre
  have hcover : ⋃ i, pullbackCarrier i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨i, z, hz⟩ := havoid p
    refine Set.mem_iUnion.mpr ⟨i, ⟨z, ?_⟩⟩
    apply S.isEmbedding.injective
    rw [embeddedSphereCirclePullback_parametrization S (circle i) (hmem i) z]
    exact hz
  have hunivMeagre : IsMeagre
      (Set.univ : Set (Metric.sphere (0 : R3) 1)) := by
    rw [← hcover]
    exact hmeagre
  obtain ⟨p, hp⟩ : (Metric.sphere (0 : R3) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hunivNonempty :
      (Set.univ : Set (Metric.sphere (0 : R3) 1)).Nonempty :=
    ⟨⟨p, hp⟩, Set.mem_univ _⟩
  exact not_isMeagre_of_isOpen isOpen_univ hunivNonempty hunivMeagre

universe u

/-- A finite family of circles on one embedded sphere, together with one stereographic pole
avoiding every circle.  Using one pole is what makes the resulting planar Jordan disks directly
comparable by inclusion. -/
structure FiniteEmbeddedSphereCircleCommonPoleData
    {ι : Type u} [Fintype ι]
    (S : EmbeddedTopologicalSphereInR3)
    (circle : ι → EmbeddedTorusIntersectionCircle Phi) where
  circle_mem : ∀ i, Set.range (circle i).circle ⊆ S.carrier
  pole : Metric.sphere (0 : R3) 1
  pole_not_mem : ∀ i,
    S.parametrization pole ∉ Set.range (circle i).circle

/-- Every finite circle family lying on one sphere admits common-pole data. -/
theorem nonempty_finiteEmbeddedSphereCircleCommonPoleData
    {ι : Type u} [Fintype ι]
    (S : EmbeddedTopologicalSphereInR3)
    (circle : ι → EmbeddedTorusIntersectionCircle Phi)
    (hmem : ∀ i, Set.range (circle i).circle ⊆ S.carrier) :
    Nonempty (FiniteEmbeddedSphereCircleCommonPoleData S circle) := by
  obtain ⟨pole, hpole⟩ :=
    exists_sphere_point_avoiding_finite_circle_family S circle hmem
  exact ⟨{
    circle_mem := hmem
    pole := pole
    pole_not_mem := hpole
  }⟩

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable {ι : Type u} [Fintype ι]
  {circle : ι → EmbeddedTorusIntersectionCircle Phi}

/-- The single-circle pole package induced by the common pole. -/
def circleData
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (i : ι) :
    EmbeddedSphereCirclePoleData S (circle i) where
  circle_mem := D.circle_mem i
  pole := D.pole
  pole_not_mem := D.pole_not_mem i

/-- The closed planar Jordan disk of one circle in the common stereographic chart. -/
def closedPlaneDisk
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (i : ι) :
    Set JordanCurve.Arcs.Plane :=
  closure (D.circleData i).planeJordanCircle.inside

/-- Disjoint ambient circles remain disjoint after both are expressed in the common chart. -/
theorem planeJordanCircles_disjoint
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle)
    {i j : ι}
    (hdisjoint : Disjoint (Set.range (circle i).circle)
      (Set.range (circle j).circle)) :
    Disjoint (D.circleData i).planeJordanCircle.carrier
      (D.circleData j).planeJordanCircle.carrier := by
  rw [(D.circleData i).carrier_planeJordanCircle,
    (D.circleData j).carrier_planeJordanCircle, Set.disjoint_left]
  rintro x ⟨z, hz⟩ ⟨w, hw⟩
  have hpullback :
      (D.circleData i).sphereCircle z = (D.circleData j).sphereCircle w := by
    apply (stereographic' 2 D.pole).injOn
    · exact (D.circleData i).sphereCircle_mem_stereographicSource z
    · exact (D.circleData j).sphereCircle_mem_stereographicSource w
    exact hz.trans hw.symm
  exact Set.disjoint_left.mp hdisjoint ⟨z, rfl⟩ ⟨w, by
    rw [← (D.circleData i).sphere_parametrization_sphereCircle z,
      ← (D.circleData j).sphere_parametrization_sphereCircle w, hpullback]⟩

/-- Closed Jordan disks of two distinct members of a pairwise-disjoint common-chart family are
disjoint or nested. -/
theorem closedPlaneDisks_disjoint_or_nested
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle)
    (hpairwise : Pairwise fun i j ↦
      Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle))
    {i j : ι} (hij : i ≠ j) :
    Disjoint (D.closedPlaneDisk i) (D.closedPlaneDisk j) ∨
      D.closedPlaneDisk i ⊆ D.closedPlaneDisk j ∨
      D.closedPlaneDisk j ⊆ D.closedPlaneDisk i := by
  let J := (D.circleData i).planeJordanCircle
  let K := (D.circleData j).planeJordanCircle
  have hdisjoint : Disjoint J.carrier K.carrier :=
    D.planeJordanCircles_disjoint (hpairwise hij)
  rcases J.disjoint_or_nested_closure_inside K hdisjoint with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl <| h.trans subset_closure)
  · exact Or.inr (Or.inr <| h.trans subset_closure)

/-- Distinct closed disks lying strictly inside one selected Jordan circle. -/
def innerClosedPlaneDiskFinset
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    Finset (Set JordanCurve.Arcs.Plane) := by
  classical
  exact (Finset.univ.filter fun i ↦
    D.closedPlaneDisk i ⊆ (D.circleData outer).planeJordanCircle.inside).image
      D.closedPlaneDisk

/-- One representative circle index for a closed inner disk. -/
def innerClosedPlaneDiskIndex
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.innerClosedPlaneDiskFinset outer}) : ι := by
  classical
  exact Classical.choose (Finset.mem_image.mp A.2)

theorem innerClosedPlaneDiskIndex_spec
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.innerClosedPlaneDiskFinset outer}) :
    D.closedPlaneDisk (D.innerClosedPlaneDiskIndex outer A) = A.1 := by
  classical
  exact (Finset.mem_image.mp A.2).choose_spec.2

theorem innerClosedPlaneDiskIndex_inside
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.innerClosedPlaneDiskFinset outer}) :
    D.closedPlaneDisk (D.innerClosedPlaneDiskIndex outer A) ⊆
      (D.circleData outer).planeJordanCircle.inside := by
  classical
  have hmem := (Finset.mem_image.mp A.2).choose_spec.1
  exact (Finset.mem_filter.mp hmem).2

/-- Inclusion-maximal disk images among the disks strictly inside `outer`. -/
def inclusionMaximalInnerClosedPlaneDiskSets
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    Finset (Set JordanCurve.Arcs.Plane) := by
  classical
  exact (D.innerClosedPlaneDiskFinset outer).filter fun A ↦
    ∀ B ∈ D.innerClosedPlaneDiskFinset outer, A ⊆ B → B ⊆ A

/-- One representative index for each maximal inner disk image. -/
def inclusionMaximalInnerClosedPlaneDiskIndex
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.inclusionMaximalInnerClosedPlaneDiskSets outer}) : ι := by
  classical
  exact D.innerClosedPlaneDiskIndex outer
    ⟨A.1, (Finset.mem_filter.mp A.2).1⟩

theorem inclusionMaximalInnerClosedPlaneDiskIndex_spec
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.inclusionMaximalInnerClosedPlaneDiskSets outer}) :
    D.closedPlaneDisk (D.inclusionMaximalInnerClosedPlaneDiskIndex outer A) = A.1 := by
  classical
  exact D.innerClosedPlaneDiskIndex_spec outer
    ⟨A.1, (Finset.mem_filter.mp A.2).1⟩

/-- The selected circle indices representing the distinct maximal inner disk images. -/
def inclusionMaximalInnerClosedPlaneDiskIndices
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    Finset ι := by
  classical
  exact (D.inclusionMaximalInnerClosedPlaneDiskSets outer).attach.image
    (D.inclusionMaximalInnerClosedPlaneDiskIndex outer)

theorem inclusionMaximalInnerClosedPlaneDiskIndex_mem
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    (A : {A // A ∈ D.inclusionMaximalInnerClosedPlaneDiskSets outer}) :
    D.inclusionMaximalInnerClosedPlaneDiskIndex outer A ∈
      D.inclusionMaximalInnerClosedPlaneDiskIndices outer := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨A, by simp, rfl⟩

/-- Every inner disk lies in one selected inclusion-maximal inner disk. -/
theorem exists_inclusionMaximalInnerClosedPlaneDisk_superset
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer j : ι)
    (hj : D.closedPlaneDisk j ⊆
      (D.circleData outer).planeJordanCircle.inside) :
    ∃ k ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer,
      D.closedPlaneDisk j ⊆ D.closedPlaneDisk k := by
  classical
  let F := D.innerClosedPlaneDiskFinset outer
  have hjF : D.closedPlaneDisk j ∈ F := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  obtain ⟨A, hjA, hAmax⟩ := F.exists_le_maximal hjF
  have hAselected : A ∈ D.inclusionMaximalInnerClosedPlaneDiskSets outer := by
    apply Finset.mem_filter.mpr
    refine ⟨hAmax.1, ?_⟩
    intro B hBF hAB
    exact hAmax.2 hBF hAB
  let As : {A // A ∈ D.inclusionMaximalInnerClosedPlaneDiskSets outer} :=
    ⟨A, hAselected⟩
  refine ⟨D.inclusionMaximalInnerClosedPlaneDiskIndex outer As,
    D.inclusionMaximalInnerClosedPlaneDiskIndex_mem outer As, ?_⟩
  rw [D.inclusionMaximalInnerClosedPlaneDiskIndex_spec outer As]
  exact hjA

/-- Distinct selected maximal inner disks are disjoint. -/
theorem inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle)
    (hpairwise : Pairwise fun i j ↦
      Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle))
    (outer : ι) :
    ∀ {i}, i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer →
      ∀ {j}, j ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer → i ≠ j →
      Disjoint (D.closedPlaneDisk i) (D.closedPlaneDisk j) := by
  classical
  intro i hi j hj hij
  obtain ⟨Ai, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨Aj, _, rfl⟩ := Finset.mem_image.mp hj
  have hAiAj : Ai.1 ≠ Aj.1 := by
    intro heq
    apply hij
    exact congrArg (D.inclusionMaximalInnerClosedPlaneDiskIndex outer) (Subtype.ext heq)
  have hAi := D.inclusionMaximalInnerClosedPlaneDiskIndex_spec outer Ai
  have hAj := D.inclusionMaximalInnerClosedPlaneDiskIndex_spec outer Aj
  have hcases := D.closedPlaneDisks_disjoint_or_nested hpairwise hij
  rw [hAi, hAj] at hcases ⊢
  rcases hcases with hdisjoint | hsub | hsub
  · exact hdisjoint
  · exfalso
    apply hAiAj
    apply Set.Subset.antisymm
    · exact hsub
    · exact (Finset.mem_filter.mp Ai.2).2 Aj.1 (Finset.mem_filter.mp Aj.2).1 hsub
  · exfalso
    apply hAiAj
    apply Set.Subset.antisymm
    · exact (Finset.mem_filter.mp Aj.2).2 Ai.1 (Finset.mem_filter.mp Ai.2).1 hsub
    · exact hsub

/-- Every selected maximal disk lies strictly inside the chosen outer Jordan circle. -/
theorem inclusionMaximalInnerClosedPlaneDisk_inside
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι)
    {i : ι} (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer) :
    D.closedPlaneDisk i ⊆ (D.circleData outer).planeJordanCircle.inside := by
  classical
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hi
  rw [D.inclusionMaximalInnerClosedPlaneDiskIndex_spec outer A]
  have hinner := D.innerClosedPlaneDiskIndex_inside outer
    ⟨A.1, (Finset.mem_filter.mp A.2).1⟩
  rw [D.innerClosedPlaneDiskIndex_spec outer
    ⟨A.1, (Finset.mem_filter.mp A.2).1⟩] at hinner
  exact hinner

/-- The union of the open Jordan disks removed from the outer disk. -/
def maximalInnerOpenUnion
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    Set JordanCurve.Arcs.Plane :=
  ⋃ i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer,
    (D.circleData i).planeJordanCircle.inside

theorem isOpen_maximalInnerOpenUnion
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    IsOpen (D.maximalInnerOpenUnion outer) := by
  apply isOpen_iUnion
  intro i
  apply isOpen_iUnion
  intro _
  exact (D.circleData i).planeJordanCircle.inside_isOpen

/-- The closed part of the outer disk left after deleting all selected inner open disks. -/
def outerDiskRemainder
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    Set JordanCurve.Arcs.Plane :=
  D.closedPlaneDisk outer \ D.maximalInnerOpenUnion outer

theorem isClosed_outerDiskRemainder
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    IsClosed (D.outerDiskRemainder outer) :=
  isClosed_closure.sdiff (D.isOpen_maximalInnerOpenUnion outer)

/-- The remainder and the selected maximal inner disks exactly cover the outer closed disk. -/
theorem outerDiskRemainder_union_maximalInnerClosedPlaneDisks
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle) (outer : ι) :
    D.outerDiskRemainder outer ∪
        ⋃ i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer,
          D.closedPlaneDisk i =
      D.closedPlaneDisk outer := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact subset_closure (D.inclusionMaximalInnerClosedPlaneDisk_inside outer hi hxi)
  · intro x hx
    by_cases hinner : x ∈ D.maximalInnerOpenUnion outer
    · right
      obtain ⟨i, hinner⟩ := Set.mem_iUnion.mp hinner
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hinner
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, subset_closure hxi⟩⟩
    · exact Or.inl ⟨hx, hinner⟩

/-- The remainder meets a selected inner closed disk exactly along that disk's boundary
carrier.  This is the overlap formula used to verify compatibility of the side-coordinate map
with the inner cap map. -/
theorem outerDiskRemainder_inter_maximalInnerClosedPlaneDisk
    (D : FiniteEmbeddedSphereCircleCommonPoleData S circle)
    (hpairwise : Pairwise fun i j ↦
      Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle))
    (outer : ι) {i : ι}
    (hi : i ∈ D.inclusionMaximalInnerClosedPlaneDiskIndices outer) :
    D.outerDiskRemainder outer ∩ D.closedPlaneDisk i =
      (D.circleData i).planeJordanCircle.carrier := by
  let J := (D.circleData i).planeJordanCircle
  apply Set.Subset.antisymm
  · rintro x ⟨hxRemainder, hxDisk⟩
    rw [show D.closedPlaneDisk i = closure J.inside by rfl, J.closure_inside] at hxDisk
    rcases hxDisk with hxInside | hxCarrier
    · exfalso
      exact hxRemainder.2 <| Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, hxInside⟩⟩
    · exact hxCarrier
  · intro x hxCarrier
    have hxDisk : x ∈ D.closedPlaneDisk i := by
      rw [show D.closedPlaneDisk i = closure J.inside by rfl, J.closure_inside]
      exact Or.inr hxCarrier
    have hxOuter : x ∈ D.closedPlaneDisk outer :=
      subset_closure (D.inclusionMaximalInnerClosedPlaneDisk_inside outer hi hxDisk)
    have hxNotInner : x ∉ D.maximalInnerOpenUnion outer := by
      intro hxInner
      obtain ⟨j, hxInner⟩ := Set.mem_iUnion.mp hxInner
      obtain ⟨hj, hxInside⟩ := Set.mem_iUnion.mp hxInner
      by_cases hji : j = i
      · subst j
        exact (D.circleData i).planeJordanCircle.inside_subset_compl hxInside hxCarrier
      · have hdisjoint :=
          D.inclusionMaximalInnerClosedPlaneDiskIndices_pairwise_disjoint
            hpairwise outer hi hj (Ne.symm hji)
        exact Set.disjoint_left.mp hdisjoint hxDisk (subset_closure hxInside)
    exact ⟨⟨hxOuter, hxNotInner⟩, hxDisk⟩

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
