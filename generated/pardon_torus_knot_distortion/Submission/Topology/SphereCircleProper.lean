import Submission.Topology.EmbeddedSphereCircleDisk

/-!
# An embedded circle is a proper subset of the two-sphere

The proof uses a dimension-sensitive but elementary invariant.  Removing two points disconnects a
circle into its two open arcs, whereas stereographic projection identifies a twice-punctured
two-sphere with a plane minus one point, which is connected.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

private theorem spherePlane_compl_pair_not_isPreconnected
    {x y : Metric.sphere (0 : JordanCurve.Arcs.Plane) 1} (hxy : x ≠ y) :
    ¬ IsPreconnected ({x, y}ᶜ : Set (Metric.sphere (0 : JordanCurve.Arcs.Plane) 1)) := by
  obtain ⟨A₁, A₂, hA₁, hA₂, hunion, hinter, _, _, hpath₁, hpath₂⟩ :=
    JordanCurve.Arcs.sphere_split hxy
  intro hconnected
  have hcover : ({x, y}ᶜ : Set (Metric.sphere (0 : JordanCurve.Arcs.Plane) 1)) ⊆
      A₂ᶜ ∪ A₁ᶜ := by
    intro z hz
    have hzUnion : z ∈ A₁ ∪ A₂ := by rw [hunion]; trivial
    rcases hzUnion with hz₁ | hz₂
    · by_cases hz₂' : z ∈ A₂
      · exfalso
        apply hz
        rw [← hinter]
        exact ⟨hz₁, hz₂'⟩
      · exact Or.inl hz₂'
    · by_cases hz₁' : z ∈ A₁
      · exfalso
        apply hz
        rw [← hinter]
        exact ⟨hz₁', hz₂⟩
      · exact Or.inr hz₁'
  have hleft : (({x, y}ᶜ : Set _) ∩ A₂ᶜ).Nonempty := by
    obtain ⟨z, hzA₁, hzPair⟩ := hpath₁.nonempty
    refine ⟨z, hzPair, ?_⟩
    intro hzA₂
    apply hzPair
    rw [← hinter]
    exact ⟨hzA₁, hzA₂⟩
  have hright : (({x, y}ᶜ : Set _) ∩ A₁ᶜ).Nonempty := by
    obtain ⟨z, hzA₂, hzPair⟩ := hpath₂.nonempty
    refine ⟨z, hzPair, ?_⟩
    intro hzA₁
    apply hzPair
    rw [← hinter]
    exact ⟨hzA₁, hzA₂⟩
  obtain ⟨z, hzPair, hzA₂, hzA₁⟩ := hconnected A₂ᶜ A₁ᶜ
    hA₂.isOpen_compl hA₁.isOpen_compl hcover hleft hright
  have hzUnion : z ∈ A₁ ∪ A₂ := by rw [hunion]; trivial
  exact hzUnion.elim hzA₁ hzA₂

private instance : Fact (Module.finrank ℝ R3 = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private theorem sphereR3_compl_pair_isConnected
    {p q : Metric.sphere (0 : R3) 1} (hpq : p ≠ q) :
    IsConnected ({p, q}ᶜ : Set (Metric.sphere (0 : R3) 1)) := by
  let e := stereographic' 2 p
  have hqSource : q ∈ e.source := by
    simp only [e, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact hpq.symm
  have hsource : ({p, q}ᶜ : Set (Metric.sphere (0 : R3) 1)) ⊆ e.source := by
    intro z hz
    change z ∈ (stereographic' 2 p).source
    rw [stereographic'_source]
    intro hzp
    apply hz
    simp only [mem_insert_iff, mem_singleton_iff]
    exact Or.inl (mem_singleton_iff.mp hzp)
  have himage : e '' ({p, q}ᶜ : Set (Metric.sphere (0 : R3) 1)) = {e q}ᶜ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      intro heq
      have hzq : z = q := e.injOn (hsource hz) hqSource heq
      exact hz (by simp [hzq])
    · intro hw
      have hwTarget : w ∈ e.target := by
        change w ∈ (stereographic' 2 p).target
        rw [stereographic'_target]
        trivial
      let z := e.symm w
      have hzSource : z ∈ e.source := e.map_target hwTarget
      have hzp : z ≠ p := by
        simpa only [e, stereographic'_source, mem_compl_iff, mem_singleton_iff]
          using hzSource
      have hzq : z ≠ q := by
        intro hzq
        apply hw
        simp only [mem_singleton_iff]
        rw [← hzq]
        exact (e.right_inv hwTarget).symm
      exact ⟨z, by simp [hzp, hzq], e.right_inv hwTarget⟩
  let h : ({p, q}ᶜ : Set (Metric.sphere (0 : R3) 1)) ≃ₜ
      ({e q}ᶜ : Set JordanCurve.Arcs.Plane) :=
    e.homeomorphOfImageSubsetSource hsource himage
  rw [isConnected_iff_connectedSpace, h.connectedSpace_iff]
  exact Subtype.connectedSpace <|
    isConnected_compl_singleton_of_one_lt_rank JordanCurve.one_lt_rank_plane (e q)

/-- A topological embedding of the circle into the standard two-sphere misses a point. -/
theorem exists_sphere_point_not_mem_range
    (f : Metric.sphere (0 : JordanCurve.Arcs.Plane) 1 →
      Metric.sphere (0 : R3) 1) (hf : IsEmbedding f) :
    ∃ p, p ∉ Set.range f := by
  by_contra hproper
  push Not at hproper
  have hsurjective : Function.Surjective f := fun p ↦ hproper p
  let F := hf.toHomeomorphOfSurjective hsurjective
  let x := JordanCurve.Arcs.param 0
  let y := JordanCurve.Arcs.param Real.pi
  have hxy : x ≠ y := by
    intro h
    obtain ⟨m, hm⟩ := JordanCurve.Arcs.param_eq_iff.mp h
    have hfactor : (2 * (m : ℝ) + 1) * Real.pi = 0 := by
      nlinarith
    have hmReal : 2 * (m : ℝ) + 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right Real.pi_ne_zero
    have hmInt : 2 * m + 1 = 0 := by exact_mod_cast hmReal
    omega
  have himage : F '' ({x, y}ᶜ : Set (Metric.sphere (0 : JordanCurve.Arcs.Plane) 1)) =
      ({F x, F y}ᶜ : Set (Metric.sphere (0 : R3) 1)) := by
    rw [Set.image_compl_eq F.bijective]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have htarget : IsConnected ({F x, F y}ᶜ : Set (Metric.sphere (0 : R3) 1)) :=
    sphereR3_compl_pair_isConnected fun h ↦ hxy (F.injective h)
  have hsource : IsConnected
      ({x, y}ᶜ : Set (Metric.sphere (0 : JordanCurve.Arcs.Plane) 1)) := by
    rw [← F.isConnected_image, himage]
    exact htarget
  exact spherePlane_compl_pair_not_isPreconnected hxy hsource.isPreconnected

/-- Pull a circle on an embedded sphere back to the standard sphere. -/
def embeddedSphereCirclePullback
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) (z : Circle) :
    Metric.sphere (0 : R3) 1 :=
  S.isEmbedding.toHomeomorph.symm ⟨C.circle z, hmem ⟨z, rfl⟩⟩

theorem continuous_embeddedSphereCirclePullback
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    Continuous (embeddedSphereCirclePullback S C hmem) :=
  S.isEmbedding.toHomeomorph.symm.continuous.comp <|
    Continuous.subtype_mk C.isEmbedding.continuous fun z ↦ hmem ⟨z, rfl⟩

theorem embeddedSphereCirclePullback_parametrization
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) (z : Circle) :
    S.parametrization (embeddedSphereCirclePullback S C hmem z) = C.circle z := by
  exact congrArg Subtype.val <|
    S.isEmbedding.toHomeomorph.apply_symm_apply ⟨C.circle z, hmem ⟨z, rfl⟩⟩

theorem injective_embeddedSphereCirclePullback
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    Function.Injective (embeddedSphereCirclePullback S C hmem) := by
  intro z w hzw
  apply C.isEmbedding.injective
  rw [← embeddedSphereCirclePullback_parametrization S C hmem z,
    ← embeddedSphereCirclePullback_parametrization S C hmem w, hzw]

/-- The pulled-back circle, parametrized on the plane model of the abstract circle. -/
def embeddedSphereJordanParametrization
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    Metric.sphere (0 : JordanCurve.Arcs.Plane) 1 → Metric.sphere (0 : R3) 1 :=
  embeddedSphereCirclePullback S C hmem ∘ JordanCurve.Arcs.spherePlaneHomeoCircle

theorem isEmbedding_embeddedSphereJordanParametrization
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    IsEmbedding (embeddedSphereJordanParametrization S C hmem) := by
  have hcontinuous : Continuous (embeddedSphereJordanParametrization S C hmem) :=
    (continuous_embeddedSphereCirclePullback S C hmem).comp
      JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  have hinjective : Function.Injective (embeddedSphereJordanParametrization S C hmem) :=
    (injective_embeddedSphereCirclePullback S C hmem).comp
      JordanCurve.Arcs.spherePlaneHomeoCircle.injective
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding

/-- Every circle lying on an embedded sphere has a stereographic pole off the circle. -/
theorem nonempty_embeddedSphereCirclePoleData
    (S : EmbeddedTopologicalSphereInR3) (C : EmbeddedTorusIntersectionCircle Phi)
    (hmem : Set.range C.circle ⊆ S.carrier) :
    Nonempty (EmbeddedSphereCirclePoleData S C) := by
  obtain ⟨p, hp⟩ := exists_sphere_point_not_mem_range
    (embeddedSphereJordanParametrization S C hmem)
    (isEmbedding_embeddedSphereJordanParametrization S C hmem)
  refine ⟨{ circle_mem := hmem, pole := p, pole_not_mem := ?_ }⟩
  rintro ⟨z, hz⟩
  apply hp
  refine ⟨JordanCurve.Arcs.spherePlaneHomeoCircle.symm z, ?_⟩
  change embeddedSphereCirclePullback S C hmem
    (JordanCurve.Arcs.spherePlaneHomeoCircle
      (JordanCurve.Arcs.spherePlaneHomeoCircle.symm z)) = p
  rw [JordanCurve.Arcs.spherePlaneHomeoCircle.apply_symm_apply]
  apply S.isEmbedding.injective
  rw [embeddedSphereCirclePullback_parametrization]
  exact hz

universe u

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
  obtain ⟨z, _, hzu, hzv⟩ :=
    isPreconnected_closed_iff.mp hs u v hu hv hsub
      ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  exact Set.disjoint_left.mp huv hzu hzv

private theorem IsConnected.subset_one_of_finite_disjoint_closed
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
          (hdisjoint (Finset.mem_insert_self i I)
            (Finset.mem_insert_of_mem hj) (Ne.symm <| fun hji ↦ hi (hji ▸ hj))) hxi hxj
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

namespace FiniteEmbeddedTopologicalSphereFamilyInR3

/-- A connected nonempty subset of a finite disjoint sphere family lies on one component. -/
theorem exists_component_of_isConnected
    (F : FiniteEmbeddedTopologicalSphereFamilyInR3) {s : Set R3}
    (hs : IsConnected s) (hsub : s ⊆ F.carrier) :
    ∃ i : Fin F.count, s ⊆ (F.sphere i).carrier := by
  classical
  have hsub' : s ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin F.count)),
      (F.sphere i).carrier := by
    simpa [FiniteEmbeddedTopologicalSphereFamilyInR3.carrier] using hsub
  obtain ⟨i, _, hi⟩ := IsConnected.subset_one_of_finite_disjoint_closed
    hs Finset.univ (fun i ↦ (F.sphere i).carrier)
    (fun i _ ↦ (F.sphere i).isClosed_carrier)
    (fun {i} _ {j} _ hij ↦ F.pairwise_disjoint hij) hsub'
  exact ⟨i, hi⟩

end FiniteEmbeddedTopologicalSphereFamilyInR3

/-- Component assignments for circles on a finite family of embedded spheres. -/
structure FiniteEmbeddedSphereCircleComponentData
    {ι : Type u} (F : FiniteEmbeddedTopologicalSphereFamilyInR3)
    (circle : ι → EmbeddedTorusIntersectionCircle Phi) where
  component : ι → Fin F.count
  circle_mem : ∀ i, Set.range (circle i).circle ⊆ (F.sphere (component i)).carrier

namespace FiniteEmbeddedSphereCircleComponentData

variable {ι : Type*} {F : FiniteEmbeddedTopologicalSphereFamilyInR3}
  {circle : ι → EmbeddedTorusIntersectionCircle Phi}

/-- Properness of embedded circles chooses all off-circle poles automatically. -/
def toPoleData (D : FiniteEmbeddedSphereCircleComponentData F circle) :
    FiniteEmbeddedSphereCirclePoleData F circle where
  component := D.component
  circle_mem := D.circle_mem
  pole i := (nonempty_embeddedSphereCirclePoleData
    (F.sphere (D.component i)) (circle i) (D.circle_mem i)).some.pole
  pole_not_mem i := (nonempty_embeddedSphereCirclePoleData
    (F.sphere (D.component i)) (circle i) (D.circle_mem i)).some.pole_not_mem

end FiniteEmbeddedSphereCircleComponentData

end Submission.Topology
