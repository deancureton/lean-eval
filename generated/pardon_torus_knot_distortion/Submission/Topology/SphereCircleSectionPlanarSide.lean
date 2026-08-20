import Submission.Topology.SphereCircleComponentSection

/-!
# Planar side localization for an exact sphere-component circle section

An exact finite torus-circle section of one embedded sphere is enough to localize the canonical
punctured outer disk to one closed side of the transported torus.  This component-local version
does not require an ambient finite sphere-stage object or a containment in a larger sphere family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {S : EmbeddedTopologicalSphereInR3}
  {iota : Type*} [Fintype iota]

namespace FiniteEmbeddedSphereCircleCommonPoleData

variable
  {circleSection : FiniteEmbeddedTorusCircleSection Phi
    (S.carrier ∩ transportedTorus Phi) iota}
  (D : FiniteEmbeddedSphereCircleCommonPoleData S circleSection.circle)
  (outer : iota)

/-- The transported-torus gauge of the component-local punctured remainder. -/
def sectionOuterDiskRemainderGauge : D.outerDiskRemainder outer → ℝ :=
  fun x ↦ tubeGauge (Phi.H 1 (D.outerDiskRemainderAmbientMap outer x))

theorem continuous_sectionOuterDiskRemainderGauge :
    Continuous (D.sectionOuterDiskRemainderGauge outer) :=
  continuous_tubeGauge.comp <|
    (continuous_timeOne_map Phi).comp (D.continuous_outerDiskRemainderAmbientMap outer)

/-- A connected dense component-local remainder core whose ambient image misses the torus. -/
structure SectionConnectedTorusFreeRemainderCoreData where
  core : Set (D.outerDiskRemainder outer)
  isConnected_core : IsConnected core
  dense_core : closure core = Set.univ
  core_disjoint_torus : ∀ x ∈ core,
    D.outerDiskRemainderAmbientMap outer x ∉ transportedTorus Phi

/-- Exact component intersection and strict planar nesting make the canonical core torus-free. -/
theorem sectionOuterDiskRemainderCore_disjoint_torus
    (x : D.outerDiskRemainder outer) (hx : x ∈ D.outerDiskRemainderCore outer) :
    D.outerDiskRemainderAmbientMap outer x ∉ transportedTorus Phi := by
  intro hxTorus
  have hxSphere : D.outerDiskRemainderAmbientMap outer x ∈ S.carrier := by
    exact ⟨(stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane), rfl⟩
  have hxIntersection : D.outerDiskRemainderAmbientMap outer x ∈
      S.carrier ∩ transportedTorus Phi := ⟨hxSphere, hxTorus⟩
  have hxUnion : D.outerDiskRemainderAmbientMap outer x ∈
      ⋃ i, Set.range (circleSection.circle i).circle :=
    circleSection.section_exact ▸ hxIntersection
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hxUnion
  have hsphereEq :
      (stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane) =
        (D.circleData j).sphereCircle z := by
    apply S.isEmbedding.injective
    rw [(D.circleData j).sphere_parametrization_sphereCircle]
    exact hz.symm
  have hxPlane : (x : JordanCurve.Arcs.Plane) = (D.circleData j).planeCircle z := by
    calc
      (x : JordanCurve.Arcs.Plane) =
          (stereographic' 2 D.pole)
            ((stereographic' 2 D.pole).symm (x : JordanCurve.Arcs.Plane)) := by
        symm
        apply (stereographic' 2 D.pole).right_inv
        rw [stereographic'_target]
        trivial
      _ = (stereographic' 2 D.pole) ((D.circleData j).sphereCircle z) :=
        congrArg (stereographic' 2 D.pole) hsphereEq
      _ = (D.circleData j).planeCircle z := rfl
  have hxCarrier : (x : JordanCurve.Arcs.Plane) ∈
      (D.circleData j).planeJordanCircle.carrier := by
    rw [(D.circleData j).carrier_planeJordanCircle]
    exact ⟨z, hxPlane.symm⟩
  change (x : JordanCurve.Arcs.Plane) ∈ D.outerDiskOpenCore outer at hx
  obtain ⟨hxOuter, hxNotClosed⟩ := hx
  by_cases hjo : j = outer
  · subst j
    exact (D.circleData outer).planeJordanCircle.inside_subset_compl hxOuter hxCarrier
  · have hjInside := D.closedPlaneDisk_subset_inside_of_carrier_meets_inside
      circleSection.pairwise_disjoint hjo hxOuter hxCarrier
    obtain ⟨k, hk, hjk⟩ :=
      D.exists_inclusionMaximalInnerClosedPlaneDisk_superset outer j hjInside
    have hxJDisk : (x : JordanCurve.Arcs.Plane) ∈ D.closedPlaneDisk j := by
      rw [show D.closedPlaneDisk j =
        closure (D.circleData j).planeJordanCircle.inside by rfl,
        (D.circleData j).planeJordanCircle.closure_inside]
      exact Or.inr hxCarrier
    apply hxNotClosed
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hjk hxJDisk⟩⟩

/-- The canonical connected core supplies the component-local torus-free core package. -/
def canonicalSectionConnectedTorusFreeRemainderCoreData :
    D.SectionConnectedTorusFreeRemainderCoreData outer where
  core := D.outerDiskRemainderCore outer
  isConnected_core := D.isConnected_outerDiskRemainderCore
    circleSection.pairwise_disjoint outer
  dense_core := dense_iff_closure_eq.mp
    (D.dense_outerDiskRemainderCore circleSection.pairwise_disjoint outer)
  core_disjoint_torus :=
    D.sectionOuterDiskRemainderCore_disjoint_torus outer

namespace SectionConnectedTorusFreeRemainderCoreData

variable (G : D.SectionConnectedTorusFreeRemainderCoreData outer)

include G in
/-- A connected dense torus-free component core places the full closed remainder on one side. -/
theorem liesOnOneTorusSide :
    (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) ∨
      (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) := by
  let low : Set (D.outerDiskRemainder outer) :=
    {x | D.sectionOuterDiskRemainderGauge outer x < 1}
  let high : Set (D.outerDiskRemainder outer) :=
    {x | 1 < D.sectionOuterDiskRemainderGauge outer x}
  have hlowOpen : IsOpen low :=
    isOpen_lt (D.continuous_sectionOuterDiskRemainderGauge outer) continuous_const
  have hhighOpen : IsOpen high :=
    isOpen_lt continuous_const (D.continuous_sectionOuterDiskRemainderGauge outer)
  have hdisjoint : Disjoint low high := by
    rw [Set.disjoint_left]
    intro x hxLow hxHigh
    change D.sectionOuterDiskRemainderGauge outer x < 1 at hxLow
    change 1 < D.sectionOuterDiskRemainderGauge outer x at hxHigh
    linarith
  have hcover : SectionConnectedTorusFreeRemainderCoreData.core G ⊆ low ∪ high := by
    intro x hx
    have hne : D.sectionOuterDiskRemainderGauge outer x ≠ 1 := by
      intro heq
      exact SectionConnectedTorusFreeRemainderCoreData.core_disjoint_torus G x hx <|
        mem_transportedTorus_of_tubeGauge_timeOne_eq_one Phi heq
    rcases lt_or_gt_of_ne hne with hlow | hhigh
    · exact Or.inl hlow
    · exact Or.inr hhigh
  rcases (SectionConnectedTorusFreeRemainderCoreData.isConnected_core G).isPreconnected
      |>.subset_or_subset
      hlowOpen hhighOpen hdisjoint hcover with hlow | hhigh
  · left
    have hclosed : IsClosed
        {x : D.outerDiskRemainder outer | D.sectionOuterDiskRemainderGauge outer x ≤ 1} :=
      isClosed_le (D.continuous_sectionOuterDiskRemainderGauge outer) continuous_const
    have hclosure : closure (SectionConnectedTorusFreeRemainderCoreData.core G) ⊆
        {x : D.outerDiskRemainder outer | D.sectionOuterDiskRemainderGauge outer x ≤ 1} :=
      closure_minimal (by
        intro x hx
        have hxLow := hlow hx
        change D.sectionOuterDiskRemainderGauge outer x < 1 at hxLow
        exact hxLow.le) hclosed
    rw [SectionConnectedTorusFreeRemainderCoreData.dense_core G] at hclosure
    exact fun x ↦ hclosure (Set.mem_univ x)
  · right
    have hclosed : IsClosed
        {x : D.outerDiskRemainder outer | 1 ≤ D.sectionOuterDiskRemainderGauge outer x} :=
      isClosed_le continuous_const (D.continuous_sectionOuterDiskRemainderGauge outer)
    have hclosure : closure (SectionConnectedTorusFreeRemainderCoreData.core G) ⊆
        {x : D.outerDiskRemainder outer | 1 ≤ D.sectionOuterDiskRemainderGauge outer x} :=
      closure_minimal (by
        intro x hx
        have hxHigh := hhigh hx
        change 1 < D.sectionOuterDiskRemainderGauge outer x at hxHigh
        exact hxHigh.le) hclosed
    rw [SectionConnectedTorusFreeRemainderCoreData.dense_core G] at hclosure
    exact fun x ↦ hclosure (Set.mem_univ x)

end SectionConnectedTorusFreeRemainderCoreData

/-- An exact component section places every canonical punctured outer disk on one torus side. -/
theorem canonicalSectionOuterDiskRemainder_liesOnOneTorusSide :
    (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedTubeSide Phi) ∨
      (∀ x, D.outerDiskRemainderAmbientMap outer x ∈ transportedExteriorSide Phi) :=
  SectionConnectedTorusFreeRemainderCoreData.liesOnOneTorusSide
    (G := D.canonicalSectionConnectedTorusFreeRemainderCoreData outer)

end FiniteEmbeddedSphereCircleCommonPoleData

end Submission.Topology
