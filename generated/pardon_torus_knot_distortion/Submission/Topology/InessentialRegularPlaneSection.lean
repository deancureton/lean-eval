import Submission.Topology.InessentialSliceCircle
import Submission.Topology.RegularLevelQuotientCharts

/-!
# Loops in an inessential regular plane section

A continuous loop in the regular section lies in one connected component.  After the component
classification identifies that component with one embedded circle, the range-only theorem from
`InessentialSliceCircle` forces its torus winding to vanish whenever all section circles are
inessential.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {a b : ℝ}

/-- The finite-section argument begins with the exact classical dichotomy: either one classified
component is essential, or every component is inessential. -/
theorem exists_essential_component_or_all_components_inessential
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level)) :
    (∃ c : ConnectedComponents
        (coordinateTorusLevelSet Phi frame S.selection.level),
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent S C c).Essential) ∨
    (∀ c : ConnectedComponents
        (coordinateTorusLevelSet Phi frame S.selection.level),
      ((FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        S C c).windingLoop).windingPair = (0, 0)) := by
  classical
  by_cases h : ∃ c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level),
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent S C c).Essential
  · exact Or.inl h
  · right
    intro c
    apply not_ne_iff.mp
    intro hc
    exact h ⟨c, hc⟩

/-- Pull a transported loop in a coordinate plane back to the genuine quotient-torus level. -/
def planeSectionLevelLoop
    (S : RegularCoordinateTorusLevel Phi frame a b)
    {u : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi u)
    (hplane : ∀ t, (L.curve t : R3) ∈
      coordinateCuttingPlane frame S.selection.level) :
    ℝ → coordinateTorusLevelSet Phi frame S.selection.level :=
  fun t ↦ ⟨(transportedTorusHomeomorph Phi).symm (L.curve t), by
    change ambientCoordinate (frame 2)
      (transportedTorusMap Phi
        ((transportedTorusHomeomorph Phi).symm (L.curve t))) = S.selection.level
    have h := congrArg Subtype.val
      ((transportedTorusHomeomorph Phi).apply_symm_apply (L.curve t))
    change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm (L.curve t)) = L.curve t at h
    rw [h]
    exact hplane t⟩

theorem continuous_planeSectionLevelLoop
    (S : RegularCoordinateTorusLevel Phi frame a b)
    {u : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi u)
    (hplane : ∀ t, (L.curve t : R3) ∈
      coordinateCuttingPlane frame S.selection.level) :
    Continuous (planeSectionLevelLoop S L hplane) := by
  apply Continuous.subtype_mk
  exact (transportedTorusHomeomorph Phi).symm.continuous.comp L.continuous_curve

/-- The pulled-back loop lies in the connected component containing its value at zero. -/
theorem planeSectionLevelLoop_mem_componentPiece
    (S : RegularCoordinateTorusLevel Phi frame a b)
    {u : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi u)
    (hplane : ∀ t, (L.curve t : R3) ∈
      coordinateCuttingPlane frame S.selection.level) (t : ℝ) :
    planeSectionLevelLoop S L hplane t ∈
      componentPiece
        (ConnectedComponents.mk (planeSectionLevelLoop S L hplane 0)) := by
  rw [componentPiece, connectedComponents_preimage_singleton]
  have hconnected : IsConnected
      (Set.range (planeSectionLevelLoop S L hplane)) :=
    isConnected_range (continuous_planeSectionLevelLoop S L hplane)
  apply hconnected.subset_connectedComponent
  · exact ⟨0, rfl⟩
  · exact ⟨t, rfl⟩

/-- A loop in the section is ambiently contained in the classified embedded circle of its
connected component. -/
theorem planeSectionLoop_range_subset_componentCircle
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    {u : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi u)
    (hplane : ∀ t, (L.curve t : R3) ∈
      coordinateCuttingPlane frame S.selection.level) :
    Set.range (fun t ↦ (L.curve t : R3)) ⊆
      Set.range (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        S C (ConnectedComponents.mk (planeSectionLevelLoop S L hplane 0))).circle := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  rw [FiniteCoordinatePlaneTorusCircleFamily.component_circle_range]
  refine ⟨planeSectionLevelLoop S L hplane t,
    planeSectionLevelLoop_mem_componentPiece S L hplane t, ?_⟩
  change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm (L.curve t)) = L.curve t
  exact congrArg Subtype.val
    ((transportedTorusHomeomorph Phi).apply_symm_apply (L.curve t))

/-- If every classified component of a regular plane section is inessential, then every
transported winding loop contained in that plane section has zero winding pair. -/
theorem windingPair_eq_zero_of_planeSection_of_all_components_inessential
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (hinessential : ∀ c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level),
      ((FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent
        S C c).windingLoop).windingPair = (0, 0))
    {u : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi u)
    (hplane : ∀ t, (L.curve t : R3) ∈
      coordinateCuttingPlane frame S.selection.level) :
    L.windingPair = (0, 0) := by
  let c := ConnectedComponents.mk (planeSectionLevelLoop S L hplane 0)
  exact EmbeddedTorusIntersectionCircle.windingPair_eq_zero_of_range_subset_of_windingPair_eq_zero
      (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent S C c) L
        (planeSectionLoop_range_subset_componentCircle S C L hplane)
        (hinessential c)

end Submission.Topology
