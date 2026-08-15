import Submission.Topology.RegularLevelComponents
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Milestones toward classification of compact one-manifolds

The classification of a nonempty compact connected Hausdorff one-manifold as a circle is not
present in the pinned Mathlib.  This module proves two substantial pieces that do not require
assuming the classification:

* compactness turns arbitrary local line charts into a finite chart cover, and therefore gives
  second countability automatically;
* a continuous periodic parametrization whose induced map from `AddCircle` is bijective gives a
  genuine homeomorphism from `Circle`, using compact-to-Hausdorff topology.

Thus the remaining classification problem is reduced to constructing one bijective cyclic
parametrization from the finite chart cover.  No classification theorem or Schoenflies result is
assumed here.
-/

open Set Topology
open scoped Topology

namespace Submission
namespace SurfaceRegularValue

noncomputable section

/-! ## Finite chart covers and second countability -/

/-- A finite family of the given local line charts covering the whole space. -/
structure FiniteLocalLineChartCover (X : Type*) [TopologicalSpace X] where
  index : Type*
  finite_index : Finite index
  chart : index → Σ x : X, LocalLineChart X x
  cover : ⋃ i, (chart i).2.source = Set.univ

/-- Compactness extracts a finite subcover from the point-indexed local chart cover. -/
def finiteLocalLineChartCoverOfCompact
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (hlocal : IsLocallyLineModeled X) : FiniteLocalLineChartCover X := by
  classical
  let C : ∀ x : X, LocalLineChart X x := fun x ↦ Classical.choice (hlocal x)
  have hcover : Set.univ ⊆ ⋃ x, (C x).source := by
    intro x _
    exact mem_iUnion.mpr ⟨x, (C x).mem_source⟩
  have hexists := isCompact_univ.elim_finite_subcover
    (fun x ↦ (C x).source) (fun x ↦ (C x).source_open) hcover
  let s := Classical.choose hexists
  have hs := Classical.choose_spec hexists
  exact {
    index := {x : X // x ∈ s}
    finite_index := inferInstance
    chart := fun x ↦ ⟨x.1, C x.1⟩
    cover := by
      apply Set.eq_univ_of_univ_subset
      intro x _
      have hx := hs (mem_univ x)
      simp only [mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨⟨y, hy⟩, hxy⟩
  }

/-- Each source in a finite local-line chart cover is second countable. -/
theorem FiniteLocalLineChartCover.secondCountable_source
    {X : Type*} [TopologicalSpace X] (F : FiniteLocalLineChartCover X) (i : F.index) :
    SecondCountableTopology (F.chart i).2.source := by
  let _ : SecondCountableTopology (F.chart i).2.target := inferInstance
  exact (F.chart i).2.equiv.secondCountableTopology

/-- A compact locally line-modelled space is automatically second countable.  In particular,
second countability is not an additional hypothesis in the compact classification problem. -/
theorem secondCountableTopology_of_compact_isLocallyLineModeled
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (hlocal : IsLocallyLineModeled X) : SecondCountableTopology X := by
  let F := finiteLocalLineChartCoverOfCompact X hlocal
  let _ : Finite F.index := F.finite_index
  let _ : Countable F.index := Finite.to_countable
  let _ (i : F.index) : SecondCountableTopology (F.chart i).2.source :=
    F.secondCountable_source i
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i ↦ (F.chart i).2.source)
    (fun i ↦ (F.chart i).2.source_open) F.cover

/-! ## The cyclic-parametrization endpoint -/

/-- The exact output of a finite cyclic chart/arc construction.

The curve is continuous and periodic, and its quotient map from `AddCircle period` is bijective.
This is weaker data than a homeomorphism: continuity of the inverse is proved below from
compactness and Hausdorffness. -/
structure CyclicLineParametrization (X : Type*) [TopologicalSpace X] where
  period : ℝ
  period_ne_zero : period ≠ 0
  curve : ℝ → X
  continuous_curve : Continuous curve
  periodic_curve : Function.Periodic curve period
  quotient_bijective : Function.Bijective periodic_curve.lift

namespace CyclicLineParametrization

variable {X : Type*} [TopologicalSpace X]

/-- The map induced on the additive circle is continuous by the quotient topology. -/
theorem continuous_lift (P : CyclicLineParametrization X) :
    Continuous P.periodic_curve.lift := by
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  convert P.continuous_curve using 1
  funext t
  exact P.periodic_curve.lift_coe t

/-- A cyclic parametrization of a Hausdorff space is a homeomorphism from its additive circle. -/
def addCircleHomeomorph [T2Space X] (P : CyclicLineParametrization X) :
    AddCircle P.period ≃ₜ X := by
  let _ : CompactSpace (AddCircle P.period) :=
    (AddCircle.homeomorphCircle P.period_ne_zero).symm.compactSpace
  exact IsHomeomorph.homeomorph P.periodic_curve.lift
    (isHomeomorph_iff_continuous_bijective.mpr ⟨P.continuous_lift, P.quotient_bijective⟩)

/-- Reparametrizing the additive circle gives the desired standard-circle homeomorphism. -/
def circleHomeomorph [T2Space X] (P : CyclicLineParametrization X) : Circle ≃ₜ X :=
  (AddCircle.homeomorphCircle P.period_ne_zero).symm.trans P.addCircleHomeomorph

end CyclicLineParametrization

/-! ## Connection to the existing component-classification interface -/

/-- Supplying the cyclic parametrization produced by the missing finite arc construction for
each component is enough to discharge `ComponentCircleClassification`. -/
def componentCircleClassificationOfCyclicParametrizations
    (X : Type*) [TopologicalSpace X] [T2Space X]
    (P : ∀ c : ConnectedComponents X, CyclicLineParametrization (componentPiece c)) :
    ComponentCircleClassification X where
  circleEquiv := fun c ↦ (P c).circleHomeomorph

/-- Every component piece is nonempty, an elementary prerequisite for its cyclic construction. -/
theorem componentPiece_nonempty
    {X : Type*} [TopologicalSpace X] (c : ConnectedComponents X) :
    (componentPiece c).Nonempty := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  exact ⟨x, hx⟩

/-- For a compact locally line-modelled space, the ambient finite chart cover and second
countability needed by a classical one-manifold proof are available without extra assumptions. -/
structure CompactConnectedLocallyLineModeledSpace
    (X : Type*) [TopologicalSpace X] : Prop where
  compact : CompactSpace X
  connected : ConnectedSpace X
  t2 : T2Space X
  nonempty : Nonempty X
  locallyLineModeled : IsLocallyLineModeled X

namespace CompactConnectedLocallyLineModeledSpace

variable {X : Type*} [TopologicalSpace X]

theorem secondCountable (H : CompactConnectedLocallyLineModeledSpace X) :
    SecondCountableTopology X := by
  let _ : CompactSpace X := H.compact
  exact secondCountableTopology_of_compact_isLocallyLineModeled X H.locallyLineModeled

def finiteChartCover (H : CompactConnectedLocallyLineModeledSpace X) :
    FiniteLocalLineChartCover X := by
  let _ : CompactSpace X := H.compact
  exact finiteLocalLineChartCoverOfCompact X H.locallyLineModeled

/-- The remaining global theorem is exactly existence of a cyclic parametrization.  Once one is
constructed from the finite charts, circle classification is immediate and contains no further
topological gap. -/
def circleHomeomorphOfCyclicParametrization
    (H : CompactConnectedLocallyLineModeledSpace X)
    (P : CyclicLineParametrization X) : Circle ≃ₜ X := by
  let _ : T2Space X := H.t2
  exact P.circleHomeomorph

end CompactConnectedLocallyLineModeledSpace

end
end SurfaceRegularValue
end Submission
