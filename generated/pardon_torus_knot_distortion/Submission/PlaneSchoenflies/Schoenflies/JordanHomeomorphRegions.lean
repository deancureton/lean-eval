import Submission.PlaneSchoenflies.Schoenflies.JordanThetaRegions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Jordan regions under ambient homeomorphisms

An ambient homeomorphism sends a parametrized Jordan circle to another Jordan circle.  This
module records the exact point-set carrier and bounded-region formulas.  They let local arc
straightenings be used without pretending that the original curved arc is literally a Euclidean
line.
-/

namespace Schoenflies

open Metric Set Function Bornology

noncomputable section

namespace JordanCircle

/-- The image of a Jordan circle under an ambient plane homeomorphism. -/
def mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) : JordanCircle where
  parametrization := h ∘ J.parametrization
  continuous := h.continuous.comp J.continuous
  injective := h.injective.comp J.injective

@[simp]
theorem carrier_mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    (J.mapHomeomorph h).carrier = h '' J.carrier := by
  rw [carrier, mapHomeomorph, Set.range_comp]
  rfl

private theorem isBounded_image_inside (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    IsBounded (h '' J.inside) := by
  let K : Set Plane := closure J.inside
  have hKcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure J.inside_bounded.closure
  exact (hKcompact.image h.continuous).isBounded.subset
    (Set.image_mono subset_closure)

/-- Ambient homeomorphisms carry the chosen bounded Jordan component exactly to the chosen
bounded component of the image circle. -/
theorem inside_mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    (J.mapHomeomorph h).inside = h '' J.inside := by
  let K := J.mapHomeomorph h
  have hcarrier : K.carrier = h '' J.carrier := J.carrier_mapHomeomorph h
  have hx : h J.insidePoint ∈ K.carrierᶜ := by
    rw [hcarrier]
    intro hxImage
    obtain ⟨x, hxCarrier, hxEq⟩ := hxImage
    exact J.inside_subset_compl J.insidePoint_mem_inside
      (h.injective hxEq ▸ hxCarrier)
  have himageCompl : h '' J.carrierᶜ = K.carrierᶜ := by
    rw [hcarrier, h.image_compl]
  have himageComponent :
      h '' connectedComponentIn J.carrierᶜ J.insidePoint =
        connectedComponentIn K.carrierᶜ (h J.insidePoint) := by
    rw [h.image_connectedComponentIn J.insidePoint_mem, himageCompl]
  have hbounded : IsBounded
      (connectedComponentIn K.carrierᶜ (h J.insidePoint)) := by
    rw [← himageComponent]
    exact J.isBounded_image_inside h
  have hunique :=
    JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT
      K.continuous K.injective (h J.insidePoint) hx
      K.insidePoint K.insidePoint_mem hbounded K.inside_bounded
  change connectedComponentIn K.carrierᶜ K.insidePoint = h '' J.inside
  exact hunique.symm.trans himageComponent.symm

/-- The closed bounded Jordan disk is also transported exactly. -/
theorem closure_inside_mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    closure (J.mapHomeomorph h).inside = h '' closure J.inside := by
  rw [J.inside_mapHomeomorph h, h.image_closure]

/-- The inverse ambient homeomorphism recovers the original bounded region. -/
theorem preimage_inside_mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    h ⁻¹' (J.mapHomeomorph h).inside = J.inside := by
  rw [J.inside_mapHomeomorph h, h.preimage_image]

end JordanCircle

namespace JordanThetaRegions

private theorem closure_interior_closure_inside (J : JordanCircle) :
    closure (interior (closure J.inside)) = closure J.inside := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact interior_maximal subset_closure J.inside_isOpen

/-- The local two-disk filling lemma transported through one ambient straightening.  This is the
invariant form needed for curved theta edges: the original shared germ need not itself be a
Euclidean line. -/
theorem mem_interior_union_closure_inside_of_common_local_straightening
    {K₀ K₁ : JordanCircle}
    (hdisjoint : Disjoint K₀.inside K₁.inside)
    {p p' d : Plane} {r : ℝ} (h : Plane ≃ₜ Plane)
    (hp : h p = p') (hr : 0 < r)
    (hpK₀ : p ∈ K₀.carrier)
    (hlocal₀ : Metric.ball p' r ∩ (K₀.mapHomeomorph h).carrier =
      Metric.ball p' r ∩ determinantLine p' d)
    (hlocal₁ : Metric.ball p' r ∩ (K₁.mapHomeomorph h).carrier =
      Metric.ball p' r ∩ determinantLine p' d) :
    p ∈ interior (closure K₀.inside ∪ closure K₁.inside) := by
  have hdisjointImage :
      Disjoint (K₀.mapHomeomorph h).inside (K₁.mapHomeomorph h).inside := by
    rw [K₀.inside_mapHomeomorph h, K₁.inside_mapHomeomorph h, Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hxz⟩
    apply Set.disjoint_left.mp hdisjoint hx
    exact h.injective hxz.symm ▸ hz
  have hpImage : h p ∈ (K₀.mapHomeomorph h).carrier := by
    rw [K₀.carrier_mapHomeomorph h]
    exact ⟨p, hpK₀, rfl⟩
  have hinterior := mem_interior_union_closure_inside_of_common_local_line
    hdisjointImage hr (hp ▸ hpImage) hlocal₀ hlocal₁
  rw [K₀.closure_inside_mapHomeomorph h,
    K₁.closure_inside_mapHomeomorph h, ← Set.image_union,
    ← h.image_interior] at hinterior
  obtain ⟨x, hx, hxp⟩ := hinterior
  exact h.injective (hxp.trans hp.symm) ▸ hx

/-- Topological form of the theta-face theorem.  The common edge only has to be locally absent
from the frontier of the two closed child disks; a literal polygonal line model is unnecessary. -/
theorem closure_inside_eq_union_of_common_interior
    {Q K₀ K₁ : JordanCircle} {B A₀ A₁ F : Set Plane}
    (hK₀ : K₀.carrier ⊆ Q.inside ∪ Q.carrier)
    (hK₁ : K₁.carrier ⊆ Q.inside ∪ Q.carrier)
    (hQ : Q.carrier = A₀ ∪ A₁)
    (hcarrier₀ : K₀.carrier = B ∪ A₀)
    (hcarrier₁ : K₁.carrier = B ∪ A₁)
    (hA₀ : (A₀ \ K₁.carrier).Nonempty)
    (hA₁ : (A₁ \ K₀.carrier).Nonempty)
    (hF : F.Finite)
    (hlocal : ∀ p ∈ B \ F,
      p ∈ interior (closure K₀.inside ∪ closure K₁.inside)) :
    closure Q.inside = closure K₀.inside ∪ closure K₁.inside := by
  have hdisjoint : Disjoint K₀.inside K₁.inside :=
    disjoint_inside hK₀ hK₁ hQ hcarrier₀ hcarrier₁ hA₀ hA₁
  let S : Set Plane := closure K₀.inside ∪ closure K₁.inside
  have hSclosed : IsClosed S := isClosed_closure.union isClosed_closure
  have hScompact : IsCompact S :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      K₀.inside_bounded.closure).union
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure
        K₁.inside_bounded.closure)
  have hSregular : closure (interior S) = S := by
    apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hSclosed
    · rintro x (hx₀ | hx₁)
      · rw [← closure_interior_closure_inside K₀] at hx₀
        exact closure_mono (interior_mono Set.subset_union_left) hx₀
      · rw [← closure_interior_closure_inside K₁] at hx₁
        exact closure_mono (interior_mono Set.subset_union_right) hx₁
  have hSsubset : S ⊆ closure Q.inside := by
    apply Set.union_subset <;> apply closure_mono
    · exact Q.inside_subset_inside_of_carrier_subset K₀ hK₀
    · exact Q.inside_subset_inside_of_carrier_subset K₁ hK₁
  have hfrontierBasic : frontier S ⊆ K₀.carrier ∪ K₁.carrier :=
    (frontier_union_subset _ _).trans <|
      Set.union_subset
        (Set.inter_subset_left.trans <|
          (frontier_closure_subset.trans <| by rw [K₀.frontier_inside]).trans
            Set.subset_union_left)
        (Set.inter_subset_right.trans <|
          (frontier_closure_subset.trans <| by rw [K₁.frontier_inside]).trans
            Set.subset_union_right)
  have hfrontierCarrierOrFinite : frontier S ⊆ Q.carrier ∪ F := by
    intro x hxFrontier
    rcases hfrontierBasic hxFrontier with hxK₀ | hxK₁
    · rw [hcarrier₀] at hxK₀
      rcases hxK₀ with hxB | hxA₀
      · by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
            (hlocal x ⟨hxB, hxF⟩) hxFrontier
      · left
        rw [hQ]
        exact Or.inl hxA₀
    · rw [hcarrier₁] at hxK₁
      rcases hxK₁ with hxB | hxA₁
      · by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
            (hlocal x ⟨hxB, hxF⟩) hxFrontier
      · left
        rw [hQ]
        exact Or.inr hxA₁
  have hfrontierSubset : frontier S ⊆ Q.carrier := by
    have hQclosed : IsClosed Q.carrier :=
      (isCompact_range Q.continuous).isClosed
    intro x hxFrontier
    apply closure_minimal _ hQclosed <|
      frontier_subset_closure_sdiff_finite_of_regularClosed
        hSclosed hSregular hF hxFrontier
    rintro y ⟨hyFrontier, hyNotF⟩
    rcases hfrontierCarrierOrFinite hyFrontier with hyQ | hyF
    · exact hyQ
    · exact False.elim (hyNotF hyF)
  have hcarrierSubset : Q.carrier ⊆ frontier S := by
    intro x hxQ
    have hxS : x ∈ S := by
      rw [hQ] at hxQ
      rcases hxQ with hxA₀ | hxA₁
      · left
        rw [K₀.closure_inside, hcarrier₀]
        exact Or.inr (Or.inr hxA₀)
      · right
        rw [K₁.closure_inside, hcarrier₁]
        exact Or.inr (Or.inr hxA₁)
    have hOutsideCompl : Q.outside ⊆ Sᶜ := by
      intro y hyOutside hyS
      have hyClosure := hSsubset hyS
      rw [Q.closure_inside] at hyClosure
      rcases hyClosure with hyInside | hyCarrier
      · exact Set.disjoint_left.mp Q.inside_disjoint_outside
          hyInside hyOutside
      · exact Q.outside_subset_compl hyOutside hyCarrier
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hxS, ?_⟩
    apply closure_mono hOutsideCompl
    apply frontier_subset_closure
    rw [Q.frontier_outside]
    exact hxQ
  have hfrontier : frontier S = Q.carrier :=
    Set.Subset.antisymm hfrontierSubset hcarrierSubset
  have hinterior : (interior S).Nonempty := by
    refine ⟨K₀.insidePoint, ?_⟩
    apply interior_maximal _ K₀.inside_isOpen K₀.insidePoint_mem_inside
    exact subset_closure.trans Set.subset_union_left
  have hrecognized : S = closure Q.inside :=
    Q.eq_closure_inside_of_isCompact_frontier_eq
      hScompact hfrontier hinterior
  exact hrecognized.symm

end JordanThetaRegions

end

end Schoenflies
