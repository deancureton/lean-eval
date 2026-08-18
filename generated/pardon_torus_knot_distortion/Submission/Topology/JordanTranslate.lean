import Submission.PlaneSchoenflies.Schoenflies.MoiseChapter9

/-!
# Translates of closed Jordan disks

A Jordan curve which is disjoint from a nontrivial translate of itself bounds a disk disjoint
from the corresponding translated disk.  The proof first establishes the usual nesting
trichotomy for two disjoint Jordan curves.  Nesting between a compact set and a nonzero
translate of itself is then ruled out by maximizing or minimizing the linear functional in the
translation direction.
-/

open Set Topology Bornology
open scoped RealInnerProductSpace

noncomputable section

namespace Schoenflies
namespace JordanCircle

/-- Transport a Jordan circle through an ambient homeomorphism of the plane. -/
def imageHomeomorph (J : JordanCircle) (e : Plane ≃ₜ Plane) : JordanCircle where
  parametrization := fun q ↦ e (J.parametrization q)
  continuous := e.continuous.comp J.continuous
  injective := e.injective.comp J.injective

theorem carrier_imageHomeomorph (J : JordanCircle) (e : Plane ≃ₜ Plane) :
    (J.imageHomeomorph e).carrier = e '' J.carrier := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨J.parametrization q, ⟨q, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩

/-- Ambient homeomorphisms carry the bounded complementary component to the bounded
complementary component. -/
theorem image_inside_imageHomeomorph (J : JordanCircle) (e : Plane ≃ₜ Plane) :
    e '' J.inside = (J.imageHomeomorph e).inside := by
  let K := J.imageHomeomorph e
  have hxCompl : J.insidePoint ∈ J.carrierᶜ := J.insidePoint_mem
  have heCompl : e J.insidePoint ∈ K.carrierᶜ := by
    dsimp only [K]
    rw [carrier_imageHomeomorph, ← e.image_compl]
    exact ⟨J.insidePoint, hxCompl, rfl⟩
  have hcomponent :
      e '' J.inside = connectedComponentIn K.carrierᶜ (e J.insidePoint) := by
    change e '' J.inside =
      connectedComponentIn (J.imageHomeomorph e).carrierᶜ (e J.insidePoint)
    rw [JordanCircle.inside, e.image_connectedComponentIn hxCompl, e.image_compl,
      carrier_imageHomeomorph]
  rcases K.mem_inside_or_outside heCompl with heInside | heOutside
  · exact hcomponent.trans (connectedComponentIn_eq heInside).symm
  · have himageBounded : IsBounded (e '' J.inside) := by
      apply (J.isCompact_closure_inside.image e.continuous).isBounded.subset
      exact image_mono subset_closure
    have houtsideBounded : IsBounded K.outside := by
      have houtsideEq : K.outside = e '' J.inside := by
        rw [JordanCircle.outside]
        exact (connectedComponentIn_eq heOutside).trans hcomponent.symm
      exact houtsideEq ▸ himageBounded
    exact False.elim (K.outside_unbounded houtsideBounded)

theorem image_closure_inside_imageHomeomorph (J : JordanCircle) (e : Plane ≃ₜ Plane) :
    e '' closure J.inside = closure (J.imageHomeomorph e).inside := by
  rw [e.image_closure, J.image_inside_imageHomeomorph]

/-- Translate a Jordan circle by a fixed vector. -/
def translate (J : JordanCircle) (v : Plane) : JordanCircle :=
  J.imageHomeomorph (Homeomorph.addRight v)

@[simp]
theorem carrier_translate (J : JordanCircle) (v : Plane) :
    (J.translate v).carrier = (fun x ↦ x + v) '' J.carrier := by
  exact J.carrier_imageHomeomorph (Homeomorph.addRight v)

@[simp]
theorem inside_translate (J : JordanCircle) (v : Plane) :
    (J.translate v).inside = (fun x ↦ x + v) '' J.inside := by
  exact (J.image_inside_imageHomeomorph (Homeomorph.addRight v)).symm

@[simp]
theorem closure_inside_translate (J : JordanCircle) (v : Plane) :
    closure (J.translate v).inside = (fun x ↦ x + v) '' closure J.inside := by
  exact (J.image_closure_inside_imageHomeomorph (Homeomorph.addRight v)).symm

/-- A connected Jordan carrier disjoint from another Jordan carrier lies wholly on one side. -/
theorem carrier_subset_inside_or_outside_of_disjoint
    (J K : JordanCircle) (hdisjoint : Disjoint J.carrier K.carrier) :
    K.carrier ⊆ J.inside ∨ K.carrier ⊆ J.outside := by
  have hcomplement : K.carrier ⊆ J.carrierᶜ := by
    intro x hxK hxJ
    exact Set.disjoint_left.mp hdisjoint hxJ hxK
  have hsides : K.carrier ⊆ J.inside ∪ J.outside := by
    rw [J.inside_union_outside]
    exact hcomplement
  exact K.isConnected_carrier.isPreconnected.subset_or_subset
    J.inside_isOpen J.outside_isOpen J.inside_disjoint_outside hsides

/-- If a Jordan carrier lies strictly inside another, then its whole closed disk does too. -/
theorem closure_inside_subset_inside_of_carrier_subset_inside
    (J K : JordanCircle) (hcarrier : K.carrier ⊆ J.inside) :
    closure K.inside ⊆ J.inside := by
  have hinterior : K.inside ⊆ J.inside :=
    J.inside_subset_inside_of_carrier_subset K fun x hx ↦ Or.inl (hcarrier hx)
  intro x hx
  rw [K.closure_inside] at hx
  rcases hx with hx | hx
  · exact hinterior hx
  · exact hcarrier hx

/-- Two Jordan circles with disjoint carriers have disjoint closed disks, or one closed disk is
strictly inside the other. -/
theorem disjoint_or_nested_closure_inside (J K : JordanCircle)
    (hdisjoint : Disjoint J.carrier K.carrier) :
    Disjoint (closure J.inside) (closure K.inside) ∨
      closure J.inside ⊆ K.inside ∨ closure K.inside ⊆ J.inside := by
  rcases carrier_subset_inside_or_outside_of_disjoint J K hdisjoint with
      hKInside | hKOutside
  · exact Or.inr <| Or.inr <|
      closure_inside_subset_inside_of_carrier_subset_inside J K hKInside
  · rcases carrier_subset_inside_or_outside_of_disjoint K J hdisjoint.symm with
        hJInside | hJOutside
    · exact Or.inr <| Or.inl <|
        closure_inside_subset_inside_of_carrier_subset_inside K J hJInside
    · have hJInteriorSide : J.inside ⊆ K.outside := by
        have hJInteriorAvoids : J.inside ⊆ K.carrierᶜ := by
          intro x hxJ hxK
          exact Set.disjoint_left.mp J.inside_disjoint_outside hxJ (hKOutside hxK)
        have hJInteriorSides : J.inside ⊆ K.inside ∪ K.outside := by
          rw [K.inside_union_outside]
          exact hJInteriorAvoids
        rcases J.inside_isConnected.isPreconnected.subset_or_subset
            K.inside_isOpen K.outside_isOpen K.inside_disjoint_outside
            hJInteriorSides with hsubInside | hsubOutside
        · exfalso
          obtain ⟨x, hxCarrier⟩ : J.carrier.Nonempty := by
            obtain ⟨z, hz⟩ : (Metric.sphere (0 : Plane) 1).Nonempty :=
              NormedSpace.sphere_nonempty.mpr zero_le_one
            exact ⟨J.parametrization ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
          have hxClosure : x ∈ closure J.inside := by
            rw [J.closure_inside]
            exact Or.inr hxCarrier
          have hxKClosure : x ∈ closure K.inside :=
            closure_mono hsubInside hxClosure
          rw [K.closure_inside] at hxKClosure
          rcases hxKClosure with hxKInside | hxKCarrier
          · exact Set.disjoint_left.mp K.inside_disjoint_outside
              hxKInside (hJOutside hxCarrier)
          · exact K.outside_subset_compl (hJOutside hxCarrier) hxKCarrier
        · exact hsubOutside
      left
      rw [J.closure_inside, K.closure_inside, Set.disjoint_left]
      rintro x (hxJInside | hxJCarrier) (hxKInside | hxKCarrier)
      · exact Set.disjoint_left.mp K.inside_disjoint_outside
          hxKInside (hJInteriorSide hxJInside)
      · exact Set.disjoint_left.mp J.inside_disjoint_outside
          hxJInside (hKOutside hxKCarrier)
      · exact Set.disjoint_left.mp K.inside_disjoint_outside
          hxKInside (hJOutside hxJCarrier)
      · exact Set.disjoint_left.mp hdisjoint hxJCarrier hxKCarrier

private theorem not_image_addRight_subset_self {K : Set Plane}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) {v : Plane} (hv : v ≠ 0) :
    ¬ (fun x ↦ x + v) '' K ⊆ K := by
  intro hsubset
  obtain ⟨x, hxK, hxMax⟩ := hcompact.exists_isMaxOn hnonempty
    ((continuous_id.inner continuous_const).continuousOn :
      ContinuousOn (fun y : Plane ↦ inner ℝ y v) K)
  have hxvK : x + v ∈ K := hsubset ⟨x, hxK, rfl⟩
  have hle := hxMax hxvK
  change inner ℝ (x + v) v ≤ inner ℝ x v at hle
  rw [inner_add_left, real_inner_self_eq_norm_sq] at hle
  nlinarith [sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)]

private theorem not_self_subset_image_addRight {K : Set Plane}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) {v : Plane} (hv : v ≠ 0) :
    ¬ K ⊆ (fun x ↦ x + v) '' K := by
  intro hsubset
  obtain ⟨x, hxK, hxMin⟩ := hcompact.exists_isMinOn hnonempty
    ((continuous_id.inner continuous_const).continuousOn :
      ContinuousOn (fun y : Plane ↦ inner ℝ y v) K)
  obtain ⟨y, hyK, hyx⟩ := hsubset hxK
  have hle := hxMin hyK
  change inner ℝ x v ≤ inner ℝ y v at hle
  rw [← hyx, inner_add_left, real_inner_self_eq_norm_sq] at hle
  nlinarith [sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)]

/-- If a Jordan carrier misses a nonzero translate of itself, then the corresponding closed
Jordan disks are disjoint as well. -/
theorem disjoint_closure_inside_translate (J : JordanCircle) (v : Plane) (hv : v ≠ 0)
    (hcarrier : Disjoint J.carrier ((fun x ↦ x + v) '' J.carrier)) :
    Disjoint (closure J.inside) ((fun x ↦ x + v) '' closure J.inside) := by
  let K := J.translate v
  have hKClosure : closure K.inside = (fun x ↦ x + v) '' closure J.inside := by
    change closure (J.translate v).inside = (fun x ↦ x + v) '' closure J.inside
    exact J.closure_inside_translate v
  have hcarriers : Disjoint J.carrier K.carrier := by
    simpa [K] using hcarrier
  rcases J.disjoint_or_nested_closure_inside K hcarriers with
      hdisjoint | hJNested | hKNested
  · rw [hKClosure] at hdisjoint
    exact hdisjoint
  · exfalso
    apply not_self_subset_image_addRight J.isCompact_closure_inside
      ⟨J.insidePoint, subset_closure J.insidePoint_mem_inside⟩ hv
    intro x hx
    have hxKClosure : x ∈ closure K.inside := subset_closure (hJNested hx)
    rw [hKClosure] at hxKClosure
    exact hxKClosure
  · exfalso
    apply not_image_addRight_subset_self J.isCompact_closure_inside
      ⟨J.insidePoint, subset_closure J.insidePoint_mem_inside⟩ hv
    intro x hx
    have hxKClosure : x ∈ closure K.inside := by
      rw [hKClosure]
      exact hx
    exact subset_closure (hKNested hxKClosure)

end JordanCircle
end Schoenflies
