import Submission.PlaneSchoenflies.Schoenflies.ClosedCoverHomeomorph
import Submission.PlaneSchoenflies.Schoenflies.JordanDiskBoundaryExtension

/-!
# Gluing two Jordan-disk extensions along a shared seam

Two closed Jordan disks whose intersection is one parametrized boundary seam can be mapped
cellwise and glued.  Pointwise agreement of the two boundary maps on that seam gives agreement
of both the extended maps and their inverses.
-/

namespace Schoenflies

open Set Function

noncomputable section

namespace JordanTwoCellBoundaryExtension

/-- Two closed Jordan disks meeting exactly along one parametrized boundary seam. -/
structure Presentation where
  lower : JordanCircle
  upper : JordanCircle
  startPoint : Plane
  endPoint : Plane
  shared : Path startPoint endPoint
  shared_lower : range shared ⊆ lower.carrier
  shared_upper : range shared ⊆ upper.carrier
  closed_inter : closure lower.inside ∩ closure upper.inside = range shared

namespace Presentation

variable (D : Presentation)

theorem shared_mem_lowerCarrier (t : unitInterval) : D.shared t ∈ D.lower.carrier :=
  D.shared_lower ⟨t, rfl⟩

theorem shared_mem_upperCarrier (t : unitInterval) : D.shared t ∈ D.upper.carrier :=
  D.shared_upper ⟨t, rfl⟩

theorem shared_mem_lowerClosed (t : unitInterval) : D.shared t ∈ closure D.lower.inside := by
  rw [D.lower.closure_inside]
  exact Or.inr (D.shared_mem_lowerCarrier t)

theorem shared_mem_upperClosed (t : unitInterval) : D.shared t ∈ closure D.upper.inside := by
  rw [D.upper.closure_inside]
  exact Or.inr (D.shared_mem_upperCarrier t)

end Presentation

variable (D E : Presentation)
  (lowerBoundary : D.lower.carrier ≃ₜ E.lower.carrier)
  (upperBoundary : D.upper.carrier ≃ₜ E.upper.carrier)
  (lowerBoundary_shared : ∀ t : unitInterval,
    lowerBoundary ⟨D.shared t, D.shared_mem_lowerCarrier t⟩ =
      ⟨E.shared t, E.shared_mem_lowerCarrier t⟩)
  (upperBoundary_shared : ∀ t : unitInterval,
    upperBoundary ⟨D.shared t, D.shared_mem_upperCarrier t⟩ =
      ⟨E.shared t, E.shared_mem_upperCarrier t⟩)

include lowerBoundary_shared upperBoundary_shared in
private theorem forward_agree :
    ∀ x (hxLower : x ∈ closure D.lower.inside) (hxUpper : x ∈ closure D.upper.inside),
      (D.lower.extendBoundaryHomeomorph E.lower lowerBoundary ⟨x, hxLower⟩ : Plane) =
        D.upper.extendBoundaryHomeomorph E.upper upperBoundary ⟨x, hxUpper⟩ := by
  intro x hxLower hxUpper
  have hxShared : x ∈ range D.shared := by
    rw [← D.closed_inter]
    exact ⟨hxLower, hxUpper⟩
  obtain ⟨t, rfl⟩ := hxShared
  calc
    (D.lower.extendBoundaryHomeomorph E.lower lowerBoundary
        ⟨D.shared t, hxLower⟩ : Plane) =
        (lowerBoundary ⟨D.shared t, D.shared_mem_lowerCarrier t⟩ : Plane) := by
      simpa only using D.lower.extendBoundaryHomeomorph_apply E.lower lowerBoundary
        ⟨D.shared t, D.shared_mem_lowerCarrier t⟩
    _ = E.shared t := congrArg Subtype.val (lowerBoundary_shared t)
    _ = (upperBoundary ⟨D.shared t, D.shared_mem_upperCarrier t⟩ : Plane) :=
      (congrArg Subtype.val (upperBoundary_shared t)).symm
    _ = D.upper.extendBoundaryHomeomorph E.upper upperBoundary
        ⟨D.shared t, hxUpper⟩ := by
      simpa only using (D.upper.extendBoundaryHomeomorph_apply E.upper upperBoundary
        ⟨D.shared t, D.shared_mem_upperCarrier t⟩).symm

include lowerBoundary_shared upperBoundary_shared in
private theorem backward_agree :
    ∀ y (hyLower : y ∈ closure E.lower.inside) (hyUpper : y ∈ closure E.upper.inside),
      ((D.lower.extendBoundaryHomeomorph E.lower lowerBoundary).symm ⟨y, hyLower⟩ : Plane) =
        ((D.upper.extendBoundaryHomeomorph E.upper upperBoundary).symm ⟨y, hyUpper⟩ :
          Plane) := by
  intro y hyLower hyUpper
  have hyShared : y ∈ range E.shared := by
    rw [← E.closed_inter]
    exact ⟨hyLower, hyUpper⟩
  obtain ⟨t, rfl⟩ := hyShared
  let xLower : closure D.lower.inside := ⟨D.shared t, D.shared_mem_lowerClosed t⟩
  let xUpper : closure D.upper.inside := ⟨D.shared t, D.shared_mem_upperClosed t⟩
  have hLower : D.lower.extendBoundaryHomeomorph E.lower lowerBoundary xLower =
      ⟨E.shared t, E.shared_mem_lowerClosed t⟩ := by
    apply Subtype.ext
    exact (D.lower.extendBoundaryHomeomorph_apply E.lower lowerBoundary
      ⟨D.shared t, D.shared_mem_lowerCarrier t⟩).trans
        (congrArg Subtype.val (lowerBoundary_shared t))
  have hUpper : D.upper.extendBoundaryHomeomorph E.upper upperBoundary xUpper =
      ⟨E.shared t, E.shared_mem_upperClosed t⟩ := by
    apply Subtype.ext
    exact (D.upper.extendBoundaryHomeomorph_apply E.upper upperBoundary
      ⟨D.shared t, D.shared_mem_upperCarrier t⟩).trans
        (congrArg Subtype.val (upperBoundary_shared t))
  rw [← hLower, ← hUpper, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

/-- Glue the two closed-disk extensions into a homeomorphism of their unions. -/
noncomputable def homeomorph :
    (closure D.lower.inside ∪ closure D.upper.inside : Set Plane) ≃ₜ
      (closure E.lower.inside ∪ closure E.upper.inside : Set Plane) :=
  ClosedCoverHomeomorph.glue isClosed_closure isClosed_closure isClosed_closure
    isClosed_closure (D.lower.extendBoundaryHomeomorph E.lower lowerBoundary)
    (D.upper.extendBoundaryHomeomorph E.upper upperBoundary)
    (forward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)
    (backward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)

/-- On the lower cell, the glued map is exactly the chosen lower-disk extension. -/
theorem homeomorph_apply_lower (x : Plane) (hx : x ∈ closure D.lower.inside) :
    (homeomorph D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared
        ⟨x, Or.inl hx⟩ : Plane) =
      D.lower.extendBoundaryHomeomorph E.lower lowerBoundary ⟨x, hx⟩ :=
  ClosedCoverHomeomorph.coe_glue_apply_of_mem_left isClosed_closure isClosed_closure
    isClosed_closure isClosed_closure
    (D.lower.extendBoundaryHomeomorph E.lower lowerBoundary)
    (D.upper.extendBoundaryHomeomorph E.upper upperBoundary)
    (forward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)
    (backward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)
    _ hx

/-- On the upper cell, the glued map is exactly the chosen upper-disk extension. -/
theorem homeomorph_apply_upper (x : Plane) (hx : x ∈ closure D.upper.inside) :
    (homeomorph D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared
        ⟨x, Or.inr hx⟩ : Plane) =
      D.upper.extendBoundaryHomeomorph E.upper upperBoundary ⟨x, hx⟩ :=
  ClosedCoverHomeomorph.coe_glue_apply_of_mem_right isClosed_closure isClosed_closure
    isClosed_closure isClosed_closure
    (D.lower.extendBoundaryHomeomorph E.lower lowerBoundary)
    (D.upper.extendBoundaryHomeomorph E.upper upperBoundary)
    (forward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)
    (backward_agree D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared)
    _ hx

end JordanTwoCellBoundaryExtension

end

end Schoenflies
