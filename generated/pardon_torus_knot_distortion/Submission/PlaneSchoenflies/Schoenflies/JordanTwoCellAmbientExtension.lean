import Submission.PlaneSchoenflies.Schoenflies.JordanAmbientBoundaryExtension
import Submission.PlaneSchoenflies.Schoenflies.JordanTwoCellBoundaryExtension

/-!
# Ambient extension of a filled two-cell Jordan disk

When two Jordan cells fill one outer Jordan disk, their seam-compatible disk extensions form a
prescribed homeomorphism of that outer closed disk.  Matching its outer boundary with a carrier
homeomorphism promotes the filled two-cell map to the whole plane without changing either cell.
-/

namespace Schoenflies

open Set

noncomputable section

namespace JordanTwoCellAmbientExtension

/-- A two-cell presentation whose two closed cells fill one outer Jordan disk. -/
structure Presentation extends JordanTwoCellBoundaryExtension.Presentation where
  outer : JordanCircle
  closed_union :
    closure toPresentation.lower.inside ∪ closure toPresentation.upper.inside =
      closure outer.inside

namespace Presentation

variable (D : Presentation)

theorem outerCarrier_mem_cells (x : D.outer.carrier) :
    (x : Plane) ∈
      closure D.toPresentation.lower.inside ∪ closure D.toPresentation.upper.inside := by
  rw [D.closed_union, D.outer.closure_inside]
  exact Or.inr x.2

end Presentation

variable (D E : Presentation)
  (lowerBoundary : D.toPresentation.lower.carrier ≃ₜ E.toPresentation.lower.carrier)
  (upperBoundary : D.toPresentation.upper.carrier ≃ₜ E.toPresentation.upper.carrier)
  (lowerBoundary_shared : ∀ t : unitInterval,
    lowerBoundary
        ⟨D.toPresentation.shared t, D.toPresentation.shared_mem_lowerCarrier t⟩ =
      ⟨E.toPresentation.shared t, E.toPresentation.shared_mem_lowerCarrier t⟩)
  (upperBoundary_shared : ∀ t : unitInterval,
    upperBoundary
        ⟨D.toPresentation.shared t, D.toPresentation.shared_mem_upperCarrier t⟩ =
      ⟨E.toPresentation.shared t, E.toPresentation.shared_mem_upperCarrier t⟩)

private abbrev cellHomeomorph :=
  JordanTwoCellBoundaryExtension.homeomorph D.toPresentation E.toPresentation
    lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared

/-- Regard the filled two-cell map as a homeomorphism of the outer closed Jordan disks. -/
noncomputable def insideHomeomorph : closure D.outer.inside ≃ₜ closure E.outer.inside :=
  (Homeomorph.setCongr D.closed_union.symm).trans <|
    cellHomeomorph D E lowerBoundary upperBoundary lowerBoundary_shared upperBoundary_shared
      |>.trans (Homeomorph.setCongr E.closed_union)

theorem insideHomeomorph_apply_cells
    (x : Plane)
    (hx : x ∈ closure D.toPresentation.lower.inside ∪
      closure D.toPresentation.upper.inside) :
    (insideHomeomorph D E lowerBoundary upperBoundary
        lowerBoundary_shared upperBoundary_shared
        ⟨x, D.closed_union ▸ hx⟩ : Plane) =
      cellHomeomorph D E lowerBoundary upperBoundary
        lowerBoundary_shared upperBoundary_shared ⟨x, hx⟩ := by
  rfl

variable (outerBoundary : D.outer.carrier ≃ₜ E.outer.carrier)
  (cell_boundary : ∀ x : D.outer.carrier,
    (cellHomeomorph D E lowerBoundary upperBoundary
      lowerBoundary_shared upperBoundary_shared
        ⟨x, D.outerCarrier_mem_cells x⟩ : Plane) =
      (outerBoundary x : Plane))

include cell_boundary in
private theorem inside_boundary (x : D.outer.carrier) :
    (insideHomeomorph D E lowerBoundary upperBoundary
      lowerBoundary_shared upperBoundary_shared
        ⟨x, by rw [D.outer.closure_inside]; exact Or.inr x.2⟩ : Plane) =
      (outerBoundary x : Plane) := by
  rw [insideHomeomorph_apply_cells]
  exact cell_boundary x

include cell_boundary in
/-- Promote the filled two-cell map to an ambient plane homeomorphism. -/
noncomputable def ambientHomeomorph : Plane ≃ₜ Plane :=
  JordanCircle.PrescribedInsideExtension.ambientHomeomorph D.outer E.outer
    (insideHomeomorph D E lowerBoundary upperBoundary
      lowerBoundary_shared upperBoundary_shared)
    outerBoundary
    (inside_boundary D E lowerBoundary upperBoundary lowerBoundary_shared
      upperBoundary_shared outerBoundary cell_boundary)

include cell_boundary in
/-- The ambient promotion retains the original two-cell filling pointwise. -/
theorem ambientHomeomorph_apply_cells
    (x : Plane)
    (hx : x ∈ closure D.toPresentation.lower.inside ∪
      closure D.toPresentation.upper.inside) :
    ambientHomeomorph D E lowerBoundary upperBoundary lowerBoundary_shared
        upperBoundary_shared outerBoundary cell_boundary x =
      cellHomeomorph D E lowerBoundary upperBoundary
        lowerBoundary_shared upperBoundary_shared ⟨x, hx⟩ := by
  unfold ambientHomeomorph
  rw [JordanCircle.PrescribedInsideExtension.ambientHomeomorph_apply_inside]
  exact insideHomeomorph_apply_cells D E lowerBoundary upperBoundary
    lowerBoundary_shared upperBoundary_shared x hx

end JordanTwoCellAmbientExtension

end

end Schoenflies
