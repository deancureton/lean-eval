import Submission.PlaneSchoenflies.Schoenflies.CompleteRegionalExtension
import Submission.PlaneSchoenflies.Schoenflies.TopologicalDiskBoundaryExtension

/-!
# Extending boundary homeomorphisms across Jordan disks

The regional Schoenflies theorem identifies the closed bounded region of an arbitrary Jordan
circle with the closed unit disk.  Conjugating the Alexander extension by these identifications
extends any prescribed boundary homeomorphism across the two closed Jordan disks.
-/

namespace Schoenflies

open Metric Set

noncomputable section

namespace JordanCircle

variable (J K : JordanCircle)

/-- Extend a prescribed homeomorphism of two Jordan carriers across their closed bounded
regions. -/
noncomputable def extendBoundaryHomeomorph (b : J.carrier ≃ₜ K.carrier) :
    closure J.inside ≃ₜ closure K.inside :=
  J.regionalExtensionData.insideHomeomorph |>.trans
    (PlaneAlexander.radialHomeomorph
      (J.carrierHomeomorph.trans (b.trans K.carrierHomeomorph.symm)) |>.trans
        K.regionalExtensionData.insideHomeomorph.symm)

/-- The Jordan-disk extension agrees pointwise with the prescribed boundary map. -/
theorem extendBoundaryHomeomorph_apply (b : J.carrier ≃ₜ K.carrier) (x : J.carrier) :
    ((J.extendBoundaryHomeomorph K b)
        ⟨x, by rw [J.closure_inside]; exact Or.inr x.2⟩ : Plane) =
      (b x : Plane) := by
  let EJ := J.regionalExtensionData
  let EK := K.regionalExtensionData
  let source : sphere (0 : Plane) 1 := J.carrierHomeomorph.symm x
  let sphereMap : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
    J.carrierHomeomorph.trans (b.trans K.carrierHomeomorph.symm)
  have hsource :
      EJ.insideHomeomorph ⟨x, by rw [J.closure_inside]; exact Or.inr x.2⟩ =
        ⟨source, sphere_subset_closedBall source.2⟩ := by
    apply Subtype.ext
    exact EJ.inside_boundary x
  have hsphere : sphereMap source = K.carrierHomeomorph.symm (b x) := by
    simp only [sphereMap, source, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply]
  change (EK.insideHomeomorph.symm
      (PlaneAlexander.radialHomeomorph sphereMap
        (EJ.insideHomeomorph
          ⟨x, by rw [J.closure_inside]; exact Or.inr x.2⟩)) : Plane) = _
  rw [hsource, PlaneAlexander.radialHomeomorph_ofSphere, hsphere]
  exact EK.inside_inverse_boundary (K.carrierHomeomorph.symm (b x)) |>.trans <| by
    simp only [Homeomorph.apply_symm_apply]

end JordanCircle

end

end Schoenflies
