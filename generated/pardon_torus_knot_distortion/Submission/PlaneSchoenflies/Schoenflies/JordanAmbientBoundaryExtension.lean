import Submission.PlaneSchoenflies.Schoenflies.BallPunctureExterior
import Submission.PlaneSchoenflies.Schoenflies.ClosedCoverHomeomorph
import Submission.PlaneSchoenflies.Schoenflies.JordanDiskBoundaryExtension

/-!
# Extending Jordan-boundary homeomorphisms to the plane

Alexander extension handles the closed bounded side of a Jordan circle.  Conjugating the same
radial extension by inversion handles the closed unbounded side.  The two extensions agree on
the Jordan carrier and therefore glue to an ambient homeomorphism.
-/

namespace Schoenflies

open Metric Set

noncomputable section

namespace PlaneAlexander

private theorem sphere_ne_zero (x : sphere (0 : Plane) 1) : (x : Plane) ≠ 0 := by
  intro hx
  have := x.2
  rw [hx, mem_sphere, dist_self] at this
  norm_num at this

/-- Restrict an Alexander radial extension away from its fixed origin. -/
noncomputable def radialHomeomorphPunctured
    (h : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1) :
    {x : closedBall (0 : Plane) 1 // (x : Plane) ≠ 0} ≃ₜ
      {x : closedBall (0 : Plane) 1 // (x : Plane) ≠ 0} :=
  (radialHomeomorph h).subtype fun x ↦ by
    constructor
    · intro hx hzero
      apply hx
      have heq : radialHomeomorph h x = radialHomeomorph h ⟨0, by simp⟩ := by
        rw [radialHomeomorph_zero]
        exact Subtype.ext hzero
      exact congrArg Subtype.val ((radialHomeomorph h).injective heq)
    · intro himage hx
      apply himage
      have heq : x = (⟨0, by simp⟩ : closedBall (0 : Plane) 1) := Subtype.ext hx
      rw [heq, radialHomeomorph_zero]

/-- Radially extend a sphere homeomorphism over the closed exterior of the unit ball. -/
noncomputable def exteriorRadialHomeomorph
    (h : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1) :
    ((ball (0 : Plane) 1)ᶜ : Set Plane) ≃ₜ ((ball (0 : Plane) 1)ᶜ : Set Plane) :=
  puncturedClosedBallToExterior.symm |>.trans
    ((radialHomeomorphPunctured h).trans puncturedClosedBallToExterior)

theorem sphere_mem_exterior (x : sphere (0 : Plane) 1) :
    (x : Plane) ∈ (ball (0 : Plane) 1)ᶜ := by
  intro hx
  rw [mem_ball, x.2] at hx
  exact lt_irrefl 1 hx

/-- The exterior radial extension has the prescribed action on the unit sphere. -/
theorem exteriorRadialHomeomorph_ofSphere
    (h : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (x : sphere (0 : Plane) 1) :
    exteriorRadialHomeomorph h ⟨x, sphere_mem_exterior x⟩ =
      ⟨h x, sphere_mem_exterior (h x)⟩ := by
  let source : {z : closedBall (0 : Plane) 1 // (z : Plane) ≠ 0} :=
    ⟨⟨x, sphere_subset_closedBall x.2⟩, sphere_ne_zero x⟩
  have hsource : puncturedClosedBallToExterior source =
      ⟨x, sphere_mem_exterior x⟩ := by
    apply Subtype.ext
    exact puncturedClosedBallToExterior_boundary x
  rw [← hsource, exteriorRadialHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change (puncturedClosedBallToExterior
      (radialHomeomorphPunctured h source) : Plane) = h x
  have hradial : radialHomeomorphPunctured h source =
      ⟨⟨h x, sphere_subset_closedBall (h x).2⟩, sphere_ne_zero (h x)⟩ := by
    apply Subtype.ext
    exact radialHomeomorph_ofSphere h x
  rw [hradial]
  exact puncturedClosedBallToExterior_boundary (h x)

end PlaneAlexander

namespace JordanCircle

variable (J K : JordanCircle)

/-- Extend a prescribed Jordan-carrier homeomorphism across the closed unbounded regions. -/
noncomputable def extendOutsideBoundaryHomeomorph (b : J.carrier ≃ₜ K.carrier) :
    closure J.outside ≃ₜ closure K.outside :=
  J.regionalExtensionData.outsideHomeomorph |>.trans
    (PlaneAlexander.exteriorRadialHomeomorph
      (J.carrierHomeomorph.trans (b.trans K.carrierHomeomorph.symm)) |>.trans
        K.regionalExtensionData.outsideHomeomorph.symm)

/-- The unbounded-side extension agrees pointwise with its boundary input. -/
theorem extendOutsideBoundaryHomeomorph_apply
    (b : J.carrier ≃ₜ K.carrier) (x : J.carrier) :
    ((J.extendOutsideBoundaryHomeomorph K b)
        ⟨x, by rw [J.closure_outside]; exact Or.inr x.2⟩ : Plane) =
      (b x : Plane) := by
  let EJ := J.regionalExtensionData
  let EK := K.regionalExtensionData
  let source : sphere (0 : Plane) 1 := J.carrierHomeomorph.symm x
  let sphereMap : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
    J.carrierHomeomorph.trans (b.trans K.carrierHomeomorph.symm)
  have hsource :
      EJ.outsideHomeomorph ⟨x, by rw [J.closure_outside]; exact Or.inr x.2⟩ =
        ⟨source, PlaneAlexander.sphere_mem_exterior source⟩ := by
    apply Subtype.ext
    exact EJ.outside_boundary x
  have hsphere : sphereMap source = K.carrierHomeomorph.symm (b x) := by
    simp only [sphereMap, source, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rw [extendOutsideBoundaryHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, hsource,
    PlaneAlexander.exteriorRadialHomeomorph_ofSphere, hsphere]
  exact EK.outside_inverse_boundary (K.carrierHomeomorph.symm (b x)) |>.trans <| by
    simp only [Homeomorph.apply_symm_apply]

private theorem closure_inside_union_closure_outside :
    closure J.inside ∪ closure J.outside = Set.univ := by
  rw [J.closure_inside, J.closure_outside]
  ext x
  by_cases hx : x ∈ J.carrier
  · simp [hx]
  · rcases J.mem_inside_or_outside hx with hxInside | hxOutside
    · simp [hxInside]
    · simp [hxOutside]

variable (b : J.carrier ≃ₜ K.carrier)

private theorem boundaryExtensions_forward_agree :
    ∀ x (hxInside : x ∈ closure J.inside) (hxOutside : x ∈ closure J.outside),
      (J.extendBoundaryHomeomorph K b ⟨x, hxInside⟩ : Plane) =
        J.extendOutsideBoundaryHomeomorph K b ⟨x, hxOutside⟩ := by
  intro x hxInside hxOutside
  have hxCarrier : x ∈ J.carrier := by
    rw [J.closure_inside] at hxInside
    rw [J.closure_outside] at hxOutside
    rcases hxInside with hxInside | hxCarrier
    · rcases hxOutside with hxOutside | hxCarrier
      · exact False.elim (J.inside_disjoint_outside.notMem_of_mem_left hxInside hxOutside)
      · exact hxCarrier
    · exact hxCarrier
  let xCarrier : J.carrier := ⟨x, hxCarrier⟩
  have hxInsideArg : (⟨x, hxInside⟩ : closure J.inside) =
      ⟨xCarrier, by rw [J.closure_inside]; exact Or.inr xCarrier.2⟩ :=
    Subtype.ext rfl
  have hxOutsideArg : (⟨x, hxOutside⟩ : closure J.outside) =
      ⟨xCarrier, by rw [J.closure_outside]; exact Or.inr xCarrier.2⟩ :=
    Subtype.ext rfl
  calc
    (J.extendBoundaryHomeomorph K b ⟨x, hxInside⟩ : Plane) = b xCarrier := by
      rw [hxInsideArg]
      exact J.extendBoundaryHomeomorph_apply K b xCarrier
    _ = (J.extendOutsideBoundaryHomeomorph K b ⟨x, hxOutside⟩ : Plane) := by
      rw [hxOutsideArg]
      exact (J.extendOutsideBoundaryHomeomorph_apply K b xCarrier).symm

private theorem boundaryExtensions_backward_agree :
    ∀ y (hyInside : y ∈ closure K.inside) (hyOutside : y ∈ closure K.outside),
      ((J.extendBoundaryHomeomorph K b).symm ⟨y, hyInside⟩ : Plane) =
        ((J.extendOutsideBoundaryHomeomorph K b).symm ⟨y, hyOutside⟩ : Plane) := by
  intro y hyInside hyOutside
  have hyCarrier : y ∈ K.carrier := by
    rw [K.closure_inside] at hyInside
    rw [K.closure_outside] at hyOutside
    rcases hyInside with hyInside | hyCarrier
    · rcases hyOutside with hyOutside | hyCarrier
      · exact False.elim (K.inside_disjoint_outside.notMem_of_mem_left hyInside hyOutside)
      · exact hyCarrier
    · exact hyCarrier
  let yCarrier : K.carrier := ⟨y, hyCarrier⟩
  let xCarrier : J.carrier := b.symm yCarrier
  have hInside : J.extendBoundaryHomeomorph K b
      ⟨xCarrier, by rw [J.closure_inside]; exact Or.inr xCarrier.2⟩ =
        ⟨yCarrier, by rw [K.closure_inside]; exact Or.inr yCarrier.2⟩ := by
    apply Subtype.ext
    exact (J.extendBoundaryHomeomorph_apply K b xCarrier).trans <| by
      exact congrArg Subtype.val (b.apply_symm_apply yCarrier)
  have hOutside : J.extendOutsideBoundaryHomeomorph K b
      ⟨xCarrier, by rw [J.closure_outside]; exact Or.inr xCarrier.2⟩ =
        ⟨yCarrier, by rw [K.closure_outside]; exact Or.inr yCarrier.2⟩ := by
    apply Subtype.ext
    exact (J.extendOutsideBoundaryHomeomorph_apply K b xCarrier).trans <| by
      exact congrArg Subtype.val (b.apply_symm_apply yCarrier)
  rw [← hInside, ← hOutside, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

private noncomputable def gluedBoundaryHomeomorph :
    (closure J.inside ∪ closure J.outside : Set Plane) ≃ₜ
      (closure K.inside ∪ closure K.outside : Set Plane) :=
  ClosedCoverHomeomorph.glue isClosed_closure isClosed_closure isClosed_closure
    isClosed_closure (J.extendBoundaryHomeomorph K b)
    (J.extendOutsideBoundaryHomeomorph K b)
    (boundaryExtensions_forward_agree J K b)
    (boundaryExtensions_backward_agree J K b)

/-- Extend a prescribed homeomorphism of Jordan carriers to an ambient plane homeomorphism. -/
noncomputable def extendAmbientBoundaryHomeomorph : Plane ≃ₜ Plane :=
  (Homeomorph.Set.univ Plane).symm |>.trans
    ((Homeomorph.setCongr (J.closure_inside_union_closure_outside.symm)).trans
      ((J.gluedBoundaryHomeomorph K b).trans
        ((Homeomorph.setCongr K.closure_inside_union_closure_outside).trans
          (Homeomorph.Set.univ Plane))))

/-- The ambient extension agrees pointwise with the prescribed boundary map. -/
theorem extendAmbientBoundaryHomeomorph_apply (x : J.carrier) :
    J.extendAmbientBoundaryHomeomorph K b x = b x := by
  let hxInside : (x : Plane) ∈ closure J.inside := by
    rw [J.closure_inside]
    exact Or.inr x.2
  let source : (closure J.inside ∪ closure J.outside : Set Plane) :=
    ⟨x, Or.inl hxInside⟩
  change ((J.gluedBoundaryHomeomorph K b source :
    (closure K.inside ∪ closure K.outside : Set Plane)) : Plane) = b x
  unfold gluedBoundaryHomeomorph
  rw [ClosedCoverHomeomorph.coe_glue_apply_of_mem_left isClosed_closure
    isClosed_closure isClosed_closure isClosed_closure
    (J.extendBoundaryHomeomorph K b) (J.extendOutsideBoundaryHomeomorph K b)
    (boundaryExtensions_forward_agree J K b)
    (boundaryExtensions_backward_agree J K b) source hxInside]
  simpa only using J.extendBoundaryHomeomorph_apply K b x

/-- The ambient extension carries the source Jordan carrier exactly onto the target carrier. -/
theorem extendAmbientBoundaryHomeomorph_image_carrier :
    J.extendAmbientBoundaryHomeomorph K b '' J.carrier = K.carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [J.extendAmbientBoundaryHomeomorph_apply K b ⟨x, hx⟩]
    exact (b ⟨x, hx⟩).2
  · intro hy
    let x : J.carrier := b.symm ⟨y, hy⟩
    refine ⟨x, x.2, ?_⟩
    rw [J.extendAmbientBoundaryHomeomorph_apply K b x]
    exact congrArg Subtype.val (b.apply_symm_apply ⟨y, hy⟩)

namespace PrescribedInsideExtension

variable (insideHomeomorph : closure J.inside ≃ₜ closure K.inside)
  (boundaryHomeomorph : J.carrier ≃ₜ K.carrier)
  (inside_boundary : ∀ x : J.carrier,
    (insideHomeomorph
      ⟨x, by rw [J.closure_inside]; exact Or.inr x.2⟩ : Plane) =
        (boundaryHomeomorph x : Plane))

include inside_boundary in
private theorem forward_agree :
    ∀ x (hxInside : x ∈ closure J.inside) (hxOutside : x ∈ closure J.outside),
      (insideHomeomorph ⟨x, hxInside⟩ : Plane) =
        J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph ⟨x, hxOutside⟩ := by
  intro x hxInside hxOutside
  have hxCarrier : x ∈ J.carrier := by
    rw [J.closure_inside] at hxInside
    rw [J.closure_outside] at hxOutside
    rcases hxInside with hxInside | hxCarrier
    · rcases hxOutside with hxOutside | hxCarrier
      · exact False.elim (J.inside_disjoint_outside.notMem_of_mem_left hxInside hxOutside)
      · exact hxCarrier
    · exact hxCarrier
  let xCarrier : J.carrier := ⟨x, hxCarrier⟩
  have hxInsideArg : (⟨x, hxInside⟩ : closure J.inside) =
      ⟨xCarrier, by rw [J.closure_inside]; exact Or.inr xCarrier.2⟩ :=
    Subtype.ext rfl
  have hxOutsideArg : (⟨x, hxOutside⟩ : closure J.outside) =
      ⟨xCarrier, by rw [J.closure_outside]; exact Or.inr xCarrier.2⟩ :=
    Subtype.ext rfl
  calc
    (insideHomeomorph ⟨x, hxInside⟩ : Plane) = boundaryHomeomorph xCarrier := by
      rw [hxInsideArg]
      exact inside_boundary xCarrier
    _ = (J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph
        ⟨x, hxOutside⟩ : Plane) := by
      rw [hxOutsideArg]
      exact (J.extendOutsideBoundaryHomeomorph_apply K boundaryHomeomorph xCarrier).symm

include inside_boundary in
private theorem backward_agree :
    ∀ y (hyInside : y ∈ closure K.inside) (hyOutside : y ∈ closure K.outside),
      (insideHomeomorph.symm ⟨y, hyInside⟩ : Plane) =
        ((J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph).symm
          ⟨y, hyOutside⟩ : Plane) := by
  intro y hyInside hyOutside
  have hyCarrier : y ∈ K.carrier := by
    rw [K.closure_inside] at hyInside
    rw [K.closure_outside] at hyOutside
    rcases hyInside with hyInside | hyCarrier
    · rcases hyOutside with hyOutside | hyCarrier
      · exact False.elim (K.inside_disjoint_outside.notMem_of_mem_left hyInside hyOutside)
      · exact hyCarrier
    · exact hyCarrier
  let yCarrier : K.carrier := ⟨y, hyCarrier⟩
  let xCarrier : J.carrier := boundaryHomeomorph.symm yCarrier
  have hInside : insideHomeomorph
      ⟨xCarrier, by rw [J.closure_inside]; exact Or.inr xCarrier.2⟩ =
        ⟨yCarrier, by rw [K.closure_inside]; exact Or.inr yCarrier.2⟩ := by
    apply Subtype.ext
    exact (inside_boundary xCarrier).trans <| by
      exact congrArg Subtype.val (boundaryHomeomorph.apply_symm_apply yCarrier)
  have hOutside : J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph
      ⟨xCarrier, by rw [J.closure_outside]; exact Or.inr xCarrier.2⟩ =
        ⟨yCarrier, by rw [K.closure_outside]; exact Or.inr yCarrier.2⟩ := by
    apply Subtype.ext
    exact (J.extendOutsideBoundaryHomeomorph_apply K boundaryHomeomorph xCarrier).trans <| by
      exact congrArg Subtype.val (boundaryHomeomorph.apply_symm_apply yCarrier)
  rw [← hInside, ← hOutside, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

include inside_boundary in
private noncomputable def gluedHomeomorph :
    (closure J.inside ∪ closure J.outside : Set Plane) ≃ₜ
      (closure K.inside ∪ closure K.outside : Set Plane) :=
  ClosedCoverHomeomorph.glue isClosed_closure isClosed_closure isClosed_closure
    isClosed_closure insideHomeomorph
    (J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph)
    (forward_agree J K insideHomeomorph boundaryHomeomorph inside_boundary)
    (backward_agree J K insideHomeomorph boundaryHomeomorph inside_boundary)

include inside_boundary in
/-- Promote a prescribed closed-inside extension to an ambient plane homeomorphism without
changing that extension on the closed Jordan disk. -/
noncomputable def ambientHomeomorph : Plane ≃ₜ Plane :=
  (Homeomorph.Set.univ Plane).symm |>.trans
    ((Homeomorph.setCongr (J.closure_inside_union_closure_outside.symm)).trans
      ((gluedHomeomorph J K insideHomeomorph boundaryHomeomorph inside_boundary).trans
        ((Homeomorph.setCongr K.closure_inside_union_closure_outside).trans
          (Homeomorph.Set.univ Plane))))

include inside_boundary in
/-- The ambient promotion retains the given inside map pointwise. -/
theorem ambientHomeomorph_apply_inside (x : Plane) (hx : x ∈ closure J.inside) :
    ambientHomeomorph J K insideHomeomorph boundaryHomeomorph inside_boundary x =
      insideHomeomorph ⟨x, hx⟩ := by
  let source : (closure J.inside ∪ closure J.outside : Set Plane) :=
    ⟨x, Or.inl hx⟩
  change ((gluedHomeomorph J K insideHomeomorph boundaryHomeomorph inside_boundary source :
    (closure K.inside ∪ closure K.outside : Set Plane)) : Plane) = _
  exact ClosedCoverHomeomorph.coe_glue_apply_of_mem_left isClosed_closure
    isClosed_closure isClosed_closure isClosed_closure insideHomeomorph
    (J.extendOutsideBoundaryHomeomorph K boundaryHomeomorph)
    (forward_agree J K insideHomeomorph boundaryHomeomorph inside_boundary)
    (backward_agree J K insideHomeomorph boundaryHomeomorph inside_boundary) source hx

end PrescribedInsideExtension

end JordanCircle

end

end Schoenflies
