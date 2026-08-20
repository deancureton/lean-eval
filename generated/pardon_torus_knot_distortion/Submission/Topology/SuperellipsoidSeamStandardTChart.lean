import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Standard endpoint charts for a superellipsoid seam

The inverse-function chart for the polynomial/height pair has target coordinates
`(outerPolynomial, height)`.  This file normalizes those coordinates at a seam point so that
the inward cutting-disk branch points into the standard horizontal band, while the outer
superellipsoid branch becomes the standard vertical branch.  The left endpoint is sent to
`(-1, 0)` and the right endpoint to `(1, 0)`.

These are genuine open partial homeomorphisms.  Their exact half-`T` equations are the local
analytic input needed when the two endpoint charts are glued to the middle tubular strip.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue

/-! ## Affine normalizations of the inverse-function target -/

/-- Target normalization at the left endpoint.  The strict polynomial sublevel is sent to the
right of the vertical line `x = -1`. -/
noncomputable def leftSeamTargetHomeomorph (R d : ℝ) : Plane ≃ₜ Plane :=
  (((Homeomorph.addLeft (-R ^ 256)).trans (Homeomorph.neg ℝ)).trans
      (Homeomorph.addLeft (-1))).prodCongr
    (Homeomorph.addLeft (-d))

/-- Target normalization at the right endpoint.  The strict polynomial sublevel is sent to the
left of the vertical line `x = 1`. -/
noncomputable def rightSeamTargetHomeomorph (R d : ℝ) : Plane ≃ₜ Plane :=
  ((Homeomorph.addLeft (-R ^ 256)).trans (Homeomorph.addLeft 1)).prodCongr
    (Homeomorph.addLeft (-d))

@[simp]
theorem leftSeamTargetHomeomorph_apply (R d : ℝ) (z : Plane) :
    leftSeamTargetHomeomorph R d z =
      (-1 - (z.1 - R ^ 256), z.2 - d) := by
  apply Prod.ext <;> simp [leftSeamTargetHomeomorph] <;> ring

@[simp]
theorem rightSeamTargetHomeomorph_apply (R d : ℝ) (z : Plane) :
    rightSeamTargetHomeomorph R d z =
      (1 + (z.1 - R ^ 256), z.2 - d) := by
  apply Prod.ext <;> simp [rightSeamTargetHomeomorph] <;> ring

/-! ## Normalized local inverse-function charts -/

/-- The seam inverse-function chart normalized at the left endpoint of a standard band. -/
noncomputable def leftStandardSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    OpenPartialHomeomorph Plane Plane :=
  (superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv).transHomeomorph
    (leftSeamTargetHomeomorph R d)

/-- The seam inverse-function chart normalized at the right endpoint of a standard band. -/
noncomputable def rightStandardSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    OpenPartialHomeomorph Plane Plane :=
  (superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv).transHomeomorph
    (rightSeamTargetHomeomorph R d)

theorem mem_source_leftStandardSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    uv ∈ (leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv).source := by
  exact mem_source_superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv

theorem mem_source_rightStandardSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    uv ∈ (rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv).source := by
  exact mem_source_superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv

@[simp]
theorem leftStandardSeamLocalHomeomorph_apply
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z =
      (-1 - (superellipsoidPolynomialLift Phi frame c z - R ^ 256),
        orientedCoordinateLift Phi frame 2 z - d) := by
  simp only [leftStandardSeamLocalHomeomorph,
    OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    superellipsoidSeamLocalHomeomorph_apply, leftSeamTargetHomeomorph_apply,
    superellipsoidSeamMap]

@[simp]
theorem rightStandardSeamLocalHomeomorph_apply
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z =
      (1 + (superellipsoidPolynomialLift Phi frame c z - R ^ 256),
        orientedCoordinateLift Phi frame 2 z - d) := by
  simp only [rightStandardSeamLocalHomeomorph,
    OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    superellipsoidSeamLocalHomeomorph_apply, rightSeamTargetHomeomorph_apply,
    superellipsoidSeamMap]

theorem leftStandardSeamLocalHomeomorph_apply_center
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv uv = (-1, 0) := by
  have huvEq : superellipsoidSeamMap Phi frame c uv = (R ^ 256, d) := huv
  have houter := congrArg Prod.fst huvEq
  have hheight := congrArg Prod.snd huvEq
  simp only [superellipsoidSeamMap] at houter hheight
  simp [houter, hheight]

theorem rightStandardSeamLocalHomeomorph_apply_center
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv uv = (1, 0) := by
  have huvEq : superellipsoidSeamMap Phi frame c uv = (R ^ 256, d) := huv
  have houter := congrArg Prod.fst huvEq
  have hheight := congrArg Prod.snd huvEq
  simp only [superellipsoidSeamMap] at houter hheight
  simp [houter, hheight]

/-! ## Exact half-`T` equations -/

/-- In the normalized left chart, the literal barrier is the vertical outer branch together
with the inward horizontal branch pointing right. -/
theorem leftStandardSeamLocalHomeomorph_mem_barrier_iff
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    transportedTorusPlaneMap Phi z ∈ G.carrier ↔
      (leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 = -1 ∨
        (-1 < (leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 ∧
          (leftStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).2 = 0) := by
  rw [transportedTorusPlaneMap_mem_barrier_iff G hR]
  simp only [leftStandardSeamLocalHomeomorph_apply]
  constructor
  · rintro (houter | ⟨houter, hheight⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (houter | ⟨houter, hheight⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- In the normalized right chart, the literal barrier is the vertical outer branch together
with the inward horizontal branch pointing left. -/
theorem rightStandardSeamLocalHomeomorph_mem_barrier_iff
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    transportedTorusPlaneMap Phi z ∈ G.carrier ↔
      (rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 = 1 ∨
        ((rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 < 1 ∧
          (rightStandardSeamLocalHomeomorph Phi frame c R d hseam uv huv z).2 = 0) := by
  rw [transportedTorusPlaneMap_mem_barrier_iff G hR]
  simp only [rightStandardSeamLocalHomeomorph_apply]
  constructor
  · rintro (houter | ⟨houter, hheight⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (houter | ⟨houter, hheight⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩

end Submission.Topology
