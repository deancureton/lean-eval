import Submission.Topology.RegularSublevelLocalPreconnected
import Submission.Topology.SuperellipsoidOuterCircleSection
import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# The initial reduced superellipsoid region

The selected strict superellipsoid sublevel on the transported torus is open, and outer-level
regularity identifies its relative frontier exactly with the analytic outer circle section.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- The strict quotient sublevel transported to the actual torus. -/
def superellipsoidReducedInside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    Set (transportedTorus Phi) :=
  transportedTorusHomeomorph Phi ''
    periodicQuotientSublevel (superellipsoidTorusPolynomial Phi frame c) (R ^ 256)

theorem isOpen_superellipsoidReducedInside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsOpen (superellipsoidReducedInside Phi frame c R) := by
  exact (transportedTorusHomeomorph Phi).isOpenMap _
    (isOpen_periodicQuotientSublevel
      (continuous_superellipsoidTorusPolynomial Phi frame c) (R ^ 256))

/-- The quotient definition is exactly the transported part of the strict ambient body. -/
theorem superellipsoidReducedInside_eq_transportedTorusPart
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R) :
    superellipsoidReducedInside Phi frame c R =
      transportedTorusPart Phi (superellipsoidBody frame c R) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change transportedTorusMap Phi z ∈ superellipsoidBody frame c R
    rw [mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ hR]
    exact hz
  · intro hx
    let z := (transportedTorusHomeomorph Phi).symm x
    refine ⟨z, ?_, (transportedTorusHomeomorph Phi).apply_symm_apply x⟩
    change superellipsoidTorusPolynomial Phi frame c z < R ^ 256
    rw [superellipsoidTorusPolynomial]
    have hxValue : transportedTorusMap Phi z = x :=
      congrArg Subtype.val ((transportedTorusHomeomorph Phi).apply_symm_apply x)
    rw [hxValue]
    exact (mem_superellipsoidBody_iff_polynomial_lt_pow frame c x hR).mp hx

private theorem image_superellipsoidTorusPolynomialLevelSet
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 ≤ R) :
    transportedTorusHomeomorph Phi ''
        superellipsoidTorusPolynomialLevelSet Phi frame c R =
      transportedTorusPart Phi (superellipsoidOuterTorusSection Phi frame c R) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change transportedTorusMap Phi z ∈
      superellipsoidOuterTorusSection Phi frame c R
    refine ⟨⟨z, rfl⟩, ?_⟩
    rw [mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR]
    exact hz
  · rintro ⟨hxTorus, hxBoundary⟩
    let z := (transportedTorusHomeomorph Phi).symm x
    refine ⟨z, ?_, (transportedTorusHomeomorph Phi).apply_symm_apply x⟩
    change superellipsoidTorusPolynomial Phi frame c z = R ^ 256
    rw [superellipsoidTorusPolynomial]
    have hxValue : transportedTorusMap Phi z = x :=
      congrArg Subtype.val ((transportedTorusHomeomorph Phi).apply_symm_apply x)
    rw [hxValue]
    exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c x hR).mp hxBoundary

/-- The analytic outer section is exactly the relative frontier of the initial reduced region. -/
theorem frontier_superellipsoidReducedInside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R)
    (hregular : IsRegularValue
      (superellipsoidPolynomialLift Phi frame c) (R ^ 256)) :
    frontier (superellipsoidReducedInside Phi frame c R) =
      transportedTorusPart Phi (superellipsoidOuterTorusSection Phi frame c R) := by
  rw [superellipsoidReducedInside,
    ← (transportedTorusHomeomorph Phi).image_frontier]
  rw [frontier_periodicQuotientSublevel
    (contDiff_superellipsoidPolynomialLift Phi frame c)
    (continuous_superellipsoidTorusPolynomial Phi frame c)
    (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c)
    hregular]
  exact image_superellipsoidTorusPolynomialLevelSet Phi frame c hR.le

/-- The initial strict superellipsoid side has arbitrarily small preconnected traces at every
point of its regular frontier. -/
theorem isLocallyPreconnectedWithinAt_superellipsoidReducedInside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R)
    (hregular : IsRegularValue
      (superellipsoidPolynomialLift Phi frame c) (R ^ 256))
    {x : transportedTorus Phi}
    (hx : x ∈ frontier (superellipsoidReducedInside Phi frame c R)) :
    IsLocallyPreconnectedWithinAt
      (superellipsoidReducedInside Phi frame c R) x := by
  have hxSection : x ∈
      transportedTorusPart Phi (superellipsoidOuterTorusSection Phi frame c R) := by
    rw [← frontier_superellipsoidReducedInside Phi frame c hR hregular]
    exact hx
  have hxImage : x ∈ transportedTorusHomeomorph Phi ''
      superellipsoidTorusPolynomialLevelSet Phi frame c R := by
    rw [image_superellipsoidTorusPolynomialLevelSet Phi frame c hR.le]
    exact hxSection
  obtain ⟨z, hz, rfl⟩ := hxImage
  exact (isLocallyPreconnectedWithinAt_periodicQuotientSublevel
      (contDiff_superellipsoidPolynomialLift Phi frame c)
      (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c)
      hregular hz).homeomorph (transportedTorusHomeomorph Phi)

end Submission.Topology
