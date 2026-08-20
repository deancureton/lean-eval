import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Closure gluing at a regular superellipsoid seam

The inverse-function chart for the simultaneous outer-polynomial and height map shows that every
regular seam lift is approached by points on the strict inward half of the height fiber.  Passing
through the transported-torus covering map gives the exact ambient closure equality required by
the finite barrier graph.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-- A regular simultaneous outer/height fiber point is approached, within its height fiber, from
the strict polynomial sublevel side. -/
private theorem mem_closure_strict_superellipsoidSeamFiber
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256)
    (hheight : orientedCoordinateLift Phi frame 2 uv = d) :
    uv ∈ closure {z : Plane |
      superellipsoidPolynomialLift Phi frame c z < R ^ 256 ∧
        orientedCoordinateLift Phi frame 2 z = d} := by
  have huvFiber :
      uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)} := by
    exact Prod.ext hlevel hheight
  let E := superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huvFiber
  have huvSource : uv ∈ E.source :=
    mem_source_superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huvFiber
  rw [mem_closure_iff]
  intro U hUopen huvU
  let V : Set Plane := E '' (E.source ∩ U)
  have hVopen : IsOpen V :=
    E.isOpen_image_of_subset_source (E.open_source.inter hUopen) inter_subset_left
  have hcenterV : (R ^ 256, d) ∈ V := by
    refine ⟨uv, ⟨huvSource, huvU⟩, ?_⟩
    rw [superellipsoidSeamLocalHomeomorph_apply]
    exact Prod.ext hlevel hheight
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVopen (R ^ 256, d) hcenterV
  let w : Plane := (R ^ 256 - δ / 2, d)
  have hwball : w ∈ Metric.ball (R ^ 256, d) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq]
      dsimp [w]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · simp [w, hδ]
  obtain ⟨z, ⟨hzSource, hzU⟩, hzE⟩ := hball hwball
  refine ⟨z, hzU, ?_⟩
  have hzMap : superellipsoidSeamMap Phi frame c z = w := by
    rw [← superellipsoidSeamLocalHomeomorph_apply
      Phi frame c R d hseam uv huvFiber]
    exact hzE
  constructor
  · have hzFirst := congrArg Prod.fst hzMap
    dsimp [superellipsoidSeamMap, w] at hzFirst
    linarith
  · have hzSecond := congrArg Prod.snd hzMap
    simpa only [superellipsoidSeamMap, w] using hzSecond

/-- Transversality supplies the exact closure-gluing equality between the inward cutting section
and the outer section. -/
theorem hasSuperellipsoidSeamClosureGluing
    (Phi : AmbientIsotopy) : HasSuperellipsoidSeamClosureGluing Phi := by
  intro frame c R d hR _houter _hcut hseam
  apply Set.Subset.antisymm
  · intro x hx
    have hcutClosed : IsClosed (superellipsoidCutTorusSection Phi frame d) :=
      (transportedTorus_isClosed Phi).inter (isClosed_coordinateCuttingPlane frame d)
    have hxCut : x ∈ superellipsoidCutTorusSection Phi frame d :=
      (closure_minimal inter_subset_left hcutClosed) hx.1
    exact ⟨⟨hxCut.1, hx.2.2⟩, hxCut.2⟩
  · intro x hx
    refine ⟨?_, hx.1⟩
    obtain ⟨uv, huvMap⟩ : ∃ uv, transportedTorusPlaneMap Phi uv = x := by
      have htorus : x ∈ transportedTorus Phi := hx.1.1
      rw [← range_transportedTorusPlaneMap Phi] at htorus
      exact htorus
    have hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256 := by
      unfold superellipsoidPolynomialLift
      rw [huvMap]
      exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp hx.1.2
    have hheight : orientedCoordinateLift Phi frame 2 uv = d := by
      unfold orientedCoordinateLift
      rw [huvMap]
      exact hx.2
    have huvClosure := mem_closure_strict_superellipsoidSeamFiber
      Phi frame c R d hseam uv hlevel hheight
    have hmaps : MapsTo (transportedTorusPlaneMap Phi)
        {z : Plane |
          superellipsoidPolynomialLift Phi frame c z < R ^ 256 ∧
            orientedCoordinateLift Phi frame 2 z = d}
        (superellipsoidCutTorusSection Phi frame d ∩
          superellipsoidBody frame c R) := by
      intro z hz
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← range_transportedTorusPlaneMap Phi]
        exact Set.mem_range_self z
      · exact hz.2
      · exact (mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ hR).mpr hz.1
    rw [← huvMap]
    exact map_mem_closure (transportedTorusPlaneMap_contDiff Phi).continuous
      huvClosure hmaps

end Submission.Topology
