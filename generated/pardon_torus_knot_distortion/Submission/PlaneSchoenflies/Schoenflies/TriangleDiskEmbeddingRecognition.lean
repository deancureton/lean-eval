import Submission.PlaneSchoenflies.ClassificationOfSurfaces.Moise.PLApproximation
import Submission.PlaneSchoenflies.Schoenflies.JordanAmbientBoundaryExtension
import Submission.PlaneSchoenflies.Schoenflies.JordanCarrierInvariance
import Submission.PlaneSchoenflies.Schoenflies.JordanHomeomorphRegions
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Recognizing injective triangular fillings

A continuous injection of a closed triangle whose boundary maps onto a Jordan circle has image
exactly the closed bounded Jordan disk.  The proof uses the existing no-retraction theorem to show
that the filling contains the bounded complementary component.  Connectedness of the image of the
triangle interior then rules out any additional sheet on the unbounded side.
-/

open Set Topology

noncomputable section

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle

/-- Ambient homeomorphisms carry the unbounded Jordan component to the unbounded component of the
image circle. -/
theorem outside_mapHomeomorph (J : JordanCircle) (h : Plane ≃ₜ Plane) :
    (J.mapHomeomorph h).outside = h '' J.outside := by
  let K := J.mapHomeomorph h
  have hcarrier : K.carrier = h '' J.carrier := J.carrier_mapHomeomorph h
  have hinside : K.inside = h '' J.inside := J.inside_mapHomeomorph h
  apply Set.Subset.antisymm
  · intro y hyOutside
    let x := h.symm y
    have hxNotCarrier : x ∉ J.carrier := by
      intro hxCarrier
      exact K.outside_subset_compl hyOutside <| by
        rw [hcarrier]
        exact ⟨x, hxCarrier, h.apply_symm_apply y⟩
    rcases J.mem_inside_or_outside hxNotCarrier with hxInside | hxOutside
    · have hyInside : y ∈ K.inside := by
        rw [hinside]
        exact ⟨x, hxInside, h.apply_symm_apply y⟩
      exact (Set.disjoint_left.mp K.inside_disjoint_outside hyInside hyOutside).elim
    · exact ⟨x, hxOutside, h.apply_symm_apply y⟩
  · rintro y ⟨x, hxOutside, rfl⟩
    have hyNotCarrier : h x ∉ K.carrier := by
      rw [hcarrier]
      rintro ⟨z, hzCarrier, hzx⟩
      have hzx' : z = x := h.injective hzx
      subst z
      exact J.outside_subset_compl hxOutside hzCarrier
    rcases K.mem_inside_or_outside hyNotCarrier with hyInside | hyOutside
    · have hxInside : x ∈ J.inside := by
        rw [hinside] at hyInside
        obtain ⟨z, hzInside, hz⟩ := hyInside
        exact h.injective hz ▸ hzInside
      exact (Set.disjoint_left.mp J.inside_disjoint_outside hxInside hxOutside).elim
    · exact hyOutside

private abbrev standardTriangleJordanCircle : JordanCircle :=
  standardTriangleCircle.toJordanCircle

/-- A fixed ambient normalization of an arbitrary Jordan circle to the standard polygonal
triangle. -/
def triangleNormalizer (J : JordanCircle) : Plane ≃ₜ Plane :=
  J.extendAmbientBoundaryHomeomorph standardTriangleJordanCircle
    (J.carrierHomeomorph.symm.trans standardTriangleJordanCircle.carrierHomeomorph)

theorem triangleNormalizer_image_carrier (J : JordanCircle) :
    J.triangleNormalizer '' J.carrier = standardTriangleCircle.carrier := by
  rw [triangleNormalizer,
    J.extendAmbientBoundaryHomeomorph_image_carrier standardTriangleJordanCircle]
  exact standardTriangleCircle.carrier_toJordanCircle

theorem triangleNormalizer_mem_exterior_iff (J : JordanCircle) (p : Plane) :
    J.triangleNormalizer p ∈ standardTriangleCircle.exteriorRegion ↔ p ∈ J.outside := by
  rw [← standardTriangleCircle.outside_toJordanCircle]
  let K := J.mapHomeomorph J.triangleNormalizer
  have hcarrier : K.carrier = standardTriangleJordanCircle.carrier := by
    rw [J.carrier_mapHomeomorph, J.triangleNormalizer_image_carrier,
      standardTriangleCircle.carrier_toJordanCircle]
  have houtside : K.outside = standardTriangleJordanCircle.outside :=
    K.outside_eq_of_carrier_eq standardTriangleJordanCircle hcarrier
  rw [← houtside, J.outside_mapHomeomorph]
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := hp
    exact J.triangleNormalizer.injective hxp ▸ hx
  · exact fun hp ↦ ⟨p, hp, rfl⟩

/-- A point omitted by a continuous triangular filling of a Jordan boundary lies on the unbounded
side of that boundary. -/
theorem mem_outside_of_triangle_continuous_extension
    (J : JordanCircle) {C : Set Plane} (hC : IsTriangle C)
    {b F : Plane → Plane} {p : Plane}
    (hbcont : ContinuousOn b (frontier C))
    (hbinj : Set.InjOn b (frontier C))
    (hbimage : b '' frontier C = J.carrier)
    (hFcont : ContinuousOn F C)
    (hFeq : Set.EqOn F b (frontier C))
    (hpavoid : p ∉ F '' C) :
    p ∈ J.outside := by
  let h := J.triangleNormalizer
  have hbcont' : ContinuousOn (h ∘ b) (frontier C) :=
    h.continuous.comp_continuousOn hbcont
  have hbinj' : Set.InjOn (h ∘ b) (frontier C) := by
    intro x hx y hy hxy
    exact hbinj hx hy (h.injective hxy)
  have hbimage' : (h ∘ b) '' frontier C = standardTriangleCircle.carrier := by
    rw [Set.image_comp, hbimage, J.triangleNormalizer_image_carrier]
  have hFcont' : ContinuousOn (h ∘ F) C :=
    h.continuous.comp_continuousOn hFcont
  have hFeq' : Set.EqOn (h ∘ F) (h ∘ b) (frontier C) := by
    intro x hx
    exact congrArg h (hFeq hx)
  have hpavoid' : h p ∉ (h ∘ F) '' C := by
    rintro ⟨x, hx, hxp⟩
    apply hpavoid
    exact ⟨x, hx, h.injective hxp⟩
  apply (J.triangleNormalizer_mem_exterior_iff p).mp
  exact standardTriangleCircle.mem_exteriorRegion_of_continuous_extension hC
    hbcont' hbinj' hbimage' hFcont' hFeq' hpavoid'

/-- A continuous injective image of a closed triangle whose boundary is a Jordan circle is exactly
the corresponding closed bounded Jordan disk. -/
theorem image_triangle_eq_closure_inside
    (J : JordanCircle) {C : Set Plane} (hC : IsTriangle C)
    {F : Plane → Plane}
    (hFcont : ContinuousOn F C)
    (hFinj : Set.InjOn F C)
    (hboundary : F '' frontier C = J.carrier) :
    F '' C = closure J.inside := by
  have hCclosed : IsClosed C := hC.isCompact.isClosed
  have hCsplit : C = interior C ∪ frontier C := by
    calc
      C = closure C := hCclosed.closure_eq.symm
      _ = interior C ∪ frontier C := closure_eq_interior_union_frontier C
  have hinsideSubset : J.inside ⊆ F '' C := by
    intro p hpInside
    by_contra hp
    have hpOutside := J.mem_outside_of_triangle_continuous_extension hC
      (hFcont.mono hCclosed.frontier_subset)
      (hFinj.mono hCclosed.frontier_subset) hboundary
      hFcont (fun _ _ ↦ rfl) hp
    exact Set.disjoint_left.mp J.inside_disjoint_outside hpInside hpOutside
  have hcarrierSubset : J.carrier ⊆ F '' C := by
    rw [← hboundary]
    exact Set.image_mono hCclosed.frontier_subset
  have hclosedDiskSubset : closure J.inside ⊆ F '' C := by
    rw [J.closure_inside]
    exact Set.union_subset hinsideSubset hcarrierSubset
  have hinteriorAvoids : F '' interior C ⊆ J.carrierᶜ := by
    rintro y ⟨x, hxInterior, rfl⟩ hyCarrier
    rw [← hboundary] at hyCarrier
    obtain ⟨z, hzFrontier, hxz⟩ := hyCarrier
    have hxz' : x = z := hFinj (interior_subset hxInterior)
      (hCclosed.frontier_subset hzFrontier) hxz.symm
    exact Set.disjoint_left.mp disjoint_interior_frontier hxInterior (hxz' ▸ hzFrontier)
  have hinteriorMeetsInside : (F '' interior C ∩ J.inside).Nonempty := by
    obtain ⟨x, hxC, hx⟩ := hinsideSubset J.insidePoint_mem_inside
    have hxInterior : x ∈ interior C := by
      rw [hCsplit] at hxC
      rcases hxC with hxInterior | hxFrontier
      · exact hxInterior
      · have hcarrier : F x ∈ J.carrier := by
          rw [← hboundary]
          exact ⟨x, hxFrontier, rfl⟩
        exact False.elim <| J.inside_subset_compl
          (hx ▸ J.insidePoint_mem_inside) hcarrier
    exact ⟨F x, ⟨x, hxInterior, rfl⟩, hx ▸ J.insidePoint_mem_inside⟩
  have hinteriorSide : F '' interior C ⊆ J.inside := by
    have hpreconnected : IsPreconnected (F '' interior C) :=
      hC.convex.interior.isPreconnected.image F (hFcont.mono interior_subset)
    have hsides : F '' interior C ⊆ J.inside ∪ J.outside := by
      rw [J.inside_union_outside]
      exact hinteriorAvoids
    rcases hpreconnected.subset_or_subset J.inside_isOpen J.outside_isOpen
        J.inside_disjoint_outside hsides with hinside | houtside
    · exact hinside
    · obtain ⟨y, hyImage, hyInside⟩ := hinteriorMeetsInside
      exact False.elim <|
        Set.disjoint_left.mp J.inside_disjoint_outside hyInside (houtside hyImage)
  apply Set.Subset.antisymm
  · rintro y ⟨x, hxC, rfl⟩
    rw [hCsplit] at hxC
    rcases hxC with hxInterior | hxFrontier
    · exact subset_closure (hinteriorSide ⟨x, hxInterior, rfl⟩)
    · rw [J.closure_inside]
      exact Or.inr <| by
        rw [← hboundary]
        exact ⟨x, hxFrontier, rfl⟩
  · exact hclosedDiskSubset

/-- A continuous injective image of a compact convex planar body whose boundary is a Jordan
circle is exactly the corresponding closed bounded Jordan disk. -/
theorem image_compactConvex_eq_closure_inside
    (J : JordanCircle) {C : Set Plane}
    (hCconvex : Convex ℝ C)
    (hCcompact : IsCompact C)
    (hCinterior : (interior C).Nonempty)
    {F : Plane → Plane}
    (hFcont : ContinuousOn F C)
    (hFinj : Set.InjOn F C)
    (hboundary : F '' frontier C = J.carrier) :
    F '' C = closure J.inside := by
  let T : Set Plane := convexHull ℝ (Set.range standardTriangleVertex)
  let hT : IsTriangle T :=
    ⟨standardTriangleVertex, standardTriangleVertex_affineIndependent, rfl⟩
  obtain ⟨e, _heInterior, heClosure, heFrontier⟩ :=
    exists_homeomorph_image_eq hCconvex hCinterior
      (NormedSpace.isVonNBounded_of_isBounded _ hCcompact.isBounded)
      hT.convex hT.infinite_interior.nonempty
      (NormedSpace.isVonNBounded_of_isBounded _ hT.isCompact.isBounded)
  have heC : e '' C = T := by
    simpa [hCcompact.isClosed.closure_eq, hT.isCompact.isClosed.closure_eq]
      using heClosure
  have hesymmImage (s : Set Plane) : e.symm '' (e '' s) = s := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
      rw [e.symm_apply_apply] at hzx
      exact hzx ▸ hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  have hesymmC : e.symm '' T = C := by
    rw [← heC, hesymmImage]
  have heMaps : Set.MapsTo e.symm T C := by
    intro y hy
    rw [← hesymmC]
    exact ⟨y, hy, rfl⟩
  let G : Plane → Plane := F ∘ e.symm
  have hGcont : ContinuousOn G T :=
    hFcont.comp e.symm.continuous.continuousOn heMaps
  have hGinj : Set.InjOn G T := by
    intro x hx y hy hxy
    apply e.symm.injective
    exact hFinj (heMaps hx) (heMaps hy) hxy
  have hGboundary : G '' frontier T = J.carrier := by
    have hesymmFrontier : e.symm '' frontier T = frontier C := by
      rw [← heFrontier, hesymmImage]
    calc
      G '' frontier T = F '' (e.symm '' frontier T) :=
        Set.image_comp F e.symm (frontier T)
      _ = F '' frontier C := by rw [hesymmFrontier]
      _ = J.carrier := hboundary
  have hGimage : G '' T = closure J.inside :=
    J.image_triangle_eq_closure_inside hT hGcont hGinj hGboundary
  calc
    F '' C = F '' (e.symm '' T) := by rw [hesymmC]
    _ = G '' T := by rw [Set.image_comp]
    _ = closure J.inside := hGimage

end JordanCircle
end Schoenflies
