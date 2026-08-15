import Submission.Coarea.SuperellipsoidCutSelection
import Submission.Topology.CoordinatePlaneIntersectionCircles
import Submission.Topology.HalfSphereSurgeryDichotomy
import Submission.Topology.SuperellipsoidTwoSurgeryCells

/-!
# The finite graph on the superellipsoid double-bubble barrier

The literal double-bubble barrier is not a disjoint union of circles.  At a transverse point of
the outer seam, the two branches of the outer section and the inward branch of the cutting-plane
section form a `T`.  In particular, replacing the barrier by a pairwise-disjoint circle family
without recording a local two-surgery is unsound.

This file records the correct intermediate object.  The two regular sections are finite disjoint
circle families.  Cutting the plane-section circles by the open superellipsoid body produces the
open edges of a finite graph; their closures attach to the outer circles at the finite transverse
seam.  A separate resolution structure records the genuinely geometric local surgery that turns
this graph into regular embedded intersection circles.

The last section gives the exact adapter from any essential resolved circle to the existing
finite innermost-circle surgery interface.  Thus no existence or embeddedness assertion about the
local surgery is hidden in the finite argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## Finite regular section families -/

/-- A finite family of pairwise-disjoint embedded torus circles whose union is an ambient
section.  This common interface is used for both the regular outer level and the regular cutting
plane. -/
structure FiniteEmbeddedTorusCircleSection
    (Phi : AmbientIsotopy) (section : Set R3) (ι : Type*) [Fintype ι] where
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  circle_mem_section : ∀ i, Set.range (circle i).circle ⊆ section
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  section_exact : section = ⋃ i, Set.range (circle i).circle

namespace FiniteEmbeddedTorusCircleSection

variable {Phi : AmbientIsotopy} {section : Set R3} {ι : Type*} [Fintype ι]

theorem section_subset_transportedTorus
    (F : FiniteEmbeddedTorusCircleSection Phi section ι) :
    section ⊆ transportedTorus Phi := by
  rw [F.section_exact]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact (F.circle i).range_subset_transportedTorus hi

end FiniteEmbeddedTorusCircleSection

/-! ## The literal finite barrier graph -/

/-- Ambient outer section of the transported torus. -/
def superellipsoidOuterTorusSection (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set R3 :=
  transportedTorus Phi ∩ superellipsoidBoundary frame c R

/-- Ambient coordinate-plane section of the transported torus. -/
def superellipsoidCutTorusSection (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) : Set R3 :=
  transportedTorus Phi ∩ coordinateCuttingPlane frame d

namespace FiniteEmbeddedTorusCircleSection

/-- The existing quotient-level coordinate section classification supplies the cutting-circle
family required by the barrier graph. -/
def ofCoordinatePlaneFamily
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}
    (F : FiniteCoordinatePlaneTorusCircleFamily Phi frame d)
    [Fintype F.index] :
    FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame d) F.index where
  circle := F.circle
  circle_mem_section := by
    intro i x hx
    exact ⟨(F.circle i).range_subset_transportedTorus hx,
      F.circle_mem_plane i hx⟩
  pairwise_disjoint := F.pairwise_disjoint
  section_exact := F.intersection_exact

end FiniteEmbeddedTorusCircleSection

/-- The finite transverse seam consists of points lying on the torus, outer surface, and cutting
plane simultaneously. -/
def superellipsoidTorusSeam (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : Set R3 :=
  transportedTorus Phi ∩ superellipsoidBoundary frame c R ∩
    coordinateCuttingPlane frame d

/-- The literal analytic barrier as an ambient subset. -/
def superellipsoidAmbientBarrier (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : Set R3 :=
  transportedTorus Phi ∩
    (superellipsoidBoundary frame c R ∪
      (superellipsoidBody frame c R ∩ coordinateCuttingPlane frame d))

/-- The common outer/height fiber in one closed fundamental square. -/
def fundamentalSuperellipsoidSeam (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) : Set Plane :=
  fundamentalSquare ∩
    (superellipsoidPolynomialLift Phi frame c) ⁻¹' {R ^ 256} ∩
    (orientedCoordinateLift Phi frame 2) ⁻¹' {d}

/-- The two-coordinate map whose Jacobian is `planarDifferentialDet`. -/
def superellipsoidSeamMap (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) : Plane :=
  (superellipsoidPolynomialLift Phi frame c uv,
    orientedCoordinateLift Phi frame 2 uv)

/-- Local injectivity along one fiber makes that fiber a discrete subset. -/
theorem isDiscrete_fiber_of_locallyInjectiveAlong
    {X Y : Type*} [TopologicalSpace X] {f : X → Y} {y : Y}
    (hlocal : ∀ x ∈ f ⁻¹' {y}, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ U.InjOn f) :
    IsDiscrete (f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hlocal x hx
  refine ⟨U, hUopen, ?_⟩
  ext z
  constructor
  · rintro ⟨hzU, hzFiber⟩
    have hzEq : f z = y := hzFiber
    have hxEq : f x = y := hx
    have hzx : z = x := hUinj hzU hxU (hzEq.trans hxEq.symm)
    simpa using hzx
  · intro hzx
    rw [Set.mem_singleton_iff] at hzx
    subst z
    exact ⟨hxU, hx⟩

/-- The common fiber of the seam map is the unrestricted lifted seam. -/
theorem superellipsoidSeamMap_fiber
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)} =
      (superellipsoidPolynomialLift Phi frame c) ⁻¹' {R ^ 256} ∩
        (orientedCoordinateLift Phi frame 2) ⁻¹' {d} := by
  ext uv
  simp only [superellipsoidSeamMap, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_inter_iff, Prod.mk.injEq]

theorem isCompact_fundamentalSuperellipsoidSeam
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsCompact (fundamentalSuperellipsoidSeam Phi frame c R d) := by
  exact (isCompact_fundamentalSquare.inter_right
    (isClosed_singleton.preimage
      (contDiff_superellipsoidPolynomialLift Phi frame c).continuous)).inter_right
        (isClosed_singleton.preimage
          (orientedCoordinateLift_contDiff Phi frame 2).continuous)

/-- Compactness turns the local discreteness supplied by the determinant condition into literal
finiteness in a fundamental square. -/
theorem fundamentalSuperellipsoidSeam_finite_of_isDiscrete
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hdiscrete : IsDiscrete (fundamentalSuperellipsoidSeam Phi frame c R d)) :
    (fundamentalSuperellipsoidSeam Phi frame c R d).Finite :=
  (isCompact_fundamentalSuperellipsoidSeam Phi frame c R d).finite hdiscrete

theorem superellipsoidPolynomialLift_planeFundamentalRepresentative
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) :
    superellipsoidPolynomialLift Phi frame c (planeFundamentalRepresentative uv) =
      superellipsoidPolynomialLift Phi frame c uv := by
  let index := planeFundamentalDeckIndex uv
  calc
    superellipsoidPolynomialLift Phi frame c (planeFundamentalRepresentative uv) =
        superellipsoidPolynomialLift Phi frame c
          (planeFundamentalRepresentative uv + planeDeckVector index.1 index.2) :=
      (superellipsoidPolynomialLift_add_planeDeckVector
        Phi frame c index.1 index.2 _).symm
    _ = superellipsoidPolynomialLift Phi frame c uv := by
      rw [planeFundamentalRepresentative_add_deck]

theorem transportedTorusPlaneMap_planeFundamentalRepresentative
    (Phi : AmbientIsotopy) (uv : Plane) :
    transportedTorusPlaneMap Phi (planeFundamentalRepresentative uv) =
      transportedTorusPlaneMap Phi uv := by
  let index := planeFundamentalDeckIndex uv
  calc
    transportedTorusPlaneMap Phi (planeFundamentalRepresentative uv) =
        transportedTorusPlaneMap Phi
          (planeFundamentalRepresentative uv + planeDeckVector index.1 index.2) := by
      rw [show planeFundamentalRepresentative uv + planeDeckVector index.1 index.2 =
          ((planeFundamentalRepresentative uv).1 + (index.1 : ℝ) * (2 * Real.pi),
            (planeFundamentalRepresentative uv).2 + (index.2 : ℝ) * (2 * Real.pi)) by
        ext <;> rfl]
      exact (transportedTorusPlaneMap_add_int_periods Phi index.1 index.2 _).symm
    _ = transportedTorusPlaneMap Phi uv := by
      rw [planeFundamentalRepresentative_add_deck]

/-- Every ambient seam point has a representative in the compact common fiber, and conversely. -/
theorem image_fundamentalSuperellipsoidSeam
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 ≤ R) (d : ℝ) :
    transportedTorusPlaneMap Phi ''
        fundamentalSuperellipsoidSeam Phi frame c R d =
      superellipsoidTorusSeam Phi frame c R d := by
  ext x
  constructor
  · rintro ⟨uv, huv, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← range_transportedTorusPlaneMap Phi]
      exact ⟨uv, rfl⟩
    · exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).2 huv.1.2
    · exact huv.2
  · rintro ⟨⟨htorus, hboundary⟩, hplane⟩
    rw [← range_transportedTorusPlaneMap Phi] at htorus
    obtain ⟨uv, rfl⟩ := htorus
    let representative := planeFundamentalRepresentative uv
    refine ⟨representative, ?_, ?_⟩
    · refine ⟨⟨planeFundamentalRepresentative_mem_fundamentalSquare uv, ?_⟩, ?_⟩
      · change superellipsoidPolynomialLift Phi frame c representative = R ^ 256
        rw [superellipsoidPolynomialLift_planeFundamentalRepresentative]
        exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).1 hboundary
      · change orientedCoordinateLift Phi frame 2 representative = d
        rw [orientedCoordinateLift_planeFundamentalRepresentative]
        exact hplane
    · exact transportedTorusPlaneMap_planeFundamentalRepresentative Phi uv

/-- Seam finiteness follows from the exact local inverse-function-theorem output in the compact
fundamental square.  This exposes the analytic remainder without assuming ambient finiteness. -/
theorem superellipsoidTorusSeam_finite_of_fundamental_isDiscrete
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 ≤ R) (d : ℝ)
    (hdiscrete : IsDiscrete (fundamentalSuperellipsoidSeam Phi frame c R d)) :
    (superellipsoidTorusSeam Phi frame c R d).Finite := by
  rw [← image_fundamentalSuperellipsoidSeam Phi frame c hR d]
  exact (fundamentalSuperellipsoidSeam_finite_of_isDiscrete
    Phi frame c R d hdiscrete).image _

/-- Exact local inverse-function-theorem statement still needed to turn the selector's nonzero
determinant into a finite seam.  It is deliberately a local-discreteness assertion, not the
desired finite-circle conclusion. -/
def HasSuperellipsoidSeamIsolation (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c R d,
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256) →
    IsRegularValue (orientedCoordinateLift Phi frame 2) d →
    IsRegularSuperellipsoidSeamHeight Phi frame c R d →
      IsDiscrete (fundamentalSuperellipsoidSeam Phi frame c R d)

/-- The exact inverse-function-theorem output at each transverse common-fiber point. -/
def HasSuperellipsoidSeamLocalInverses (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c R d,
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256) →
    IsRegularValue (orientedCoordinateLift Phi frame 2) d →
    IsRegularSuperellipsoidSeamHeight Phi frame c R d →
    ∀ uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)},
      ∃ U : Set Plane, IsOpen U ∧ uv ∈ U ∧
        U.InjOn (superellipsoidSeamMap Phi frame c)

/-- Local inverses of the two-coordinate seam map supply the isolation contract. -/
theorem hasSuperellipsoidSeamIsolation_of_localInverses
    {Phi : AmbientIsotopy} (hlocal : HasSuperellipsoidSeamLocalInverses Phi) :
    HasSuperellipsoidSeamIsolation Phi := by
  intro frame c R d houter hcut hseam
  have hfullDiscrete : IsDiscrete
      ((superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :=
    isDiscrete_fiber_of_locallyInjectiveAlong
      (hlocal frame c R d houter hcut hseam)
  rw [superellipsoidSeamMap_fiber] at hfullDiscrete
  exact hfullDiscrete.mono fun _ hx ↦ ⟨hx.1.2, hx.2⟩

/-- Exact closure-gluing consequence of transverse crossing.  It says that every seam point is
approached by the inward half of the cutting section and that no other outer point is. -/
def HasSuperellipsoidSeamClosureGluing (Phi : AmbientIsotopy) : Prop :=
  ∀ frame c R d,
    0 < R →
    IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256) →
    IsRegularValue (orientedCoordinateLift Phi frame 2) d →
    IsRegularSuperellipsoidSeamHeight Phi frame c R d →
      closure
          ((superellipsoidCutTorusSection Phi frame d) ∩
            superellipsoidBody frame c R) ∩
        superellipsoidOuterTorusSection Phi frame c R =
          superellipsoidTorusSeam Phi frame c R d

/-- Finite graph data extracted from the two regular section families.

`seam_finite` is the compact-isolated conclusion of seam transversality.  The local inverse
function theorem is the only analytic ingredient in this field: the determinant condition in
`IsRegularSuperellipsoidSeamHeight` makes the common fiber locally discrete, and compactness of
the quotient torus then makes it finite.

The closure equality is deliberately stated separately.  The cutting piece uses the *open* body,
so it is disjoint from the outer piece as a set; its closure meets the outer piece exactly at the
seam. -/
structure FiniteSuperellipsoidBarrierGraph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (outerIndex cutIndex : Type*) [Fintype outerIndex] [Fintype cutIndex] where
  outer : FiniteEmbeddedTorusCircleSection Phi
    (superellipsoidOuterTorusSection Phi frame c R) outerIndex
  cut : FiniteEmbeddedTorusCircleSection Phi
    (superellipsoidCutTorusSection Phi frame d) cutIndex
  seam_finite : (superellipsoidTorusSeam Phi frame c R d).Finite
  cut_inside_closure_meets_outer :
    closure
        ((superellipsoidCutTorusSection Phi frame d) ∩
          superellipsoidBody frame c R) ∩
      superellipsoidOuterTorusSection Phi frame c R =
        superellipsoidTorusSeam Phi frame c R d

/-- Constructor exposing the exact analytic input left after the two finite circle families are
known: local discreteness of the transverse common fiber and the elementary closure-gluing fact. -/
def FiniteSuperellipsoidBarrierGraph.ofRegularSections
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (hR : 0 ≤ R)
    (outer : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R) outerIndex)
    (cut : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame d) cutIndex)
    (hdiscrete : IsDiscrete (fundamentalSuperellipsoidSeam Phi frame c R d))
    (hclosure :
      closure
          ((superellipsoidCutTorusSection Phi frame d) ∩
            superellipsoidBody frame c R) ∩
        superellipsoidOuterTorusSection Phi frame c R =
          superellipsoidTorusSeam Phi frame c R d) :
    FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex where
  outer := outer
  cut := cut
  seam_finite := superellipsoidTorusSeam_finite_of_fundamental_isDiscrete
    Phi frame c hR d hdiscrete
  cut_inside_closure_meets_outer := hclosure

/-- The validated outer, cutting, and seam regularity fields construct the finite graph as soon
as the two regular one-manifold circle classifications and the two local transverse-fiber lemmas
are available. -/
def FiniteSuperellipsoidBarrierGraph.ofSelectedRegularCut
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
    {c : R3} {r D : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    {outer : SuperellipsoidOuterSelection K Phi frame c r}
    (cutSelection : SuperellipsoidRegularCutSelection
      K Phi frame c r D W outer)
    (hr : 0 < r)
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (outerCircles : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c outer.scale) outerIndex)
    (cutCircles : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame cutSelection.height) cutIndex)
    (hisolation : HasSuperellipsoidSeamIsolation Phi)
    (hclosure : HasSuperellipsoidSeamClosureGluing Phi) :
    FiniteSuperellipsoidBarrierGraph Phi frame c outer.scale cutSelection.height
      outerIndex cutIndex :=
  .ofRegularSections (outer.scale_pos hr).le outerCircles cutCircles
    (hisolation frame c outer.scale cutSelection.height outer.surfaceRegular
      cutSelection.surfaceRegular cutSelection.seamRegular)
    (hclosure frame c outer.scale cutSelection.height (outer.scale_pos hr)
      outer.surfaceRegular cutSelection.surfaceRegular cutSelection.seamRegular)

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]

/-- The inward portions of the cutting circles are the noncompact graph edges. -/
def cutInsideRange
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Set R3 :=
  Set.range (G.cut.circle j).circle ∩ superellipsoidBody frame c R

/-- The set carried by the finite barrier graph: complete outer circles together with the inward
parts of the cutting circles. -/
def carrier
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) : Set R3 :=
  (⋃ i, Set.range (G.outer.circle i).circle) ∪
    ⋃ j, G.cutInsideRange j

/-- The two finite regular section descriptions identify the graph carrier with the literal
analytic outer/cut barrier. -/
theorem carrier_eq_ambientBarrier
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    G.carrier = superellipsoidAmbientBarrier Phi frame c R d := by
  ext x
  have houter : x ∈ (⋃ i, Set.range (G.outer.circle i).circle) ↔
      x ∈ superellipsoidOuterTorusSection Phi frame c R := by
    rw [← G.outer.section_exact]
  have hcut : x ∈ (⋃ j, G.cutInsideRange j) ↔
      x ∈ superellipsoidCutTorusSection Phi frame d ∧
        x ∈ superellipsoidBody frame c R := by
    simp only [cutInsideRange, Set.mem_iUnion, Set.mem_inter_iff]
    rw [G.cut.section_exact]
    simp only [Set.mem_iUnion]
  rw [show x ∈ G.carrier ↔
      x ∈ (⋃ i, Set.range (G.outer.circle i).circle) ∨
        x ∈ (⋃ j, G.cutInsideRange j) by rfl, houter, hcut]
  simp only [superellipsoidOuterTorusSection, superellipsoidCutTorusSection,
    superellipsoidAmbientBarrier, Set.mem_union, Set.mem_inter_iff]
  tauto

/-- The ambient graph is exactly the subtype-valued barrier used by the cell partition. -/
theorem subtype_carrier_eq_outerCutBarrierPart
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    Subtype.val ⁻¹' G.carrier =
      superellipsoidOuterCutBarrierPart Phi frame c R d := by
  rw [G.carrier_eq_ambientBarrier]
  ext x
  simp only [superellipsoidAmbientBarrier, superellipsoidOuterCutBarrierPart,
    transportedTorusPart, Set.mem_preimage, Set.mem_inter_iff]
  exact and_iff_right x.property

/-- The open cutting edges do not literally meet the outer circles. -/
theorem cutInsideRange_disjoint_outer
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :
    Disjoint (G.cutInsideRange j)
      (superellipsoidOuterTorusSection Phi frame c R) := by
  rw [Set.disjoint_left]
  intro x hxCut hxOuter
  exact (ne_of_lt hxCut.2) hxOuter.2

/-- Their closures attach only at the finite seam. -/
theorem closure_cutInside_union_meets_outer
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    closure (⋃ j, G.cutInsideRange j) ∩
        superellipsoidOuterTorusSection Phi frame c R =
      superellipsoidTorusSeam Phi frame c R d := by
  have hcutUnion : (⋃ j, G.cutInsideRange j) =
      superellipsoidCutTorusSection Phi frame d ∩
        superellipsoidBody frame c R := by
    ext x
    simp only [cutInsideRange, Set.mem_iUnion, Set.mem_inter_iff]
    rw [G.cut.section_exact]
    simp only [Set.mem_iUnion]
  rw [hcutUnion]
  exact G.cut_inside_closure_meets_outer

/-- The attachment locus of the open cutting edges is finite. -/
theorem finite_closure_attachment
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    (closure (⋃ j, G.cutInsideRange j) ∩
      superellipsoidOuterTorusSection Phi frame c R).Finite := by
  rw [G.closure_cutInside_union_meets_outer]
  exact G.seam_finite

end FiniteSuperellipsoidBarrierGraph

/-! ## Honest local two-surgery resolution -/

/-- A finite arc presentation of the literal barrier graph.

The endpoints are seam vertices, path interiors avoid the seam, and the edge ranges cover the
literal graph.  At seam vertices the incident-edge data is not required to be cyclic: in the
actual double bubble it has the `T`-shaped valence pattern. -/
structure FiniteBarrierArcPresentation
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (vertex edge : Type*) [Fintype vertex] [Fintype edge] where
  point : vertex → R3
  point_injective : Function.Injective point
  vertex_exact : Set.range point = superellipsoidTorusSeam Phi frame c R d
  sourcePoint targetPoint : edge → R3
  arc : ∀ e, Path (sourcePoint e) (targetPoint e)
  closed_or_endpoints_are_vertices : ∀ e,
    sourcePoint e = targetPoint e ∨
      sourcePoint e ∈ Set.range point ∧ targetPoint e ∈ Set.range point
  arc_in_graph : ∀ e, Set.range (arc e) ⊆ G.carrier
  interior_avoids_vertices : ∀ e t,
    sourcePoint e ≠ targetPoint e → (t : ℝ) ≠ 0 → (t : ℝ) ≠ 1 →
      arc e t ∉ Set.range point
  graph_exact : G.carrier = ⋃ e, Set.range (arc e)

/-- Local resolution data for the transverse `T`-vertices.

This is intentionally not derivable from the finite graph by combinatorics alone.  A resolution
must specify an embedded moving sphere and prove that its regular torus intersection is the given
pairwise-disjoint circle family.  `trace_mem_event` retains the whole moving-sphere trace consumed
by the later charging contract. -/
structure FiniteBarrierTwoSurgeryResolution
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    (A : FiniteBarrierArcPresentation G vertex edge)
    (resolvedIndex : Type*) [Fintype resolvedIndex] where
  stage : FiniteSphereSurgeryIntersectionSystem Phi resolvedIndex
  vertexNeighborhood : vertex → Set R3
  vertexNeighborhood_open : ∀ v, IsOpen (vertexNeighborhood v)
  vertex_mem_neighborhood : ∀ v, A.point v ∈ vertexNeighborhood v
  vertexNeighborhood_pairwise : Pairwise fun v w ↦
    Disjoint (vertexNeighborhood v) (vertexNeighborhood w)
  /-- Away from the selected disjoint seam charts, the resolution is literally unchanged. -/
  fixed_off_vertexNeighborhoods :
    G.carrier \ (⋃ v, vertexNeighborhood v) =
      (stage.sphere.carrier ∩ transportedTorus Phi) \
        (⋃ v, vertexNeighborhood v)
  /-- Every resolved boundary is traced by the local surgery through the moving-sphere event region.
  The event region here is the whole moving-sphere trace, not merely the singular endpoint
  barrier: a regular resolved circle generally lies slightly off that endpoint. -/
  trace : resolvedIndex → ℝ → ℝ → R3
  continuous_trace : ∀ i, Continuous (Function.uncurry (trace i))
  periodic_trace : ∀ i s, Function.Periodic (trace i s) (2 * Real.pi)
  trace_zero : ∀ i t, trace i 0 t = (stage.circle i).windingLoop.curve t
  trace_mem_event : ∀ i s t, trace i s t ∈ stage.eventRegion
  /-- The arc presentation is consumed by the local construction, rather than silently discarded.
  The precise correspondence is a geometric field because it depends on the chosen smoothing. -/
  graph_arc_used : ∀ e, ∃ i s, Set.range (A.arc e) ⊆ Set.range (trace i s)

namespace FiniteBarrierTwoSurgeryResolution

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge resolvedIndex : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  [Fintype resolvedIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}

/-- The entire singular graph lies in the moving-sphere event region recorded by a resolution. -/
theorem carrier_subset_eventRegion
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex) :
    G.carrier ⊆ Q.stage.eventRegion := by
  rw [A.graph_exact]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨e, he⟩ := hx
  obtain ⟨i, s, his⟩ := Q.graph_arc_used e
  obtain ⟨t, ht⟩ := his he
  rw [← ht]
  exact Q.trace_mem_event i s t

end FiniteBarrierTwoSurgeryResolution

/-! ## Essential resolved circles and innermost surgery -/

/-- Innermost-surgery input for an essential resolved barrier circle, independent of any claim
that the singular barrier itself is a circle union. -/
structure EssentialResolvedBarrierCircleSurgeryData
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι) (i : ι) where
  system : FinitePlaneDiskTorusCircleSystem Phi ι
  innermost : system.InnermostEssential i
  boundary_eq : (system.circle i).windingLoop = (S.circle i).windingLoop
  surgery : FiniteInnermostCircleSurgeryContract Phi ι system

namespace EssentialResolvedBarrierCircleSurgeryData

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι} {i : ι}

/-- An essential resolved circle produces the exact event-covered compression consumed by the
charged-compression layer. -/
theorem exists_eventCoveredCompressingDisk
    (D : EssentialResolvedBarrierCircleSurgeryData S i) :
    Nonempty (EventCoveredCompressingDisk (Phi := Phi) S.eventRegion) := by
  obtain ⟨disk, hboundary⟩ :=
    D.surgery.exists_generalCompressingDiskWitness_with_boundary i D.innermost
  refine ⟨⟨disk, ?_⟩⟩
  intro t
  rw [hboundary, D.boundary_eq]
  exact S.circle_mem_event i t

end EssentialResolvedBarrierCircleSurgeryData

/-- A local two-surgery resolution is ready for the essential branch precisely when every
essential regular stage circle has an explicit finite disk system and surgery contract. -/
def FiniteBarrierTwoSurgeryResolution.HasEssentialSurgeryInputs
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge resolvedIndex : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    [Fintype resolvedIndex] [DecidableEq resolvedIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex) : Prop :=
  ∀ i, (Q.stage.circle i).Essential →
    Nonempty (EssentialResolvedBarrierCircleSurgeryData Q.stage i)

/-- The essential branch of a resolved barrier is an event-covered compression. -/
theorem FiniteBarrierTwoSurgeryResolution.compression_of_essential
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge resolvedIndex : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    [Fintype resolvedIndex] [DecidableEq resolvedIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex)
    (hinputs : Q.HasEssentialSurgeryInputs)
    {i : resolvedIndex} (hi : (Q.stage.circle i).Essential) :
    Nonempty (EventCoveredCompressingDisk (Phi := Phi) Q.stage.eventRegion) := by
  obtain ⟨D⟩ := hinputs i hi
  exact D.exists_eventCoveredCompressingDisk

end Submission.Topology
