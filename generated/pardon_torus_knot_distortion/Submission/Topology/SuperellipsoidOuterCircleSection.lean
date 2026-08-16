import Submission.Topology.PeriodicRegularLevelClassification
import Submission.Topology.SuperellipsoidBarrierGraph

/-!
# Finite circle sections of a regular superellipsoid level

The superellipsoid polynomial descends from the covering plane to the product-circle model of
the transported torus.  This file turns a componentwise circle classification of that quotient
level into the finite ambient circle section required by the barrier graph.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-- The superellipsoid polynomial evaluated directly on product-circle torus coordinates. -/
def superellipsoidTorusPolynomial (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (z : Circle × Circle) : ℝ :=
  superellipsoidPolynomial frame c (transportedTorusMap Phi z)

theorem continuous_superellipsoidTorusPolynomial (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) :
    Continuous (superellipsoidTorusPolynomial Phi frame c) :=
  (contDiff_superellipsoidPolynomial frame c).continuous.comp
    (transportedTorusMap_continuous Phi)

/-- The genuine quotient-torus polynomial level underlying an outer superellipsoid section. -/
def superellipsoidTorusPolynomialLevelSet (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set (Circle × Circle) :=
  periodicQuotientLevelSet (superellipsoidTorusPolynomial Phi frame c) (R ^ 256)

theorem isClosed_superellipsoidTorusPolynomialLevelSet (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsClosed (superellipsoidTorusPolynomialLevelSet Phi frame c R) :=
  isClosed_singleton.preimage (continuous_superellipsoidTorusPolynomial Phi frame c)

theorem isCompact_superellipsoidTorusPolynomialLevelSet (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    IsCompact (superellipsoidTorusPolynomialLevelSet Phi frame c R) :=
  (isClosed_superellipsoidTorusPolynomialLevelSet Phi frame c R).isCompact

/-- The planar polynomial lift is the pullback of the quotient-torus polynomial. -/
theorem superellipsoidPolynomialLift_eq_torusPolynomial_expPair
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (uv : Plane) :
    superellipsoidPolynomialLift Phi frame c uv =
      superellipsoidTorusPolynomial Phi frame c (planeExpPair uv) := by
  rw [superellipsoidPolynomialLift, superellipsoidTorusPolynomial,
    transportedTorusPlaneMap_eq_expPair]

/-- A classified quotient component, transported to an ambient embedded torus circle. -/
def superellipsoidEmbeddedCircleOfComponent
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}
    (C : ComponentCircleClassification
      (superellipsoidTorusPolynomialLevelSet Phi frame c R))
    (k : ConnectedComponents
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)) :
    EmbeddedTorusIntersectionCircle Phi := by
  let beta : Circle → Circle × Circle := fun z ↦ C.circleEquiv k z
  have hbeta : Continuous beta := by
    change Continuous (fun z ↦ ((C.circleEquiv k z : componentPiece k) :
      superellipsoidTorusPolynomialLevelSet Phi frame c R).1)
    exact continuous_subtype_val.comp (C.isEmbedding k).continuous
  let loop := FiniteCoordinatePlaneTorusCircleFamily.windingLoopOfCircle
    (Phi := Phi) beta hbeta
  exact {
    circle := fun z ↦ transportedTorusMap Phi (beta z)
    isEmbedding := by
      apply (transportedTorusMap_isEmbedding Phi).comp
      change IsEmbedding (fun z ↦ ((C.circleEquiv k z : componentPiece k) :
        superellipsoidTorusPolynomialLevelSet Phi frame c R).1)
      exact IsEmbedding.subtypeVal.comp (C.isEmbedding k)
    windingLoop := loop
    parametrization := fun _ ↦ rfl }

theorem range_superellipsoidEmbeddedCircleOfComponent
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}
    (C : ComponentCircleClassification
      (superellipsoidTorusPolynomialLevelSet Phi frame c R))
    (k : ConnectedComponents
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)) :
    Set.range (superellipsoidEmbeddedCircleOfComponent C k).circle =
      (fun z : superellipsoidTorusPolynomialLevelSet Phi frame c R ↦
        transportedTorusMap Phi z) '' componentPiece k := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨C.circleEquiv k z, (C.circleEquiv k z).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := (C.circleEquiv k).surjective ⟨z, hz⟩
    refine ⟨w, ?_⟩
    change transportedTorusMap Phi (C.circleEquiv k w) = transportedTorusMap Phi z
    exact congrArg (fun q ↦ transportedTorusMap Phi q.1) hw

/-- A finite family of ambient embedded circles covering one regular outer level. -/
structure FiniteSuperellipsoidOuterTorusCircleFamily
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) where
  index : Type*
  finite_index : Finite index
  circle : index → EmbeddedTorusIntersectionCircle Phi
  circle_mem_outer : ∀ i, Set.range (circle i).circle ⊆
    superellipsoidOuterTorusSection Phi frame c R
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  outer_exact : superellipsoidOuterTorusSection Phi frame c R =
    ⋃ i, Set.range (circle i).circle

namespace FiniteSuperellipsoidOuterTorusCircleFamily

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R : ℝ}

/-- A quotient-level component classification gives the exact finite ambient outer section. -/
def ofClassification
    (hR : 0 ≤ R)
    (hlocal : IsLocallyLineModeled
      (superellipsoidTorusPolynomialLevelSet Phi frame c R))
    (C : ComponentCircleClassification
      (superellipsoidTorusPolynomialLevelSet Phi frame c R)) :
    FiniteSuperellipsoidOuterTorusCircleFamily Phi frame c R := by
  let _ : CompactSpace (superellipsoidTorusPolynomialLevelSet Phi frame c R) :=
    isCompact_iff_compactSpace.mp
      (isCompact_superellipsoidTorusPolynomialLevelSet Phi frame c R)
  let _ : LocallyConnectedSpace
      (superellipsoidTorusPolynomialLevelSet Phi frame c R) :=
    locallyConnectedSpace_of_isLocallyLineModeled hlocal
  let components := finiteComponentDecompositionOfCompactLocallyConnected
    (superellipsoidTorusPolynomialLevelSet Phi frame c R)
  exact {
    index := ConnectedComponents (superellipsoidTorusPolynomialLevelSet Phi frame c R)
    finite_index := components.finite_index
    circle := superellipsoidEmbeddedCircleOfComponent C
    circle_mem_outer := by
      intro k _ hx
      rw [range_superellipsoidEmbeddedCircleOfComponent C k] at hx
      obtain ⟨z, _, rfl⟩ := hx
      exact ⟨⟨z, rfl⟩,
        (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).2 z.property⟩
    pairwise_disjoint := by
      intro k l hkl
      rw [range_superellipsoidEmbeddedCircleOfComponent C k,
        range_superellipsoidEmbeddedCircleOfComponent C l, Set.disjoint_left]
      rintro x ⟨z, hzk, rfl⟩ ⟨w, hwl, hw⟩
      have hzw : z = w := by
        apply Subtype.ext
        apply transportedTorusMap_injective Phi
        exact hw.symm
      exact Set.disjoint_left.mp (pairwise_disjoint_componentPiece hkl) hzk (hzw ▸ hwl)
    outer_exact := by
      ext x
      constructor
      · rintro ⟨⟨z, rfl⟩, hxboundary⟩
        let q : superellipsoidTorusPolynomialLevelSet Phi frame c R :=
          ⟨z, (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).1
            hxboundary⟩
        have hq : q ∈ ⋃ k, componentPiece k := by
          rw [iUnion_componentPiece]
          exact mem_univ q
        simp only [Set.mem_iUnion] at hq ⊢
        obtain ⟨k, hk⟩ := hq
        refine ⟨k, ?_⟩
        rw [range_superellipsoidEmbeddedCircleOfComponent C k]
        exact ⟨q, hk, rfl⟩
      · simp only [Set.mem_iUnion]
        rintro ⟨k, hx⟩
        rw [range_superellipsoidEmbeddedCircleOfComponent C k] at hx
        obtain ⟨z, _, rfl⟩ := hx
        exact ⟨⟨z, rfl⟩,
          (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).2 z.property⟩ }

/-- Regularity of the polynomial lift supplies both quotient local-line charts and the complete
componentwise circle classification. -/
def ofRegularValue
    (hR : 0 ≤ R)
    (hregular : IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256)) :
    FiniteSuperellipsoidOuterTorusCircleFamily Phi frame c R := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (superellipsoidPolynomialLift Phi frame c) :=
    contDiff_superellipsoidPolynomialLift Phi frame c
  have hlocal : IsLocallyLineModeled
      (superellipsoidTorusPolynomialLevelSet Phi frame c R) := by
    change IsLocallyLineModeled
      (periodicQuotientLevelSet (superellipsoidTorusPolynomial Phi frame c) (R ^ 256))
    exact isLocallyLineModeled_periodicQuotientLevel_of_regularValue hf
      (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c) hregular
  have hclassification : ComponentCircleClassification
      (superellipsoidTorusPolynomialLevelSet Phi frame c R) := by
    change ComponentCircleClassification
      (periodicQuotientLevelSet (superellipsoidTorusPolynomial Phi frame c) (R ^ 256))
    exact componentCircleClassification_periodicRegularLevel hf
      (continuous_superellipsoidTorusPolynomial Phi frame c)
      (superellipsoidPolynomialLift_eq_torusPolynomial_expPair Phi frame c) hregular
  exact ofClassification hR hlocal hclassification

/-- Forget the internal finite-index packaging and expose the common barrier-section interface. -/
def toFiniteEmbeddedTorusCircleSection
    (F : FiniteSuperellipsoidOuterTorusCircleFamily Phi frame c R)
    [Fintype F.index] :
    FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R) F.index where
  circle := F.circle
  circle_mem_section := F.circle_mem_outer
  pairwise_disjoint := F.pairwise_disjoint
  section_exact := F.outer_exact

/-- Direct common-interface constructor for a regular outer polynomial level. -/
def finiteSectionOfRegularValue
    (hR : 0 ≤ R)
    (hregular : IsRegularValue (superellipsoidPolynomialLift Phi frame c) (R ^ 256))
    [Fintype (ofRegularValue hR hregular).index] :
    FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R)
      (ofRegularValue hR hregular).index :=
  (ofRegularValue hR hregular).toFiniteEmbeddedTorusCircleSection

end FiniteSuperellipsoidOuterTorusCircleFamily

end Submission.Topology
