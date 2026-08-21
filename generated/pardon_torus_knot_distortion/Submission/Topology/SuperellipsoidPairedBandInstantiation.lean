import Submission.Coarea.SuperellipsoidSeamFubini
import Submission.Topology.SuperellipsoidOuterCircleSection
import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.CircleIntersectionCovering
import Submission.Topology.CrossingSignFlip
import Submission.Topology.SmoothSectionCircleFromOrbit
import Submission.Topology.MaximalDiskSeparatedSupports
import Submission.PlaneSchoenflies.Schoenflies.FiniteCrossingParity

/-!
# Concrete inputs for the superellipsoid paired-band move

This file begins the geometric instantiation of the abstract paired-band surgery layer.  The
first result closes the analytic isolation input: the nonzero seam determinant makes the
polynomial/height map a local homeomorphism by the two-dimensional inverse function theorem.

The second part separates the remaining circle-ordering problem from the ambient collar problem.
A paired seam enumeration is an even cyclic enumeration of the vertices.  From it, chosen inward
excursion arcs, and disjoint support bands, we construct the exact `FiniteBarrierExcursionPairing`
consumed by the standard four-port smoothing.  Thus the only data still geometric are the actual
cyclic decomposition of each regular cutting circle and the ambient transported-torus band
charts; uniqueness of the paired band containing a vertex is proved here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## Seam isolation from the two-dimensional inverse function theorem -/

/-- The derivative of the seam map is invertible at every selected seam point. -/
theorem superellipsoidSeamMap_fderiv_det_ne_zero
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    {uv : Plane}
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    (fderiv ℝ (superellipsoidSeamMap Phi frame c) uv).det ≠ 0 := by
  have huvEq : superellipsoidSeamMap Phi frame c uv = (R ^ 256, d) := huv
  have hlevel : superellipsoidPolynomialLift Phi frame c uv = R ^ 256 :=
    by simpa only [superellipsoidSeamMap] using congrArg Prod.fst huvEq
  have hheight : orientedCoordinateLift Phi frame 2 uv = d :=
    by simpa only [superellipsoidSeamMap] using congrArg Prod.snd huvEq
  have hdetFormula :
      (fderiv ℝ (superellipsoidSeamMap Phi frame c) uv).det =
        planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
          (orientedCoordinateLift Phi frame 2) uv := by
    change (fderiv ℝ (superellipsoidSeamPairMap Phi frame c) uv).det = _
    exact det_fderiv_superellipsoidSeamPairMap Phi frame c uv
  rw [hdetFormula]
  exact hseam uv hlevel hheight

/-- The selected regular seam has the exact local-inverse neighborhoods required by the finite
barrier graph.  The separate regularity hypotheses are retained in the interface for compatibility
with the selector, but transversality of the simultaneous map is the operative hypothesis. -/
theorem hasSuperellipsoidSeamLocalInverses
    (Phi : AmbientIsotopy) : HasSuperellipsoidSeamLocalInverses Phi := by
  intro frame c R d _houter _hcut hseam uv huv
  let L := fderiv ℝ (superellipsoidSeamMap Phi frame c) uv
  have hdet : L.det ≠ 0 :=
    superellipsoidSeamMap_fderiv_det_ne_zero Phi frame c R d hseam huv
  let e : Plane ≃L[ℝ] Plane := L.toContinuousLinearEquivOfDetNeZero hdet
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamMap Phi frame c) := by
    change ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamPairMap Phi frame c)
    exact contDiff_superellipsoidSeamPairMap Phi frame c
  have hderiv : HasFDerivAt (superellipsoidSeamMap Phi frame c)
      (e : Plane →L[ℝ] Plane) uv := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hsmooth.differentiable (by simp) uv).hasFDerivAt
  let chart := hsmooth.contDiffAt.toOpenPartialHomeomorph
    (superellipsoidSeamMap Phi frame c) hderiv (by simp)
  refine ⟨chart.source, chart.open_source, ?_, chart.injOn⟩
  exact hsmooth.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)

/-- The actual local inverse-function chart retained at a selected seam lift.  Unlike the
set-level isolation contract, this object keeps the inverse map needed for the endpoint patch. -/
noncomputable def superellipsoidSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    OpenPartialHomeomorph Plane Plane := by
  let L := fderiv ℝ (superellipsoidSeamMap Phi frame c) uv
  have hdet : L.det ≠ 0 :=
    superellipsoidSeamMap_fderiv_det_ne_zero Phi frame c R d hseam huv
  let e : Plane ≃L[ℝ] Plane := L.toContinuousLinearEquivOfDetNeZero hdet
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamMap Phi frame c) := by
    change ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamPairMap Phi frame c)
    exact contDiff_superellipsoidSeamPairMap Phi frame c
  have hderiv : HasFDerivAt (superellipsoidSeamMap Phi frame c)
      (e : Plane →L[ℝ] Plane) uv := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hsmooth.differentiable (by simp) uv).hasFDerivAt
  exact hsmooth.contDiffAt.toOpenPartialHomeomorph
    (superellipsoidSeamMap Phi frame c) hderiv (by simp)

theorem mem_source_superellipsoidSeamLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    uv ∈ (superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv).source := by
  let L := fderiv ℝ (superellipsoidSeamMap Phi frame c) uv
  have hdet : L.det ≠ 0 :=
    superellipsoidSeamMap_fderiv_det_ne_zero Phi frame c R d hseam huv
  let e : Plane ≃L[ℝ] Plane := L.toContinuousLinearEquivOfDetNeZero hdet
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamMap Phi frame c) := by
    change ContDiff ℝ (⊤ : ℕ∞) (superellipsoidSeamPairMap Phi frame c)
    exact contDiff_superellipsoidSeamPairMap Phi frame c
  have hderiv : HasFDerivAt (superellipsoidSeamMap Phi frame c)
      (e : Plane →L[ℝ] Plane) uv := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hsmooth.differentiable (by simp) uv).hasFDerivAt
  exact hsmooth.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)

@[simp]
theorem superellipsoidSeamLocalHomeomorph_apply
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv z =
      superellipsoidSeamMap Phi frame c z := by
  rfl

/-- Consequently the compact fundamental seam is discrete, hence finite. -/
theorem hasSuperellipsoidSeamIsolation
    (Phi : AmbientIsotopy) : HasSuperellipsoidSeamIsolation Phi :=
  hasSuperellipsoidSeamIsolation_of_localInverses
    (hasSuperellipsoidSeamLocalInverses Phi)

/-- On a positive scale, the open metric superellipsoid is exactly the strict polynomial
sublevel.  This is the signed-coordinate form needed in the seam inverse-function chart. -/
theorem mem_superellipsoidBody_iff_polynomial_lt_pow
    (frame : Equiv.Perm (Fin 3)) (c x : R3) {R : ℝ} (hR : 0 < R) :
    x ∈ superellipsoidBody frame c R ↔
      superellipsoidPolynomial frame c x < R ^ 256 := by
  have hpoly : 0 ≤ superellipsoidPolynomial frame c x :=
    superellipsoidPolynomial_nonneg frame c x
  rw [superellipsoidBody, Set.mem_ofPred_eq,
    superellipsoidGauge_eq_polynomial_rpow]
  have hroot :
      ((superellipsoidPolynomial frame c x) ^ (1 / (256 : ℝ))) ^ 256 =
        superellipsoidPolynomial frame c x := by
    simpa [one_div] using Real.rpow_inv_natCast_pow hpoly (n := 256) (by norm_num)
  nth_rewrite 2 [← hroot]
  exact (pow_lt_pow_iff_left₀ (n := 256) (Real.rpow_nonneg hpoly _) hR.le
    (by norm_num)).symm

/-- In covering-plane coordinates, the literal barrier has the elementary signed equation
`outer = 0` or (`outer < 0` and `height = 0`).  This global pointwise identity is the analytic
input for identifying every local seam inverse chart with a standard `T`-patch. -/
theorem transportedTorusPlaneMap_mem_barrier_iff
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (hR : 0 < R) (uv : Plane) :
    transportedTorusPlaneMap Phi uv ∈ G.carrier ↔
      superellipsoidPolynomialLift Phi frame c uv = R ^ 256 ∨
        (superellipsoidPolynomialLift Phi frame c uv < R ^ 256 ∧
          orientedCoordinateLift Phi frame 2 uv = d) := by
  rw [G.carrier_eq_ambientBarrier]
  have htorus : transportedTorusPlaneMap Phi uv ∈ transportedTorus Phi := by
    rw [← range_transportedTorusPlaneMap Phi]
    exact Set.mem_range_self uv
  rw [superellipsoidAmbientBarrier, Set.mem_inter_iff, and_iff_right htorus]
  simp only [Set.mem_union, Set.mem_inter_iff]
  rw [mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le,
    mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ hR]
  simp only [coordinateCuttingPlane, Set.mem_ofPred_eq, superellipsoidPolynomialLift,
    orientedCoordinateLift, ambientCoordinate_apply]

/-- Seam coordinates centered at the chosen outer level and cutting height. -/
def centeredSuperellipsoidSeamMap
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (R d : ℝ) (uv : Plane) : Plane :=
  (superellipsoidPolynomialLift Phi frame c uv - R ^ 256,
    orientedCoordinateLift Phi frame 2 uv - d)

/-- The covering-plane barrier is exactly the standard signed `T` equation in centered seam
coordinates.  A local inverse for this map therefore supplies the endpoint four-port model; the
remaining global gluing only joins the two endpoint models along the embedded inward arc. -/
theorem centeredSuperellipsoidSeamMap_mem_standardT_iff
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (hR : 0 < R) (uv : Plane) :
    transportedTorusPlaneMap Phi uv ∈ G.carrier ↔
      (centeredSuperellipsoidSeamMap Phi frame c R d uv).1 = 0 ∨
        ((centeredSuperellipsoidSeamMap Phi frame c R d uv).1 < 0 ∧
          (centeredSuperellipsoidSeamMap Phi frame c R d uv).2 = 0) := by
  rw [transportedTorusPlaneMap_mem_barrier_iff G hR]
  simp only [centeredSuperellipsoidSeamMap, sub_eq_zero, sub_lt_zero]

/-- On the retained inverse-function neighborhood at a seam lift, membership in the literal
barrier is read directly in the two local chart coordinates. -/
theorem superellipsoidSeamLocalHomeomorph_mem_barrier_iff
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)})
    (z : Plane) :
    transportedTorusPlaneMap Phi z ∈ G.carrier ↔
      (superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 =
          R ^ 256 ∨
        ((superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv z).1 <
            R ^ 256 ∧
          (superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv z).2 = d) := by
  rw [superellipsoidSeamLocalHomeomorph_apply,
    transportedTorusPlaneMap_mem_barrier_iff G hR]
  rfl

/-- With seam isolation now discharged, two classified regular circle sections and the local
closure-gluing statement construct the finite analytic barrier graph directly. -/
def FiniteSuperellipsoidBarrierGraph.ofRegularSectionsAndTransversality
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (hR : 0 ≤ R)
    (houterRegular : IsRegularValue
      (superellipsoidPolynomialLift Phi frame c) (R ^ 256))
    (hcutRegular : IsRegularValue (orientedCoordinateLift Phi frame 2) d)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (outer : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidOuterTorusSection Phi frame c R) outerIndex)
    (cut : FiniteEmbeddedTorusCircleSection Phi
      (superellipsoidCutTorusSection Phi frame d) cutIndex)
    (hclosure :
      closure
          (superellipsoidCutTorusSection Phi frame d ∩
            superellipsoidBody frame c R) ∩
        superellipsoidOuterTorusSection Phi frame c R =
          superellipsoidTorusSeam Phi frame c R d) :
    FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex :=
  .ofRegularSections hR outer cut
    (hasSuperellipsoidSeamIsolation Phi frame c R d
      houterRegular hcutRegular hseam)
    hclosure

/-! ## Pure paired cyclic ordering -/

/-- The canonical vertex type of the analytic barrier graph. -/
def SuperellipsoidSeamVertex (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :=
  superellipsoidTorusSeam Phi frame c R d

/-- Seam finiteness supplies a concrete finite type without adding an enumeration field to the
analytic graph. -/
@[instance_reducible]
noncomputable def FiniteSuperellipsoidBarrierGraph.seamVertexFintype
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    Fintype (SuperellipsoidSeamVertex Phi frame c R d) :=
  G.seam_finite.fintype

/-- An explicit even enumeration of a finite seam.  The first coordinate is the inward excursion
band and the second coordinate chooses its two endpoints.  This is the precise finite output of
sorting the transverse intersections cyclically along the cutting circles. -/
structure PairedSeamEnumeration (vertex : Type*) where
  bandCount : ℕ
  endpointEquiv : Fin bandCount × Fin 2 ≃ vertex

namespace PairedSeamEnumeration

variable {vertex : Type*}

/-- Once cyclic sign alternation proves that the vertex count is twice the number of inward
excursions, the finite enumeration itself is automatic. -/
noncomputable def of_card_eq_two_mul [Fintype vertex] (bandCount : ℕ)
    (hcard : Fintype.card vertex = 2 * bandCount) :
    PairedSeamEnumeration vertex where
  bandCount := bandCount
  endpointEquiv := Fintype.equivOfCardEq (by
    simp [hcard, Nat.mul_comm])

def firstVertex (E : PairedSeamEnumeration vertex) (b : Fin E.bandCount) : vertex :=
  E.endpointEquiv (b, 0)

def secondVertex (E : PairedSeamEnumeration vertex) (b : Fin E.bandCount) : vertex :=
  E.endpointEquiv (b, 1)

theorem paired_vertices_ne (E : PairedSeamEnumeration vertex)
    (b : Fin E.bandCount) : E.firstVertex b ≠ E.secondVertex b := by
  intro h
  have hp : (b, (0 : Fin 2)) = (b, (1 : Fin 2)) := E.endpointEquiv.injective h
  have := congrArg Prod.snd hp
  norm_num at this

theorem every_vertex_in_unique_band (E : PairedSeamEnumeration vertex) (v : vertex) :
    ∃! b, v = E.firstVertex b ∨ v = E.secondVertex b := by
  let p := E.endpointEquiv.symm v
  refine ⟨p.1, ?_, ?_⟩
  · have hp : p.2 = 0 ∨ p.2 = 1 := by omega
    rcases hp with hp | hp
    · left
      change v = E.endpointEquiv (p.1, 0)
      rw [← hp]
      exact (E.endpointEquiv.apply_symm_apply v).symm
    · right
      change v = E.endpointEquiv (p.1, 1)
      rw [← hp]
      exact (E.endpointEquiv.apply_symm_apply v).symm
  · intro b hb
    rcases hb with hb | hb
    · have hp : (b, (0 : Fin 2)) = p := by
        apply E.endpointEquiv.injective
        rw [E.endpointEquiv.apply_symm_apply]
        exact hb.symm
      exact congrArg Prod.fst hp
    · have hp : (b, (1 : Fin 2)) = p := by
        apply E.endpointEquiv.injective
        rw [E.endpointEquiv.apply_symm_apply]
        exact hb.symm
      exact congrArg Prod.fst hp

end PairedSeamEnumeration

/-! ## Pairing derived from cyclic sign alternation -/

/-- A finite cyclic list of complementary intervals with a side label that changes at every
crossing.  This is the pure output of applying the local seam chart to the intervals between the
sorted crossings of one cutting circle.  `false` is the inward side.

Unlike `PairedSeamEnumeration`, this structure contains no pairing: the perfect pairing of
vertices is proved below. -/
structure AlternatingCyclicSideData (n : ℕ) where
  neZero : NeZero n
  side : ZMod n → Bool
  changes : ∀ i, side (i + 1) ≠ side i

namespace AlternatingCyclicSideData

variable {n : ℕ}

/-- The cyclic intervals lying strictly in the superellipsoid body. -/
def InwardGap (D : AlternatingCyclicSideData n) :=
  {i : ZMod n // D.side i = false}

noncomputable instance (D : AlternatingCyclicSideData n) : Fintype D.InwardGap := by
  letI := D.neZero
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The two endpoints of an inward interval: its left crossing and its cyclic successor. -/
def endpoint (D : AlternatingCyclicSideData n) : D.InwardGap × Fin 2 → ZMod n
  | (i, e) => if e = 0 then i.1 else i.1 + 1

theorem side_pred_eq_false_of_side_eq_true
    (D : AlternatingCyclicSideData n) {i : ZMod n}
    (hi : D.side i = true) : D.side (i - 1) = false := by
  have hchange := D.changes (i - 1)
  have hadd : i - 1 + 1 = i := by abel
  rw [hadd, hi] at hchange
  cases hpred : D.side (i - 1) <;> simp_all

/-- Each crossing is incident to an inward interval: if the outgoing interval is outward, the
incoming one is inward. -/
theorem surjective_endpoint (D : AlternatingCyclicSideData n) :
    Function.Surjective D.endpoint := by
  intro i
  cases hi : D.side i with
  | false =>
      refine ⟨(⟨i, hi⟩, (0 : Fin 2)), ?_⟩
      simp [endpoint]
  | true =>
      have hpred := D.side_pred_eq_false_of_side_eq_true hi
      refine ⟨(⟨i - 1, hpred⟩, (1 : Fin 2)), ?_⟩
      simp [endpoint]

/-- No crossing is an endpoint of two distinct inward intervals.  The mixed endpoint cases would
make two adjacent intervals inward, contrary to transversality. -/
theorem injective_endpoint (D : AlternatingCyclicSideData n) :
    Function.Injective D.endpoint := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · apply Prod.ext
    · apply Subtype.ext
      simpa [endpoint] using h
    · rfl
  · have hij : i.1 = j.1 + 1 := by
      simpa [endpoint] using h
    have hchange := D.changes j.1
    rw [← hij, i.property, j.property] at hchange
    contradiction
  · have hij : i.1 + 1 = j.1 := by
      simpa [endpoint] using h
    have hchange := D.changes i.1
    rw [hij, i.property, j.property] at hchange
    contradiction
  · apply Prod.ext
    · apply Subtype.ext
      have hij : i.1 + 1 = j.1 + 1 := by
        simpa [endpoint] using h
      exact add_right_cancel hij
    · rfl

/-- Cyclic sign alternation canonically identifies the two endpoints of all inward intervals with
the complete crossing set. -/
noncomputable def endpointEquiv (D : AlternatingCyclicSideData n) :
    D.InwardGap × Fin 2 ≃ ZMod n :=
  Equiv.ofBijective D.endpoint ⟨D.injective_endpoint, D.surjective_endpoint⟩

/-- After identifying the cyclic crossing indices with geometric vertices, the pairing required
by the moving-sphere construction is a theorem, not an enumeration hypothesis. -/
noncomputable def toPairedSeamEnumeration
    (D : AlternatingCyclicSideData n) {vertex : Type*} [Fintype vertex]
    (crossingEquiv : ZMod n ≃ vertex) : PairedSeamEnumeration vertex where
  bandCount := Fintype.card D.InwardGap
  endpointEquiv :=
    ((Fintype.equivFin D.InwardGap).symm.prodCongr (Equiv.refl (Fin 2))).trans
      (D.endpointEquiv.trans crossingEquiv)

end AlternatingCyclicSideData

/-! ## Canonical crossings on each cutting circle -/

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]

/-- Parameters in one half-open period where a chosen cutting circle meets the outer seam. -/
def cutCircleSeamParameterSet
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Set ℝ :=
  Ico (0 : ℝ) (2 * Real.pi) ∩
    (fun t ↦ ((G.cut.circle j).windingLoop.curve t : R3)) ⁻¹'
      superellipsoidTorusSeam Phi frame c R d

theorem cutCircle_curve_injective_on_period
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :
    Set.InjOn (fun t ↦ ((G.cut.circle j).windingLoop.curve t : R3))
      (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  have hexp : Circle.exp s = Circle.exp t := by
    apply (G.cut.circle j).isEmbedding.injective
    rw [(G.cut.circle j).parametrization, (G.cut.circle j).parametrization]
    exact hst
  exact Circle.exp_injOn_Ico (by simp) hs ht hexp

/-- Finiteness is inherited from the ambient finite seam; no regular-fiber theorem is rerun on
the one-dimensional parametrization. -/
theorem cutCircleSeamParameterSet_finite
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : (G.cutCircleSeamParameterSet j).Finite := by
  apply Set.Finite.of_finite_image
  · apply G.seam_finite.subset
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  · exact (G.cutCircle_curve_injective_on_period j).mono inter_subset_left

/-- The canonical finite set of seam parameters on a cutting circle. -/
noncomputable def cutCircleSeamCrossings
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Finset ℝ :=
  (G.cutCircleSeamParameterSet_finite j).toFinset

theorem mem_cutCircleSeamCrossings_iff
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) :
    t ∈ G.cutCircleSeamCrossings j ↔
      t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
        ((G.cut.circle j).windingLoop.curve t : R3) ∈
          superellipsoidTorusSeam Phi frame c R d := by
  simp only [cutCircleSeamCrossings, Set.Finite.mem_toFinset,
    cutCircleSeamParameterSet, Set.mem_inter_iff, Set.mem_preimage]

/-- Geometric seam vertices lying on one specified cutting circle. -/
def CutCircleSeamVertex
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :=
  Set.range (G.cut.circle j).circle ∩
    superellipsoidTorusSeam Phi frame c R d

noncomputable instance cutCircleSeamVertexFintype
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Fintype (G.CutCircleSeamVertex j) :=
  (G.seam_finite.subset inter_subset_right).fintype

/-- The seam vertices indexed by the unique cutting circle on which they lie. -/
def CutCircleIndexedSeamVertex
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :=
  Σ j : cutIndex, G.CutCircleSeamVertex j

/-- Pairwise disjointness and exact coverage of the cutting-circle family identify the sigma type
of per-circle vertices with the full analytic seam. -/
noncomputable def cutCircleIndexedSeamVertexEquiv
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    G.CutCircleIndexedSeamVertex ≃
      SuperellipsoidSeamVertex Phi frame c R d := by
  let eval : G.CutCircleIndexedSeamVertex →
      SuperellipsoidSeamVertex Phi frame c R d :=
    fun x ↦ ⟨x.2.1, x.2.2.2⟩
  apply Equiv.ofBijective eval
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : x.1 = y.1 := congrArg Subtype.val hxy
    have hij : i = j := by
      by_contra hij
      have hdisjoint := G.cut.pairwise_disjoint hij
      change Disjoint (Set.range (G.cut.circle i).circle)
        (Set.range (G.cut.circle j).circle) at hdisjoint
      rw [Set.disjoint_left] at hdisjoint
      exact hdisjoint x.2.1 (hval.symm ▸ y.2.1)
    subst j
    have hxy : x = y := Subtype.ext hval
    subst y
    rfl
  · intro x
    have hxCut : x.1 ∈ superellipsoidCutTorusSection Phi frame d :=
      ⟨x.2.1.1, x.2.2⟩
    rw [G.cut.section_exact] at hxCut
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut
    exact ⟨⟨j, ⟨x.1, ⟨hj, x.2⟩⟩⟩, by
      apply Subtype.ext
      rfl⟩

/-- Evaluation identifies the canonical real crossing set with the geometric seam vertices on
the circle.  In particular, the cyclic enumeration below is not supplied as geometric data. -/
noncomputable def cutCircleCrossingEquiv
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :
    {t // t ∈ G.cutCircleSeamCrossings j} ≃ G.CutCircleSeamVertex j := by
  let eval : {t // t ∈ G.cutCircleSeamCrossings j} → G.CutCircleSeamVertex j :=
    fun t ↦ ⟨(G.cut.circle j).windingLoop.curve t.1, by
      have ht := (G.mem_cutCircleSeamCrossings_iff j t.1).mp t.2
      exact ⟨⟨Circle.exp t.1, (G.cut.circle j).parametrization t.1⟩, ht.2⟩⟩
  apply Equiv.ofBijective eval
  constructor
  · intro s t hst
    apply Subtype.ext
    apply G.cutCircle_curve_injective_on_period j
    · exact (G.mem_cutCircleSeamCrossings_iff j s.1).mp s.2 |>.1
    · exact (G.mem_cutCircleSeamCrossings_iff j t.1).mp t.2 |>.1
    · change ((G.cut.circle j).windingLoop.curve s.1 : R3) =
        ((G.cut.circle j).windingLoop.curve t.1 : R3)
      exact congrArg (fun z ↦ (z.1 : R3)) hst
  · intro x
    obtain ⟨z, hz⟩ := x.2.1
    let t := circlePhaseRepresentative z
    have htcurve : (G.cut.circle j).windingLoop.curve t = x.1 := by
      rw [← (G.cut.circle j).parametrization t,
        exp_circlePhaseRepresentative, hz]
    have htmem : t ∈ G.cutCircleSeamCrossings j :=
      (G.mem_cutCircleSeamCrossings_iff j t).mpr
        ⟨circlePhaseRepresentative_mem z, htcurve.symm ▸ x.2.2⟩
    refine ⟨⟨t, htmem⟩, ?_⟩
    apply Subtype.ext
    exact htcurve

/-- A geometric seam vertex makes the canonical crossing finset on its cutting circle nonempty. -/
theorem cutCircleSeamCrossings_nonempty_of_vertex
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (x : G.CutCircleSeamVertex j) :
    (G.cutCircleSeamCrossings j).Nonempty := by
  obtain ⟨z, hz⟩ := x.2.1
  let t := circlePhaseRepresentative z
  have htcurve : (G.cut.circle j).windingLoop.curve t = x.1 := by
    rw [← (G.cut.circle j).parametrization t,
      exp_circlePhaseRepresentative, hz]
  exact ⟨t, (G.mem_cutCircleSeamCrossings_iff j t).mpr
    ⟨circlePhaseRepresentative_mem z, htcurve.symm ▸ x.2.2⟩⟩

/-- Therefore a cutting circle with no canonical crossing contributes no seam vertex. -/
theorem cutCircleSeamVertex_isEmpty_of_not_nonempty
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (h : ¬(G.cutCircleSeamCrossings j).Nonempty) :
  IsEmpty (G.CutCircleSeamVertex j) :=
  ⟨fun x ↦ h (G.cutCircleSeamCrossings_nonempty_of_vertex j x)⟩

/-- Cutting circles that actually participate in the finite barrier graph. -/
def ActiveCutCircle
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :=
  {j : cutIndex // (G.cutCircleSeamCrossings j).Nonempty}

noncomputable instance activeCutCircleFintype
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    Fintype G.ActiveCutCircle := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Restricting the sigma decomposition to active cutting circles loses no seam vertex. -/
noncomputable def activeCutCircleSeamVertexEquiv
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    (Σ j : G.ActiveCutCircle, G.CutCircleSeamVertex j.1) ≃
      SuperellipsoidSeamVertex Phi frame c R d := by
  let eval : (Σ j : G.ActiveCutCircle, G.CutCircleSeamVertex j.1) →
      SuperellipsoidSeamVertex Phi frame c R d :=
    fun x ↦ ⟨x.2.1, x.2.2.2⟩
  apply Equiv.ofBijective eval
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : x.1 = y.1 := congrArg Subtype.val hxy
    have hij : i.1 = j.1 := by
      by_contra hij
      have hdisjoint := G.cut.pairwise_disjoint hij
      change Disjoint (Set.range (G.cut.circle i.1).circle)
        (Set.range (G.cut.circle j.1).circle) at hdisjoint
      rw [Set.disjoint_left] at hdisjoint
      exact hdisjoint x.2.1 (hval.symm ▸ y.2.1)
    have hijSubtype : i = j := Subtype.ext hij
    subst j
    have hxy : x = y := Subtype.ext hval
    subst y
    rfl
  · intro x
    have hxCut : x.1 ∈ superellipsoidCutTorusSection Phi frame d :=
      ⟨x.2.1.1, x.2.2⟩
    rw [G.cut.section_exact] at hxCut
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxCut
    let y : G.CutCircleSeamVertex j := ⟨x.1, ⟨hj, x.2⟩⟩
    let ja : G.ActiveCutCircle :=
      ⟨j, G.cutCircleSeamCrossings_nonempty_of_vertex j y⟩
    exact ⟨⟨ja, y⟩, by
      apply Subtype.ext
      rfl⟩

/-- If a cutting circle has a seam crossing, its canonical sorted crossing set has a cyclic
indexing.  This is merely finite sorting plus the canonical phase representative. -/
noncomputable def cutCircleCyclicCrossingEquiv
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    ZMod (G.cutCircleSeamCrossings j).card ≃ G.CutCircleSeamVertex j := by
  letI : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  exact (ZMod.finEquiv (G.cutCircleSeamCrossings j).card).symm.toEquiv.trans
    (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).toEquiv.trans
      (G.cutCircleCrossingEquiv j))

end FiniteSuperellipsoidBarrierGraph

/-! ## Cyclic inward excursions derived from the canonical crossings -/

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]

/-- Signed outer gauge along a cutting circle.  Its negative set is exactly the inward part of
that circle, while its zero set is the seam. -/
def cutCircleOuterGaugeDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) : ℝ :=
  superellipsoidGauge frame c ((G.cut.circle j).windingLoop.curve t : R3) - R

theorem continuous_cutCircleOuterGaugeDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Continuous (G.cutCircleOuterGaugeDifference j) := by
  exact ((continuous_superellipsoidGauge frame c).comp
    (continuous_subtype_val.comp
      (G.cut.circle j).windingLoop.continuous_curve)).sub continuous_const

theorem periodic_cutCircleOuterGaugeDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :
    Function.Periodic (G.cutCircleOuterGaugeDifference j) (2 * Real.pi) := by
  intro t
  simp only [cutCircleOuterGaugeDifference]
  rw [(G.cut.circle j).windingLoop.periodic_curve]

theorem cutCircleOuterGaugeDifference_eq_zero_iff_seam
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) :
    G.cutCircleOuterGaugeDifference j t = 0 ↔
      ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
  have hcut := G.cut.circle_mem_section j
    ⟨Circle.exp t, (G.cut.circle j).parametrization t⟩
  simp only [cutCircleOuterGaugeDifference, sub_eq_zero,
    superellipsoidTorusSeam, superellipsoidBoundary, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  exact ⟨fun h ↦ ⟨⟨hcut.1, h⟩, hcut.2⟩, fun h ↦ h.1.2⟩

theorem cutCircleOuterGaugeDifference_neg_iff_body
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) :
    G.cutCircleOuterGaugeDifference j t < 0 ↔
      ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidBody frame c R := by
  simp only [cutCircleOuterGaugeDifference, sub_neg, superellipsoidBody,
    Set.mem_ofPred_eq]

/-- The smooth polynomial version of the outer signed coordinate.  This is the coordinate to
which the ordinary one-variable sign-flip theorem is applied. -/
def cutCircleOuterPolynomialDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) : ℝ :=
  superellipsoidPolynomial frame c ((G.cut.circle j).windingLoop.curve t : R3) - R ^ 256

theorem continuous_cutCircleOuterPolynomialDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : Continuous (G.cutCircleOuterPolynomialDifference j) := by
  exact ((contDiff_superellipsoidPolynomial frame c).continuous.comp
    (continuous_subtype_val.comp
      (G.cut.circle j).windingLoop.continuous_curve)).sub continuous_const

theorem periodic_cutCircleOuterPolynomialDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) :
    Function.Periodic (G.cutCircleOuterPolynomialDifference j) (2 * Real.pi) := by
  intro t
  simp only [cutCircleOuterPolynomialDifference]
  rw [(G.cut.circle j).windingLoop.periodic_curve]

theorem cutCircleOuterPolynomialDifference_eq_zero_iff_seam
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hR : 0 ≤ R) (t : ℝ) :
    G.cutCircleOuterPolynomialDifference j t = 0 ↔
      ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
  have hcut := G.cut.circle_mem_section j
    ⟨Circle.exp t, (G.cut.circle j).parametrization t⟩
  rw [cutCircleOuterPolynomialDifference, sub_eq_zero]
  constructor
  · intro h
    exact ⟨⟨hcut.1,
      (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mpr h⟩,
        hcut.2⟩
  · intro h
    exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mp
      h.1.2

theorem cutCircleOuterPolynomialDifference_neg_iff_body
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hR : 0 < R) (t : ℝ) :
    G.cutCircleOuterPolynomialDifference j t < 0 ↔
      ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidBody frame c R := by
  let x : R3 := (G.cut.circle j).windingLoop.curve t
  have hpoly : 0 ≤ superellipsoidPolynomial frame c x :=
    superellipsoidPolynomial_nonneg frame c x
  change superellipsoidPolynomial frame c x - R ^ 256 < 0 ↔
    superellipsoidGauge frame c x < R
  rw [sub_neg, superellipsoidGauge_eq_polynomial_rpow]
  have hroot :
      ((superellipsoidPolynomial frame c x) ^ (1 / (256 : ℝ))) ^ 256 =
        superellipsoidPolynomial frame c x := by
    simpa [one_div] using Real.rpow_inv_natCast_pow hpoly (n := 256) (by norm_num)
  nth_rewrite 1 [← hroot]
  exact pow_lt_pow_iff_left₀ (n := 256) (Real.rpow_nonneg hpoly _) hR.le (by norm_num)

/-- The retained real lift of a smooth coordinate-level orbit.  The canonical cutting-circle
family produced by `RegularOrbitStandardPeriodData` has exactly this data: `lift` is
`standardLift`, and `scale` is its nonzero affine reparametrization factor.

This structure contains no crossing order or pairing. -/
structure SmoothCutCircleLiftData
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) where
  lift : ℝ → Plane
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  contDiff_lift : ContDiff ℝ 1 lift
  curve_eq : ∀ t,
    transportedTorusPlaneMap Phi (lift t) =
      ((G.cut.circle j).windingLoop.curve t : R3)
  height_level : ∀ t, orientedCoordinateLift Phi frame 2 (lift t) = d
  integral : ∀ t, HasDerivAt lift
    (scale • rotatedDerivativeField
      (orientedCoordinateLift Phi frame 2) (lift t)) t

namespace SmoothCutCircleLiftData

variable {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {j : cutIndex}

/-- The complete rotated-gradient orbit used to construct the canonical smooth cutting circle
instantiates the retained-lift interface without any additional analytic hypothesis. -/
def ofRegularOrbitStandardPeriodData
    {component : ConnectedComponents (coordinateTorusLevelSet Phi frame d)}
    [CompactSpace (componentPiece component)]
    (O : Submission.SurfaceRegularValue.RegularComponentCompleteOrbit
      Phi frame d component)
    (M : RegularOrbitStandardPeriodData O)
    (hcircle : G.cut.circle j = M.embeddedCircle) :
    SmoothCutCircleLiftData G j where
  lift := O.standardLift
  scale := (2 * Real.pi)⁻¹ * O.cyclicLineParametrization.period
  scale_ne_zero := mul_ne_zero (inv_ne_zero (ne_of_gt Real.two_pi_pos))
    O.cyclicLineParametrization.period_ne_zero
  contDiff_lift := O.contDiff_standardLift
  curve_eq := by
    intro t
    rw [hcircle]
    change transportedTorusPlaneMap Phi (O.standardLift t) =
      transportedTorusMap Phi (M.coordinates t)
    rw [transportedTorusPlaneMap_eq_expPair]
    rfl
  height_level := O.standardLift_stays_in_level
  integral := by
    intro t
    have hderiv := (O.contDiff_standardLift.differentiable (by simp) t).hasDerivAt
    rw [O.deriv_standardLift] at hderiv
    exact hderiv

/-- Differentiating the outer polynomial along the rotated-gradient cutting orbit gives the
swapped planar Jacobian, multiplied by the nonzero time-rescaling factor. -/
theorem hasDerivAt_outerPolynomialDifference
    (D : SmoothCutCircleLiftData G j) (t : ℝ) :
    HasDerivAt (G.cutCircleOuterPolynomialDifference j)
      (D.scale * planarDifferentialDet
        (orientedCoordinateLift Phi frame 2)
        (superellipsoidPolynomialLift Phi frame c) (D.lift t)) t := by
  have hpoly : DifferentiableAt ℝ (superellipsoidPolynomialLift Phi frame c) (D.lift t) :=
    (contDiff_superellipsoidPolynomialLift Phi frame c).differentiable
      (by simp) (D.lift t)
  have hcomp := hpoly.hasFDerivAt.comp_hasDerivAt t (D.integral t)
  have heval :
      fderiv ℝ (superellipsoidPolynomialLift Phi frame c) (D.lift t)
          (rotatedDerivativeField
            (orientedCoordinateLift Phi frame 2) (D.lift t)) =
        planarDifferentialDet (orientedCoordinateLift Phi frame 2)
          (superellipsoidPolynomialLift Phi frame c) (D.lift t) := by
    rw [rotatedDerivativeField_eq_linearCombination, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, planarDifferentialDet]
    ring
  have hfunction :
      (fun u ↦ superellipsoidPolynomialLift Phi frame c (D.lift u)) =
        fun u ↦ G.cutCircleOuterPolynomialDifference j u + R ^ 256 := by
    funext u
    rw [cutCircleOuterPolynomialDifference, superellipsoidPolynomialLift,
      D.curve_eq]
    ring
  have hderivComp : HasDerivAt
      (fun u ↦ superellipsoidPolynomialLift Phi frame c (D.lift u))
      (D.scale * planarDifferentialDet
        (orientedCoordinateLift Phi frame 2)
        (superellipsoidPolynomialLift Phi frame c) (D.lift t)) t := by
    change HasDerivAt (fun u ↦
      superellipsoidPolynomialLift Phi frame c (D.lift u)) _ t at hcomp
    rw [map_smul, smul_eq_mul, heval] at hcomp
    exact hcomp
  have hadd := hderivComp.sub_const (R ^ 256)
  have hsubfunction :
      (fun u ↦ superellipsoidPolynomialLift Phi frame c (D.lift u) - R ^ 256) =
        G.cutCircleOuterPolynomialDifference j := by
    funext u
    have hu := congrFun hfunction u
    linarith
  rw [hsubfunction] at hadd
  exact hadd

/-- Seam transversality makes every canonical crossing of the smooth cutting orbit a simple zero
of the outer polynomial coordinate. -/
theorem outerPolynomialDerivative_ne_zero_at_crossing
    (D : SmoothCutCircleLiftData G j)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    {t : ℝ} (ht : t ∈ G.cutCircleSeamCrossings j) :
    D.scale * planarDifferentialDet
      (orientedCoordinateLift Phi frame 2)
      (superellipsoidPolynomialLift Phi frame c) (D.lift t) ≠ 0 := by
  have htSeam := (G.mem_cutCircleSeamCrossings_iff j t).mp ht |>.2
  have hR : 0 ≤ R :=
    (superellipsoidGauge_nonneg frame c _).trans_eq htSeam.1.2
  have houter : superellipsoidPolynomialLift Phi frame c (D.lift t) = R ^ 256 := by
    rw [superellipsoidPolynomialLift, D.curve_eq]
    exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mp
      htSeam.1.2
  have hdet : planarDifferentialDet
      (superellipsoidPolynomialLift Phi frame c)
      (orientedCoordinateLift Phi frame 2) (D.lift t) ≠ 0 :=
    hseam (D.lift t) houter (D.height_level t)
  have hswap : planarDifferentialDet
      (orientedCoordinateLift Phi frame 2)
      (superellipsoidPolynomialLift Phi frame c) (D.lift t) =
        -planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
          (orientedCoordinateLift Phi frame 2) (D.lift t) := by
    simp only [planarDifferentialDet]
    ring
  rw [hswap]
  exact mul_ne_zero D.scale_ne_zero (neg_ne_zero.mpr hdet)

/-- The local IFT input closes to the exact analytic sign-flip statement at every canonical seam
crossing of a smooth cutting circle. -/
theorem hasLocalPolynomialSignFlipAtCrossings
    (D : SmoothCutCircleLiftData G j)
    (hR : 0 ≤ R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    ∀ t ∈ G.cutCircleSeamCrossings j, ∃ ε > 0,
      ∀ x ∈ Ioo (t - ε) t, ∀ y ∈ Ioo t (t + ε),
        G.cutCircleOuterPolynomialDifference j x *
          G.cutCircleOuterPolynomialDifference j y < 0 := by
  intro t ht
  apply hasLocalSignFlip_of_hasDerivAt (D.hasDerivAt_outerPolynomialDifference t)
  · have htSeam := (G.mem_cutCircleSeamCrossings_iff j t).mp ht |>.2
    exact sub_eq_zero.mpr
      ((mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR).mp
        htSeam.1.2)
  · exact D.outerPolynomialDerivative_ne_zero_at_crossing hseam ht

end SmoothCutCircleLiftData

/-- Increasing crossing in the canonical half-open period. -/
def cutCircleSortedCrossing
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (i : Fin (G.cutCircleSeamCrossings j).card) : ℝ :=
  (G.cutCircleSeamCrossings j).orderEmbOfFin rfl i

/-- Evaluating the cyclic crossing equivalence is the sorted crossing with the canonical
`ZMod` representative. -/
private theorem val_finEquiv_symm {n : ℕ} [NeZero n] (i : ZMod n) :
    ((ZMod.finEquiv n).symm i).val = i.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem cutCircleCyclicCrossingEquiv_val
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : ZMod (G.cutCircleSeamCrossings j).card) :
    (G.cutCircleCyclicCrossingEquiv j hne i).1 =
      ((G.cut.circle j).windingLoop.curve
        (G.cutCircleSortedCrossing j ⟨i.val, by
          let _ : NeZero (G.cutCircleSeamCrossings j).card :=
            ⟨(Finset.card_pos.mpr hne).ne'⟩
          exact ZMod.val_lt i⟩) : R3) := by
  let _ : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  change ((G.cut.circle j).windingLoop.curve
      (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).toEquiv
        ((ZMod.finEquiv (G.cutCircleSeamCrossings j).card).symm.toEquiv i)).1 : R3) = _
  congr 2
  let k := (ZMod.finEquiv (G.cutCircleSeamCrossings j).card).symm i
  calc
    ↑(((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).toEquiv
        ((ZMod.finEquiv (G.cutCircleSeamCrossings j).card).symm.toEquiv i)) =
        ↑((G.cutCircleSeamCrossings j).orderIsoOfFin rfl k) := rfl
    _ = (G.cutCircleSeamCrossings j).orderEmbOfFin rfl k :=
      Finset.coe_orderIsoOfFin_apply _ _ _
    _ = (G.cutCircleSeamCrossings j).orderEmbOfFin rfl
        ⟨i.val, by exact ZMod.val_lt i⟩ := by
      apply congrArg
      apply Fin.ext
      exact val_finEquiv_symm i
    _ = G.cutCircleSortedCrossing j ⟨i.val, by exact ZMod.val_lt i⟩ := rfl

@[simp]
theorem cutCircleSortedCrossing_mem
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleSortedCrossing j i ∈ G.cutCircleSeamCrossings j :=
  (G.cutCircleSeamCrossings j).orderEmbOfFin_mem rfl i

theorem strictMono_cutCircleSortedCrossing
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) : StrictMono (G.cutCircleSortedCrossing j) :=
  ((G.cutCircleSeamCrossings j).orderEmbOfFin rfl).strictMono

theorem cutCircleSortedCrossing_mem_period
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleSortedCrossing j i ∈ Ico (0 : ℝ) (2 * Real.pi) :=
  (G.mem_cutCircleSeamCrossings_iff j _).mp
    (G.cutCircleSortedCrossing_mem j i) |>.1

theorem cutCircleSortedCrossing_curve_mem_seam
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (i : Fin (G.cutCircleSeamCrossings j).card) :
    ((G.cut.circle j).windingLoop.curve
      (G.cutCircleSortedCrossing j i) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d :=
  (G.mem_cutCircleSeamCrossings_iff j _).mp
    (G.cutCircleSortedCrossing_mem j i) |>.2

theorem cutCircleSortedCrossing_translate_curve_mem_seam
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (i : Fin (G.cutCircleSeamCrossings j).card) (n : ℤ) :
    ((G.cut.circle j).windingLoop.curve
      (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi)) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
  have hperiod := ((G.cut.circle j).windingLoop.periodic_curve.int_mul n)
    (G.cutCircleSortedCrossing j i)
  exact hperiod.symm ▸ G.cutCircleSortedCrossing_curve_mem_seam j i

/-- Lifted cyclic successor of one sorted crossing; the final successor is the first crossing in
the next period. -/
def cutCircleCyclicRight
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) : ℝ :=
  if hi : i.1 + 1 < (G.cutCircleSeamCrossings j).card then
    G.cutCircleSortedCrossing j ⟨i.1 + 1, hi⟩
  else
    G.cutCircleSortedCrossing j
      ⟨0, Finset.card_pos.mpr hne⟩ + 2 * Real.pi

theorem cutCircleSortedCrossing_lt_cyclicRight
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleSortedCrossing j i < G.cutCircleCyclicRight j hne i := by
  unfold cutCircleCyclicRight
  split_ifs with hi
  · exact G.strictMono_cutCircleSortedCrossing j
      (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.1))
  · have hilast : i.1 + 1 = (G.cutCircleSeamCrossings j).card := by omega
    have hiPeriod := G.cutCircleSortedCrossing_mem_period j i
    have hfirstPeriod := G.cutCircleSortedCrossing_mem_period j
      ⟨0, Finset.card_pos.mpr hne⟩
    exact hiPeriod.2.trans_le (by linarith [hfirstPeriod.1])

theorem cutCircleCyclicRight_curve_mem_seam
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    ((G.cut.circle j).windingLoop.curve
      (G.cutCircleCyclicRight j hne i) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
  unfold cutCircleCyclicRight
  split_ifs with hnext
  · exact G.cutCircleSortedCrossing_curve_mem_seam j _
  · have hperiod := (G.cut.circle j).windingLoop.periodic_curve
      (G.cutCircleSortedCrossing j ⟨0, Finset.card_pos.mpr hne⟩)
    exact hperiod.symm ▸ G.cutCircleSortedCrossing_curve_mem_seam j _

theorem cutCircleCyclicRight_le_add_period
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleCyclicRight j hne i ≤
      G.cutCircleSortedCrossing j i + 2 * Real.pi := by
  let _ : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  unfold cutCircleCyclicRight
  split_ifs with hi
  · have hnext := G.cutCircleSortedCrossing_mem_period j ⟨i.1 + 1, hi⟩
    have hcurrent := G.cutCircleSortedCrossing_mem_period j i
    exact hnext.2.le.trans (le_add_of_nonneg_left hcurrent.1)
  · have hmono : G.cutCircleSortedCrossing j
        ⟨0, Finset.card_pos.mpr hne⟩ ≤ G.cutCircleSortedCrossing j i := by
      exact ((G.cutCircleSeamCrossings j).orderEmbOfFin rfl).monotone
        (Fin.zero_le i)
    linarith

/-- No seam point occurs in the open interval between two cyclically successive crossings. -/
theorem no_cutCircleSeam_between_cyclic
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) {t : ℝ}
    (ht : t ∈ Ioo (G.cutCircleSortedCrossing j i)
      (G.cutCircleCyclicRight j hne i)) :
    ((G.cut.circle j).windingLoop.curve t : R3) ∉
      superellipsoidTorusSeam Phi frame c R d := by
  let _ : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  intro htSeam
  unfold cutCircleCyclicRight at ht
  split_ifs at ht with hnext
  · have htPeriod : t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨(G.cutCircleSortedCrossing_mem_period j i).1.trans ht.1.le,
        ht.2.trans (G.cutCircleSortedCrossing_mem_period j _).2⟩
    have htCross : t ∈ G.cutCircleSeamCrossings j :=
      (G.mem_cutCircleSeamCrossings_iff j t).mpr ⟨htPeriod, htSeam⟩
    let q : Fin (G.cutCircleSeamCrossings j).card :=
      ((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).symm ⟨t, htCross⟩
    have hq : G.cutCircleSortedCrossing j q = t := by
      exact congrArg Subtype.val
        (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).apply_symm_apply
          ⟨t, htCross⟩)
    have hiq : i < q := by
      apply (G.strictMono_cutCircleSortedCrossing j).lt_iff_lt.mp
      simpa only [hq] using ht.1
    have hqnext : q < ⟨i.1 + 1, hnext⟩ := by
      apply (G.strictMono_cutCircleSortedCrossing j).lt_iff_lt.mp
      simpa only [hq] using ht.2
    change i.1 < q.1 at hiq
    change q.1 < i.1 + 1 at hqnext
    omega
  · have hilast : i.1 + 1 = (G.cutCircleSeamCrossings j).card := by omega
    by_cases htBase : t < 2 * Real.pi
    · have htPeriod : t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
        ⟨(G.cutCircleSortedCrossing_mem_period j i).1.trans ht.1.le, htBase⟩
      have htCross : t ∈ G.cutCircleSeamCrossings j :=
        (G.mem_cutCircleSeamCrossings_iff j t).mpr ⟨htPeriod, htSeam⟩
      let q : Fin (G.cutCircleSeamCrossings j).card :=
        ((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).symm ⟨t, htCross⟩
      have hq : G.cutCircleSortedCrossing j q = t := by
        exact congrArg Subtype.val
          (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).apply_symm_apply
            ⟨t, htCross⟩)
      have hiq : i < q := by
        apply (G.strictMono_cutCircleSortedCrossing j).lt_iff_lt.mp
        simpa only [hq] using ht.1
      omega
    · let u := t - 2 * Real.pi
      have hu0 : 0 ≤ u := by dsimp [u]; linarith [le_of_not_gt htBase]
      have hufirst : u < G.cutCircleSortedCrossing j
          ⟨0, Finset.card_pos.mpr hne⟩ := by
        dsimp [u]
        exact sub_lt_iff_lt_add.mpr ht.2
      have huPeriod : u ∈ Ico (0 : ℝ) (2 * Real.pi) :=
        ⟨hu0, hufirst.trans (G.cutCircleSortedCrossing_mem_period j _).2⟩
      have huSeam : ((G.cut.circle j).windingLoop.curve u : R3) ∈
          superellipsoidTorusSeam Phi frame c R d := by
        have hperiod := (G.cut.circle j).windingLoop.periodic_curve u
        have hut : u + 2 * Real.pi = t := by dsimp [u]; ring
        rw [hut] at hperiod
        exact hperiod ▸ htSeam
      have huCross : u ∈ G.cutCircleSeamCrossings j :=
        (G.mem_cutCircleSeamCrossings_iff j u).mpr ⟨huPeriod, huSeam⟩
      let q : Fin (G.cutCircleSeamCrossings j).card :=
        ((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).symm ⟨u, huCross⟩
      have hq : G.cutCircleSortedCrossing j q = u := by
        exact congrArg Subtype.val
          (((G.cutCircleSeamCrossings j).orderIsoOfFin rfl).apply_symm_apply
            ⟨u, huCross⟩)
      have hfirstLe : G.cutCircleSortedCrossing j
          ⟨0, Finset.card_pos.mpr hne⟩ ≤ G.cutCircleSortedCrossing j q :=
        ((G.cutCircleSeamCrossings j).orderEmbOfFin rfl).monotone (Fin.zero_le q)
      rw [hq] at hfirstLe
      exact (not_lt_of_ge hfirstLe) hufirst

/-- Integer translates of a cyclic successor interval remain seam-free. -/
theorem no_cutCircleSeam_between_cyclic_translate
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) (n : ℤ) {t : ℝ}
    (ht : t ∈ Ioo
      (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi))
      (G.cutCircleCyclicRight j hne i + (n : ℝ) * (2 * Real.pi))) :
    ((G.cut.circle j).windingLoop.curve t : R3) ∉
      superellipsoidTorusSeam Phi frame c R d := by
  let u := t - (n : ℝ) * (2 * Real.pi)
  have hu : u ∈ Ioo (G.cutCircleSortedCrossing j i)
      (G.cutCircleCyclicRight j hne i) := by
    dsimp [u]
    constructor <;> linarith [ht.1, ht.2]
  intro htSeam
  apply G.no_cutCircleSeam_between_cyclic j hne i hu
  have hperiod := ((G.cut.circle j).windingLoop.periodic_curve.int_mul n) u
  have hut : u + (n : ℝ) * (2 * Real.pi) = t := by dsimp [u]; ring
  rw [hut] at hperiod
  exact hperiod ▸ htSeam

/-- Lifted sorted crossing parameters, with their deck index, are unique. -/
theorem injective_cutCircleSortedCrossing_add_int_period
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    Function.Injective (fun p :
      Fin (G.cutCircleSeamCrossings j).card × ℤ ↦
        G.cutCircleSortedCrossing j p.1 + (p.2 : ℝ) * (2 * Real.pi)) := by
  let _ : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  rintro ⟨i, n⟩ ⟨k, m⟩ h
  have hn := ((G.cut.circle j).windingLoop.periodic_curve.int_mul n)
    (G.cutCircleSortedCrossing j i)
  have hm := ((G.cut.circle j).windingLoop.periodic_curve.int_mul m)
    (G.cutCircleSortedCrossing j k)
  have hcurve : (G.cut.circle j).windingLoop.curve
      (G.cutCircleSortedCrossing j i) =
        (G.cut.circle j).windingLoop.curve
          (G.cutCircleSortedCrossing j k) := by
    calc
      (G.cut.circle j).windingLoop.curve (G.cutCircleSortedCrossing j i) =
          (G.cut.circle j).windingLoop.curve
            (G.cutCircleSortedCrossing j i + (n : ℝ) * (2 * Real.pi)) := hn.symm
      _ = (G.cut.circle j).windingLoop.curve
            (G.cutCircleSortedCrossing j k + (m : ℝ) * (2 * Real.pi)) :=
        congrArg (G.cut.circle j).windingLoop.curve h
      _ = (G.cut.circle j).windingLoop.curve
            (G.cutCircleSortedCrossing j k) := hm
  have hparam : G.cutCircleSortedCrossing j i =
      G.cutCircleSortedCrossing j k := by
    apply G.cutCircle_curve_injective_on_period j
    · exact G.cutCircleSortedCrossing_mem_period j i
    · exact G.cutCircleSortedCrossing_mem_period j k
    · exact congrArg Subtype.val hcurve
  have hik : i = k := (G.strictMono_cutCircleSortedCrossing j).injective hparam
  subst k
  have hcast : (n : ℝ) = (m : ℝ) := by
    nlinarith [Real.pi_pos]
  have hnm : n = m := by exact_mod_cast hcast
  subst m
  rfl

/-- Distinct lifted cyclic successor intervals have disjoint interiors.  If two interiors met,
the later left endpoint would be a seam point inside the earlier seam-free interval. -/
theorem translated_open_cutCircleCyclicGaps_pairwise_disjoint
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    Pairwise fun p q : Fin (G.cutCircleSeamCrossings j).card × ℤ ↦
      Disjoint
        (Ioo
          (G.cutCircleSortedCrossing j p.1 + (p.2 : ℝ) * (2 * Real.pi))
          (G.cutCircleCyclicRight j hne p.1 + (p.2 : ℝ) * (2 * Real.pi)))
        (Ioo
          (G.cutCircleSortedCrossing j q.1 + (q.2 : ℝ) * (2 * Real.pi))
          (G.cutCircleCyclicRight j hne q.1 + (q.2 : ℝ) * (2 * Real.pi))) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro t htp htq
  let lp := G.cutCircleSortedCrossing j p.1 + (p.2 : ℝ) * (2 * Real.pi)
  let lq := G.cutCircleSortedCrossing j q.1 + (q.2 : ℝ) * (2 * Real.pi)
  rcases lt_trichotomy lp lq with hpqlt | hpqeq | hqplt
  · apply G.no_cutCircleSeam_between_cyclic_translate j hne p.1 p.2
      ⟨hpqlt, htq.1.trans htp.2⟩
    exact G.cutCircleSortedCrossing_translate_curve_mem_seam j q.1 q.2
  · exact hpq (G.injective_cutCircleSortedCrossing_add_int_period j hne hpqeq)
  · apply G.no_cutCircleSeam_between_cyclic_translate j hne q.1 q.2
      ⟨hqplt, htp.1.trans htq.2⟩
    exact G.cutCircleSortedCrossing_translate_curve_mem_seam j p.1 p.2

/-- Continuity and absence of an intermediate seam point make the outer polynomial sign constant
on every cyclic successor interval. -/
theorem cutCircleCyclicGap_all_neg_or_all_pos
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hR : 0 ≤ R)
    (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    (∀ t ∈ Ioo (G.cutCircleSortedCrossing j i)
        (G.cutCircleCyclicRight j hne i),
      G.cutCircleOuterPolynomialDifference j t < 0) ∨
    (∀ t ∈ Ioo (G.cutCircleSortedCrossing j i)
        (G.cutCircleCyclicRight j hne i),
      0 < G.cutCircleOuterPolynomialDifference j t) := by
  let I := Ioo (G.cutCircleSortedCrossing j i)
    (G.cutCircleCyclicRight j hne i)
  have hIne : I.Nonempty :=
    nonempty_Ioo.mpr (G.cutCircleSortedCrossing_lt_cyclicRight j hne i)
  have hzero : ∀ t ∈ I, G.cutCircleOuterPolynomialDifference j t ≠ 0 := by
    intro t ht htzero
    exact G.no_cutCircleSeam_between_cyclic j hne i ht
      ((G.cutCircleOuterPolynomialDifference_eq_zero_iff_seam j hR t).mp htzero)
  obtain ⟨t₀, ht₀⟩ := hIne
  rcases lt_or_gt_of_ne (hzero t₀ ht₀) with hneg | hpos
  · left
    intro t ht
    by_contra hnot
    have htNonneg : 0 ≤ G.cutCircleOuterPolynomialDifference j t :=
      le_of_not_gt hnot
    have hbetween : 0 ∈ Icc
        (G.cutCircleOuterPolynomialDifference j t₀)
        (G.cutCircleOuterPolynomialDifference j t) := ⟨hneg.le, htNonneg⟩
    obtain ⟨u, hu, huzero⟩ := isPreconnected_Ioo.intermediate_value ht₀ ht
      (G.continuous_cutCircleOuterPolynomialDifference j).continuousOn hbetween
    exact hzero u hu huzero
  · right
    intro t ht
    by_contra hnot
    have htNonpos : G.cutCircleOuterPolynomialDifference j t ≤ 0 :=
      le_of_not_gt hnot
    have hbetween : 0 ∈ Icc
        (G.cutCircleOuterPolynomialDifference j t)
        (G.cutCircleOuterPolynomialDifference j t₀) := ⟨htNonpos, hpos.le⟩
    obtain ⟨u, hu, huzero⟩ := isPreconnected_Ioo.intermediate_value ht ht₀
      (G.continuous_cutCircleOuterPolynomialDifference j).continuousOn hbetween
    exact hzero u hu huzero

/-- Midpoint used to label one cyclic successor gap. -/
def cutCircleCyclicGapMidpoint
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) : ℝ :=
  (G.cutCircleSortedCrossing j i + G.cutCircleCyclicRight j hne i) / 2

theorem cutCircleCyclicGapMidpoint_mem
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleCyclicGapMidpoint j hne i ∈
      Ioo (G.cutCircleSortedCrossing j i)
        (G.cutCircleCyclicRight j hne i) := by
  constructor <;> unfold cutCircleCyclicGapMidpoint <;>
    linarith [G.cutCircleSortedCrossing_lt_cyclicRight j hne i]

/-- Boolean sign of a cyclic gap, chosen from its midpoint. -/
def cutCircleCyclicGapSide
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) : Bool :=
  decide (0 < G.cutCircleOuterPolynomialDifference j
    (G.cutCircleCyclicGapMidpoint j hne i))

/-- The midpoint label is the strict sign throughout its whole crossing-free gap. -/
theorem cutCircleCyclicGapSide_strict
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hR : 0 ≤ R)
    (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) (t : ℝ)
    (ht : t ∈ Ioo (G.cutCircleSortedCrossing j i)
      (G.cutCircleCyclicRight j hne i)) :
    if G.cutCircleCyclicGapSide j hne i then
      0 < G.cutCircleOuterPolynomialDifference j t
    else G.cutCircleOuterPolynomialDifference j t < 0 := by
  rcases G.cutCircleCyclicGap_all_neg_or_all_pos j hR hne i with hneg | hpos
  · have hmid := hneg _ (G.cutCircleCyclicGapMidpoint_mem j hne i)
    have hside : G.cutCircleCyclicGapSide j hne i = false := by
      simp [cutCircleCyclicGapSide, not_lt_of_ge hmid.le]
    simp only [hside, Bool.false_eq_true, if_false]
    exact hneg t ht
  · have hmid := hpos _ (G.cutCircleCyclicGapMidpoint_mem j hne i)
    have hside : G.cutCircleCyclicGapSide j hne i = true := by
      simp [cutCircleCyclicGapSide, hmid]
    simp only [hside, if_true]
    exact hpos t ht

/-- The canonical midpoint sign, indexed cyclically rather than linearly. -/
noncomputable def cutCircleZModGapSide
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    ZMod (G.cutCircleSeamCrossings j).card → Bool := by
  letI : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  exact fun i ↦ G.cutCircleCyclicGapSide j hne
    ⟨i.val, ZMod.val_lt i⟩

/-- The precise output of finite sorting and the local two-dimensional seam chart on one cutting
circle.  There is deliberately no endpoint pairing field.  The side label is the canonical
midpoint sign, already proved valid throughout its crossing-free interval.  The sole field says
that adjacent canonical labels differ; the local sign-flip theorem proves it after the elementary
successor-index calculation.  The perfect endpoint pairing is then derived below. -/
structure CutCircleTransverseCyclicOrder
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) where
  radius_pos : 0 < R
  crossings_nonempty : (G.cutCircleSeamCrossings j).Nonempty
  adjacent_gap_sides_ne : letI : NeZero (G.cutCircleSeamCrossings j).card :=
      ⟨(Finset.card_pos.mpr crossings_nonempty).ne'⟩
    ∀ i : ZMod (G.cutCircleSeamCrossings j).card,
      G.cutCircleZModGapSide j crossings_nonempty (i + 1) ≠
        G.cutCircleZModGapSide j crossings_nonempty i

namespace CutCircleTransverseCyclicOrder

variable {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {j : cutIndex}

/-- The local simple-zero theorem and cyclic sorting prove the sole alternation field.  The two
cases are an ordinary successor crossing and the wrap from the last crossing to the first one in
the next period. -/
theorem ofSmoothLift
    (D : SmoothCutCircleLiftData G j) (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    CutCircleTransverseCyclicOrder G j := by
  let _ : NeZero (G.cutCircleSeamCrossings j).card :=
    ⟨(Finset.card_pos.mpr hne).ne'⟩
  refine {
    radius_pos := hR
    crossings_nonempty := hne
    adjacent_gap_sides_ne := ?_
  }
  intro i heq
  let q : Fin (G.cutCircleSeamCrossings j).card :=
    ⟨i.val, ZMod.val_lt i⟩
  let qnext : Fin (G.cutCircleSeamCrossings j).card :=
    ⟨(i + 1).val, ZMod.val_lt (i + 1)⟩
  have hnextVal : (i + 1).val = (i.val + 1) %
      (G.cutCircleSeamCrossings j).card := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    nth_rewrite 1 [← Nat.mod_eq_of_lt (ZMod.val_lt i)]
    exact (Nat.add_mod i.val 1 (G.cutCircleSeamCrossings j).card).symm
  by_cases hnext : q.1 + 1 < (G.cutCircleSeamCrossings j).card
  · have hqnext : qnext = ⟨q.1 + 1, hnext⟩ := by
      apply Fin.ext
      change (i + 1).val = i.val + 1
      rw [hnextVal, Nat.mod_eq_of_lt hnext]
    let left := G.cutCircleSortedCrossing j q
    let crossing := G.cutCircleSortedCrossing j ⟨q.1 + 1, hnext⟩
    let right := G.cutCircleCyclicRight j hne ⟨q.1 + 1, hnext⟩
    have hleftCrossing : left < crossing := by
      exact G.strictMono_cutCircleSortedCrossing j
        (Fin.mk_lt_mk.mpr (Nat.lt_succ_self q.1))
    have hcrossingRight : crossing < right :=
      G.cutCircleSortedCrossing_lt_cyclicRight j hne _
    obtain ⟨ε, hε, hflip⟩ := D.hasLocalPolynomialSignFlipAtCrossings
      hR.le hseam crossing (G.cutCircleSortedCrossing_mem j _)
    let δ := min (ε / 2) (min ((crossing - left) / 2) ((right - crossing) / 2))
    have hδ : 0 < δ := by
      exact lt_min (half_pos hε) <| lt_min
        (half_pos (sub_pos.mpr hleftCrossing))
        (half_pos (sub_pos.mpr hcrossingRight))
    have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hδleft : δ < crossing - left :=
      (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hleftCrossing))
    have hδright : δ < right - crossing :=
      (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hcrossingRight))
    let x := crossing - δ
    let y := crossing + δ
    have hxLocal : x ∈ Ioo (crossing - ε) crossing := by
      dsimp [x]
      constructor <;> linarith
    have hyLocal : y ∈ Ioo crossing (crossing + ε) := by
      dsimp [y]
      constructor <;> linarith
    have hxGap : x ∈ Ioo left crossing := by
      dsimp [x]
      constructor <;> linarith
    have hyGap : y ∈ Ioo crossing right := by
      dsimp [y]
      constructor <;> linarith
    have hxsign := G.cutCircleCyclicGapSide_strict j hR.le hne q x (by
      simpa [left, crossing, cutCircleCyclicRight, hnext] using hxGap)
    have hysign := G.cutCircleCyclicGapSide_strict j hR.le hne qnext y (by
      rw [hqnext]
      simpa [crossing, right] using hyGap)
    change (if G.cutCircleZModGapSide j hne i then
      0 < G.cutCircleOuterPolynomialDifference j x
      else G.cutCircleOuterPolynomialDifference j x < 0) at hxsign
    change (if G.cutCircleZModGapSide j hne (i + 1) then
      0 < G.cutCircleOuterPolynomialDifference j y
      else G.cutCircleOuterPolynomialDifference j y < 0) at hysign
    rw [heq] at hysign
    have hxy := hflip x hxLocal y hyLocal
    cases hs : G.cutCircleZModGapSide j hne i <;>
      simp only [hs, Bool.false_eq_true, if_false, if_true] at hxsign hysign
    · exact (not_lt_of_ge
        (mul_nonneg_of_nonpos_of_nonpos hxsign.le hysign.le)) hxy
    · exact (not_lt_of_ge (mul_nonneg hxsign.le hysign.le)) hxy
  · have hlast : q.1 + 1 = (G.cutCircleSeamCrossings j).card := by omega
    have hqnext : qnext = ⟨0, Finset.card_pos.mpr hne⟩ := by
      apply Fin.ext
      change (i + 1).val = 0
      rw [hnextVal, show i.val + 1 = (G.cutCircleSeamCrossings j).card by
        simpa only [q] using hlast, Nat.mod_self]
    let first : Fin (G.cutCircleSeamCrossings j).card :=
      ⟨0, Finset.card_pos.mpr hne⟩
    let left := G.cutCircleSortedCrossing j q
    let crossing := G.cutCircleSortedCrossing j first
    let right := G.cutCircleCyclicRight j hne first
    have hleftCrossing : left < crossing + 2 * Real.pi := by
      have hleftPeriod := G.cutCircleSortedCrossing_mem_period j q
      have hfirstPeriod := G.cutCircleSortedCrossing_mem_period j first
      exact hleftPeriod.2.trans_le (by linarith [hfirstPeriod.1])
    have hcrossingRight : crossing < right :=
      G.cutCircleSortedCrossing_lt_cyclicRight j hne first
    obtain ⟨ε, hε, hflip⟩ := D.hasLocalPolynomialSignFlipAtCrossings
      hR.le hseam crossing (G.cutCircleSortedCrossing_mem j first)
    let δ := min (ε / 2)
      (min ((crossing + 2 * Real.pi - left) / 2) ((right - crossing) / 2))
    have hδ : 0 < δ := by
      exact lt_min (half_pos hε) <| lt_min
        (half_pos (sub_pos.mpr hleftCrossing))
        (half_pos (sub_pos.mpr hcrossingRight))
    have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hδleft : δ < crossing + 2 * Real.pi - left :=
      (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hleftCrossing))
    have hδright : δ < right - crossing :=
      (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt
        (half_lt_self (sub_pos.mpr hcrossingRight))
    let x := crossing - δ
    let xLast := x + 2 * Real.pi
    let y := crossing + δ
    have hxLocal : x ∈ Ioo (crossing - ε) crossing := by
      dsimp [x]
      constructor <;> linarith
    have hyLocal : y ∈ Ioo crossing (crossing + ε) := by
      dsimp [y]
      constructor <;> linarith
    have hxLastGap : xLast ∈ Ioo left (crossing + 2 * Real.pi) := by
      dsimp [xLast, x]
      constructor <;> linarith
    have hyGap : y ∈ Ioo crossing right := by
      dsimp [y]
      constructor <;> linarith
    have hxsign := G.cutCircleCyclicGapSide_strict j hR.le hne q xLast (by
      simpa [left, crossing, first, cutCircleCyclicRight, hnext] using hxLastGap)
    have hysign := G.cutCircleCyclicGapSide_strict j hR.le hne qnext y (by
      rw [hqnext]
      simpa [first, crossing, right] using hyGap)
    have hxperiod : G.cutCircleOuterPolynomialDifference j xLast =
        G.cutCircleOuterPolynomialDifference j x := by
      simpa only [xLast] using G.periodic_cutCircleOuterPolynomialDifference j x
    change (if G.cutCircleZModGapSide j hne i then
      0 < G.cutCircleOuterPolynomialDifference j xLast
      else G.cutCircleOuterPolynomialDifference j xLast < 0) at hxsign
    change (if G.cutCircleZModGapSide j hne (i + 1) then
      0 < G.cutCircleOuterPolynomialDifference j y
      else G.cutCircleOuterPolynomialDifference j y < 0) at hysign
    rw [hxperiod] at hxsign
    rw [heq] at hysign
    have hxy := hflip x hxLocal y hyLocal
    cases hs : G.cutCircleZModGapSide j hne i <;>
      simp only [hs, Bool.false_eq_true, if_false, if_true] at hxsign hysign
    · exact (not_lt_of_ge
        (mul_nonneg_of_nonpos_of_nonpos hxsign.le hysign.le)) hxy
    · exact (not_lt_of_ge (mul_nonneg hxsign.le hysign.le)) hxy

/-- The alternating cyclic side data are derived from the canonical midpoint signs. -/
noncomputable def sideData (O : CutCircleTransverseCyclicOrder G j) :
    AlternatingCyclicSideData (G.cutCircleSeamCrossings j).card where
  neZero := ⟨(Finset.card_pos.mpr O.crossings_nonempty).ne'⟩
  side := G.cutCircleZModGapSide j O.crossings_nonempty
  changes := O.adjacent_gap_sides_ne

/-- The seam pairing on one cutting circle, derived from its sorted transverse crossings. -/
noncomputable def toPairedSeamEnumeration
    (O : CutCircleTransverseCyclicOrder G j) :
    PairedSeamEnumeration (G.CutCircleSeamVertex j) := by
  letI := O.sideData.neZero
  exact O.sideData.toPairedSeamEnumeration
    (G.cutCircleCyclicCrossingEquiv j O.crossings_nonempty)

/-- The inward interval represented by one band in the derived pairing. -/
noncomputable def inwardGapOfBand (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) : O.sideData.InwardGap :=
  (Fintype.equivFin O.sideData.InwardGap).symm b

/-- The sorted real index of a cyclic inward gap. -/
def inwardGapFinIndex (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) :
    Fin (G.cutCircleSeamCrossings j).card := by
  letI := O.sideData.neZero
  exact ⟨(O.inwardGapOfBand b).1.val, ZMod.val_lt _⟩

/-- Affine parametrization of the actual cutting-circle excursion between its two successive seam
crossings.  The seam interval is allowed to end in the next period. -/
noncomputable def inwardExcursionPath (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) :
    Path
      ((G.cut.circle j).windingLoop.curve
        (G.cutCircleSortedCrossing j (O.inwardGapFinIndex b)))
      ((G.cut.circle j).windingLoop.curve
        (G.cutCircleCyclicRight j O.crossings_nonempty
          (O.inwardGapFinIndex b))) where
  toContinuousMap := ⟨fun u ↦ (G.cut.circle j).windingLoop.curve
      (G.cutCircleSortedCrossing j (O.inwardGapFinIndex b) +
        (u : ℝ) *
          (G.cutCircleCyclicRight j O.crossings_nonempty
              (O.inwardGapFinIndex b) -
            G.cutCircleSortedCrossing j (O.inwardGapFinIndex b))),
    (G.cut.circle j).windingLoop.continuous_curve.comp
      (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩
  source' := by simp
  target' := by simp

/-- The open interior of every derived inward excursion lies strictly in the superellipsoid
body. -/
theorem inwardExcursionPath_mem_body
    (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((O.inwardExcursionPath b u : transportedTorus Phi) : R3) ∈
      superellipsoidBody frame c R := by
  let q := O.inwardGapFinIndex b
  let left := G.cutCircleSortedCrossing j q
  let right := G.cutCircleCyclicRight j O.crossings_nonempty q
  have hu : (0 : ℝ) < (u : ℝ) ∧ (u : ℝ) < 1 := by
    exact ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0),
      lt_of_le_of_ne u.2.2 hu1⟩
  have hleftRight : left < right :=
    G.cutCircleSortedCrossing_lt_cyclicRight j O.crossings_nonempty q
  have ht : left + (u : ℝ) * (right - left) ∈ Ioo left right := by
    constructor <;> nlinarith
  have hside := G.cutCircleCyclicGapSide_strict j O.radius_pos.le
    O.crossings_nonempty q
    (left + (u : ℝ) * (right - left))
    (by simpa [left, right] using ht)
  have hnegative : G.cutCircleOuterPolynomialDifference j
      (left + (u : ℝ) * (right - left)) < 0 := by
    have hgap : G.cutCircleCyclicGapSide j O.crossings_nonempty q = false := by
      simpa [sideData, cutCircleZModGapSide, q, inwardGapFinIndex] using
        (O.inwardGapOfBand b).2
    rw [hgap] at hside
    simpa using hside
  exact (G.cutCircleOuterPolynomialDifference_neg_iff_body j O.radius_pos _).mp hnegative

end CutCircleTransverseCyclicOrder

end FiniteSuperellipsoidBarrierGraph

/-! ## Global pairing assembled from the active cutting circles -/

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

/-- The cyclic order constructed on every cutting circle that actually meets the seam. -/
structure CutCircleTransverseCyclicOrderFamily
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) where
  order : ∀ j : G.ActiveCutCircle, CutCircleTransverseCyclicOrder G j.1

namespace CutCircleTransverseCyclicOrderFamily

/-- A smooth complete orbit for every active cut circle constructs the whole cyclic-order family. -/
theorem ofSmoothLifts
    (D : ∀ j : G.ActiveCutCircle, SmoothCutCircleLiftData G j.1)
    (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    CutCircleTransverseCyclicOrderFamily G where
  order := fun j ↦
    CutCircleTransverseCyclicOrder.ofSmoothLift (D j) hR hseam j.2

/-- All inward cyclic gaps, retaining the cutting-circle index. -/
def GlobalInwardGap (F : CutCircleTransverseCyclicOrderFamily G) :=
  Σ j : G.ActiveCutCircle, (F.order j).sideData.InwardGap

noncomputable instance (F : CutCircleTransverseCyclicOrderFamily G) :
    Fintype F.GlobalInwardGap := by
  classical
  exact Sigma.instFintype

/-- Product distributes over this dependent finite sum. -/
def globalGapEndpointDistrib (F : CutCircleTransverseCyclicOrderFamily G) :
    F.GlobalInwardGap × Fin 2 ≃
      Σ j : G.ActiveCutCircle, (F.order j).sideData.InwardGap × Fin 2 where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun p := (⟨p.1, p.2.1⟩, p.2.2)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Sorted linear index of a global inward gap. -/
def globalGapFinIndex (F : CutCircleTransverseCyclicOrderFamily G)
    (g : F.GlobalInwardGap) :
    Fin (G.cutCircleSeamCrossings g.1.1).card := by
  letI := (F.order g.1).sideData.neZero
  exact ⟨g.2.1.val, ZMod.val_lt _⟩

/-- The local alternating endpoint equivalences distribute over the active cutting circles. -/
noncomputable def globalGapEndpointEquiv
    (F : CutCircleTransverseCyclicOrderFamily G) :
    F.GlobalInwardGap × Fin 2 ≃
      Σ j : G.ActiveCutCircle, ZMod (G.cutCircleSeamCrossings j.1).card :=
  F.globalGapEndpointDistrib.trans
    (Equiv.sigmaCongrRight fun j ↦ (F.order j).sideData.endpointEquiv)

/-- Cyclic crossing indices identify the seam vertices on each active cutting circle. -/
noncomputable def globalCyclicCrossingEquiv
    (F : CutCircleTransverseCyclicOrderFamily G) :
    (Σ j : G.ActiveCutCircle, ZMod (G.cutCircleSeamCrossings j.1).card) ≃
      Σ j : G.ActiveCutCircle, G.CutCircleSeamVertex j.1 :=
  Equiv.sigmaCongrRight fun j ↦
    G.cutCircleCyclicCrossingEquiv j.1 (F.order j).crossings_nonempty

/-- The local alternating endpoint equivalences and exact active-circle seam decomposition give
the global perfect pairing of every analytic seam vertex. -/
noncomputable def globalEndpointEquiv
    (F : CutCircleTransverseCyclicOrderFamily G) :
    F.GlobalInwardGap × Fin 2 ≃
      SuperellipsoidSeamVertex Phi frame c R d :=
  (F.globalGapEndpointEquiv.trans F.globalCyclicCrossingEquiv).trans
    G.activeCutCircleSeamVertexEquiv

@[simp]
theorem globalEndpointEquiv_zero_val
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap) :
    (F.globalEndpointEquiv (g, (0 : Fin 2))).1 =
      ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g)) : R3) := by
  let _ := (F.order g.1).sideData.neZero
  change (G.cutCircleCyclicCrossingEquiv g.1.1
      (F.order g.1).crossings_nonempty g.2.1).1 = _
  rw [G.cutCircleCyclicCrossingEquiv_val]
  apply congrArg (fun q : Fin (G.cutCircleSeamCrossings g.1.1).card ↦
    ((G.cut.circle g.1.1).windingLoop.curve (G.cutCircleSortedCrossing g.1.1 q) : R3))
  apply Fin.ext
  rfl

@[simp]
theorem globalEndpointEquiv_one_val
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap) :
    (F.globalEndpointEquiv (g, (1 : Fin 2))).1 =
      ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
          (F.globalGapFinIndex g)) : R3) := by
  let _ := (F.order g.1).sideData.neZero
  change (G.cutCircleCyclicCrossingEquiv g.1.1
      (F.order g.1).crossings_nonempty (g.2.1 + 1)).1 = _
  rw [G.cutCircleCyclicCrossingEquiv_val]
  let n := (G.cutCircleSeamCrossings g.1.1).card
  let q := F.globalGapFinIndex g
  have hnextVal : (g.2.1 + 1).val = (g.2.1.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    nth_rewrite 1 [← Nat.mod_eq_of_lt (ZMod.val_lt g.2.1)]
    exact (Nat.add_mod g.2.1.val 1 n).symm
  by_cases hnext : q.1 + 1 < n
  · have hval : (g.2.1 + 1).val = q.1 + 1 := by
      rw [hnextVal]
      change (g.2.1.val + 1) % n = g.2.1.val + 1
      exact Nat.mod_eq_of_lt hnext
    change ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleSortedCrossing g.1.1
          ⟨(g.2.1 + 1).val, ZMod.val_lt _⟩) : R3) = _
    rw [show (⟨(g.2.1 + 1).val, ZMod.val_lt _⟩ : Fin n) =
        ⟨q.1 + 1, hnext⟩ by ext; exact hval]
    have hnext' : (F.globalGapFinIndex g).1 + 1 <
        (G.cutCircleSeamCrossings g.1.1).card := by simpa [q, n] using hnext
    simp only [cutCircleCyclicRight, hnext']
    apply congrArg (fun r : Fin (G.cutCircleSeamCrossings g.1.1).card ↦
      ((G.cut.circle g.1.1).windingLoop.curve (G.cutCircleSortedCrossing g.1.1 r) : R3))
    apply Fin.ext
    rfl
  · have hlast : q.1 + 1 = n := by omega
    have hval : (g.2.1 + 1).val = 0 := by
      rw [hnextVal, show g.2.1.val + 1 = n by simpa only [q, globalGapFinIndex] using hlast,
        Nat.mod_self]
    change ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleSortedCrossing g.1.1
          ⟨(g.2.1 + 1).val, ZMod.val_lt _⟩) : R3) = _
    rw [show (⟨(g.2.1 + 1).val, ZMod.val_lt _⟩ : Fin n) =
        ⟨0, Finset.card_pos.mpr (F.order g.1).crossings_nonempty⟩ by
          ext; exact hval]
    have hnext' : ¬(F.globalGapFinIndex g).1 + 1 <
        (G.cutCircleSeamCrossings g.1.1).card := by simpa [q, n] using hnext
    simp [cutCircleCyclicRight, hnext']
    exact congrArg Subtype.val <|
      ((G.cut.circle g.1.1).windingLoop.periodic_curve
        (G.cutCircleSortedCrossing g.1.1
          ⟨0, Finset.card_pos.mpr (F.order g.1).crossings_nonempty⟩)).symm

/-- The global seam enumeration is therefore derived from the smooth transverse cutting-circle
orbits, with no independent vertex pairing input. -/
noncomputable def toPairedSeamEnumeration
    (F : CutCircleTransverseCyclicOrderFamily G) :
    PairedSeamEnumeration (SuperellipsoidSeamVertex Phi frame c R d) := by
  letI := G.seamVertexFintype
  exact {
    bandCount := Fintype.card F.GlobalInwardGap
    endpointEquiv :=
      ((Fintype.equivFin F.GlobalInwardGap).symm.prodCongr
        (Equiv.refl (Fin 2))).trans F.globalEndpointEquiv }

/-- The actual closed inward arc represented by a global gap. -/
noncomputable def globalInwardExcursionPath
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap) :
    Path
      ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g)))
      ((G.cut.circle g.1.1).windingLoop.curve
        (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
          (F.globalGapFinIndex g))) where
  toContinuousMap := ⟨fun u ↦ (G.cut.circle g.1.1).windingLoop.curve
      (G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g) +
        (u : ℝ) *
          (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
              (F.globalGapFinIndex g) -
            G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g))),
    (G.cut.circle g.1.1).windingLoop.continuous_curve.comp
      (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩
  source' := by simp
  target' := by simp

/-- The two endpoint labels as parameters of the closed unit interval. -/
def finTwoUnitInterval (e : Fin 2) : unitInterval :=
  ⟨e.1, by
    constructor
    · exact Nat.cast_nonneg e.1
    · exact_mod_cast Nat.le_of_lt_succ e.2⟩

@[simp] theorem finTwoUnitInterval_zero : finTwoUnitInterval 0 = 0 := by
  apply Subtype.ext
  norm_num [finTwoUnitInterval]

@[simp] theorem finTwoUnitInterval_one : finTwoUnitInterval 1 = 1 := by
  apply Subtype.ext
  norm_num [finTwoUnitInterval]

/-- Real lift parameter used by a global excursion path. -/
def globalInwardExcursionParameter
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (u : unitInterval) : ℝ :=
  G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g) +
    (u : ℝ) *
      (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
          (F.globalGapFinIndex g) -
        G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g))

@[simp]
theorem globalInwardExcursionPath_apply
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (u : unitInterval) :
    F.globalInwardExcursionPath g u =
      (G.cut.circle g.1.1).windingLoop.curve
        (F.globalInwardExcursionParameter g u) := rfl

theorem globalInwardExcursionParameter_mem_gap
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (u : unitInterval) (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    F.globalInwardExcursionParameter g u ∈
      Ioo
        (G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g))
        (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
          (F.globalGapFinIndex g)) := by
  have hu : (0 : ℝ) < (u : ℝ) ∧ (u : ℝ) < 1 :=
    ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0), lt_of_le_of_ne u.2.2 hu1⟩
  have hlr := G.cutCircleSortedCrossing_lt_cyclicRight g.1.1
    (F.order g.1).crossings_nonempty (F.globalGapFinIndex g)
  unfold globalInwardExcursionParameter
  constructor <;> nlinarith

theorem globalEndpointEquiv_val_eq_path_endpoint
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (e : Fin 2) :
    (F.globalEndpointEquiv (g, e)).1 =
      ((F.globalInwardExcursionPath g (finTwoUnitInterval e) :
        transportedTorus Phi) : R3) := by
  fin_cases e
  · simp
  · simp

/-- Distinct global endpoint labels give distinct ambient endpoints. -/
theorem global_path_endpoint_injective
    (F : CutCircleTransverseCyclicOrderFamily G) :
    Function.Injective (fun p : F.GlobalInwardGap × Fin 2 ↦
      ((F.globalInwardExcursionPath p.1 (finTwoUnitInterval p.2) :
        transportedTorus Phi) : R3)) := by
  intro p q hpq
  apply F.globalEndpointEquiv.injective
  apply Subtype.ext
  rw [F.globalEndpointEquiv_val_eq_path_endpoint,
    F.globalEndpointEquiv_val_eq_path_endpoint]
  exact hpq

/-- An endpoint of any inward arc cannot equal an interior point of any inward arc: endpoints lie
on the seam, whereas an interior parameter belongs to a seam-free cyclic gap. -/
theorem global_path_endpoint_ne_interior
    (F : CutCircleTransverseCyclicOrderFamily G)
    (g h : F.GlobalInwardGap) (e : Fin 2) (u : unitInterval)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((F.globalInwardExcursionPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ≠
      ((F.globalInwardExcursionPath h u : transportedTorus Phi) : R3) := by
  intro heq
  have hend : ((F.globalInwardExcursionPath g (finTwoUnitInterval e) :
      transportedTorus Phi) : R3) ∈
        superellipsoidTorusSeam Phi frame c R d := by
    rw [← F.globalEndpointEquiv_val_eq_path_endpoint]
    exact (F.globalEndpointEquiv (g, e)).2
  have hinterior : ((F.globalInwardExcursionPath h u :
      transportedTorus Phi) : R3) ∉
        superellipsoidTorusSeam Phi frame c R d := by
    rw [F.globalInwardExcursionPath_apply]
    exact G.no_cutCircleSeam_between_cyclic h.1.1
      (F.order h.1).crossings_nonempty (F.globalGapFinIndex h)
      (F.globalInwardExcursionParameter_mem_gap h u hu0 hu1)
  exact hinterior (heq.symm ▸ hend)

/-- Every global excursion stays on its selected cutting circle. -/
theorem globalInwardExcursionPath_mem_cutCircle
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (u : unitInterval) :
    ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3) ∈
      Set.range (G.cut.circle g.1.1).circle := by
  let t := G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g) +
    (u : ℝ) *
      (G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
          (F.globalGapFinIndex g) -
        G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g))
  exact ⟨Circle.exp t, (G.cut.circle g.1.1).parametrization t⟩

/-- Open interiors of the global excursions lie in the open superellipsoid body. -/
theorem globalInwardExcursionPath_mem_body
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap)
    (u : unitInterval) (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3) ∈
      superellipsoidBody frame c R := by
  let O := F.order g.1
  let q := F.globalGapFinIndex g
  let left := G.cutCircleSortedCrossing g.1.1 q
  let right := G.cutCircleCyclicRight g.1.1 O.crossings_nonempty q
  have hu : (0 : ℝ) < (u : ℝ) ∧ (u : ℝ) < 1 :=
    ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0), lt_of_le_of_ne u.2.2 hu1⟩
  have hlr : left < right :=
    G.cutCircleSortedCrossing_lt_cyclicRight g.1.1 O.crossings_nonempty q
  have ht : left + (u : ℝ) * (right - left) ∈ Ioo left right := by
    constructor <;> nlinarith
  have hside := G.cutCircleCyclicGapSide_strict g.1.1 O.radius_pos.le
    O.crossings_nonempty q (left + (u : ℝ) * (right - left))
    (by simpa [left, right] using ht)
  have hgap : G.cutCircleCyclicGapSide g.1.1 O.crossings_nonempty q = false := by
    simpa [CutCircleTransverseCyclicOrder.sideData, cutCircleZModGapSide,
      q, globalGapFinIndex] using g.2.2
  rw [hgap] at hside
  exact (G.cutCircleOuterPolynomialDifference_neg_iff_body
    g.1.1 O.radius_pos _).mp (by simpa using hside)

/-- A global inward arc has compact, hence ambiently closed, range. -/
theorem isClosed_range_globalInwardExcursionPath
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap) :
    IsClosed (Set.range fun u ↦
      ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3)) := by
  rw [← Set.image_univ]
  exact (isCompact_univ.image
    (continuous_subtype_val.comp (F.globalInwardExcursionPath g).continuous)).isClosed

/-- Interior points on distinct inward gaps of one cutting circle are distinct.  Equality in the
circle quotient would translate one lifted parameter by an integral period into the other lifted
gap, contradicting disjointness of the translated cyclic-gap interiors. -/
theorem globalInwardExcursionPath_interior_ne_of_same_circle
    (F : CutCircleTransverseCyclicOrderFamily G) (j : G.ActiveCutCircle)
    (g h : (F.order j).sideData.InwardGap) (hgh : g ≠ h)
    (u v : unitInterval) (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1)
    (hv0 : (v : ℝ) ≠ 0) (hv1 : (v : ℝ) ≠ 1) :
    ((F.globalInwardExcursionPath ⟨j, g⟩ u : transportedTorus Phi) : R3) ≠
      ((F.globalInwardExcursionPath ⟨j, h⟩ v : transportedTorus Phi) : R3) := by
  intro huv
  let _ := (F.order j).sideData.neZero
  let sg := F.globalInwardExcursionParameter ⟨j, g⟩ u
  let sh := F.globalInwardExcursionParameter ⟨j, h⟩ v
  have hsg : sg ∈ Ioo
      (G.cutCircleSortedCrossing j.1 (F.globalGapFinIndex ⟨j, g⟩))
      (G.cutCircleCyclicRight j.1 (F.order j).crossings_nonempty
        (F.globalGapFinIndex ⟨j, g⟩)) :=
    F.globalInwardExcursionParameter_mem_gap ⟨j, g⟩ u hu0 hu1
  have hsh : sh ∈ Ioo
      (G.cutCircleSortedCrossing j.1 (F.globalGapFinIndex ⟨j, h⟩))
      (G.cutCircleCyclicRight j.1 (F.order j).crossings_nonempty
        (F.globalGapFinIndex ⟨j, h⟩)) :=
    F.globalInwardExcursionParameter_mem_gap ⟨j, h⟩ v hv0 hv1
  have hexp : Circle.exp sg = Circle.exp sh := by
    apply (G.cut.circle j.1).isEmbedding.injective
    rw [(G.cut.circle j.1).parametrization, (G.cut.circle j.1).parametrization]
    change (((G.cut.circle j.1).windingLoop.curve sg : transportedTorus Phi) : R3) =
      (((G.cut.circle j.1).windingLoop.curve sh : transportedTorus Phi) : R3) at huv
    exact huv
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hsgTranslated : sg ∈ Ioo
      (G.cutCircleSortedCrossing j.1 (F.globalGapFinIndex ⟨j, h⟩) +
        (n : ℝ) * (2 * Real.pi))
      (G.cutCircleCyclicRight j.1 (F.order j).crossings_nonempty
          (F.globalGapFinIndex ⟨j, h⟩) +
        (n : ℝ) * (2 * Real.pi)) := by
    constructor <;> linarith [hsh.1, hsh.2]
  have hpairs :
      (F.globalGapFinIndex ⟨j, g⟩, (0 : ℤ)) ≠
        (F.globalGapFinIndex ⟨j, h⟩, n) := by
    intro hpairs
    have hfin : F.globalGapFinIndex ⟨j, g⟩ =
        F.globalGapFinIndex ⟨j, h⟩ := congrArg Prod.fst hpairs
    have hval : g.1.val = h.1.val := by
      simpa [globalGapFinIndex] using congrArg Fin.val hfin
    apply hgh
    apply Subtype.ext
    exact ZMod.val_injective _ hval
  have hdisjoint :=
    G.translated_open_cutCircleCyclicGaps_pairwise_disjoint j.1
      (F.order j).crossings_nonempty hpairs
  apply Set.disjoint_left.mp hdisjoint
  · simpa only [Int.cast_zero, zero_mul, add_zero] using hsg
  · exact hsgTranslated

/-- The closed inward excursions are globally pairwise disjoint.  Different cutting circles are
disjoint by the regular-section decomposition.  On one circle, seam endpoints are globally
unique and the open arc interiors are disjoint after passing to all integral period translates. -/
theorem globalInwardExcursionPath_ranges_pairwise_disjoint
    (F : CutCircleTransverseCyclicOrderFamily G) :
    Pairwise fun g h : F.GlobalInwardGap ↦
      Disjoint
        (Set.range fun u ↦
          ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3))
        (Set.range fun u ↦
          ((F.globalInwardExcursionPath h u : transportedTorus Phi) : R3)) := by
  rintro ⟨j, g⟩ ⟨k, h⟩ hgh
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  by_cases hjk : j = k
  · subst k
    have hgh' : g ≠ h := by
      intro hEq
      subst h
      exact hgh rfl
    by_cases hu0 : (u : ℝ) = 0
    · have hu : u = (0 : unitInterval) := Subtype.ext hu0
      subst u
      by_cases hv0 : (v : ℝ) = 0
      · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
        subst v
        have hp : ((⟨j, g⟩ : F.GlobalInwardGap), (0 : Fin 2)) =
            ((⟨j, h⟩ : F.GlobalInwardGap), (0 : Fin 2)) :=
          F.global_path_endpoint_injective (by simpa using hv.symm)
        exact hgh (congrArg Prod.fst hp)
      · by_cases hv1 : (v : ℝ) = 1
        · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
          subst v
          have hp : ((⟨j, g⟩ : F.GlobalInwardGap), (0 : Fin 2)) =
              ((⟨j, h⟩ : F.GlobalInwardGap), (1 : Fin 2)) :=
            F.global_path_endpoint_injective (by simpa using hv.symm)
          exact hgh (congrArg Prod.fst hp)
        · exact F.global_path_endpoint_ne_interior ⟨j, g⟩ ⟨j, h⟩ 0 v
            hv0 hv1 (by simpa using hv.symm)
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = (1 : unitInterval) := Subtype.ext hu1
        subst u
        by_cases hv0 : (v : ℝ) = 0
        · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
          subst v
          have hp : ((⟨j, g⟩ : F.GlobalInwardGap), (1 : Fin 2)) =
              ((⟨j, h⟩ : F.GlobalInwardGap), (0 : Fin 2)) :=
            F.global_path_endpoint_injective (by simpa using hv.symm)
          exact hgh (congrArg Prod.fst hp)
        · by_cases hv1 : (v : ℝ) = 1
          · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
            subst v
            have hp : ((⟨j, g⟩ : F.GlobalInwardGap), (1 : Fin 2)) =
                ((⟨j, h⟩ : F.GlobalInwardGap), (1 : Fin 2)) :=
              F.global_path_endpoint_injective (by simpa using hv.symm)
            exact hgh (congrArg Prod.fst hp)
          · exact F.global_path_endpoint_ne_interior ⟨j, g⟩ ⟨j, h⟩ 1 v
              hv0 hv1 (by simpa using hv.symm)
      · by_cases hv0 : (v : ℝ) = 0
        · have hv' : v = (0 : unitInterval) := Subtype.ext hv0
          subst v
          exact F.global_path_endpoint_ne_interior ⟨j, h⟩ ⟨j, g⟩ 0 u
            hu0 hu1 (by simpa using hv)
        · by_cases hv1 : (v : ℝ) = 1
          · have hv' : v = (1 : unitInterval) := Subtype.ext hv1
            subst v
            exact F.global_path_endpoint_ne_interior ⟨j, h⟩ ⟨j, g⟩ 1 u
              hu0 hu1 (by simpa using hv)
          · exact F.globalInwardExcursionPath_interior_ne_of_same_circle j g h hgh'
              u v hu0 hu1 hv0 hv1 hv.symm
  · have hcircles := G.cut.pairwise_disjoint (fun h ↦ hjk (Subtype.ext h))
    change Disjoint (Set.range (G.cut.circle j.1).circle)
      (Set.range (G.cut.circle k.1).circle) at hcircles
    rw [Set.disjoint_left] at hcircles
    apply hcircles
    · exact F.globalInwardExcursionPath_mem_cutCircle ⟨j, g⟩ u
    · have hmem := F.globalInwardExcursionPath_mem_cutCircle ⟨k, h⟩ v
      change ((fun w ↦ ((F.globalInwardExcursionPath ⟨k, h⟩ w :
        transportedTorus Phi) : R3)) v) ∈ Set.range (G.cut.circle k.1).circle at hmem
      rw [hv] at hmem
      exact hmem

/-- Each individual closed inward excursion is an embedded arc.  The only possible collision in
the circle quotient differs by an integral period; the cyclic successor interval has length
strictly less than one period because its two globally enumerated endpoints are distinct. -/
theorem globalInwardExcursionPath_injective
    (F : CutCircleTransverseCyclicOrderFamily G) (g : F.GlobalInwardGap) :
    Function.Injective (fun u ↦
      ((F.globalInwardExcursionPath g u : transportedTorus Phi) : R3)) := by
  intro u v huv
  let left := G.cutCircleSortedCrossing g.1.1 (F.globalGapFinIndex g)
  let right := G.cutCircleCyclicRight g.1.1 (F.order g.1).crossings_nonempty
    (F.globalGapFinIndex g)
  let period := 2 * Real.pi
  have hlr : left < right :=
    G.cutCircleSortedCrossing_lt_cyclicRight g.1.1
      (F.order g.1).crossings_nonempty (F.globalGapFinIndex g)
  have hrightLe : right ≤ left + period := by
    simpa [left, right, period] using
      G.cutCircleCyclicRight_le_add_period g.1.1
        (F.order g.1).crossings_nonempty (F.globalGapFinIndex g)
  have hrightLt : right < left + period := by
    apply lt_of_le_of_ne hrightLe
    intro heq
    have hpath :
        ((F.globalInwardExcursionPath g (0 : unitInterval) :
          transportedTorus Phi) : R3) =
          ((F.globalInwardExcursionPath g (1 : unitInterval) :
            transportedTorus Phi) : R3) := by
      rw [F.globalInwardExcursionPath_apply, F.globalInwardExcursionPath_apply]
      change (((G.cut.circle g.1.1).windingLoop.curve
          (left + (0 : ℝ) * (right - left)) :
        transportedTorus Phi) : R3) =
          (((G.cut.circle g.1.1).windingLoop.curve
            (left + (1 : ℝ) * (right - left)) :
            transportedTorus Phi) : R3)
      simp only [zero_mul, add_zero, one_mul]
      rw [heq]
      apply congrArg Subtype.val
      convert ((G.cut.circle g.1.1).windingLoop.periodic_curve left).symm using 1
      all_goals
        dsimp [period]
        ring_nf
    have hp : (g, (0 : Fin 2)) = (g, (1 : Fin 2)) :=
      F.global_path_endpoint_injective (by simpa using hpath)
    have he : (0 : Fin 2) = 1 := congrArg Prod.snd hp
    norm_num at he
  let su := F.globalInwardExcursionParameter g u
  let sv := F.globalInwardExcursionParameter g v
  have hsu : su ∈ Icc left right := by
    change left ≤ left + (u : ℝ) * (right - left) ∧
      left + (u : ℝ) * (right - left) ≤ right
    constructor <;> nlinarith [u.2.1, u.2.2]
  have hsv : sv ∈ Icc left right := by
    change left ≤ left + (v : ℝ) * (right - left) ∧
      left + (v : ℝ) * (right - left) ≤ right
    constructor <;> nlinarith [v.2.1, v.2.2]
  have hexp : Circle.exp su = Circle.exp sv := by
    apply (G.cut.circle g.1.1).isEmbedding.injective
    rw [(G.cut.circle g.1.1).parametrization,
      (G.cut.circle g.1.1).parametrization]
    simpa [su, sv, F.globalInwardExcursionPath_apply] using huv
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hnzero : n = 0 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · have hnleInt : n ≤ -1 := by omega
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast hnleInt
      have hshift : (n : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by
        simpa only [neg_mul, one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      dsimp [period] at hrightLt
      linarith [hsu.1, hsv.2, hn, hshift]
    · exact hnzero
    · have hnleInt : 1 ≤ n := by omega
      have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hnleInt
      have hshift : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      dsimp [period] at hrightLt
      linarith [hsv.1, hsu.2, hn, hshift]
  rw [hnzero, Int.cast_zero, zero_mul, add_zero] at hn
  apply Subtype.ext
  change left + (u : ℝ) * (right - left) =
    left + (v : ℝ) * (right - left) at hn
  nlinarith

/-- The global inward gap represented by a finite band index in the canonical enumeration. -/
noncomputable def globalGapOfBand
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) : F.GlobalInwardGap :=
  (Fintype.equivFin F.GlobalInwardGap).symm b

/-- The canonical seam enumeration evaluates by taking the corresponding global gap endpoint. -/
@[simp]
theorem toPairedSeamEnumeration_endpointEquiv_apply
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) (e : Fin 2) :
    F.toPairedSeamEnumeration.endpointEquiv (b, e) =
      F.globalEndpointEquiv (F.globalGapOfBand b, e) := by
  rfl

/-- The geometrically constructed inward arc indexed by a canonical finite band. -/
noncomputable def globalBandPath
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) :=
  F.globalInwardExcursionPath (F.globalGapOfBand b)

@[simp]
theorem globalBandPath_endpoint_val
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) (e : Fin 2) :
    (F.toPairedSeamEnumeration.endpointEquiv (b, e)).1 =
      ((F.globalBandPath b (finTwoUnitInterval e) : transportedTorus Phi) : R3) := by
  rw [F.toPairedSeamEnumeration_endpointEquiv_apply]
  exact F.globalEndpointEquiv_val_eq_path_endpoint (F.globalGapOfBand b) e

/-- Closed ranges of the canonically finite-indexed global bands remain pairwise disjoint. -/
theorem globalBandPath_ranges_pairwise_disjoint
    (F : CutCircleTransverseCyclicOrderFamily G) :
    Pairwise fun b e : Fin F.toPairedSeamEnumeration.bandCount ↦
      Disjoint
        (Set.range fun u ↦ ((F.globalBandPath b u : transportedTorus Phi) : R3))
        (Set.range fun u ↦
          ((F.globalBandPath e u : transportedTorus Phi) : R3)) := by
  intro b e hbe
  apply F.globalInwardExcursionPath_ranges_pairwise_disjoint
  intro hgap
  apply hbe
  exact (Fintype.equivFin F.GlobalInwardGap).symm.injective hgap

/-- Disjoint open ambient neighborhoods around the canonical closed inward bands.  This is now a
consequence of cyclic ordering and normality of Euclidean space, rather than collar input. -/
noncomputable def globalBandOpenNeighborhood
    (F : CutCircleTransverseCyclicOrderFamily G) :
    Fin F.toPairedSeamEnumeration.bandCount → Set R3 := by
  let K : Fin F.toPairedSeamEnumeration.bandCount → Set R3 :=
    fun b ↦ Set.range fun u ↦
      ((F.globalBandPath b u : transportedTorus Phi) : R3)
  have hclosed : ∀ b, IsClosed (K b) := by
    intro b
    exact F.isClosed_range_globalInwardExcursionPath (F.globalGapOfBand b)
  exact Classical.choose
    (exists_pairwise_disjoint_open_supersets K hclosed
      F.globalBandPath_ranges_pairwise_disjoint)

theorem globalBandOpenNeighborhood_spec
    (F : CutCircleTransverseCyclicOrderFamily G) :
    (∀ b, IsOpen (F.globalBandOpenNeighborhood b) ∧
      Set.range (fun u ↦
        ((F.globalBandPath b u : transportedTorus Phi) : R3)) ⊆
          F.globalBandOpenNeighborhood b) ∧
      Pairwise fun b e ↦
        Disjoint (F.globalBandOpenNeighborhood b) (F.globalBandOpenNeighborhood e) := by
  let K : Fin F.toPairedSeamEnumeration.bandCount → Set R3 :=
    fun b ↦ Set.range fun u ↦
      ((F.globalBandPath b u : transportedTorus Phi) : R3)
  have hclosed : ∀ b, IsClosed (K b) := by
    intro b
    exact F.isClosed_range_globalInwardExcursionPath (F.globalGapOfBand b)
  exact Classical.choose_spec
    (exists_pairwise_disjoint_open_supersets K hclosed
      F.globalBandPath_ranges_pairwise_disjoint)

/-- A finite subcover of one closed excursion by the canonical transported-torus point charts.
This is the precise compactness output available from `LocalFlatness`; the later tubular gluing
step may use these finitely many compatible local charts without pretending that one point chart
contains the entire excursion. -/
structure GlobalBandFiniteTorusChartCover
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) where
  index : Type*
  finite_index : Finite index
  center : index → unitInterval
  cover : ⋃ i, (F.globalBandPath b) ⁻¹'
      (transportedTorusChart Phi (F.globalBandPath b (center i))).source = Set.univ

/-- Compactness of the parameter interval constructs the finite local-chart cover of each
excursion unconditionally. -/
noncomputable def globalBandFiniteTorusChartCover
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) :
    GlobalBandFiniteTorusChartCover F b := by
  let U : unitInterval → Set unitInterval := fun u ↦
    (F.globalBandPath b) ⁻¹'
      (transportedTorusChart Phi (F.globalBandPath b u)).source
  have hUopen : ∀ u, IsOpen (U u) := fun u ↦
    (transportedTorusChart Phi (F.globalBandPath b u)).open_source.preimage
      (F.globalBandPath b).continuous
  have hcover : Set.univ ⊆ ⋃ u, U u := by
    intro u _
    exact mem_iUnion.mpr
      ⟨u, mem_transportedTorusChart_source Phi (F.globalBandPath b u)⟩
  let s := Classical.choose
    (isCompact_univ.elim_finite_subcover U hUopen hcover)
  have hs := Classical.choose_spec
    (isCompact_univ.elim_finite_subcover U hUopen hcover)
  exact {
    index := {u : unitInterval // u ∈ s}
    finite_index := inferInstance
    center := fun u ↦ u.1
    cover := by
      apply Set.eq_univ_of_univ_subset
      intro u _
      have hu := hs (mem_univ u)
      simp only [mem_iUnion] at hu ⊢
      obtain ⟨v, hv, huv⟩ := hu
      exact ⟨⟨v, hv⟩, huv⟩
  }

/-- The honest remaining tubular-neighborhood gluing datum for one excursion.  Its `localCover`
is already constructed from transported-torus charts.  The only new geometric datum is their
compatible gluing to one planar strip, with an exact parametrized core and image control inside
the automatically separated ambient neighborhood.  No moving sphere or resolved intersection
is included in this structure. -/
structure GlobalBandTubularChartData
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) where
  localCover : GlobalBandFiniteTorusChartCover F b :=
    F.globalBandFiniteTorusChartCover b
  surfacePatch : Set (transportedTorus Phi)
  strip : Plane ≃ₜ surfacePatch
  strip_mem_neighborhood : Set.range (fun z ↦
    (((strip z : surfacePatch) : transportedTorus Phi) : R3)) ⊆
      F.globalBandOpenNeighborhood b
  eventRegion : Set R3
  strip_mem_eventRegion : Set.range (fun z ↦
    (((strip z : surfacePatch) : transportedTorus Phi) : R3)) ⊆ eventRegion
  core_alignment : ∀ u : unitInterval,
    (((strip (bandSeamPath u) : surfacePatch) : transportedTorus Phi) : R3) =
      ((F.globalBandPath b u : transportedTorus Phi) : R3)

namespace GlobalBandTubularChartData

variable {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

/-- A tubular strip contained in the canonical disjoint neighborhood may use that neighborhood
itself as its event region; event-region bookkeeping is not additional geometry. -/
def ofStrip
    (surfacePatch : Set (transportedTorus Phi))
    (strip : Plane ≃ₜ surfacePatch)
    (hstrip : Set.range (fun z ↦
      (((strip z : surfacePatch) : transportedTorus Phi) : R3)) ⊆
        F.globalBandOpenNeighborhood b)
    (halign : ∀ u : unitInterval,
      (((strip (bandSeamPath u) : surfacePatch) : transportedTorus Phi) : R3) =
        ((F.globalBandPath b u : transportedTorus Phi) : R3)) :
    GlobalBandTubularChartData F b where
  surfacePatch := surfacePatch
  strip := strip
  strip_mem_neighborhood := hstrip
  eventRegion := F.globalBandOpenNeighborhood b
  strip_mem_eventRegion := hstrip
  core_alignment := halign

/-- A glued transported-torus tubular strip gives the standardized planar four-port chart. -/
def toPairedSeamBandChart (T : GlobalBandTubularChartData F b) :
    PairedSeamBandChart :=
  PairedSeamBandChart.ofTransportedTorusHomeomorph T.strip
    ((fun uv ↦ (((T.strip uv : T.surfacePatch) : transportedTorus Phi) : R3)) ''
      standardBandPatchCarrier)
    (F.globalBandOpenNeighborhood b) Set.Subset.rfl (by
      rintro _ ⟨z, _, rfl⟩
      exact T.strip_mem_neighborhood ⟨z, rfl⟩)

@[simp]
theorem toPairedSeamBandChart_support (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.support =
      (fun uv ↦ (((T.strip uv : T.surfacePatch) : transportedTorus Phi) : R3)) ''
        standardBandPatchCarrier := rfl

theorem toPairedSeamBandChart_support_subset_neighborhood
    (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.support ⊆ F.globalBandOpenNeighborhood b := by
  rintro _ ⟨z, _, rfl⟩
  exact T.strip_mem_neighborhood ⟨z, rfl⟩

@[simp]
theorem toPairedSeamBandChart_eventRegion (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.eventRegion = F.globalBandOpenNeighborhood b := rfl

theorem toPairedSeamBandChart_seamPath_apply
    (T : GlobalBandTubularChartData F b) (u : unitInterval) :
    T.toPairedSeamBandChart.seamPath u =
      ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
  exact T.core_alignment u

theorem toPairedSeamBandChart_seamPath_range
    (T : GlobalBandTubularChartData F b) :
    Set.range T.toPairedSeamBandChart.seamPath =
      Set.range (fun u ↦ ((F.globalBandPath b u : transportedTorus Phi) : R3)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, (T.toPairedSeamBandChart_seamPath_apply u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, T.toPairedSeamBandChart_seamPath_apply u⟩

theorem toPairedSeamBandChart_leftVertex
    (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.leftVertex =
      (F.toPairedSeamEnumeration.firstVertex b).1 := by
  calc
    T.toPairedSeamBandChart.leftVertex =
        T.toPairedSeamBandChart.seamPath 0 :=
      T.toPairedSeamBandChart.seamPath.source.symm
    _ = ((F.globalBandPath b 0 : transportedTorus Phi) : R3) :=
      T.toPairedSeamBandChart_seamPath_apply 0
    _ = (F.toPairedSeamEnumeration.firstVertex b).1 :=
      by
        unfold PairedSeamEnumeration.firstVertex
        simpa only [finTwoUnitInterval_zero] using
          (F.globalBandPath_endpoint_val b 0).symm

theorem toPairedSeamBandChart_rightVertex
    (T : GlobalBandTubularChartData F b) :
    T.toPairedSeamBandChart.rightVertex =
      (F.toPairedSeamEnumeration.secondVertex b).1 := by
  calc
    T.toPairedSeamBandChart.rightVertex =
        T.toPairedSeamBandChart.seamPath 1 :=
      T.toPairedSeamBandChart.seamPath.target.symm
    _ = ((F.globalBandPath b 1 : transportedTorus Phi) : R3) :=
      T.toPairedSeamBandChart_seamPath_apply 1
    _ = (F.toPairedSeamEnumeration.secondVertex b).1 :=
      by
        unfold PairedSeamEnumeration.secondVertex
        simpa only [finTwoUnitInterval_one] using
          (F.globalBandPath_endpoint_val b 1).symm

end GlobalBandTubularChartData

/-- Compatible tubular-strip gluings for every globally ordered inward excursion. -/
structure GlobalBandTubularChartFamily
    (F : CutCircleTransverseCyclicOrderFamily G) where
  band : ∀ b : Fin F.toPairedSeamEnumeration.bandCount,
    GlobalBandTubularChartData F b

namespace GlobalBandTubularChartFamily

variable {F : CutCircleTransverseCyclicOrderFamily G}

def chart (T : GlobalBandTubularChartFamily F)
    (b : Fin F.toPairedSeamEnumeration.bandCount) : PairedSeamBandChart :=
  (T.band b).toPairedSeamBandChart

theorem chart_support_pairwise (T : GlobalBandTubularChartFamily F) :
    Pairwise fun b e ↦ Disjoint (T.chart b).support (T.chart e).support := by
  intro b e hbe
  exact (F.globalBandOpenNeighborhood_spec.2 hbe).mono
    (T.band b).toPairedSeamBandChart_support_subset_neighborhood
    (T.band e).toPairedSeamBandChart_support_subset_neighborhood

/-- Forget alignment and retain the disjoint standardized four-port charts. -/
def toFinitePairedSeamBandCharts (T : GlobalBandTubularChartFamily F) :
    FinitePairedSeamBandCharts F.toPairedSeamEnumeration.bandCount where
  band := T.chart
  support_pairwise := T.chart_support_pairwise

end GlobalBandTubularChartFamily

end CutCircleTransverseCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

/-! ## Excursion arcs and disjoint ambient bands -/

/-- The cyclic ordering has been matched with the inward cutting-plane arcs in a finite barrier
arc presentation.  No ambient neighborhood or smoothing is assumed here. -/
structure OrderedInwardExcursionData
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    (A : FiniteBarrierArcPresentation G vertex edge) where
  enumeration : PairedSeamEnumeration vertex
  excursionEdge : Fin enumeration.bandCount → edge
  excursion_source : ∀ b,
    A.sourcePoint (excursionEdge b) = A.point (enumeration.firstVertex b)
  excursion_target : ∀ b,
    A.targetPoint (excursionEdge b) = A.point (enumeration.secondVertex b)

/-- Disjoint ambient support bands around the ordered inward excursions.  These are still only
neighborhoods; the transported-torus chart realizing the standard four-port patch is supplied
separately by `BarrierExcursionBandChartRealization`. -/
structure OrderedExcursionBandNeighborhoods
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (E : OrderedInwardExcursionData A) where
  neighborhood : Fin E.enumeration.bandCount → Set R3
  isOpen_neighborhood : ∀ b, IsOpen (neighborhood b)
  firstVertex_mem : ∀ b,
    A.point (E.enumeration.firstVertex b) ∈ neighborhood b
  secondVertex_mem : ∀ b,
    A.point (E.enumeration.secondVertex b) ∈ neighborhood b
  excursion_mem : ∀ b,
    Set.range (A.arc (E.excursionEdge b)) ⊆ neighborhood b
  pairwise_disjoint : Pairwise fun b e ↦
    Disjoint (neighborhood b) (neighborhood e)

/-- Once the finitely many closed excursion arcs are proved disjoint, normality of `ℝ³`
constructs the disjoint ambient support neighborhoods automatically.  Thus support separation is
not an additional moving-sphere hypothesis. -/
noncomputable def OrderedExcursionBandNeighborhoods.ofPairwiseDisjointClosedExcursions
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (E : OrderedInwardExcursionData A)
    (hclosed : ∀ b, IsClosed (Set.range (A.arc (E.excursionEdge b))))
    (hdisjoint : Pairwise fun b e ↦
      Disjoint (Set.range (A.arc (E.excursionEdge b)))
        (Set.range (A.arc (E.excursionEdge e)))) :
    OrderedExcursionBandNeighborhoods E := by
  let K : Fin E.enumeration.bandCount → Set R3 :=
    fun b ↦ Set.range (A.arc (E.excursionEdge b))
  let U := Classical.choose
    (exists_pairwise_disjoint_open_supersets K hclosed hdisjoint)
  have hUall := Classical.choose_spec
    (exists_pairwise_disjoint_open_supersets K hclosed hdisjoint)
  have hU := hUall.1
  have hUpairwise := hUall.2
  exact {
    neighborhood := U
    isOpen_neighborhood := fun b ↦ (hU b).1
    firstVertex_mem := fun b ↦ (hU b).2 ⟨0, by
      rw [Path.source, E.excursion_source]⟩
    secondVertex_mem := fun b ↦ (hU b).2 ⟨1, by
      rw [Path.target, E.excursion_target]⟩
    excursion_mem := fun b ↦ (hU b).2
    pairwise_disjoint := hUpairwise
  }

/-- The sorted cyclic enumeration and disjoint support bands construct the exact pairing consumed
by the four-port smoothing layer.  In particular, uniqueness of the band at each seam vertex is
not repeated as a geometric hypothesis. -/
def OrderedInwardExcursionData.toFiniteBarrierExcursionPairing
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (E : OrderedInwardExcursionData A)
    (N : OrderedExcursionBandNeighborhoods E) :
    FiniteBarrierExcursionPairing A where
  bandCount := E.enumeration.bandCount
  firstVertex := E.enumeration.firstVertex
  secondVertex := E.enumeration.secondVertex
  paired_vertices_ne := E.enumeration.paired_vertices_ne
  excursionEdge := E.excursionEdge
  excursion_source := E.excursion_source
  excursion_target := E.excursion_target
  every_vertex_in_unique_band := E.enumeration.every_vertex_in_unique_band
  bandNeighborhood := N.neighborhood
  bandNeighborhood_open := N.isOpen_neighborhood
  firstVertex_mem_band := N.firstVertex_mem
  secondVertex_mem_band := N.secondVertex_mem
  excursion_mem_band := N.excursion_mem
  bandNeighborhood_pairwise := N.pairwise_disjoint

/-! ## Canonical adapters from the analytic cyclic ordering -/

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : CutCircleTransverseCyclicOrderFamily G}
  [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]
  {A : FiniteBarrierArcPresentation G
    (SuperellipsoidSeamVertex Phi frame c R d) edge}

/-- Identification of the inward arcs already present in a finite barrier presentation with the
canonical cyclicly ordered paths.  This contains no neighborhood, chart, or sphere data. -/
structure GlobalBandArcPresentationAlignment
    (F : CutCircleTransverseCyclicOrderFamily G)
    (A : FiniteBarrierArcPresentation G
      (SuperellipsoidSeamVertex Phi frame c R d) edge) where
  point_eq : ∀ v, A.point v = v.1
  excursionEdge : Fin F.toPairedSeamEnumeration.bandCount → edge
  excursion_source : ∀ b,
    A.sourcePoint (excursionEdge b) =
      A.point (F.toPairedSeamEnumeration.firstVertex b)
  excursion_target : ∀ b,
    A.targetPoint (excursionEdge b) =
      A.point (F.toPairedSeamEnumeration.secondVertex b)
  arc_range_eq : ∀ b,
    Set.range (A.arc (excursionEdge b)) =
      Set.range (fun u ↦ ((F.globalBandPath b u : transportedTorus Phi) : R3))

namespace GlobalBandArcPresentationAlignment

/-- The canonical cyclic order and its automatic disjoint neighborhoods supply the complete
finite barrier excursion pairing. -/
@[reducible]
noncomputable def toFiniteBarrierExcursionPairing
    (L : GlobalBandArcPresentationAlignment F A) :
    FiniteBarrierExcursionPairing A where
  bandCount := F.toPairedSeamEnumeration.bandCount
  firstVertex := F.toPairedSeamEnumeration.firstVertex
  secondVertex := F.toPairedSeamEnumeration.secondVertex
  paired_vertices_ne := F.toPairedSeamEnumeration.paired_vertices_ne
  excursionEdge := L.excursionEdge
  excursion_source := L.excursion_source
  excursion_target := L.excursion_target
  every_vertex_in_unique_band := F.toPairedSeamEnumeration.every_vertex_in_unique_band
  bandNeighborhood := F.globalBandOpenNeighborhood
  bandNeighborhood_open := fun b ↦ (F.globalBandOpenNeighborhood_spec.1 b).1
  firstVertex_mem_band := fun b ↦ by
    rw [L.point_eq]
    unfold PairedSeamEnumeration.firstVertex
    rw [F.globalBandPath_endpoint_val b 0]
    refine (F.globalBandOpenNeighborhood_spec.1 b).2 ⟨0, ?_⟩
    simp
  secondVertex_mem_band := fun b ↦ by
    rw [L.point_eq]
    unfold PairedSeamEnumeration.secondVertex
    rw [F.globalBandPath_endpoint_val b 1]
    refine (F.globalBandOpenNeighborhood_spec.1 b).2 ⟨1, ?_⟩
    simp
  excursion_mem_band := fun b ↦ by
    rw [L.arc_range_eq]
    exact (F.globalBandOpenNeighborhood_spec.1 b).2
  bandNeighborhood_pairwise := F.globalBandOpenNeighborhood_spec.2

end GlobalBandArcPresentationAlignment

/-- The local analytic equation after a tubular strip has been glued: inside each automatically
separated support, the literal outer-sphere/cutting-disk barrier is the standard four-port
singular patch.  This is the local IFT computation still required beyond the purely topological
tubular-neighborhood theorem; no resolved stage is assumed. -/
structure GlobalBandBarrierChartExactness
    (T : CutCircleTransverseCyclicOrderFamily.GlobalBandTubularChartFamily F)
    (L : GlobalBandArcPresentationAlignment F A) where
  singular_local_exact : ∀ b,
    G.carrier ∩ (T.chart b).support = (T.chart b).singularPatch

namespace GlobalBandBarrierChartExactness

/-- Tubular strips, canonical arc alignment, and the local barrier equation construct the exact
chart realization consumed by the four-port smoothing layer. -/
noncomputable def toBarrierExcursionBandChartRealization
    {T : CutCircleTransverseCyclicOrderFamily.GlobalBandTubularChartFamily F}
    {L : GlobalBandArcPresentationAlignment F A}
    (X : GlobalBandBarrierChartExactness T L) :
    BarrierExcursionBandChartRealization L.toFiniteBarrierExcursionPairing where
  chart := T.chart
  support_subset := fun b ↦
    (T.band b).toPairedSeamBandChart_support_subset_neighborhood
  neighborhood_subset_eventRegion := fun b ↦ by
    change F.globalBandOpenNeighborhood b ⊆
      (T.band b).toPairedSeamBandChart.eventRegion
    rw [(T.band b).toPairedSeamBandChart_eventRegion]
  leftVertex_eq := fun b ↦ by
    let b' : Fin F.toPairedSeamEnumeration.bandCount := ⟨b.1, by
      have hb := b.2
      change b.1 < F.toPairedSeamEnumeration.bandCount at hb
      exact hb⟩
    change (T.chart b').leftVertex = A.point (F.toPairedSeamEnumeration.firstVertex b')
    unfold CutCircleTransverseCyclicOrderFamily.GlobalBandTubularChartFamily.chart
    rw [(T.band b').toPairedSeamBandChart_leftVertex, L.point_eq]
  rightVertex_eq := fun b ↦ by
    let b' : Fin F.toPairedSeamEnumeration.bandCount := ⟨b.1, by
      have hb := b.2
      change b.1 < F.toPairedSeamEnumeration.bandCount at hb
      exact hb⟩
    change (T.chart b').rightVertex = A.point (F.toPairedSeamEnumeration.secondVertex b')
    unfold CutCircleTransverseCyclicOrderFamily.GlobalBandTubularChartFamily.chart
    rw [(T.band b').toPairedSeamBandChart_rightVertex, L.point_eq]
  seamPath_range_eq := fun b ↦ by
    let b' : Fin F.toPairedSeamEnumeration.bandCount := ⟨b.1, by
      have hb := b.2
      change b.1 < F.toPairedSeamEnumeration.bandCount at hb
      exact hb⟩
    change Set.range (T.chart b').seamPath = Set.range (A.arc (L.excursionEdge b'))
    unfold CutCircleTransverseCyclicOrderFamily.GlobalBandTubularChartFamily.chart
    rw [(T.band b').toPairedSeamBandChart_seamPath_range, L.arc_range_eq]
  chart_mem_torus := fun b z ↦ ((T.band b).strip z).1.2
  singular_local_exact := X.singular_local_exact

end GlobalBandBarrierChartExactness

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
