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
    simpa only [superellipsoidSeamMap, superellipsoidSeamPairMap] using
      det_fderiv_superellipsoidSeamPairMap Phi frame c uv
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
    simpa only [superellipsoidSeamMap, superellipsoidSeamPairMap] using
      contDiff_superellipsoidSeamPairMap Phi frame c
  have hderiv : HasFDerivAt (superellipsoidSeamMap Phi frame c)
      (e : Plane →L[ℝ] Plane) uv := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hsmooth.differentiable (by simp) uv).hasFDerivAt
  let local := hsmooth.contDiffAt.toOpenPartialHomeomorph
    (superellipsoidSeamMap Phi frame c) hderiv (by simp)
  refine ⟨local.source, local.open_source, ?_, local.injOn⟩
  exact hsmooth.contDiffAt.mem_toOpenPartialHomeomorph hderiv (by simp)

/-- Consequently the compact fundamental seam is discrete, hence finite. -/
theorem hasSuperellipsoidSeamIsolation
    (Phi : AmbientIsotopy) : HasSuperellipsoidSeamIsolation Phi :=
  hasSuperellipsoidSeamIsolation_of_localInverses
    (hasSuperellipsoidSeamLocalInverses Phi)

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
noncomputable def FiniteSuperellipsoidBarrierGraph.seamVertexFintype
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    Fintype (SuperellipsoidSeamVertex Phi frame c R d) :=
  G.seam_finite.fintype

/-- An explicit even enumeration of a finite seam.  The first coordinate is the inward excursion
band and the second coordinate chooses its two endpoints.  This is the precise finite output of
sorting the transverse intersections cyclically along the cutting circles. -/
structure PairedSeamEnumeration (vertex : Type*) [Fintype vertex] where
  bandCount : ℕ
  endpointEquiv : Fin bandCount × Fin 2 ≃ vertex

namespace PairedSeamEnumeration

variable {vertex : Type*} [Fintype vertex]

/-- Once cyclic sign alternation proves that the vertex count is twice the number of inward
excursions, the finite enumeration itself is automatic. -/
noncomputable def of_card_eq_two_mul (bandCount : ℕ)
    (hcard : Fintype.card vertex = 2 * bandCount) :
    PairedSeamEnumeration vertex where
  bandCount := bandCount
  endpointEquiv := Fintype.equivOfCardEq (by
    simpa [hcard, Nat.mul_comm])

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
  · fin_cases p.2
    · exact Or.inl (E.endpointEquiv.apply_symm_apply v).symm
    · exact Or.inr (E.endpointEquiv.apply_symm_apply v).symm
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
structure AlternatingCyclicSideData (n : ℕ) [NeZero n] where
  side : ZMod n → Bool
  changes : ∀ i, side (i + 1) ≠ side i

namespace AlternatingCyclicSideData

variable {n : ℕ} [NeZero n]

/-- The cyclic intervals lying strictly in the superellipsoid body. -/
def InwardGap (D : AlternatingCyclicSideData n) :=
  {i : ZMod n // D.side i = false}

instance (D : AlternatingCyclicSideData n) : Fintype D.InwardGap :=
  inferInstance

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
  · have hij : (i : ZMod n) = j + 1 := by
      simpa [endpoint] using h
    have hchange := D.changes j
    rw [← hij, i.property, j.property] at hchange
    contradiction
  · have hij : (i : ZMod n) + 1 = j := by
      simpa [endpoint] using h
    have hchange := D.changes i
    rw [hij, i.property, j.property] at hchange
    contradiction
  · apply Prod.ext
    · apply Subtype.ext
      have hij : (i : ZMod n) + 1 = j + 1 := by
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
      rw [Set.disjoint_left] at hdisjoint
      exact hdisjoint x.2.1 (hval.symm ▸ y.2.1)
    subst j
    apply Sigma.ext rfl
    apply Subtype.ext
    exact hval
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
    · exact congrArg Subtype.val hst
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

instance activeCutCircleFintype
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex) :
    Fintype G.ActiveCutCircle := inferInstance

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
      rw [Set.disjoint_left] at hdisjoint
      exact hdisjoint x.2.1 (hval.symm ▸ y.2.1)
    have hijSubtype : i = j := Subtype.ext hij
    subst j
    apply Sigma.ext rfl
    apply Subtype.ext
    exact hval
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
  superellipsoidGauge frame c (G.cut.circle j).windingLoop.curve t - R

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
    Set.mem_setOf_eq]
  exact ⟨fun h ↦ ⟨⟨hcut.1, h⟩, hcut.2⟩, fun h ↦ h.1.2⟩

theorem cutCircleOuterGaugeDifference_neg_iff_body
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) :
    G.cutCircleOuterGaugeDifference j t < 0 ↔
      ((G.cut.circle j).windingLoop.curve t : R3) ∈
        superellipsoidBody frame c R := by
  simp only [cutCircleOuterGaugeDifference, sub_neg, superellipsoidBody,
    Set.mem_setOf_eq]

/-- The smooth polynomial version of the outer signed coordinate.  This is the coordinate to
which the ordinary one-variable sign-flip theorem is applied. -/
def cutCircleOuterPolynomialDifference
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (t : ℝ) : ℝ :=
  superellipsoidPolynomial frame c (G.cut.circle j).windingLoop.curve t - R ^ 256

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
  have hpow : 0 ≤ R ^ 256 := pow_nonneg hR.le _
  have hroot : (R ^ 256 : ℝ) ^ (1 / (256 : ℝ)) = R := by
    simpa only [one_div] using
      Real.pow_rpow_inv_natCast hR.le (n := 256) (by norm_num)
  change superellipsoidPolynomial frame c x - R ^ 256 < 0 ↔
    superellipsoidGauge frame c x < R
  rw [sub_neg, superellipsoidGauge_eq_polynomial_rpow, ← hroot]
  exact (Real.rpow_lt_rpow_iff hpoly hpow (by norm_num)).symm

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
    (M : Submission.SurfaceRegularValue.RegularComponentCompleteOrbit.RegularOrbitStandardPeriodData O)
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
    simpa only [map_smul, smul_eq_mul, heval] using hcomp
  have hadd := hderivComp.sub_const (R ^ 256)
  simpa only [hfunction, add_sub_cancel_right] using hadd

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

theorem cutCircleCyclicRight_le_add_period
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (j : cutIndex) (hne : (G.cutCircleSeamCrossings j).Nonempty)
    (i : Fin (G.cutCircleSeamCrossings j).card) :
    G.cutCircleCyclicRight j hne i ≤
      G.cutCircleSortedCrossing j i + 2 * Real.pi := by
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
        linarith [ht.2]
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

noncomputable local instance (O : CutCircleTransverseCyclicOrder G j) :
    NeZero (G.cutCircleSeamCrossings j).card :=
  ⟨(Finset.card_pos.mpr O.crossings_nonempty).ne'⟩

/-- The local simple-zero theorem and cyclic sorting prove the sole alternation field.  The two
cases are an ordinary successor crossing and the wrap from the last crossing to the first one in
the next period. -/
noncomputable def ofSmoothLift
    (D : SmoothCutCircleLiftData G j) (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (hne : (G.cutCircleSeamCrossings j).Nonempty) :
    CutCircleTransverseCyclicOrder G j := by
  letI : NeZero (G.cutCircleSeamCrossings j).card :=
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
      simpa [left, crossing, cutCircleCyclicRight, hnext] using hxLastGap)
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
  side := G.cutCircleZModGapSide j O.crossings_nonempty
  changes := O.adjacent_gap_sides_ne

/-- The seam pairing on one cutting circle, derived from its sorted transverse crossings. -/
noncomputable def toPairedSeamEnumeration
    (O : CutCircleTransverseCyclicOrder G j) :
    PairedSeamEnumeration (G.CutCircleSeamVertex j) :=
  O.sideData.toPairedSeamEnumeration
    (G.cutCircleCyclicCrossingEquiv j O.crossings_nonempty)

/-- The inward interval represented by one band in the derived pairing. -/
noncomputable def inwardGapOfBand (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) : O.sideData.InwardGap :=
  (Fintype.equivFin O.sideData.InwardGap).symm b

/-- The sorted real index of a cyclic inward gap. -/
def inwardGapFinIndex (O : CutCircleTransverseCyclicOrder G j)
    (b : Fin O.toPairedSeamEnumeration.bandCount) :
    Fin (G.cutCircleSeamCrossings j).card :=
  ⟨(O.inwardGapOfBand b).1.val, ZMod.val_lt _⟩

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
  target' := by ring_nf

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
noncomputable def ofSmoothLifts
    (D : ∀ j : G.ActiveCutCircle, SmoothCutCircleLiftData G j.1)
    (hR : 0 < R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    CutCircleTransverseCyclicOrderFamily G where
  order := fun j ↦
    CutCircleTransverseCyclicOrder.ofSmoothLift (D j) hR hseam j.2

/-- All inward cyclic gaps, retaining the cutting-circle index. -/
def GlobalInwardGap (F : CutCircleTransverseCyclicOrderFamily G) :=
  Σ j : G.ActiveCutCircle, (F.order j).sideData.InwardGap

instance (F : CutCircleTransverseCyclicOrderFamily G) :
    Fintype F.GlobalInwardGap := inferInstance

/-- Product distributes over this dependent finite sum. -/
def globalGapEndpointDistrib (F : CutCircleTransverseCyclicOrderFamily G) :
    F.GlobalInwardGap × Fin 2 ≃
      Σ j : G.ActiveCutCircle, (F.order j).sideData.InwardGap × Fin 2 where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun p := (⟨p.1, p.2.1⟩, p.2.2)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The local alternating endpoint equivalences and exact active-circle seam decomposition give
the global perfect pairing of every analytic seam vertex. -/
noncomputable def globalEndpointEquiv
    (F : CutCircleTransverseCyclicOrderFamily G) :
    F.GlobalInwardGap × Fin 2 ≃
      SuperellipsoidSeamVertex Phi frame c R d :=
  (F.globalGapEndpointDistrib.trans
    (Equiv.sigmaCongrRight fun j ↦ (F.order j).sideData.endpointEquiv)).trans
      G.activeCutCircleSeamVertexEquiv

/-- The global seam enumeration is therefore derived from the smooth transverse cutting-circle
orbits, with no independent vertex pairing input. -/
noncomputable def toPairedSeamEnumeration
    (F : CutCircleTransverseCyclicOrderFamily G) :
    PairedSeamEnumeration (SuperellipsoidSeamVertex Phi frame c R d) where
  bandCount := Fintype.card F.GlobalInwardGap
  endpointEquiv :=
    ((Fintype.equivFin F.GlobalInwardGap).symm.prodCongr
      (Equiv.refl (Fin 2))).trans F.globalEndpointEquiv

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

/-- Once the finitely many closed excursion arcs are proved disjoint, normality of `ℝ³` constructs
the disjoint ambient support neighborhoods automatically.  Thus support separation is not an
additional moving-sphere hypothesis. -/
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
  obtain ⟨U, hU, hUpairwise⟩ :=
    exists_pairwise_disjoint_open_supersets K hclosed hdisjoint
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

end Submission.Topology
