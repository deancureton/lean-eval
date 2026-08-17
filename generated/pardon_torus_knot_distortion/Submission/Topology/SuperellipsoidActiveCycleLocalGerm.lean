import Submission.Topology.SuperellipsoidActiveCycleConcatenation
import Submission.Topology.SuperellipsoidInwardClosedGapPackage

/-!
# Local seam germs for the canonical alternating cycles

The closed-gap incidence package gives all of the finite separation needed at a seam vertex.
Together with exact closed-half coverage, it also identifies the selected two branches locally,
so no additional local-germ premise is needed for the truncated-sphere construction.

For a finite two-colour endpoint system, the complement of all nonincident closed arcs is an open
neighborhood of a vertex on which the total carrier is exactly the union of its two incident arcs.
For the superellipsoid system, the inverse-function chart
`superellipsoidSeamLocalHomeomorph` identifies the lifted ambient barrier with the standard signed
`T`.  The covering-chart structures below retain that independent route.  The final constructor
instead uses exact global closed-gap coverage and the canonical finite-isolation neighborhood to
obtain the same ambient `R3` germ directly.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

namespace FiniteAlternatingEndpointSystem

universe u v

variable {vertex : Type u} {X : Type v} [Fintype vertex]
  [TopologicalSpace X] [T2Space X]
  {A : FiniteAlternatingEndpointSystem vertex} {point : vertex → X}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- The union of every closed constituent arc in a two-colour endpoint system. -/
def totalClosedArcCarrier : Set X :=
  (⋃ e, Set.range (firstPaths.path e)) ∪
    ⋃ e, Set.range (secondPaths.path e)

/-- The two closed arcs incident to a specified vertex. -/
def incidentClosedArcCarrier (v : vertex) : Set X :=
  Set.range (firstPaths.path (A.first.endpointEquiv.symm v).1) ∪
    Set.range (secondPaths.path (A.second.endpointEquiv.symm v).1)

/-- The union of all closed arcs except the two incident to a specified vertex. -/
noncomputable def nonincidentClosedArcCarrier (v : vertex) : Set X := by
  classical
  exact
    (⋃ e, if e = (A.first.endpointEquiv.symm v).1 then ∅
        else Set.range (firstPaths.path e)) ∪
      ⋃ e, if e = (A.second.endpointEquiv.symm v).1 then ∅
        else Set.range (secondPaths.path e)

/-- Canonical finite-separation output at a vertex. -/
structure IncidentClosedArcIsolationData (v : vertex) where
  neighborhood : Set X
  isOpen_neighborhood : IsOpen neighborhood
  point_mem_neighborhood : point v ∈ neighborhood
  point_mem_incident :
    point v ∈ incidentClosedArcCarrier (A := A) (point := point)
      (firstPaths := firstPaths) (secondPaths := secondPaths) v
  total_local_eq_incident :
    totalClosedArcCarrier (A := A) (point := point) (firstPaths := firstPaths)
        (secondPaths := secondPaths) ∩ neighborhood =
      incidentClosedArcCarrier (A := A) (point := point) (firstPaths := firstPaths)
        (secondPaths := secondPaths) v ∩ neighborhood

/-- The endpoint numbered zero on the first edge incident to `v` lies in the same alternating
cycle as `v`. -/
theorem cycleOf_first_edgeOf_zero_eq (A : FiniteAlternatingEndpointSystem vertex)
    (v : vertex) :
    A.cycleOfVertex
        (A.first.endpointEquiv ((A.first.endpointEquiv.symm v).1, (0 : Fin 2))) =
      A.cycleOfVertex v := by
  let e := A.first.endpointEquiv.symm v
  have he : A.first.endpointEquiv e = v := A.first.endpointEquiv.apply_symm_apply v
  change A.cycleOfVertex (A.first.endpointEquiv (e.1, 0)) = A.cycleOfVertex v
  by_cases hj : e.2 = 0
  · have he0 : A.first.endpointEquiv (e.1, (0 : Fin 2)) = v := by
      rw [← hj]
      exact he
    exact congrArg A.cycleOfVertex he0
  · have hj1 : e.2 = 1 := by
      apply Fin.ext
      simp only [Fin.ext_iff] at hj ⊢
      omega
    have he1 : A.first.endpointEquiv (e.1, (1 : Fin 2)) = v := by
      rw [← hj1]
      exact he
    exact (A.first_edge_endpoints_same_cycle e.1).symm.trans
      (congrArg A.cycleOfVertex he1)

/-- The endpoint numbered zero on the second edge incident to `v` lies in the same alternating
cycle as `v`. -/
theorem cycleOf_second_edgeOf_zero_eq (A : FiniteAlternatingEndpointSystem vertex)
    (v : vertex) :
    A.cycleOfVertex
        (A.second.endpointEquiv ((A.second.endpointEquiv.symm v).1, (0 : Fin 2))) =
      A.cycleOfVertex v := by
  let e := A.second.endpointEquiv.symm v
  have he : A.second.endpointEquiv e = v := A.second.endpointEquiv.apply_symm_apply v
  change A.cycleOfVertex (A.second.endpointEquiv (e.1, 0)) = A.cycleOfVertex v
  by_cases hj : e.2 = 0
  · have he0 : A.second.endpointEquiv (e.1, (0 : Fin 2)) = v := by
      rw [← hj]
      exact he
    exact congrArg A.cycleOfVertex he0
  · have hj1 : e.2 = 1 := by
      apply Fin.ext
      simp only [Fin.ext_iff] at hj ⊢
      omega
    have he1 : A.second.endpointEquiv (e.1, (1 : Fin 2)) = v := by
      rw [← hj1]
      exact he
    exact (A.second_edge_endpoints_same_cycle e.1).symm.trans
      (congrArg A.cycleOfVertex he1)

private theorem isClosed_range_path {x y : X} (p : Path x y) :
    IsClosed (Set.range p) := by
  rw [← Set.image_univ]
  exact (isCompact_univ.image p.continuous).isClosed

omit [T2Space X] in
private theorem point_mem_incident_first
    (v : vertex) :
    point v ∈ Set.range (firstPaths.path (A.first.endpointEquiv.symm v).1) := by
  let e := A.first.endpointEquiv.symm v
  have he : A.first.endpointEquiv e = v := A.first.endpointEquiv.apply_symm_apply v
  change point v ∈ Set.range (firstPaths.path e.1)
  by_cases hj : e.2 = 0
  · refine ⟨0, ?_⟩
    rw [Path.source]
    have he0 : A.first.endpointEquiv (e.1, (0 : Fin 2)) = v := by
      rw [show (e.1, (0 : Fin 2)) = e by ext <;> simp [hj]]
      exact he
    exact congrArg point he0
  · have hj1 : e.2 = 1 := by
      apply Fin.ext
      simp only [Fin.ext_iff] at hj ⊢
      omega
    refine ⟨1, ?_⟩
    rw [Path.target]
    have he1 : A.first.endpointEquiv (e.1, (1 : Fin 2)) = v := by
      rw [show (e.1, (1 : Fin 2)) = e by ext <;> simp [hj1]]
      exact he
    exact congrArg point he1

omit [T2Space X] in
private theorem point_mem_incident_second
    (v : vertex) :
    point v ∈ Set.range (secondPaths.path (A.second.endpointEquiv.symm v).1) := by
  let e := A.second.endpointEquiv.symm v
  have he : A.second.endpointEquiv e = v := A.second.endpointEquiv.apply_symm_apply v
  change point v ∈ Set.range (secondPaths.path e.1)
  by_cases hj : e.2 = 0
  · refine ⟨0, ?_⟩
    rw [Path.source]
    have he0 : A.second.endpointEquiv (e.1, (0 : Fin 2)) = v := by
      rw [show (e.1, (0 : Fin 2)) = e by ext <;> simp [hj]]
      exact he
    exact congrArg point he0
  · have hj1 : e.2 = 1 := by
      apply Fin.ext
      simp only [Fin.ext_iff] at hj ⊢
      omega
    refine ⟨1, ?_⟩
    rw [Path.target]
    have he1 : A.second.endpointEquiv (e.1, (1 : Fin 2)) = v := by
      rw [show (e.1, (1 : Fin 2)) = e by ext <;> simp [hj1]]
      exact he
    exact congrArg point he1

/-- Closed constituent incidence canonically separates the two arcs incident to a vertex from
all other arcs.  The neighborhood is the complement of the finite union of nonincident ranges. -/
noncomputable def ClosedArcIncidenceData.incidentClosedArcIsolationData
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) (v : vertex) :
    IncidentClosedArcIsolationData (A := A) (point := point)
      (firstPaths := firstPaths) (secondPaths := secondPaths) v := by
  let bad := nonincidentClosedArcCarrier (A := A)
    (firstPaths := firstPaths) (secondPaths := secondPaths) v
  letI : Fintype A.first.edge := A.first.finite_edge
  letI : Fintype A.second.edge := A.second.finite_edge
  have hbadClosed : IsClosed bad := by
    apply IsClosed.union
    · apply isClosed_iUnion_of_finite
      intro e
      split
      · exact isClosed_empty
      · exact isClosed_range_path _
    · apply isClosed_iUnion_of_finite
      intro e
      split
      · exact isClosed_empty
      · exact isClosed_range_path _
  have hvFirst := point_mem_incident_first
    (A := A) (point := point) (firstPaths := firstPaths) v
  have hvSecond := point_mem_incident_second
    (A := A) (point := point) (secondPaths := secondPaths) v
  have hvBad : point v ∉ bad := by
    rintro (hv | hv)
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
      by_cases hev : e = (A.first.endpointEquiv.symm v).1
      · simp only [hev, if_pos] at he
        exact he
      · simp only [if_neg hev] at he
        exact Set.disjoint_left.mp (H.first_pairwise hev) he hvFirst
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
      by_cases hev : e = (A.second.endpointEquiv.symm v).1
      · simp only [hev, if_pos] at he
        exact he
      · simp only [if_neg hev] at he
        exact Set.disjoint_left.mp (H.second_pairwise hev) he hvSecond
  refine
    { neighborhood := badᶜ
      isOpen_neighborhood := hbadClosed.isOpen_compl
      point_mem_neighborhood := hvBad
      point_mem_incident := Or.inl hvFirst
      total_local_eq_incident := ?_ }
  ext x
  constructor
  · rintro ⟨hx, hxGood⟩
    refine ⟨?_, hxGood⟩
    rcases hx with hx | hx
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      by_cases hev : e = (A.first.endpointEquiv.symm v).1
      · subst e
        exact Or.inl he
      · exact (hxGood (Or.inl (Set.mem_iUnion.mpr ⟨e, by simpa [hev] using he⟩))).elim
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      by_cases hev : e = (A.second.endpointEquiv.symm v).1
      · subst e
        exact Or.inr he
      · exact (hxGood (Or.inr (Set.mem_iUnion.mpr ⟨e, by simpa [hev] using he⟩))).elim
  · rintro ⟨hx, hxGood⟩
    refine ⟨?_, hxGood⟩
    rcases hx with hx | hx
    · exact Or.inl (Set.mem_iUnion.mpr
        ⟨(A.first.endpointEquiv.symm v).1, hx⟩)
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨(A.second.endpointEquiv.symm v).1, hx⟩)

end FiniteAlternatingEndpointSystem

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe idx

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type idx} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (outerOrder : OuterCircleTransverseHeightCyclicOrderFamily G)
  (cutOrder : CutCircleTransverseCyclicOrderFamily G)

variable [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]

/- The covering/IFT alternative is superseded by the exact closed-coverage constructor below.

/-- The product-exponential covering map, with codomain restricted to the transported torus. -/
def planeToTransportedTorus (Phi : AmbientIsotopy) (uv : Plane) : transportedTorus Phi :=
  transportedTorusHomeomorph Phi (planeExpPair uv)

@[simp]
theorem coe_planeToTransportedTorus (Phi : AmbientIsotopy) (uv : Plane) :
    (planeToTransportedTorus Phi uv : R3) = transportedTorusPlaneMap Phi uv := by
  exact (transportedTorusPlaneMap_eq_expPair Phi uv).symm

/-- The plane-to-transported-torus covering is a local homeomorphism. -/
theorem planeToTransportedTorus_isLocalHomeomorph (Phi : AmbientIsotopy) :
    IsLocalHomeomorph (planeToTransportedTorus Phi) := by
  exact (transportedTorusHomeomorph Phi).isLocalHomeomorph.comp
    planeExpPair_isLocalHomeomorph

/-- A local covering sheet whose relatively open target is represented exactly as the trace of
an ambient open subset of `R3`. -/
structure PlaneToTransportedTorusAmbientChartData (Phi : AmbientIsotopy) (uv : Plane) where
  chart : OpenPartialHomeomorph Plane (transportedTorus Phi)
  uv_mem_source : uv ∈ chart.source
  chart_eq_covering : (chart : Plane → transportedTorus Phi) = planeToTransportedTorus Phi
  ambientNeighborhood : Set R3
  ambientNeighborhood_open : IsOpen ambientNeighborhood
  target_image_eq :
    ((fun x : transportedTorus Phi ↦ (x : R3)) '' chart.target) =
      ambientNeighborhood ∩ transportedTorus Phi

/-- The induced subtype topology removes the apparent relative-open/ambient-open gap for every
local covering sheet. -/
noncomputable def planeToTransportedTorusAmbientChartData
    (Phi : AmbientIsotopy) (uv : Plane) :
    PlaneToTransportedTorusAmbientChartData Phi uv := by
  let hlocal := planeToTransportedTorus_isLocalHomeomorph Phi
  let chart : OpenPartialHomeomorph Plane (transportedTorus Phi) :=
    (hlocal uv).choose
  have huv : uv ∈ chart.source := (hlocal uv).choose_spec.1
  have hchart : (chart : Plane → transportedTorus Phi) = planeToTransportedTorus Phi :=
    (hlocal uv).choose_spec.2
  obtain ⟨U, hUopen, htarget⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range chart.open_target
  refine
    { chart := chart
      uv_mem_source := huv
      chart_eq_covering := hchart
      ambientNeighborhood := U
      ambientNeighborhood_open := hUopen
      target_image_eq := ?_ }
  simpa only [Subtype.range_val] using htarget

/-- A simultaneous seam inverse-function chart and local covering sheet.  The source of the
covering chart is restricted to the inverse-function source; its target is still the exact torus
trace of an ambient open set. -/
structure SuperellipsoidSeamAmbientChartData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) where
  seamChart : OpenPartialHomeomorph Plane Plane :=
    superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv
  coveringChart : OpenPartialHomeomorph Plane (transportedTorus Phi)
  uv_mem_source : uv ∈ coveringChart.source
  source_subset_seamChart : coveringChart.source ⊆ seamChart.source
  coveringChart_eq :
    (coveringChart : Plane → transportedTorus Phi) = planeToTransportedTorus Phi
  ambientNeighborhood : Set R3
  ambientNeighborhood_open : IsOpen ambientNeighborhood
  target_image_eq :
    ((fun x : transportedTorus Phi ↦ (x : R3)) '' coveringChart.target) =
      ambientNeighborhood ∩ transportedTorus Phi

/-- Restricting a covering sheet by the open seam-chart source gives the simultaneous chart. -/
noncomputable def superellipsoidSeamAmbientChartData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (uv : Plane)
    (huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}) :
    SuperellipsoidSeamAmbientChartData Phi frame c R d hseam uv huv := by
  let seam := superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv
  let raw := planeToTransportedTorusAmbientChartData Phi uv
  let chart := raw.chart.restrOpen seam.source seam.open_source
  have huvRaw : uv ∈ raw.chart.source := raw.uv_mem_source
  have huvSeam : uv ∈ seam.source :=
    mem_source_superellipsoidSeamLocalHomeomorph Phi frame c R d hseam uv huv
  have huvChart : uv ∈ chart.source := ⟨huvRaw, huvSeam⟩
  obtain ⟨U, hUopen, htarget⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range chart.open_target
  refine
    { coveringChart := chart
      uv_mem_source := huvChart
      source_subset_seamChart := ?_
      coveringChart_eq := ?_
      ambientNeighborhood := U
      ambientNeighborhood_open := hUopen
      target_image_eq := ?_ }
  · intro z hz
    exact hz.2
  · change (chart : Plane → transportedTorus Phi) = planeToTransportedTorus Phi
    rw [show (chart : Plane → transportedTorus Phi) = raw.chart by rfl]
    exact raw.chart_eq_covering
  · simpa only [Subtype.range_val] using htarget

/-- A seam vertex together with a fundamental covering-plane lift and its simultaneous ambient
chart. -/
structure SeamVertexAmbientChartData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hR : 0 ≤ R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (p : SuperellipsoidSeamVertex Phi frame c R d) where
  lift : Plane
  lift_mem_fundamentalSeam :
    lift ∈ fundamentalSuperellipsoidSeam Phi frame c R d
  covering_lift_eq : transportedTorusPlaneMap Phi lift = (p : R3)
  lift_mem_seamFiber :
    lift ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}
  chartData :
    SuperellipsoidSeamAmbientChartData Phi frame c R d hseam lift lift_mem_seamFiber

/-- Every seam vertex has a fundamental lift and a simultaneous IFT/covering chart with an exact
ambient-open target trace. -/
noncomputable def seamVertexAmbientChartData
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ)
    (hR : 0 ≤ R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (p : SuperellipsoidSeamVertex Phi frame c R d) :
    SeamVertexAmbientChartData Phi frame c R d hR hseam p := by
  have hpImage : (p : R3) ∈ transportedTorusPlaneMap Phi ''
      fundamentalSuperellipsoidSeam Phi frame c R d := by
    rw [image_fundamentalSuperellipsoidSeam Phi frame c hR d]
    exact p.2
  obtain ⟨uv, huvFund, huvEq⟩ := hpImage
  have huvFiber :
      uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)} := by
    change superellipsoidSeamMap Phi frame c uv = (R ^ 256, d)
    exact Prod.ext huvFund.1.2 huvFund.2
  exact
    { lift := uv
      lift_mem_fundamentalSeam := huvFund
      covering_lift_eq := huvEq
      lift_mem_seamFiber := huvFiber
      chartData :=
        superellipsoidSeamAmbientChartData Phi frame c R d hseam uv huvFiber }

/-- Equality of two ambient carriers can be checked after pulling them back to one local covering
sheet, provided both carriers lie on the transported torus. -/
theorem SuperellipsoidSeamAmbientChartData.inter_ambientNeighborhood_eq_of_preimage_eq
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d}
    {uv : Plane}
    {huv : uv ∈ (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)}}
    (D : SuperellipsoidSeamAmbientChartData Phi frame c R d hseam uv huv)
    {A B : Set R3}
    (hA : A ⊆ transportedTorus Phi) (hB : B ⊆ transportedTorus Phi)
    (hpull :
      {z | z ∈ D.coveringChart.source ∧
          (D.coveringChart z : R3) ∈ A} =
        {z | z ∈ D.coveringChart.source ∧
          (D.coveringChart z : R3) ∈ B}) :
    A ∩ D.ambientNeighborhood = B ∩ D.ambientNeighborhood := by
  ext x
  constructor
  · rintro ⟨hxA, hxU⟩
    let y : transportedTorus Phi := ⟨x, hA hxA⟩
    have hxTargetImage : x ∈
        (fun y : transportedTorus Phi ↦ (y : R3)) '' D.coveringChart.target := by
      rw [D.target_image_eq]
      exact ⟨hxU, hA hxA⟩
    obtain ⟨y', hy'Target, hy'x⟩ := hxTargetImage
    have hy'y : y' = y := Subtype.ext hy'x
    subst y'
    let z := D.coveringChart.symm y
    have hzSource : z ∈ D.coveringChart.source := D.coveringChart.map_target hy'Target
    have hzy : D.coveringChart z = y := D.coveringChart.right_inv hy'Target
    have hzA : z ∈ {z | z ∈ D.coveringChart.source ∧
        (D.coveringChart z : R3) ∈ A} := by
      refine ⟨hzSource, ?_⟩
      rw [hzy]
      exact hxA
    rw [hpull] at hzA
    refine ⟨?_, hxU⟩
    simpa only [hzy, y] using hzA.2
  · rintro ⟨hxB, hxU⟩
    let y : transportedTorus Phi := ⟨x, hB hxB⟩
    have hxTargetImage : x ∈
        (fun y : transportedTorus Phi ↦ (y : R3)) '' D.coveringChart.target := by
      rw [D.target_image_eq]
      exact ⟨hxU, hB hxB⟩
    obtain ⟨y', hy'Target, hy'x⟩ := hxTargetImage
    have hy'y : y' = y := Subtype.ext hy'x
    subst y'
    let z := D.coveringChart.symm y
    have hzSource : z ∈ D.coveringChart.source := D.coveringChart.map_target hy'Target
    have hzy : D.coveringChart z = y := D.coveringChart.right_inv hy'Target
    have hzB : z ∈ {z | z ∈ D.coveringChart.source ∧
        (D.coveringChart z : R3) ∈ B} := by
      refine ⟨hzSource, ?_⟩
      rw [hzy]
      exact hxB
    rw [← hpull] at hzB
    refine ⟨?_, hxU⟩
    simpa only [hzy, y] using hzB.2
-/

/-- The local two-branch equality isolated from cycle concatenation and finite separation. -/
structure CanonicalSeamBranchCompatibilityData where
  lower_branch : ∀ p : SuperellipsoidSeamVertex Phi frame c R d,
    ∃ U : Set R3, IsOpen U ∧ (p : R3) ∈ U ∧
      (Set.range ((lowerOuterEndpointPaths outerOrder).path
          ((outerOrder.globalLowerEndpointEquiv.symm p).1)) ∪
        Set.range ((inwardCutEndpointPaths cutOrder).path
          ((cutOrder.globalEndpointEquiv.symm p).1))) ∩ U =
        ((Set.range (G.outer.circle
              (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
            lowerClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U
  upper_branch : ∀ p : SuperellipsoidSeamVertex Phi frame c R d,
    ∃ U : Set R3, IsOpen U ∧ (p : R3) ∈ U ∧
      (Set.range ((upperOuterEndpointPaths outerOrder).path
          ((outerOrder.globalUpperEndpointEquiv.symm p).1)) ∪
        Set.range ((inwardCutEndpointPaths cutOrder).path
          ((cutOrder.globalEndpointEquiv.symm p).1))) ∩ U =
        ((Set.range (G.outer.circle
              (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
            upperClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ U

/- The source-preimage alternative is superseded by direct closed coverage.

/-- The strongest plane-sheet form of the remaining selected-branch compatibility.

The ambient-open target is already constructed by `seamVertexAmbientChartData`.  Thus these two
equalities only assert that, on that one injective covering sheet, the canonical endpoint-selected
outer and cut arcs are exactly the appropriate two closed signed branches.  The local IFT equation
`superellipsoidSeamLocalHomeomorph_mem_barrier_iff` and the closed-half coverage theorems are the
intended inputs for these equalities. -/
structure CanonicalSeamLiftBranchCompatibilityData
    (hR : 0 ≤ R)
    (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) where
  lower_source_preimage : ∀ p : SuperellipsoidSeamVertex Phi frame c R d,
    let D := seamVertexAmbientChartData Phi frame c R d hR hseam p
    {z | z ∈ D.chartData.coveringChart.source ∧
        (D.chartData.coveringChart z : R3) ∈
          FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := lowerSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := lowerOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p} =
      {z | z ∈ D.chartData.coveringChart.source ∧
        (D.chartData.coveringChart z : R3) ∈
          ((Set.range (G.outer.circle
                (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
              lowerClosedHalfspace frame d) ∪
            (Set.range (G.cut.circle
                (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
              closedSuperellipsoidBody frame c R))}
  upper_source_preimage : ∀ p : SuperellipsoidSeamVertex Phi frame c R d,
    let D := seamVertexAmbientChartData Phi frame c R d hR hseam p
    {z | z ∈ D.chartData.coveringChart.source ∧
        (D.chartData.coveringChart z : R3) ∈
          FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := upperSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := upperOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p} =
      {z | z ∈ D.chartData.coveringChart.source ∧
        (D.chartData.coveringChart z : R3) ∈
          ((Set.range (G.outer.circle
                (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
              upperClosedHalfspace frame d) ∪
            (Set.range (G.cut.circle
                (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
              closedSuperellipsoidBody frame c R))}

/-- A source-preimage branch identification on the canonical sheet gives the ambient-open branch
compatibility required by the finite local-germ adapter. -/
noncomputable def CanonicalSeamLiftBranchCompatibilityData.toCanonicalSeamBranchCompatibilityData
    {hR : 0 ≤ R}
    {hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d}
    (L : CanonicalSeamLiftBranchCompatibilityData outerOrder cutOrder hR hseam) :
    CanonicalSeamBranchCompatibilityData outerOrder cutOrder where
  lower_branch := by
    intro p
    let D := seamVertexAmbientChartData Phi frame c R d hR hseam p
    let A := FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
      (A := lowerSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := lowerOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p
    let B :=
      (Set.range (G.outer.circle
          (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
        lowerClosedHalfspace frame d) ∪
      (Set.range (G.cut.circle
          (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
        closedSuperellipsoidBody frame c R)
    have hA : A ⊆ transportedTorus Phi := by
      rintro x (hx | hx)
      · obtain ⟨u, rfl⟩ := hx
        rw [lowerOuterEndpointPaths_path_apply]
        exact Subtype.property _
      · obtain ⟨u, rfl⟩ := hx
        rw [inwardCutEndpointPaths_path_apply]
        exact Subtype.property _
    have hB : B ⊆ transportedTorus Phi := by
      rintro x (hx | hx)
      · exact (G.outer.circle_mem_section _ hx.1).1
      · exact (G.cut.circle_mem_section _ hx.1).1
    have hpTarget : D.chartData.coveringChart D.lift ∈
        D.chartData.coveringChart.target :=
      D.chartData.coveringChart.map_source D.chartData.uv_mem_source
    have hpImage : (p : R3) ∈
        (fun y : transportedTorus Phi ↦ (y : R3)) ''
          D.chartData.coveringChart.target := by
      refine ⟨D.chartData.coveringChart D.lift, hpTarget, ?_⟩
      rw [D.chartData.coveringChart_eq]
      simp only [coe_planeToTransportedTorus]
      exact D.covering_lift_eq
    rw [D.chartData.target_image_eq] at hpImage
    refine ⟨D.chartData.ambientNeighborhood,
      D.chartData.ambientNeighborhood_open, hpImage.1, ?_⟩
    change A ∩ D.chartData.ambientNeighborhood =
      B ∩ D.chartData.ambientNeighborhood
    apply D.chartData.inter_ambientNeighborhood_eq_of_preimage_eq hA hB
    exact L.lower_source_preimage p
  upper_branch := by
    intro p
    let D := seamVertexAmbientChartData Phi frame c R d hR hseam p
    let A := FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
      (A := upperSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := upperOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p
    let B :=
      (Set.range (G.outer.circle
          (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
        upperClosedHalfspace frame d) ∪
      (Set.range (G.cut.circle
          (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
        closedSuperellipsoidBody frame c R)
    have hA : A ⊆ transportedTorus Phi := by
      rintro x (hx | hx)
      · obtain ⟨u, rfl⟩ := hx
        rw [upperOuterEndpointPaths_path_apply]
        exact Subtype.property _
      · obtain ⟨u, rfl⟩ := hx
        rw [inwardCutEndpointPaths_path_apply]
        exact Subtype.property _
    have hB : B ⊆ transportedTorus Phi := by
      rintro x (hx | hx)
      · exact (G.outer.circle_mem_section _ hx.1).1
      · exact (G.cut.circle_mem_section _ hx.1).1
    have hpTarget : D.chartData.coveringChart D.lift ∈
        D.chartData.coveringChart.target :=
      D.chartData.coveringChart.map_source D.chartData.uv_mem_source
    have hpImage : (p : R3) ∈
        (fun y : transportedTorus Phi ↦ (y : R3)) ''
          D.chartData.coveringChart.target := by
      refine ⟨D.chartData.coveringChart D.lift, hpTarget, ?_⟩
      rw [D.chartData.coveringChart_eq]
      simp only [coe_planeToTransportedTorus]
      exact D.covering_lift_eq
    rw [D.chartData.target_image_eq] at hpImage
    refine ⟨D.chartData.ambientNeighborhood,
      D.chartData.ambientNeighborhood_open, hpImage.1, ?_⟩
    change A ∩ D.chartData.ambientNeighborhood =
      B ∩ D.chartData.ambientNeighborhood
    apply D.chartData.inter_ambientNeighborhood_eq_of_preimage_eq hA hB
    exact L.upper_source_preimage p
-/
/-- The lower canonical system has the finite incident-arc isolation required by the local-germ
adapter. -/
noncomputable def lowerIncidentClosedArcIsolationData
    (p : SuperellipsoidSeamVertex Phi frame c R d) :
    FiniteAlternatingEndpointSystem.IncidentClosedArcIsolationData
      (A := lowerSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := lowerOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p :=
  (lowerClosedArcIncidenceData outerOrder cutOrder).incidentClosedArcIsolationData p

/-- The upper canonical system has the finite incident-arc isolation required by the local-germ
adapter. -/
noncomputable def upperIncidentClosedArcIsolationData
    (p : SuperellipsoidSeamVertex Phi frame c R d) :
    FiniteAlternatingEndpointSystem.IncidentClosedArcIsolationData
      (A := upperSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := upperOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p :=
  (upperClosedArcIncidenceData outerOrder cutOrder).incidentClosedArcIsolationData p

theorem lowerTotalClosedArcCarrier_eq_activeBranches
    (hR : 0 < R) :
    FiniteAlternatingEndpointSystem.totalClosedArcCarrier
        (A := lowerSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := lowerOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) =
      (((⋃ i : outerOrder.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
          lowerClosedHalfspace frame d) ∪
        ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
          closedSuperellipsoidBody frame c R)) := by
  change ((⋃ g, Set.range ((lowerOuterEndpointPaths outerOrder).path g)) ∪
    ⋃ g, Set.range ((inwardCutEndpointPaths cutOrder).path g)) = _
  congr 1
  · calc
      (⋃ g, Set.range ((lowerOuterEndpointPaths outerOrder).path g)) =
          ⋃ g, Set.range fun u ↦
            ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) := by
        apply iUnion_congr
        intro g
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, lowerOuterEndpointPaths_path_apply outerOrder g u⟩
        · rintro ⟨u, rfl⟩
          exact ⟨u, (lowerOuterEndpointPaths_path_apply outerOrder g u).symm⟩
      _ = _ := outerOrder.iUnion_range_globalLowerOuterPath_eq
  · calc
      (⋃ g, Set.range ((inwardCutEndpointPaths cutOrder).path g)) =
          ⋃ g, Set.range fun u ↦
            ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3) := by
        apply iUnion_congr
        intro g
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, inwardCutEndpointPaths_path_apply cutOrder g u⟩
        · rintro ⟨u, rfl⟩
          exact ⟨u, (inwardCutEndpointPaths_path_apply cutOrder g u).symm⟩
      _ = _ := cutOrder.iUnion_range_globalInwardExcursionPath_eq hR

theorem upperTotalClosedArcCarrier_eq_activeBranches
    (hR : 0 < R) :
    FiniteAlternatingEndpointSystem.totalClosedArcCarrier
        (A := upperSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := upperOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) =
      (((⋃ i : outerOrder.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
          upperClosedHalfspace frame d) ∪
        ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
          closedSuperellipsoidBody frame c R)) := by
  change ((⋃ g, Set.range ((upperOuterEndpointPaths outerOrder).path g)) ∪
    ⋃ g, Set.range ((inwardCutEndpointPaths cutOrder).path g)) = _
  congr 1
  · calc
      (⋃ g, Set.range ((upperOuterEndpointPaths outerOrder).path g)) =
          ⋃ g, Set.range fun u ↦
            ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) := by
        apply iUnion_congr
        intro g
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, upperOuterEndpointPaths_path_apply outerOrder g u⟩
        · rintro ⟨u, rfl⟩
          exact ⟨u, (upperOuterEndpointPaths_path_apply outerOrder g u).symm⟩
      _ = _ := outerOrder.iUnion_range_globalUpperOuterPath_eq
  · calc
      (⋃ g, Set.range ((inwardCutEndpointPaths cutOrder).path g)) =
          ⋃ g, Set.range fun u ↦
            ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3) := by
        apply iUnion_congr
        intro g
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, inwardCutEndpointPaths_path_apply cutOrder g u⟩
        · rintro ⟨u, rfl⟩
          exact ⟨u, (inwardCutEndpointPaths_path_apply cutOrder g u).symm⟩
      _ = _ := cutOrder.iUnion_range_globalInwardExcursionPath_eq hR

/-- Exact closed-half coverage discharges the ambient branch compatibility: finite isolation
removes all other closed gaps, while the selected two gaps lie on the prescribed outer and cut
circles. -/
theorem canonicalSeamBranchCompatibilityData_of_closedCoverage
    (hR : 0 < R) : CanonicalSeamBranchCompatibilityData outerOrder cutOrder where
  lower_branch := by
    intro p
    let I := lowerIncidentClosedArcIsolationData outerOrder cutOrder p
    let A := FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
      (A := lowerSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := lowerOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p
    let B :=
      (Set.range (G.outer.circle
          (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
        lowerClosedHalfspace frame d) ∪
      (Set.range (G.cut.circle
          (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
        closedSuperellipsoidBody frame c R)
    refine ⟨I.neighborhood, I.isOpen_neighborhood,
      I.point_mem_neighborhood, ?_⟩
    change A ∩ I.neighborhood = B ∩ I.neighborhood
    ext x
    constructor
    · rintro ⟨hx, hxI⟩
      refine ⟨?_, hxI⟩
      rcases hx with hx | hx
      · obtain ⟨u, rfl⟩ := hx
        apply Or.inl
        change ((lowerOuterEndpointPaths outerOrder).path
          (outerOrder.globalLowerEndpointEquiv.symm p).1 u) ∈ _
        rw [lowerOuterEndpointPaths_path_apply]
        exact ⟨outerOrder.gapPath_mem_outerCircle
          (outerOrder.lowerGapAsGlobalOuterGap
            (outerOrder.globalLowerEndpointEquiv.symm p).1) u,
          outerOrder.lowerGapPath_mem
            (outerOrder.lowerGapAsLowerGap
              (outerOrder.globalLowerEndpointEquiv.symm p).1) u⟩
      · obtain ⟨u, rfl⟩ := hx
        apply Or.inr
        change ((inwardCutEndpointPaths cutOrder).path
          (cutOrder.globalEndpointEquiv.symm p).1 u) ∈ _
        rw [inwardCutEndpointPaths_path_apply]
        refine ⟨cutOrder.globalInwardExcursionPath_mem_cutCircle _ u, ?_⟩
        have hAll : ((cutOrder.globalInwardExcursionPath
            (cutOrder.globalEndpointEquiv.symm p).1 u : transportedTorus Phi) : R3) ∈
            (⋃ g : cutOrder.GlobalInwardGap, Set.range fun v ↦
              ((cutOrder.globalInwardExcursionPath g v : transportedTorus Phi) : R3)) :=
          Set.mem_iUnion.mpr ⟨_, u, rfl⟩
        rw [cutOrder.iUnion_range_globalInwardExcursionPath_eq hR] at hAll
        exact hAll.2
    · rintro ⟨hx, hxI⟩
      have hxGlobal : x ∈
          (((⋃ i : outerOrder.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
              lowerClosedHalfspace frame d) ∪
            ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
              closedSuperellipsoidBody frame c R)) := by
        rcases hx with hx | hx
        · exact Or.inl ⟨Set.mem_iUnion.mpr
            ⟨(outerOrder.globalLowerEndpointEquiv.symm p).1.1, hx.1⟩, hx.2⟩
        · exact Or.inr ⟨Set.mem_iUnion.mpr
            ⟨(cutOrder.globalEndpointEquiv.symm p).1.1, hx.1⟩, hx.2⟩
      rw [← lowerTotalClosedArcCarrier_eq_activeBranches outerOrder cutOrder hR]
        at hxGlobal
      have hxLocal := (show x ∈
          FiniteAlternatingEndpointSystem.totalClosedArcCarrier
              (A := lowerSystem outerOrder cutOrder)
              (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
              (firstPaths := lowerOuterEndpointPaths outerOrder)
              (secondPaths := inwardCutEndpointPaths cutOrder) ∩ I.neighborhood from
        ⟨hxGlobal, hxI⟩)
      rw [I.total_local_eq_incident] at hxLocal
      exact hxLocal
  upper_branch := by
    intro p
    let I := upperIncidentClosedArcIsolationData outerOrder cutOrder p
    let A := FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
      (A := upperSystem outerOrder cutOrder)
      (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
      (firstPaths := upperOuterEndpointPaths outerOrder)
      (secondPaths := inwardCutEndpointPaths cutOrder) p
    let B :=
      (Set.range (G.outer.circle
          (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
        upperClosedHalfspace frame d) ∪
      (Set.range (G.cut.circle
          (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
        closedSuperellipsoidBody frame c R)
    refine ⟨I.neighborhood, I.isOpen_neighborhood,
      I.point_mem_neighborhood, ?_⟩
    change A ∩ I.neighborhood = B ∩ I.neighborhood
    ext x
    constructor
    · rintro ⟨hx, hxI⟩
      refine ⟨?_, hxI⟩
      rcases hx with hx | hx
      · obtain ⟨u, rfl⟩ := hx
        apply Or.inl
        change ((upperOuterEndpointPaths outerOrder).path
          (outerOrder.globalUpperEndpointEquiv.symm p).1 u) ∈ _
        rw [upperOuterEndpointPaths_path_apply]
        exact ⟨outerOrder.gapPath_mem_outerCircle
          (outerOrder.upperGapAsGlobalOuterGap
            (outerOrder.globalUpperEndpointEquiv.symm p).1) u,
          outerOrder.upperGapPath_mem
            (outerOrder.upperGapAsUpperGap
              (outerOrder.globalUpperEndpointEquiv.symm p).1) u⟩
      · obtain ⟨u, rfl⟩ := hx
        apply Or.inr
        change ((inwardCutEndpointPaths cutOrder).path
          (cutOrder.globalEndpointEquiv.symm p).1 u) ∈ _
        rw [inwardCutEndpointPaths_path_apply]
        refine ⟨cutOrder.globalInwardExcursionPath_mem_cutCircle _ u, ?_⟩
        have hAll : ((cutOrder.globalInwardExcursionPath
            (cutOrder.globalEndpointEquiv.symm p).1 u : transportedTorus Phi) : R3) ∈
            (⋃ g : cutOrder.GlobalInwardGap, Set.range fun v ↦
              ((cutOrder.globalInwardExcursionPath g v : transportedTorus Phi) : R3)) :=
          Set.mem_iUnion.mpr ⟨_, u, rfl⟩
        rw [cutOrder.iUnion_range_globalInwardExcursionPath_eq hR] at hAll
        exact hAll.2
    · rintro ⟨hx, hxI⟩
      have hxGlobal : x ∈
          (((⋃ i : outerOrder.ActiveOuterCircle, Set.range (G.outer.circle i.1).circle) ∩
              upperClosedHalfspace frame d) ∪
            ((⋃ j : G.ActiveCutCircle, Set.range (G.cut.circle j.1).circle) ∩
              closedSuperellipsoidBody frame c R)) := by
        rcases hx with hx | hx
        · exact Or.inl ⟨Set.mem_iUnion.mpr
            ⟨(outerOrder.globalUpperEndpointEquiv.symm p).1.1, hx.1⟩, hx.2⟩
        · exact Or.inr ⟨Set.mem_iUnion.mpr
            ⟨(cutOrder.globalEndpointEquiv.symm p).1.1, hx.1⟩, hx.2⟩
      rw [← upperTotalClosedArcCarrier_eq_activeBranches outerOrder cutOrder hR]
        at hxGlobal
      have hxLocal := (show x ∈
          FiniteAlternatingEndpointSystem.totalClosedArcCarrier
              (A := upperSystem outerOrder cutOrder)
              (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
              (firstPaths := upperOuterEndpointPaths outerOrder)
              (secondPaths := inwardCutEndpointPaths cutOrder) ∩ I.neighborhood from
        ⟨hxGlobal, hxI⟩)
      rw [I.total_local_eq_incident] at hxLocal
      exact hxLocal

private theorem lower_incident_subset_cycleCarrier
    (p : SuperellipsoidSeamVertex Phi frame c R d) :
    FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
        (A := lowerSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := lowerOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) p ⊆
      lowerCycleCarrier outerOrder cutOrder
        ((lowerSystem outerOrder cutOrder).cycleOfVertex p) := by
  rintro x (hx | hx)
  · obtain ⟨u, rfl⟩ := hx
    rw [lowerCycleCarrier]
    apply Or.inl
    refine Set.mem_iUnion.mpr
      ⟨(outerOrder.globalLowerEndpointEquiv.symm p).1, ?_⟩
    rw [if_pos]
    · exact ⟨u, (lowerOuterEndpointPaths_path_apply outerOrder _ u).symm⟩
    · exact FiniteAlternatingEndpointSystem.cycleOf_first_edgeOf_zero_eq
        (lowerSystem outerOrder cutOrder) p
  · obtain ⟨u, rfl⟩ := hx
    rw [lowerCycleCarrier]
    apply Or.inr
    refine Set.mem_iUnion.mpr
      ⟨(cutOrder.globalEndpointEquiv.symm p).1, ?_⟩
    rw [if_pos]
    · exact ⟨u, (inwardCutEndpointPaths_path_apply cutOrder _ u).symm⟩
    · exact FiniteAlternatingEndpointSystem.cycleOf_second_edgeOf_zero_eq
        (lowerSystem outerOrder cutOrder) p

private theorem upper_incident_subset_cycleCarrier
    (p : SuperellipsoidSeamVertex Phi frame c R d) :
    FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
        (A := upperSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := upperOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) p ⊆
      upperCycleCarrier outerOrder cutOrder
        ((upperSystem outerOrder cutOrder).cycleOfVertex p) := by
  rintro x (hx | hx)
  · obtain ⟨u, rfl⟩ := hx
    rw [upperCycleCarrier]
    apply Or.inl
    refine Set.mem_iUnion.mpr
      ⟨(outerOrder.globalUpperEndpointEquiv.symm p).1, ?_⟩
    rw [if_pos]
    · exact ⟨u, (upperOuterEndpointPaths_path_apply outerOrder _ u).symm⟩
    · exact FiniteAlternatingEndpointSystem.cycleOf_first_edgeOf_zero_eq
        (upperSystem outerOrder cutOrder) p
  · obtain ⟨u, rfl⟩ := hx
    rw [upperCycleCarrier]
    apply Or.inr
    refine Set.mem_iUnion.mpr
      ⟨(cutOrder.globalEndpointEquiv.symm p).1, ?_⟩
    rw [if_pos]
    · exact ⟨u, (inwardCutEndpointPaths_path_apply cutOrder _ u).symm⟩
    · exact FiniteAlternatingEndpointSystem.cycleOf_second_edgeOf_zero_eq
        (upperSystem outerOrder cutOrder) p

theorem lowerCycleCarrier_subset_totalClosedArcCarrier
    (q : LowerCycleIndex outerOrder cutOrder) :
    lowerCycleCarrier outerOrder cutOrder q ⊆
      FiniteAlternatingEndpointSystem.totalClosedArcCarrier
        (A := lowerSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := lowerOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) := by
  intro x hx
  rw [lowerCycleCarrier] at hx
  rcases hx with hx | hx
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    split at hg
    · obtain ⟨u, rfl⟩ := hg
      apply Or.inl
      refine Set.mem_iUnion.mpr ⟨g, u, ?_⟩
      exact lowerOuterEndpointPaths_path_apply outerOrder g u
    · exact hg.elim
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    split at hg
    · obtain ⟨u, rfl⟩ := hg
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨g, u, ?_⟩
      exact inwardCutEndpointPaths_path_apply cutOrder g u
    · exact hg.elim

theorem upperCycleCarrier_subset_totalClosedArcCarrier
    (q : UpperCycleIndex outerOrder cutOrder) :
    upperCycleCarrier outerOrder cutOrder q ⊆
      FiniteAlternatingEndpointSystem.totalClosedArcCarrier
        (A := upperSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := upperOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) := by
  intro x hx
  rw [upperCycleCarrier] at hx
  rcases hx with hx | hx
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    split at hg
    · obtain ⟨u, rfl⟩ := hg
      apply Or.inl
      refine Set.mem_iUnion.mpr ⟨g, u, ?_⟩
      exact upperOuterEndpointPaths_path_apply outerOrder g u
    · exact hg.elim
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    split at hg
    · obtain ⟨u, rfl⟩ := hg
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨g, u, ?_⟩
      exact inwardCutEndpointPaths_path_apply cutOrder g u
    · exact hg.elim

/-- Finite closed-arc separation turns the canonical two-branch compatibility statement into the
exact local-germ datum required by the active-cycle realization constructor. -/
theorem CanonicalSeamBranchCompatibilityData.toActiveCycleLocalGermData
    (C : ActiveCycleConcatenationData outerOrder cutOrder)
    (B : CanonicalSeamBranchCompatibilityData outerOrder cutOrder) :
    ActiveCycleLocalGermData outerOrder cutOrder where
  lower_local_v := by
    intro x hx
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hx⟩
    let q := (lowerSystem outerOrder cutOrder).cycleOfVertex p
    let I := lowerIncidentClosedArcIsolationData outerOrder cutOrder p
    obtain ⟨V, hVopen, hpV, hbranch⟩ := B.lower_branch p
    have hpCarrier : (p : R3) ∈ lowerCycleCarrier outerOrder cutOrder q :=
      lower_incident_subset_cycleCarrier outerOrder cutOrder p I.point_mem_incident
    have hpRange : (p : R3) ∈
        Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) := by
      rw [C.lower_range q]
      exact hpCarrier
    obtain ⟨z, hz⟩ := hpRange
    have hlocal :
        Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) ∩ I.neighborhood =
          FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
              (A := lowerSystem outerOrder cutOrder)
              (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
              (firstPaths := lowerOuterEndpointPaths outerOrder)
              (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ I.neighborhood := by
      ext x
      constructor
      · rintro ⟨hx, hxI⟩
        have hxCarrier : x ∈ lowerCycleCarrier outerOrder cutOrder q := by
          rw [← C.lower_range q]
          exact hx
        have hxTotal := lowerCycleCarrier_subset_totalClosedArcCarrier
          outerOrder cutOrder q hxCarrier
        have hxLocal : x ∈
            FiniteAlternatingEndpointSystem.totalClosedArcCarrier
                (A := lowerSystem outerOrder cutOrder)
                (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
                (firstPaths := lowerOuterEndpointPaths outerOrder)
                (secondPaths := inwardCutEndpointPaths cutOrder) ∩ I.neighborhood :=
          ⟨hxTotal, hxI⟩
        rw [I.total_local_eq_incident] at hxLocal
        exact hxLocal
      · rintro ⟨hx, hxI⟩
        refine ⟨?_, hxI⟩
        rw [C.lower_range q]
        exact lower_incident_subset_cycleCarrier outerOrder cutOrder p hx
    change FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
        (A := lowerSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := lowerOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ V = _ at hbranch
    refine ⟨q, z,
      (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1,
      (cutOrder.globalEndpointEquiv.symm p).1.1.1,
      I.neighborhood ∩ V, I.isOpen_neighborhood.inter hVopen,
      ⟨I.point_mem_neighborhood, hpV⟩, hz, ?_⟩
    calc
      Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) ∩
          (I.neighborhood ∩ V) =
          (Set.range ((lowerOrientedArcs outerOrder cutOrder).circleMap q) ∩
            I.neighborhood) ∩ V := by ac_rfl
      _ = (FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := lowerSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := lowerOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ I.neighborhood) ∩ V := by
          rw [hlocal]
      _ = (FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := lowerSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := lowerOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ V) ∩ I.neighborhood := by
          ac_rfl
      _ = (((Set.range (G.outer.circle
              (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
            lowerClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ V) ∩ I.neighborhood := by
          rw [hbranch]
      _ = ((Set.range (G.outer.circle
              (outerOrder.globalLowerEndpointEquiv.symm p).1.1.1).circle ∩
            lowerClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ (I.neighborhood ∩ V) := by
          ac_rfl
  upper_local_v := by
    intro x hx
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨x, hx⟩
    let q := (upperSystem outerOrder cutOrder).cycleOfVertex p
    let I := upperIncidentClosedArcIsolationData outerOrder cutOrder p
    obtain ⟨V, hVopen, hpV, hbranch⟩ := B.upper_branch p
    have hpCarrier : (p : R3) ∈ upperCycleCarrier outerOrder cutOrder q :=
      upper_incident_subset_cycleCarrier outerOrder cutOrder p I.point_mem_incident
    have hpRange : (p : R3) ∈
        Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) := by
      rw [C.upper_range q]
      exact hpCarrier
    obtain ⟨z, hz⟩ := hpRange
    have hlocal :
        Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) ∩ I.neighborhood =
          FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
              (A := upperSystem outerOrder cutOrder)
              (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
              (firstPaths := upperOuterEndpointPaths outerOrder)
              (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ I.neighborhood := by
      ext x
      constructor
      · rintro ⟨hx, hxI⟩
        have hxCarrier : x ∈ upperCycleCarrier outerOrder cutOrder q := by
          rw [← C.upper_range q]
          exact hx
        have hxTotal := upperCycleCarrier_subset_totalClosedArcCarrier
          outerOrder cutOrder q hxCarrier
        have hxLocal : x ∈
            FiniteAlternatingEndpointSystem.totalClosedArcCarrier
                (A := upperSystem outerOrder cutOrder)
                (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
                (firstPaths := upperOuterEndpointPaths outerOrder)
                (secondPaths := inwardCutEndpointPaths cutOrder) ∩ I.neighborhood :=
          ⟨hxTotal, hxI⟩
        rw [I.total_local_eq_incident] at hxLocal
        exact hxLocal
      · rintro ⟨hx, hxI⟩
        refine ⟨?_, hxI⟩
        rw [C.upper_range q]
        exact upper_incident_subset_cycleCarrier outerOrder cutOrder p hx
    change FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
        (A := upperSystem outerOrder cutOrder)
        (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
        (firstPaths := upperOuterEndpointPaths outerOrder)
        (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ V = _ at hbranch
    refine ⟨q, z,
      (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1,
      (cutOrder.globalEndpointEquiv.symm p).1.1.1,
      I.neighborhood ∩ V, I.isOpen_neighborhood.inter hVopen,
      ⟨I.point_mem_neighborhood, hpV⟩, hz, ?_⟩
    calc
      Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) ∩
          (I.neighborhood ∩ V) =
          (Set.range ((upperOrientedArcs outerOrder cutOrder).circleMap q) ∩
            I.neighborhood) ∩ V := by ac_rfl
      _ = (FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := upperSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := upperOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ I.neighborhood) ∩ V := by
          rw [hlocal]
      _ = (FiniteAlternatingEndpointSystem.incidentClosedArcCarrier
            (A := upperSystem outerOrder cutOrder)
            (point := fun v : SuperellipsoidSeamVertex Phi frame c R d ↦ (v : R3))
            (firstPaths := upperOuterEndpointPaths outerOrder)
            (secondPaths := inwardCutEndpointPaths cutOrder) p ∩ V) ∩ I.neighborhood := by
          ac_rfl
      _ = (((Set.range (G.outer.circle
              (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
            upperClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ V) ∩ I.neighborhood := by
          rw [hbranch]
      _ = ((Set.range (G.outer.circle
              (outerOrder.globalUpperEndpointEquiv.symm p).1.1.1).circle ∩
            upperClosedHalfspace frame d) ∪
          (Set.range (G.cut.circle
              (cutOrder.globalEndpointEquiv.symm p).1.1.1).circle ∩
            closedSuperellipsoidBody frame c R)) ∩ (I.neighborhood ∩ V) := by
          ac_rfl

/-- The canonical finite concatenations have the required ambient seam germ with no additional
geometric premise once exact closed outer- and inward-gap coverage is available. -/
theorem ActiveCycleConcatenationData.toActiveCycleLocalGermData_of_closedCoverage
    (C : ActiveCycleConcatenationData outerOrder cutOrder) (hR : 0 < R) :
    ActiveCycleLocalGermData outerOrder cutOrder :=
  CanonicalSeamBranchCompatibilityData.toActiveCycleLocalGermData outerOrder cutOrder C
    (canonicalSeamBranchCompatibilityData_of_closedCoverage outerOrder cutOrder hR)

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
