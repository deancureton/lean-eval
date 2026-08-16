import Submission.Topology.SuperellipsoidBarrierGraph

/-!
# The local band move at a paired pair of seam vertices

A single transverse `T`-vertex has three ends and cannot be replaced, relative to the boundary of
a small neighborhood, by a compact one-manifold.  The honest local unit is a cutting-plane arc
joining two seam vertices.  A band around that whole arc has four boundary ports, and there are
two planar noncrossing pairings of those ports.

This file constructs those two pairings explicitly in a standard band and transports them by an
embedded chart.  The resulting patches are disjoint pairs of paths, are supported in the chosen
band, agree exactly with the old carrier off that band, and lie in the recorded moving-sphere
event region.  No circle family or moving-sphere embedding is postulated as a conclusion field.
The remaining global step is to glue these paths to the four outside arcs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## The standard four-port band -/

def bandLeftBottom : Plane := (-1, -1)
def bandLeftTop : Plane := (-1, 1)
def bandRightBottom : Plane := (1, -1)
def bandRightTop : Plane := (1, 1)
def bandLeftVertex : Plane := (-1, 0)
def bandRightVertex : Plane := (1, 0)

def bandLeftPath : Path bandLeftBottom bandLeftTop :=
  Path.segment bandLeftBottom bandLeftTop

def bandRightPath : Path bandRightBottom bandRightTop :=
  Path.segment bandRightBottom bandRightTop

def bandBottomPath : Path bandLeftBottom bandRightBottom :=
  Path.segment bandLeftBottom bandRightBottom

def bandTopPath : Path bandLeftTop bandRightTop :=
  Path.segment bandLeftTop bandRightTop

def bandSeamPath : Path bandLeftVertex bandRightVertex :=
  Path.segment bandLeftVertex bandRightVertex

theorem bandLeftPath_injective : Function.Injective bandLeftPath :=
  Path.segment_injective_of_ne (by
    intro h
    have hsnd := congrArg Prod.snd h
    norm_num [bandLeftBottom, bandLeftTop] at hsnd)

theorem bandRightPath_injective : Function.Injective bandRightPath :=
  Path.segment_injective_of_ne (by
    intro h
    have hsnd := congrArg Prod.snd h
    norm_num [bandRightBottom, bandRightTop] at hsnd)

theorem bandBottomPath_injective : Function.Injective bandBottomPath :=
  Path.segment_injective_of_ne (by
    intro h
    have hfst := congrArg Prod.fst h
    norm_num [bandLeftBottom, bandRightBottom] at hfst)

theorem bandTopPath_injective : Function.Injective bandTopPath :=
  Path.segment_injective_of_ne (by
    intro h
    have hfst := congrArg Prod.fst h
    norm_num [bandLeftTop, bandRightTop] at hfst)

theorem bandSeamPath_injective : Function.Injective bandSeamPath :=
  Path.segment_injective_of_ne (by
    intro h
    have hfst := congrArg Prod.fst h
    norm_num [bandLeftVertex, bandRightVertex] at hfst)

theorem bandLeftPath_fst (t : unitInterval) : (bandLeftPath t).1 = -1 := by
  rw [bandLeftPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (t : ℝ)) * (-1) + (t : ℝ) * (-1) = -1
  ring

theorem bandRightPath_fst (t : unitInterval) : (bandRightPath t).1 = 1 := by
  rw [bandRightPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 = 1
  ring

theorem bandBottomPath_snd (t : unitInterval) : (bandBottomPath t).2 = -1 := by
  rw [bandBottomPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (t : ℝ)) * (-1) + (t : ℝ) * (-1) = -1
  ring

theorem bandTopPath_snd (t : unitInterval) : (bandTopPath t).2 = 1 := by
  rw [bandTopPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 = 1
  ring

/-- A chart containing one complete paired seam arc.  The whole planar chart is allowed to be
compressed into a small ambient neighborhood; only its four standard segments are used below. -/
structure PairedSeamBandChart where
  chart : Plane → R3
  chartEmbedding : IsEmbedding chart
  support : Set R3
  chart_mem_support : Set.range chart ⊆ support
  eventRegion : Set R3
  chart_mem_eventRegion : Set.range chart ⊆ eventRegion

/-- Forget the transported-torus subtype in an embedded planar surface patch.  This is the direct
adapter from a transported-torus chart (after its planar domain has been standardized by a
Schoenflies homeomorphism) to the ambient four-port construction. -/
def PairedSeamBandChart.ofTransportedTorusEmbedding
    {Phi : AmbientIsotopy}
    (surfaceMap : Plane → transportedTorus Phi)
    (surfaceEmbedding : IsEmbedding surfaceMap)
    (support eventRegion : Set R3)
    (hSupport : Set.range (fun uv ↦ ((surfaceMap uv : transportedTorus Phi) : R3)) ⊆
      support)
    (hEvent : Set.range (fun uv ↦ ((surfaceMap uv : transportedTorus Phi) : R3)) ⊆
      eventRegion) : PairedSeamBandChart where
  chart := fun uv ↦ surfaceMap uv
  chartEmbedding := IsEmbedding.subtypeVal.comp surfaceEmbedding
  support := support
  chart_mem_support := hSupport
  eventRegion := eventRegion
  chart_mem_eventRegion := hEvent

/-- Homeomorphic planar torus patches are the form produced by `transportedTorusBallHomeomorph`
after choosing a smaller planar ball and standardizing it by `Schoenflies.planeHomeomorphBall`. -/
def PairedSeamBandChart.ofTransportedTorusHomeomorph
    {Phi : AmbientIsotopy} {surfacePatch : Set (transportedTorus Phi)}
    (e : Plane ≃ₜ surfacePatch)
    (support eventRegion : Set R3)
    (hSupport : Set.range
      (fun uv ↦ (((e uv : surfacePatch) : transportedTorus Phi) : R3)) ⊆ support)
    (hEvent : Set.range
      (fun uv ↦ (((e uv : surfacePatch) : transportedTorus Phi) : R3)) ⊆ eventRegion) :
    PairedSeamBandChart :=
  PairedSeamBandChart.ofTransportedTorusEmbedding
    (fun uv ↦ (e uv : transportedTorus Phi))
    (IsEmbedding.subtypeVal.comp e.isEmbedding) support eventRegion hSupport hEvent

namespace PairedSeamBandChart

variable (B : PairedSeamBandChart)

def leftBottom : R3 := B.chart bandLeftBottom
def leftTop : R3 := B.chart bandLeftTop
def rightBottom : R3 := B.chart bandRightBottom
def rightTop : R3 := B.chart bandRightTop
def leftVertex : R3 := B.chart bandLeftVertex
def rightVertex : R3 := B.chart bandRightVertex

def leftPath : Path B.leftBottom B.leftTop :=
  bandLeftPath.map B.chartEmbedding.continuous

def rightPath : Path B.rightBottom B.rightTop :=
  bandRightPath.map B.chartEmbedding.continuous

def bottomPath : Path B.leftBottom B.rightBottom :=
  bandBottomPath.map B.chartEmbedding.continuous

def topPath : Path B.leftTop B.rightTop :=
  bandTopPath.map B.chartEmbedding.continuous

def seamPath : Path B.leftVertex B.rightVertex :=
  bandSeamPath.map B.chartEmbedding.continuous

theorem leftPath_injective : Function.Injective B.leftPath :=
  B.chartEmbedding.injective.comp bandLeftPath_injective

theorem rightPath_injective : Function.Injective B.rightPath :=
  B.chartEmbedding.injective.comp bandRightPath_injective

theorem bottomPath_injective : Function.Injective B.bottomPath :=
  B.chartEmbedding.injective.comp bandBottomPath_injective

theorem topPath_injective : Function.Injective B.topPath :=
  B.chartEmbedding.injective.comp bandTopPath_injective

theorem seamPath_injective : Function.Injective B.seamPath :=
  B.chartEmbedding.injective.comp bandSeamPath_injective

/-- The two paths in the parallel smoothing are disjoint. -/
theorem leftPath_disjoint_rightPath :
    Disjoint (Set.range B.leftPath) (Set.range B.rightPath) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  have hchart : B.chart (bandLeftPath s) = B.chart (bandRightPath t) := by
    exact hs.trans ht.symm
  have hplane := B.chartEmbedding.injective hchart
  have hfst := congrArg Prod.fst hplane
  rw [bandLeftPath_fst, bandRightPath_fst] at hfst
  norm_num at hfst

/-- The two paths in the surgery smoothing are disjoint. -/
theorem bottomPath_disjoint_topPath :
    Disjoint (Set.range B.bottomPath) (Set.range B.topPath) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  have hchart : B.chart (bandBottomPath s) = B.chart (bandTopPath t) := by
    exact hs.trans ht.symm
  have hplane := B.chartEmbedding.injective hchart
  have hsnd := congrArg Prod.snd hplane
  rw [bandBottomPath_snd, bandTopPath_snd] at hsnd
  norm_num at hsnd

private theorem path_range_subset_chart_range
    {x y : Plane} (p : Path x y) (h : Continuous B.chart) :
    Set.range (p.map h) ⊆ Set.range B.chart := by
  rintro _ ⟨t, rfl⟩
  exact ⟨p t, rfl⟩

theorem leftPath_range_subset_support : Set.range B.leftPath ⊆ B.support :=
  (B.path_range_subset_chart_range bandLeftPath B.chartEmbedding.continuous).trans
    B.chart_mem_support

theorem rightPath_range_subset_support : Set.range B.rightPath ⊆ B.support :=
  (B.path_range_subset_chart_range bandRightPath B.chartEmbedding.continuous).trans
    B.chart_mem_support

theorem bottomPath_range_subset_support : Set.range B.bottomPath ⊆ B.support :=
  (B.path_range_subset_chart_range bandBottomPath B.chartEmbedding.continuous).trans
    B.chart_mem_support

theorem topPath_range_subset_support : Set.range B.topPath ⊆ B.support :=
  (B.path_range_subset_chart_range bandTopPath B.chartEmbedding.continuous).trans
    B.chart_mem_support

theorem seamPath_range_subset_support : Set.range B.seamPath ⊆ B.support :=
  (B.path_range_subset_chart_range bandSeamPath B.chartEmbedding.continuous).trans
    B.chart_mem_support

theorem leftPath_range_subset_eventRegion : Set.range B.leftPath ⊆ B.eventRegion :=
  (B.path_range_subset_chart_range bandLeftPath B.chartEmbedding.continuous).trans
    B.chart_mem_eventRegion

theorem rightPath_range_subset_eventRegion : Set.range B.rightPath ⊆ B.eventRegion :=
  (B.path_range_subset_chart_range bandRightPath B.chartEmbedding.continuous).trans
    B.chart_mem_eventRegion

theorem bottomPath_range_subset_eventRegion : Set.range B.bottomPath ⊆ B.eventRegion :=
  (B.path_range_subset_chart_range bandBottomPath B.chartEmbedding.continuous).trans
    B.chart_mem_eventRegion

theorem topPath_range_subset_eventRegion : Set.range B.topPath ⊆ B.eventRegion :=
  (B.path_range_subset_chart_range bandTopPath B.chartEmbedding.continuous).trans
    B.chart_mem_eventRegion

theorem seamPath_range_subset_eventRegion : Set.range B.seamPath ⊆ B.eventRegion :=
  (B.path_range_subset_chart_range bandSeamPath B.chartEmbedding.continuous).trans
    B.chart_mem_eventRegion

/-- The singular paired `T`-graph in the band: two vertical branches joined by the seam arc. -/
def singularPatch : Set R3 :=
  Set.range B.leftPath ∪ Set.range B.rightPath ∪ Set.range B.seamPath

theorem singularPatch_subset_support : B.singularPatch ⊆ B.support :=
  union_subset
    (union_subset B.leftPath_range_subset_support B.rightPath_range_subset_support)
    B.seamPath_range_subset_support

theorem singularPatch_subset_eventRegion : B.singularPatch ⊆ B.eventRegion :=
  union_subset
    (union_subset B.leftPath_range_subset_eventRegion
      B.rightPath_range_subset_eventRegion)
    B.seamPath_range_subset_eventRegion

/-- The pairing which reconnects the two branches separately at the two seam vertices. -/
def parallelPatch : Set R3 :=
  Set.range B.leftPath ∪ Set.range B.rightPath

/-- The band-surgery pairing, joining the upper ports and the lower ports across the band. -/
def surgeryPatch : Set R3 :=
  Set.range B.bottomPath ∪ Set.range B.topPath

theorem parallelPatch_subset_support : B.parallelPatch ⊆ B.support :=
  union_subset B.leftPath_range_subset_support B.rightPath_range_subset_support

theorem surgeryPatch_subset_support : B.surgeryPatch ⊆ B.support :=
  union_subset B.bottomPath_range_subset_support B.topPath_range_subset_support

theorem parallelPatch_subset_eventRegion : B.parallelPatch ⊆ B.eventRegion :=
  union_subset B.leftPath_range_subset_eventRegion B.rightPath_range_subset_eventRegion

theorem surgeryPatch_subset_eventRegion : B.surgeryPatch ⊆ B.eventRegion :=
  union_subset B.bottomPath_range_subset_eventRegion B.topPath_range_subset_eventRegion

/-- Choose either of the two noncrossing four-port smoothings. -/
def smoothingPatch : Bool → Set R3
  | false => B.parallelPatch
  | true => B.surgeryPatch

theorem smoothingPatch_subset_support (side : Bool) :
    B.smoothingPatch side ⊆ B.support := by
  cases side <;> simp only [smoothingPatch]
  · exact B.parallelPatch_subset_support
  · exact B.surgeryPatch_subset_support

theorem smoothingPatch_subset_eventRegion (side : Bool) :
    B.smoothingPatch side ⊆ B.eventRegion := by
  cases side <;> simp only [smoothingPatch]
  · exact B.parallelPatch_subset_eventRegion
  · exact B.surgeryPatch_subset_eventRegion

/-! ## Exact supported replacement -/

/-- Replace everything inside the band by one of the two explicit patches, leaving the named
outside carrier untouched. -/
def resolvedCarrier (oldCarrier : Set R3) (side : Bool) : Set R3 :=
  (oldCarrier \ B.support) ∪ B.smoothingPatch side

/-- A band resolution agrees literally with the old carrier away from the support. -/
theorem resolvedCarrier_sdiff_support (oldCarrier : Set R3) (side : Bool) :
    B.resolvedCarrier oldCarrier side \ B.support = oldCarrier \ B.support := by
  ext x
  constructor
  · rintro ⟨hx, hxSupport⟩
    rcases hx with hxOld | hxPatch
    · exact hxOld
    · exact False.elim <| hxSupport (B.smoothingPatch_subset_support side hxPatch)
  · intro hx
    exact ⟨Or.inl hx, hx.2⟩

/-- Every new point created by the resolution lies in the moving-sphere event region. -/
theorem resolvedCarrier_subset_oldOutside_union_eventRegion
    (oldCarrier : Set R3) (side : Bool) :
    B.resolvedCarrier oldCarrier side ⊆
      (oldCarrier \ B.support) ∪ B.eventRegion := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (B.smoothingPatch_subset_eventRegion side hx)

/-- Both resolutions have exactly the same carrier outside the band. -/
theorem parallel_surgery_agree_off_support (oldCarrier : Set R3) :
    B.resolvedCarrier oldCarrier false \ B.support =
      B.resolvedCarrier oldCarrier true \ B.support := by
  rw [B.resolvedCarrier_sdiff_support, B.resolvedCarrier_sdiff_support]

end PairedSeamBandChart

/-! ## Simultaneous resolution in finitely many disjoint bands -/

/-- A finite collection of paired seam bands.  Pairwise-disjoint support is the only interaction
hypothesis needed for simultaneous local replacement. -/
structure FinitePairedSeamBandCharts (bandCount : ℕ) where
  band : Fin bandCount → PairedSeamBandChart
  support_pairwise : Pairwise fun b e ↦
    Disjoint (band b).support (band e).support

namespace FinitePairedSeamBandCharts

variable {bandCount : ℕ} (F : FinitePairedSeamBandCharts bandCount)

def supportUnion : Set R3 :=
  ⋃ b, (F.band b).support

def eventRegion : Set R3 :=
  ⋃ b, (F.band b).eventRegion

def patchUnion (choice : Fin bandCount → Bool) : Set R3 :=
  ⋃ b, (F.band b).smoothingPatch (choice b)

theorem smoothingPatch_subset_supportUnion
    (choice : Fin bandCount → Bool) (b : Fin bandCount) :
    (F.band b).smoothingPatch (choice b) ⊆ F.supportUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr
    ⟨b, (F.band b).smoothingPatch_subset_support (choice b) hx⟩

theorem patchUnion_subset_supportUnion (choice : Fin bandCount → Bool) :
    F.patchUnion choice ⊆ F.supportUnion := by
  intro x hx
  simp only [patchUnion, Set.mem_iUnion] at hx
  obtain ⟨b, hb⟩ := hx
  exact F.smoothingPatch_subset_supportUnion choice b hb

theorem smoothingPatch_subset_eventRegion
    (choice : Fin bandCount → Bool) (b : Fin bandCount) :
    (F.band b).smoothingPatch (choice b) ⊆ F.eventRegion := by
  intro x hx
  exact Set.mem_iUnion.mpr
    ⟨b, (F.band b).smoothingPatch_subset_eventRegion (choice b) hx⟩

theorem patchUnion_subset_eventRegion (choice : Fin bandCount → Bool) :
    F.patchUnion choice ⊆ F.eventRegion := by
  intro x hx
  simp only [patchUnion, Set.mem_iUnion] at hx
  obtain ⟨b, hb⟩ := hx
  exact F.smoothingPatch_subset_eventRegion choice b hb

/-- Simultaneously replace the singular graph inside every paired band. -/
def resolvedCarrier (oldCarrier : Set R3) (choice : Fin bandCount → Bool) : Set R3 :=
  (oldCarrier \ F.supportUnion) ∪ F.patchUnion choice

/-- Simultaneous disjoint-band resolution is literally unchanged off the union of supports. -/
theorem resolvedCarrier_sdiff_supportUnion
    (oldCarrier : Set R3) (choice : Fin bandCount → Bool) :
    F.resolvedCarrier oldCarrier choice \ F.supportUnion =
      oldCarrier \ F.supportUnion := by
  ext x
  constructor
  · rintro ⟨hx, hxSupport⟩
    rcases hx with hxOld | hxPatch
    · exact hxOld
    · exact False.elim <| hxSupport (F.patchUnion_subset_supportUnion choice hxPatch)
  · intro hx
    exact ⟨Or.inl hx, hx.2⟩

/-- Every point introduced by the finite surgery is covered by one recorded event region. -/
theorem resolvedCarrier_subset_oldOutside_union_eventRegion
    (oldCarrier : Set R3) (choice : Fin bandCount → Bool) :
    F.resolvedCarrier oldCarrier choice ⊆
      (oldCarrier \ F.supportUnion) ∪ F.eventRegion := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (F.patchUnion_subset_eventRegion choice hx)

/-- Any two choices of the local noncrossing smoothing agree off all band supports. -/
theorem choices_agree_off_support
    (oldCarrier : Set R3) (first second : Fin bandCount → Bool) :
    F.resolvedCarrier oldCarrier first \ F.supportUnion =
      F.resolvedCarrier oldCarrier second \ F.supportUnion := by
  rw [F.resolvedCarrier_sdiff_supportUnion,
    F.resolvedCarrier_sdiff_supportUnion]

end FinitePairedSeamBandCharts

/-! ## Alignment with a finite barrier excursion pairing -/

/-- Standard band charts aligned with the paired graph excursions.  These fields identify the
already constructed standard singular patch with the actual graph inside each support; they do
not postulate a resolved circle family. -/
structure BarrierExcursionBandChartRealization
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex vertex edge : Type*}
    [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {A : FiniteBarrierArcPresentation G vertex edge}
    (P : FiniteBarrierExcursionPairing A) where
  chart : Fin P.bandCount → PairedSeamBandChart
  support_eq : ∀ b, (chart b).support = P.bandNeighborhood b
  leftVertex_eq : ∀ b,
    (chart b).leftVertex = A.point (P.firstVertex b)
  rightVertex_eq : ∀ b,
    (chart b).rightVertex = A.point (P.secondVertex b)
  seamPath_range_eq : ∀ b,
    Set.range (chart b).seamPath = Set.range (A.arc (P.excursionEdge b))
  /-- The band chart is a transported-torus chart, not merely an ambient planar embedding. -/
  chart_mem_torus : ∀ b z, (chart b).chart z ∈ transportedTorus Phi
  singular_local_exact : ∀ b,
    G.carrier ∩ P.bandNeighborhood b = (chart b).singularPatch

namespace BarrierExcursionBandChartRealization

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}

/-- Forget alignment and retain the finite disjoint family of standard band charts. -/
def toFinitePairedSeamBandCharts
    (C : BarrierExcursionBandChartRealization P) :
    FinitePairedSeamBandCharts P.bandCount where
  band := C.chart
  support_pairwise := by
    intro b e hbe
    rw [C.support_eq b, C.support_eq e]
    exact P.bandNeighborhood_pairwise hbe

/-- The support union of the transported standard charts is exactly the support union named by
the graph pairing. -/
theorem supportUnion_eq
    (C : BarrierExcursionBandChartRealization P) :
    C.toFinitePairedSeamBandCharts.supportUnion =
      ⋃ b, P.bandNeighborhood b := by
  ext x
  simp only [FinitePairedSeamBandCharts.supportUnion,
    toFinitePairedSeamBandCharts, Set.mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, C.support_eq b ▸ hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (C.support_eq b).symm ▸ hb⟩

/-- Every standard smoothing arc lies on the transported torus because the ambient band chart
is required to be a transported-torus chart. -/
theorem patchUnion_subset_transportedTorus
    (C : BarrierExcursionBandChartRealization P)
    (choice : Fin P.bandCount → Bool) :
    C.toFinitePairedSeamBandCharts.patchUnion choice ⊆ transportedTorus Phi := by
  intro x hx
  simp only [FinitePairedSeamBandCharts.patchUnion, Set.mem_iUnion] at hx
  obtain ⟨b, hb⟩ := hx
  cases hchoice : choice b <;>
      simp only [PairedSeamBandChart.smoothingPatch,
        PairedSeamBandChart.parallelPatch, PairedSeamBandChart.surgeryPatch,
        hchoice, Set.mem_union] at hb
  · rcases hb with hb | hb
    · obtain ⟨t, rfl⟩ := hb
      exact C.chart_mem_torus b _
    · obtain ⟨t, rfl⟩ := hb
      exact C.chart_mem_torus b _
  · rcases hb with hb | hb
    · obtain ⟨t, rfl⟩ := hb
      exact C.chart_mem_torus b _
    · obtain ⟨t, rfl⟩ := hb
      exact C.chart_mem_torus b _

/-- The simultaneous standard replacement, now regarded as a construction on the analytic
barrier graph. -/
def resolvedGraphCarrier
    (C : BarrierExcursionBandChartRealization P)
    (choice : Fin P.bandCount → Bool) : Set R3 :=
  C.toFinitePairedSeamBandCharts.resolvedCarrier G.carrier choice

/-- The transported construction agrees exactly with the analytic graph outside all paired
excursion bands. -/
theorem resolvedGraphCarrier_sdiff_bandNeighborhoods
    (C : BarrierExcursionBandChartRealization P)
    (choice : Fin P.bandCount → Bool) :
    C.resolvedGraphCarrier choice \ (⋃ b, P.bandNeighborhood b) =
      G.carrier \ (⋃ b, P.bandNeighborhood b) := by
  rw [← C.supportUnion_eq, resolvedGraphCarrier,
    FinitePairedSeamBandCharts.resolvedCarrier_sdiff_supportUnion]

/-- If all transported band traces are charged to a common event region, every newly introduced
point is charged there. -/
theorem resolvedGraphCarrier_subset_oldOutside_union_eventRegion
    (C : BarrierExcursionBandChartRealization P)
    (choice : Fin P.bandCount → Bool) (eventRegion : Set R3)
    (hevent : ∀ b, (C.chart b).eventRegion ⊆ eventRegion) :
    C.resolvedGraphCarrier choice ⊆
      (G.carrier \ (⋃ b, P.bandNeighborhood b)) ∪ eventRegion := by
  intro x hx
  have hx' := C.toFinitePairedSeamBandCharts
    |>.resolvedCarrier_subset_oldOutside_union_eventRegion G.carrier choice hx
  rcases hx' with hxOld | hxEvent
  · rw [C.supportUnion_eq] at hxOld
    exact Or.inl hxOld
  · right
    simp only [FinitePairedSeamBandCharts.eventRegion, Set.mem_iUnion] at hxEvent
    obtain ⟨b, hb⟩ := hxEvent
    exact hevent b hb

end BarrierExcursionBandChartRealization

/-! ## Realization as a regular moving-sphere stage -/

namespace FiniteBarrierTwoSurgeryResolution

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge resolvedIndex : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  [Fintype resolvedIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}

/-- Once the ambient sphere construction identifies its regular intersection with the explicitly
resolved graph carrier, exact outside-band agreement is a theorem rather than a resolution field. -/
theorem fixed_off_bandNeighborhoods_of_stageIntersection
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex)
    (C : BarrierExcursionBandChartRealization Q.toFiniteBarrierExcursionPairing)
    (choice : Fin Q.bandCount → Bool)
    (hstage : Q.stage.sphereFamily.carrier ∩ transportedTorus Phi =
      C.resolvedGraphCarrier choice) :
    G.carrier \ (⋃ b, Q.bandNeighborhood b) =
      (Q.stage.sphereFamily.carrier ∩ transportedTorus Phi) \
        (⋃ b, Q.bandNeighborhood b) := by
  rw [hstage, C.resolvedGraphCarrier_sdiff_bandNeighborhoods]

/-- The same identification transfers local event coverage to the whole newly introduced part of
the regular stage. -/
theorem stageIntersection_subset_oldOutside_union_eventRegion
    (Q : FiniteBarrierTwoSurgeryResolution A resolvedIndex)
    (C : BarrierExcursionBandChartRealization Q.toFiniteBarrierExcursionPairing)
    (choice : Fin Q.bandCount → Bool)
    (hstage : Q.stage.sphereFamily.carrier ∩ transportedTorus Phi =
      C.resolvedGraphCarrier choice)
    (hevent : ∀ b, (C.chart b).eventRegion ⊆ Q.stage.eventRegion) :
    Q.stage.sphereFamily.carrier ∩ transportedTorus Phi ⊆
      (G.carrier \ (⋃ b, Q.bandNeighborhood b)) ∪ Q.stage.eventRegion := by
  rw [hstage]
  exact C.resolvedGraphCarrier_subset_oldOutside_union_eventRegion
    choice Q.stage.eventRegion hevent

end FiniteBarrierTwoSurgeryResolution

end Submission.Topology
