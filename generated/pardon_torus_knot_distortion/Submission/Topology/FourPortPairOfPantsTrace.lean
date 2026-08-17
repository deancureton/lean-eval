import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.SuperellipsoidGlobalFourPortCarrier
import Submission.Topology.ThreeBoundaryOuterDisk

/-!
# The pair-of-pants trace of one four-port move

The quadratic four-port graph determines the local endpoint patches of an elementary saddle
move: at time zero its torus intersection is the two vertical paths, while at time one it is the
two horizontal paths.  Determining whether this is a split or a merge requires the four outside
arcs, so that global reconnection is kept as explicit endpoint data below.  Since the literal
resolutions share those outside arcs, separate collar homeomorphisms push them to disjoint
parallel boundary circles before a pair-of-pants trace is formed.

`EmbeddedPairOfPantsTrace` is the smallest codimension-zero trace used by the disk-side parity
argument.  It records a connected dense interior, the exact union of three affected boundary
circles, and containment of the parity-change locus.  It does not assume boundary generation of
homology or the complement classification; those remain the separate fields of
`ThreeBoundaryPairOfPantsTopology`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-! ## Endpoint sets of one local move -/

/-- The transported-torus boundary of one regular sphere-family stage. -/
def regularStageTorusBoundary
    (S : RegularSphereFamilyParityStage Phi) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi S.sphereFamily.carrier

/-- The exact locus on which the two parity-inside predicates differ. -/
def regularStageLabelChangeLocus
    (pre post : RegularSphereFamilyParityStage Phi) : Set (transportedTorus Phi) :=
  {x | (x ∈ pre.inside) ≠ (x ∈ post.inside)}

/-- The open part of the parity-change locus, excluding both endpoint boundaries. -/
def regularStageStrictLabelChangeLocus
    (pre post : RegularSphereFamilyParityStage Phi) : Set (transportedTorus Phi) :=
  (pre.inside ∩ post.outside) ∪ (pre.outside ∩ post.inside)

theorem isOpen_regularStageStrictLabelChangeLocus
    (pre post : RegularSphereFamilyParityStage Phi) :
    IsOpen (regularStageStrictLabelChangeLocus pre post) :=
  (pre.isOpen_inside.inter post.isOpen_outside).union
    (pre.isOpen_outside.inter post.isOpen_inside)

/-- Every strict change point has different endpoint inside labels. -/
theorem strictLabelChangeLocus_subset_labelChangeLocus
    (pre post : RegularSphereFamilyParityStage Phi) :
    regularStageStrictLabelChangeLocus pre post ⊆
      regularStageLabelChangeLocus pre post := by
  rintro x (⟨hxPre, hxPostOutside⟩ | ⟨hxPreOutside, hxPost⟩)
  · intro hlabels
    exact Set.disjoint_left.mp post.inside_disjoint_outside
      (hlabels ▸ hxPre) hxPostOutside
  · intro hlabels
    exact Set.disjoint_left.mp pre.inside_disjoint_outside
      (hlabels.symm ▸ hxPost) hxPreOutside

/-- The part of the transported torus lying in one four-port support. -/
def fourPortBandPart (B : PairedSeamBandChart) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi B.support

/-- The vertical endpoint patch, regarded as a transported-torus subset. -/
def fourPortParallelPart (B : PairedSeamBandChart) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi B.parallelPatch

/-- The horizontal endpoint patch, regarded as a transported-torus subset. -/
def fourPortSurgeryPart (B : PairedSeamBandChart) : Set (transportedTorus Phi) :=
  transportedTorusPart Phi B.surgeryPatch

/-- The global reconnection of the four ports either splits one circle into two or merges two
circles into one. -/
inductive FourPortBoundaryDirection where
  | split
  | merge
  deriving DecidableEq

/-- Boundary points of one embedded intersection circle, in the transported-torus subtype. -/
def torusCircleCarrier (C : EmbeddedTorusIntersectionCircle Phi) :
    Set (transportedTorus Phi) :=
  Set.range C.torusCircle

/-- Affected endpoint boundary before the move. -/
def fourPortPreAffectedBoundary
    (direction : FourPortBoundaryDirection)
    (circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi) :
    Set (transportedTorus Phi) :=
  match direction with
  | .split => torusCircleCarrier (circle 0)
  | .merge => torusCircleCarrier (circle 1) ∪ torusCircleCarrier (circle 2)

/-- Affected endpoint boundary after the move. -/
def fourPortPostAffectedBoundary
    (direction : FourPortBoundaryDirection)
    (circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi) :
    Set (transportedTorus Phi) :=
  match direction with
  | .split => torusCircleCarrier (circle 1) ∪ torusCircleCarrier (circle 2)
  | .merge => torusCircleCarrier (circle 0)

/-- The explicit union of all three affected boundary circles. -/
def threeCircleBoundaryUnion
    (circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi) :
    Set (transportedTorus Phi) :=
  torusCircleCarrier (circle 0) ∪
    (torusCircleCarrier (circle 1) ∪ torusCircleCarrier (circle 2))

theorem iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion
    (circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi) :
    (⋃ i, torusCircleCarrier (circle i)) = threeCircleBoundaryUnion circle := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · intro x hx
    rcases hx with hzero | hone | htwo
    · exact Set.mem_iUnion.mpr ⟨0, hzero⟩
    · exact Set.mem_iUnion.mpr ⟨1, hone⟩
    · exact Set.mem_iUnion.mpr ⟨2, htwo⟩

/-- Before and after together contain exactly the three affected circles, independently of
whether the local saddle is globally a split or a merge. -/
theorem preAffected_union_postAffected
    (direction : FourPortBoundaryDirection)
    (circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi) :
    fourPortPreAffectedBoundary direction circle ∪
        fourPortPostAffectedBoundary direction circle =
      threeCircleBoundaryUnion circle := by
  cases direction
  · rfl
  · exact Set.union_comm _ _

/-- Raw endpoint bookkeeping around one four-port chart.

The raw endpoint carriers meet the band in precisely the explicit vertical and horizontal
quadratic patches and agree on the four common outside arcs.  They are not treated as three
pairwise-disjoint circles: literal outside agreement makes that impossible. -/
structure FourPortRawEndpointData
    (B : PairedSeamBandChart)
    (pre post : RegularSphereFamilyParityStage Phi) where
  preAffectedBoundary : Set (transportedTorus Phi)
  postAffectedBoundary : Set (transportedTorus Phi)
  unaffectedBoundary : Set (transportedTorus Phi)
  unaffectedBoundary_disjoint_band :
    Disjoint unaffectedBoundary (fourPortBandPart B)
  preBoundary_exact : regularStageTorusBoundary pre =
    unaffectedBoundary ∪ preAffectedBoundary
  postBoundary_exact : regularStageTorusBoundary post =
    unaffectedBoundary ∪ postAffectedBoundary
  pre_local_patch_exact :
    preAffectedBoundary ∩ fourPortBandPart B =
      fourPortParallelPart B
  post_local_patch_exact :
    postAffectedBoundary ∩ fourPortBandPart B =
      fourPortSurgeryPart B
  affected_agree_off_band :
    preAffectedBoundary \ fourPortBandPart B =
      postAffectedBoundary \ fourPortBandPart B
  inside_agree_off_band : ∀ x, x ∉ fourPortBandPart B →
    (x ∈ pre.inside ↔ x ∈ post.inside)

namespace FourPortRawEndpointData

open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}

/-- Outside agreement localizes every parity-label change to the four-port band. -/
theorem labelChangeLocus_subset_bandPart
    (E : FourPortRawEndpointData B pre post) :
    regularStageLabelChangeLocus pre post ⊆ fourPortBandPart B := by
  intro x hx
  change (x ∈ pre.inside) ≠ (x ∈ post.inside) at hx
  by_contra hxBand
  exact hx (propext (E.inside_agree_off_band x hxBand))

/-- The full pre-stage boundary has exactly the vertical local patch. -/
theorem preBoundary_inter_bandPart
    (E : FourPortRawEndpointData B pre post) :
    regularStageTorusBoundary pre ∩ fourPortBandPart B =
      fourPortParallelPart B := by
  rw [E.preBoundary_exact]
  apply Set.Subset.antisymm
  · rintro x ⟨hxUnaffected | hxAffected, hxBand⟩
    · exact False.elim <|
        Set.disjoint_left.mp E.unaffectedBoundary_disjoint_band hxUnaffected hxBand
    · rw [← E.pre_local_patch_exact]
      exact ⟨hxAffected, hxBand⟩
  · intro x hx
    rw [← E.pre_local_patch_exact] at hx
    exact ⟨Or.inr hx.1, hx.2⟩

/-- The full post-stage boundary has exactly the horizontal local patch. -/
theorem postBoundary_inter_bandPart
    (E : FourPortRawEndpointData B pre post) :
    regularStageTorusBoundary post ∩ fourPortBandPart B =
      fourPortSurgeryPart B := by
  rw [E.postBoundary_exact]
  apply Set.Subset.antisymm
  · rintro x ⟨hxUnaffected | hxAffected, hxBand⟩
    · exact False.elim <|
        Set.disjoint_left.mp E.unaffectedBoundary_disjoint_band hxUnaffected hxBand
    · rw [← E.post_local_patch_exact]
      exact ⟨hxAffected, hxBand⟩
  · intro x hx
    rw [← E.post_local_patch_exact] at hx
    exact ⟨Or.inr hx.1, hx.2⟩

/-- The two complete stage boundaries agree literally away from the four-port band. -/
theorem stageBoundaries_agree_off_bandPart
    (E : FourPortRawEndpointData B pre post) :
    regularStageTorusBoundary pre \ fourPortBandPart B =
      regularStageTorusBoundary post \ fourPortBandPart B := by
  ext x
  rw [E.preBoundary_exact, E.postBoundary_exact]
  have hAffected := Set.ext_iff.mp E.affected_agree_off_band x
  simp only [Set.mem_sdiff, Set.mem_union] at hAffected ⊢
  constructor
  · rintro ⟨hxUnaffected | hxAffected, hxBand⟩
    · exact ⟨Or.inl hxUnaffected, hxBand⟩
    · exact ⟨Or.inr (hAffected.mp ⟨hxAffected, hxBand⟩).1, hxBand⟩
  · rintro ⟨hxUnaffected | hxAffected, hxBand⟩
    · exact ⟨Or.inl hxUnaffected, hxBand⟩
    · exact ⟨Or.inr (hAffected.mpr ⟨hxAffected, hxBand⟩).1, hxBand⟩

end FourPortRawEndpointData

/-! ## Disjoint collar-pushed endpoints -/

/-- Three disjoint boundary circles obtained by pushing the two raw endpoints to opposite levels
of a torus collar.  The two endpoint embeddings are the smallest additional local geometric
input needed to turn literally overlapping outside arcs into disjoint pair-of-pants boundary
components. -/
structure FourPortEndpointCircleData
    {B : PairedSeamBandChart}
    {pre post : RegularSphereFamilyParityStage Phi}
    (raw : FourPortRawEndpointData B pre post) where
  direction : FourPortBoundaryDirection
  circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi
  zeroWinding : ∀ i, (circle i).windingLoop.windingPair = (0, 0)
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  prePush : raw.preAffectedBoundary → transportedTorus Phi
  postPush : raw.postAffectedBoundary → transportedTorus Phi
  prePush_isEmbedding : IsEmbedding prePush
  postPush_isEmbedding : IsEmbedding postPush
  prePush_range : Set.range prePush =
    fourPortPreAffectedBoundary direction circle
  postPush_range : Set.range postPush =
    fourPortPostAffectedBoundary direction circle

/-! ## Identification with the explicit global quadratic graph -/

namespace FiniteSuperellipsoidBarrierGraph

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace CutCircleTransverseCyclicOrderFamily

variable {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

/-- The time-zero global quadratic graph induces exactly the vertical torus patch. -/
theorem torusPart_range_globalBandFourPortMorseGraph_zero
    (T : GlobalBandTubularChartData F b) :
    transportedTorusPart Phi
        (Set.range (globalBandFourPortMorseGraph T ⟨0, by norm_num⟩)) =
      fourPortParallelPart T.toPairedSeamBandChart := by
  ext x
  have hset := Set.ext_iff.mp
    (range_globalBandFourPortMorseGraph_zero_inter_transportedTorus T) (x : R3)
  change (x : R3) ∈ Set.range (globalBandFourPortMorseGraph T ⟨0, by norm_num⟩) ↔
    (x : R3) ∈ T.toPairedSeamBandChart.parallelPatch
  simpa only [Set.mem_inter_iff, x.property, and_true] using hset

/-- The time-one global quadratic graph induces exactly the horizontal torus patch. -/
theorem torusPart_range_globalBandFourPortMorseGraph_one
    (T : GlobalBandTubularChartData F b) :
    transportedTorusPart Phi
        (Set.range (globalBandFourPortMorseGraph T ⟨1, by norm_num⟩)) =
      fourPortSurgeryPart T.toPairedSeamBandChart := by
  ext x
  have hset := Set.ext_iff.mp
    (range_globalBandFourPortMorseGraph_one_inter_transportedTorus T) (x : R3)
  change (x : R3) ∈ Set.range (globalBandFourPortMorseGraph T ⟨1, by norm_num⟩) ↔
    (x : R3) ∈ T.toPairedSeamBandChart.surgeryPatch
  simpa only [Set.mem_inter_iff, x.property, and_true] using hset

end CutCircleTransverseCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

namespace FourPortRawEndpointData

open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

/-- Package a raw pre/post endpoint move whose local patches are identified with the actual
time-zero and time-one global quadratic Morse graphs.  The two graph-to-patch equalities are
proved above; only the global outside reconnection and parity agreement remain arguments. -/
def ofGlobalBandFourPortMorseGraph
    (T : GlobalBandTubularChartData F b)
    (pre post : RegularSphereFamilyParityStage Phi)
    (preAffectedBoundary postAffectedBoundary : Set (transportedTorus Phi))
    (unaffectedBoundary : Set (transportedTorus Phi))
    (unaffectedBoundary_disjoint_band :
      Disjoint unaffectedBoundary (fourPortBandPart T.toPairedSeamBandChart))
    (preBoundary_exact : regularStageTorusBoundary pre =
      unaffectedBoundary ∪ preAffectedBoundary)
    (postBoundary_exact : regularStageTorusBoundary post =
      unaffectedBoundary ∪ postAffectedBoundary)
    (pre_local_graph_exact :
      preAffectedBoundary ∩ fourPortBandPart T.toPairedSeamBandChart =
        transportedTorusPart Phi
          (Set.range (globalBandFourPortMorseGraph T ⟨0, by norm_num⟩)))
    (post_local_graph_exact :
      postAffectedBoundary ∩ fourPortBandPart T.toPairedSeamBandChart =
        transportedTorusPart Phi
          (Set.range (globalBandFourPortMorseGraph T ⟨1, by norm_num⟩)))
    (affected_agree_off_band :
      preAffectedBoundary \ fourPortBandPart T.toPairedSeamBandChart =
        postAffectedBoundary \ fourPortBandPart T.toPairedSeamBandChart)
    (inside_agree_off_band : ∀ x,
      x ∉ fourPortBandPart T.toPairedSeamBandChart →
        (x ∈ pre.inside ↔ x ∈ post.inside)) :
    FourPortRawEndpointData T.toPairedSeamBandChart pre post where
  preAffectedBoundary := preAffectedBoundary
  postAffectedBoundary := postAffectedBoundary
  unaffectedBoundary := unaffectedBoundary
  unaffectedBoundary_disjoint_band := unaffectedBoundary_disjoint_band
  preBoundary_exact := preBoundary_exact
  postBoundary_exact := postBoundary_exact
  pre_local_patch_exact := pre_local_graph_exact.trans
    (torusPart_range_globalBandFourPortMorseGraph_zero T)
  post_local_patch_exact := post_local_graph_exact.trans
    (torusPart_range_globalBandFourPortMorseGraph_one T)
  affected_agree_off_band := affected_agree_off_band
  inside_agree_off_band := inside_agree_off_band

end FourPortRawEndpointData

/-! ## The codimension-zero trace -/

/-- The embedded pair-of-pants trace carried by one explicit endpoint surgery.

Only the local/codimension-zero geometry is included.  In particular, this structure has no
field asserting that its loops are boundary-generated and no field classifying its complement.
-/
structure EmbeddedPairOfPantsTrace
    {B : PairedSeamBandChart}
    {pre post : RegularSphereFamilyParityStage Phi}
    {raw : FourPortRawEndpointData B pre post}
    (endpoint : FourPortEndpointCircleData raw) where
  carrier : Set (transportedTorus Phi)
  interior : Set (transportedTorus Phi)
  interior_nonempty : interior.Nonempty
  interior_isConnected : IsConnected interior
  interior_isOpen : IsOpen interior
  interior_subset_carrier : interior ⊆ carrier
  carrier_subset_closure_interior : carrier ⊆ closure interior
  boundary_exact : carrier \ interior =
    ⋃ i, torusCircleCarrier (endpoint.circle i)
  labelChange_subset_carrier :
    regularStageLabelChangeLocus pre post ⊆ carrier

namespace EmbeddedPairOfPantsTrace

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {endpoint : FourPortEndpointCircleData raw}

/-- Construct the trace from a collar-augmented open interior.

The interior is not set equal to the raw parity-change locus.  The latter omits the thin annular
strips swept while separating the common outside arcs into disjoint parallel copies.  The collar
construction must supply those strips, prove connectedness, and identify the resulting frontier.
-/
def ofCollarAugmentedInterior
    (endpoint : FourPortEndpointCircleData raw)
    (interior : Set (transportedTorus Phi))
    (hnonempty : interior.Nonempty)
    (hconnected : IsConnected interior)
    (hopen : IsOpen interior)
    (hlabelChange : regularStageLabelChangeLocus pre post ⊆ closure interior)
    (hboundary : closure interior \ interior =
        ⋃ i, torusCircleCarrier (endpoint.circle i)) :
    EmbeddedPairOfPantsTrace endpoint where
  carrier := closure interior
  interior := interior
  interior_nonempty := hnonempty
  interior_isConnected := hconnected
  interior_isOpen := hopen
  interior_subset_carrier := subset_closure
  carrier_subset_closure_interior := Subset.rfl
  boundary_exact := hboundary
  labelChange_subset_carrier := hlabelChange

/-- Forget the endpoint-surgery bookkeeping and retain the exact three-boundary carrier. -/
def toThreeBoundaryPairOfPantsCarrier
    (P : EmbeddedPairOfPantsTrace endpoint) :
    ThreeBoundaryPairOfPantsCarrier Phi where
  carrier := P.carrier
  interior := P.interior
  circle := endpoint.circle
  zeroWinding := endpoint.zeroWinding
  pairwise_disjoint := endpoint.pairwise_disjoint
  interior_nonempty := P.interior_nonempty
  interior_isConnected := P.interior_isConnected
  interior_isOpen := P.interior_isOpen
  interior_subset_carrier := P.interior_subset_carrier
  carrier_subset_closure_interior := P.carrier_subset_closure_interior
  boundary_exact := P.boundary_exact

/-- The trace boundary is exactly the union of its affected pre- and post-stage boundaries. -/
theorem boundary_eq_preAffected_union_postAffected
    (P : EmbeddedPairOfPantsTrace endpoint) :
    P.carrier \ P.interior =
      fourPortPreAffectedBoundary endpoint.direction endpoint.circle ∪
        fourPortPostAffectedBoundary endpoint.direction endpoint.circle := by
  calc
    P.carrier \ P.interior =
        ⋃ i, torusCircleCarrier (endpoint.circle i) := P.boundary_exact
    _ = threeCircleBoundaryUnion endpoint.circle :=
      iUnion_torusCircleCarrier_eq_threeCircleBoundaryUnion endpoint.circle
    _ = fourPortPreAffectedBoundary endpoint.direction endpoint.circle ∪
        fourPortPostAffectedBoundary endpoint.direction endpoint.circle :=
      (preAffected_union_postAffected endpoint.direction endpoint.circle).symm

/-- The parity-change locus lies in the pair-of-pants carrier. -/
theorem labelChangeLocus_subset_carrier
    (P : EmbeddedPairOfPantsTrace endpoint) :
    regularStageLabelChangeLocus pre post ⊆ P.carrier :=
  P.labelChange_subset_carrier

/-- The parity-change locus is simultaneously contained in the trace and in the explicit
four-port band. -/
theorem labelChangeLocus_subset_carrier_inter_bandPart
    (P : EmbeddedPairOfPantsTrace endpoint) :
    regularStageLabelChangeLocus pre post ⊆
      P.carrier ∩ fourPortBandPart B := by
  exact subset_inter P.labelChangeLocus_subset_carrier
    raw.labelChangeLocus_subset_bandPart

/-- Once the separate global pair-of-pants topology is supplied, one canonical affected disk
covers the entire local parity-change locus. -/
theorem exists_canonicalDisk_covers_labelChangeLocus
    (P : EmbeddedPairOfPantsTrace endpoint)
    (T : ThreeBoundaryPairOfPantsTopology P.toThreeBoundaryPairOfPantsCarrier) :
    ∃ i, regularStageLabelChangeLocus pre post ⊆
      P.toThreeBoundaryPairOfPantsCarrier.disk i := by
  obtain ⟨i, hi⟩ := T.exists_canonicalDisk_contains_carrier
  exact ⟨i, P.labelChangeLocus_subset_carrier.trans hi⟩

end EmbeddedPairOfPantsTrace

end Submission.Topology
