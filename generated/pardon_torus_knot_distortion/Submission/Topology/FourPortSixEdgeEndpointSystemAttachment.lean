import Submission.Topology.FourPortQuadraticLabelChangeContainment
import Submission.Topology.PairedBandBooleanRegularStageFamily
import Submission.Topology.SuperellipsoidCanonicalStageEntries
import Submission.Topology.SuperellipsoidFiniteQuadraticStageSideCovers

/-!
# Endpoint-system indices for a six-edge four-port move

The six-edge outer-face theorem chooses one of its three graph circles only after the planar
rectangle has been constructed.  Consequently a stage constructor should not have to guess the
selected circle in advance.  It is enough to identify all three graph circles with their ordinary
indices on the pre or post audited endpoint system.

This file converts those six finite identifications into the selected endpoint attachment and
then into the forward-or-reverse disk-side alternative for the explicit quadratic move.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

namespace FourPortRawSixEdgeBandPresentation

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {F : G.CutCircleTransverseCyclicOrderFamily}
  {b : Fin F.toPairedSeamEnumeration.bandCount}
  {T : F.LiftedGlobalBandTubularChartData b}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {C : FourPortRawCircleData raw}
  (P : FourPortRawSixEdgeBandPresentation C)

/-- Whether one six-edge raw circle belongs to the pre endpoint. -/
private def circleBelongsToPre
    (direction : FourPortBoundaryDirection) (i : Fin 3) : Prop :=
  match direction with
  | .split => i = 0
  | .merge => i = 1 ∨ i = 2

/-- Whether one six-edge raw circle belongs to the post endpoint. -/
private def circleBelongsToPost
    (direction : FourPortBoundaryDirection) (i : Fin 3) : Prop :=
  match direction with
  | .split => i = 1 ∨ i = 2
  | .merge => i = 0

private theorem circleBelongsToPre_or_post
    (direction : FourPortBoundaryDirection) (i : Fin 3) :
    circleBelongsToPre direction i ∨ circleBelongsToPost direction i := by
  cases direction <;> fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)

/-- Ordinary endpoint-system indices for all three canonical six-edge graph circles.  Ownership
of each index is determined by the raw split/merge direction. -/
structure EndpointSystemCircleData
    {preCircleCount postCircleCount : ℕ}
    (preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount))
    (postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)) where
  preIndex : ∀ i, circleBelongsToPre C.direction i → Fin preCircleCount
  preCircle_eq : ∀ i h,
    preSystem.circle (preIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i
  postIndex : ∀ i, circleBelongsToPost C.direction i → Fin postCircleCount
  postCircle_eq : ∀ i h,
    postSystem.circle (postIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i

namespace EndpointSystemCircleData

variable {P : FourPortRawSixEdgeBandPresentation C}
  {preCircleCount postCircleCount : ℕ}
  {preSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin preCircleCount)}
  {postSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin postCircleCount)}

/-- Transport endpoint-circle indices along pointwise identifications with two new systems. -/
def transport
    {newPreCircleCount newPostCircleCount : ℕ}
    {newPreSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin newPreCircleCount)}
    {newPostSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin newPostCircleCount)}
    (D : EndpointSystemCircleData P preSystem postSystem)
    (preIndexMap : Fin preCircleCount → Fin newPreCircleCount)
    (postIndexMap : Fin postCircleCount → Fin newPostCircleCount)
    (preCircle_transport : ∀ i, newPreSystem.circle (preIndexMap i) = preSystem.circle i)
    (postCircle_transport : ∀ i, newPostSystem.circle (postIndexMap i) = postSystem.circle i) :
    EndpointSystemCircleData P newPreSystem newPostSystem where
  preIndex i h := preIndexMap (D.preIndex i h)
  preCircle_eq i h := (preCircle_transport (D.preIndex i h)).trans (D.preCircle_eq i h)
  postIndex i h := postIndexMap (D.postIndex i h)
  postCircle_eq i h := (postCircle_transport (D.postIndex i h)).trans (D.postCircle_eq i h)

/-- The outer face selected by the lifted rectangle belongs to its uniquely determined endpoint
system, so the six raw indices construct the selected endpoint attachment. -/
def canonicalEndpointCircleSideAttachment
    (D : EndpointSystemCircleData P preSystem postSystem) :
    CanonicalEndpointCircleSideAttachment T P preSystem postSystem := by
  classical
  let outer := P.canonicalOuterRawFaceData T
  by_cases hpre : circleBelongsToPre C.direction outer.outerIndex
  · exact Sum.inl {
      circleIndex := D.preIndex outer.outerIndex hpre
      outerCircle_eq := D.preCircle_eq outer.outerIndex hpre }
  · have hpost : circleBelongsToPost C.direction outer.outerIndex := by
      rcases circleBelongsToPre_or_post C.direction outer.outerIndex with h | h
      · exact False.elim (hpre h)
      · exact h
    exact Sum.inr {
      circleIndex := D.postIndex outer.outerIndex hpost
      outerCircle_eq := D.postCircle_eq outer.outerIndex hpost }

/-- Explicit endpoint indices and quadratic inside labels discharge the former selected-circle
attachment input of the local stage-side theorem. -/
noncomputable def canonicalStageSideAlternative
    {preZero : preSystem.AllInessential}
    {postZero : postSystem.AllInessential}
    (D : EndpointSystemCircleData P preSystem postSystem)
    (labels : QuadraticEndpointLabelData (pre := pre) (post := post) T) :
    FiniteElementaryDiskSideCover preSystem preZero pre post ⊕
      FiniteElementaryDiskSideCover postSystem postZero post pre :=
  P.canonicalEndpointCircleSideAlternative_of_quadraticLabels T
    D.canonicalEndpointCircleSideAttachment labels

end EndpointSystemCircleData

/-- Endpoint indices before the canonical finite-stage systems are reindexed by `Fin`. -/
structure SourceEndpointSystemCircleData
    {preIndexType postIndexType : Type*}
    [Fintype preIndexType] [Fintype postIndexType]
    (preSource : FiniteSphereSurgeryIntersectionSystem Phi preIndexType)
    (postSource : FiniteSphereSurgeryIntersectionSystem Phi postIndexType) where
  preIndex : ∀ i, circleBelongsToPre C.direction i → preIndexType
  preCircle_eq : ∀ i h,
    preSource.circle (preIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i
  postIndex : ∀ i, circleBelongsToPost C.direction i → postIndexType
  postCircle_eq : ∀ i h,
    postSource.circle (postIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i

namespace SourceEndpointSystemCircleData

variable {P : FourPortRawSixEdgeBandPresentation C}
  {preIndexType postIndexType : Type*}
  [Fintype preIndexType] [Fintype postIndexType]
  {preSource : FiniteSphereSurgeryIntersectionSystem Phi preIndexType}
  {postSource : FiniteSphereSurgeryIntersectionSystem Phi postIndexType}

/-- Canonical `Fintype.equivFin` reindexing transports the three source indices to exactly the
`Fin`-indexed systems stored by regular finite-stage entries. -/
def toFinEndpointSystemCircleData
    (D : SourceEndpointSystemCircleData P preSource postSource) :
    EndpointSystemCircleData P
      (preSource.reindex (Fintype.equivFin preIndexType).symm)
      (postSource.reindex (Fintype.equivFin postIndexType).symm) where
  preIndex i h := Fintype.equivFin preIndexType (D.preIndex i h)
  preCircle_eq := by
    intro i h
    change preSource.circle
        ((Fintype.equivFin preIndexType).symm
          (Fintype.equivFin preIndexType (D.preIndex i h))) = _
    rw [Equiv.symm_apply_apply]
    exact D.preCircle_eq i h
  postIndex i h := Fintype.equivFin postIndexType (D.postIndex i h)
  postCircle_eq := by
    intro i h
    change postSource.circle
        ((Fintype.equivFin postIndexType).symm
          (Fintype.equivFin postIndexType (D.postIndex i h))) = _
    rw [Equiv.symm_apply_apply]
    exact D.postCircle_eq i h

end SourceEndpointSystemCircleData

section DecorationReindexing

variable {vertex edge : Type*} [Fintype vertex] [Fintype edge]
  {A : FiniteBarrierArcPresentation G vertex edge}
  {pairing : FiniteBarrierExcursionPairing A}
  {realization : BarrierExcursionBandChartRealization pairing}
  {preChoice postChoice : Fin pairing.bandCount → Bool}
  {preCollar : PairedBandMovingSphereCollarData realization preChoice}
  {postCollar : PairedBandMovingSphereCollarData realization postChoice}
  {preIndexType postIndexType : Type*}
  [Fintype preIndexType] [Fintype postIndexType]
  (preDecoration : RegularStageBasicDecoration preCollar preIndexType)
  (postDecoration : RegularStageBasicDecoration postCollar postIndexType)

/-- Native decoration indices identifying the three graph circles at their actual endpoint. -/
structure DecorationEndpointCircleData where
  preIndex : ∀ i, circleBelongsToPre C.direction i → preIndexType
  preCircle_eq : ∀ i h,
    preDecoration.circle (preIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i
  postIndex : ∀ i, circleBelongsToPost C.direction i → postIndexType
  postCircle_eq : ∀ i h,
    postDecoration.circle (postIndex i h) =
      P.toFourPortRawSixEdgePresentation.zeroWindingData.rawEmbeddedCircle i

namespace DecorationEndpointCircleData

variable {P : FourPortRawSixEdgeBandPresentation C}
  {preDecoration : RegularStageBasicDecoration preCollar preIndexType}
  {postDecoration : RegularStageBasicDecoration postCollar postIndexType}

/-- The systems stored in the two finite stage entries inherit the native decoration indices
through the canonical `Fintype.equivFin` reindexing. -/
def toEndpointSystemCircleData
    (D : DecorationEndpointCircleData P preDecoration postDecoration)
    (preOpen : IsOpen preDecoration.insideCell)
    (postOpen : IsOpen postDecoration.insideCell) :
    EndpointSystemCircleData P
      (preDecoration.toFiniteStageEntry preOpen).system
      (postDecoration.toFiniteStageEntry postOpen).system := by
  let source : SourceEndpointSystemCircleData P
      preDecoration.toFiniteSphereSurgeryIntersectionSystem
      postDecoration.toFiniteSphereSurgeryIntersectionSystem := {
    preIndex := D.preIndex
    preCircle_eq := D.preCircle_eq
    postIndex := D.postIndex
    postCircle_eq := D.postCircle_eq }
  exact source.toFinEndpointSystemCircleData

end DecorationEndpointCircleData
end DecorationReindexing
end FourPortRawSixEdgeBandPresentation

/-! ## Finite-stage packaging -/

variable {Phi : AmbientIsotopy}

/-- Local quadratic data for one audited transition, with concrete endpoint indices for all
three raw graph circles instead of a preselected outer-circle attachment. -/
structure IndexedQuadraticFourPortStageSideCoverData
    (S : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : S.AllInessential) (k : ℕ) (hk : k < S.length) where
  frame : Equiv.Perm (Fin 3)
  center : R3
  outerScale : ℝ
  cutHeight : ℝ
  outerIndex : Type
  cutIndex : Type
  [outerIndex_fintype : Fintype outerIndex]
  [cutIndex_fintype : Fintype cutIndex]
  barrier : FiniteSuperellipsoidBarrierGraph Phi frame center outerScale cutHeight
    outerIndex cutIndex
  order : barrier.CutCircleTransverseCyclicOrderFamily
  band : Fin order.toPairedSeamEnumeration.bandCount
  chart : order.LiftedGlobalBandTubularChartData band
  raw : FourPortRawEndpointData chart.toGlobalBandTubularChartData.toPairedSeamBandChart
    (S.parityStage k) (S.parityStage (k + 1))
  circles : FourPortRawCircleData raw
  presentation : FourPortRawSixEdgeBandPresentation circles
  endpointCircles : presentation.EndpointSystemCircleData
    (S.system k) (S.system (k + 1))
  endpointLabels : FourPortRawSixEdgeBandPresentation.QuadraticEndpointLabelData
    (pre := S.parityStage k) (post := S.parityStage (k + 1)) chart

namespace IndexedQuadraticFourPortStageSideCoverData

variable {S : FiniteRegularSphereSurgeryStageSequence Phi}
  {hzero : S.AllInessential} {k : ℕ} {hk : k < S.length}

/-- The indexed local package constructs the pre-sided or post-sided elementary cover required
at this transition. -/
def toStageSideCover
    (D : IndexedQuadraticFourPortStageSideCoverData S hzero k hk) :
    (FiniteElementaryDiskSideCover (S.system k) (hzero k (Nat.le_of_lt hk))
      (S.parityStage k) (S.parityStage (k + 1))) ⊕
    (FiniteElementaryDiskSideCover (S.system (k + 1))
      (hzero (k + 1) hk) (S.parityStage (k + 1)) (S.parityStage k)) := by
  letI := D.outerIndex_fintype
  letI := D.cutIndex_fintype
  exact D.endpointCircles.canonicalStageSideAlternative D.endpointLabels

/-- Forget the three explicit endpoint indices only after they have constructed the selected
outer-circle attachment expected by the older quadratic stage interface. -/
def toQuadraticFourPortStageSideCoverData
    (D : IndexedQuadraticFourPortStageSideCoverData S hzero k hk) :
    QuadraticFourPortStageSideCoverData S hzero k hk := by
  letI := D.outerIndex_fintype
  letI := D.cutIndex_fintype
  exact {
    frame := D.frame
    center := D.center
    outerScale := D.outerScale
    cutHeight := D.cutHeight
    outerIndex := D.outerIndex
    cutIndex := D.cutIndex
    barrier := D.barrier
    order := D.order
    band := D.band
    chart := D.chart
    raw := D.raw
    circles := D.circles
    presentation := D.presentation
    endpointAttachment := D.endpointCircles.canonicalEndpointCircleSideAttachment
    endpointLabels := D.endpointLabels }

end IndexedQuadraticFourPortStageSideCoverData

/-- Concrete raw-circle indices and quadratic data at every transition of a finite sequence. -/
structure FiniteIndexedQuadraticFourPortStageSideCoverData
    (S : FiniteRegularSphereSurgeryStageSequence Phi)
    (hzero : S.AllInessential) where
  move : ∀ k (hk : k < S.length),
    Nonempty (IndexedQuadraticFourPortStageSideCoverData S hzero k hk)

namespace FiniteIndexedQuadraticFourPortStageSideCoverData

variable {S : FiniteRegularSphereSurgeryStageSequence Phi}
  {hzero : S.AllInessential}

/-- The indexed quadratic packages give the heterogeneous stage-side cover family consumed by
the global all-inessential resolution. -/
def toFiniteStageSideDiskCoverData
    (D : FiniteIndexedQuadraticFourPortStageSideCoverData S hzero) :
    FiniteStageSideDiskCoverData S hzero where
  cover k hk := (D.move k hk).some.toStageSideCover

/-- Explicit endpoint indices produce the quadratic cover family used by the global axis
integration. -/
theorem toFiniteQuadraticFourPortStageSideCoverData
    (D : FiniteIndexedQuadraticFourPortStageSideCoverData S hzero) :
    FiniteQuadraticFourPortStageSideCoverData S hzero where
  move k hk := (D.move k hk).map
    IndexedQuadraticFourPortStageSideCoverData.toQuadraticFourPortStageSideCoverData

end FiniteIndexedQuadraticFourPortStageSideCoverData

namespace PairedBandMovingSphereCollarData.BooleanChoicePairedBandRegularStageData

universe u

variable {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {pairing : FiniteBarrierExcursionPairing A}
  {realization : BarrierExcursionBandChartRealization pairing}

/-- The natural-indexed sequence obtained by following the canonical Boolean flip path. -/
def booleanFlipStageSequence
    (D : BooleanChoicePairedBandRegularStageData (C := realization)) :
    FiniteRegularSphereSurgeryStageSequence Phi :=
  D.toBooleanChoiceRegularStageData
    |>.toFiniteRegularSphereSurgeryStageFamily
    |>.toFiniteRegularSphereSurgeryStageSequence

@[simp] theorem booleanFlipStageSequence_length
    (D : BooleanChoicePairedBandRegularStageData (C := realization)) :
    D.booleanFlipStageSequence.length = pairing.bandCount :=
  rfl

/-- Natural stage `k` is the decoration with the first `k` bands resolved. -/
theorem booleanFlipStageSequence_circleCount_castSucc
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    D.booleanFlipStageSequence.circleCount k =
      (D.stageEntry (prefixBandChoice k.castSucc)).circleCount := by
  change
    (D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
      |>.extendedCircleCount k) = _
  unfold FiniteRegularSphereSurgeryStageFamily.extendedCircleCount
  rw [FiniteRegularSphereSurgeryStageFamily.boundedIndex_eq_of_le _ k.isLt.le]
  rfl

/-- Natural stage `k + 1` is the decoration obtained by flipping band `k`. -/
theorem booleanFlipStageSequence_circleCount_succ
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    D.booleanFlipStageSequence.circleCount (k + 1) =
      (D.stageEntry (prefixBandChoice k.succ)).circleCount := by
  have hk : k.1 + 1 ≤ pairing.bandCount := k.isLt
  change
    (D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
      |>.extendedCircleCount (k.1 + 1)) = _
  unfold FiniteRegularSphereSurgeryStageFamily.extendedCircleCount
  rw [FiniteRegularSphereSurgeryStageFamily.boundedIndex_eq_of_le _ hk]
  rfl

/-- Transport a native circle index at the stage before flip `k` to the natural-indexed
sequence, preserving its ordinal value. -/
def booleanFlipStageSequenceIndexCastSucc
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    Fin (D.stageEntry (prefixBandChoice k.castSucc)).circleCount →
      Fin (D.booleanFlipStageSequence.circleCount k) :=
  D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
    |>.extendedIndexOfLE k.isLt.le

/-- Transport a native circle index at the stage after flip `k` to the natural-indexed
sequence, preserving its ordinal value. -/
def booleanFlipStageSequenceIndexSucc
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    Fin (D.stageEntry (prefixBandChoice k.succ)).circleCount →
      Fin (D.booleanFlipStageSequence.circleCount (k + 1)) :=
  D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
    |>.extendedIndexOfLE k.isLt

@[simp] theorem booleanFlipStageSequenceIndexCastSucc_val
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (i : Fin (D.stageEntry (prefixBandChoice k.castSucc)).circleCount) :
    (D.booleanFlipStageSequenceIndexCastSucc k i).1 = i.1 :=
  rfl

@[simp] theorem booleanFlipStageSequenceIndexSucc_val
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (i : Fin (D.stageEntry (prefixBandChoice k.succ)).circleCount) :
    (D.booleanFlipStageSequenceIndexSucc k i).1 = i.1 :=
  rfl

/-- Pointwise circle transport from the native stage entry to natural stage `k`. -/
theorem booleanFlipStageSequence_circle_castSucc
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (i : Fin (D.stageEntry (prefixBandChoice k.castSucc)).circleCount) :
    (D.booleanFlipStageSequence.system k).circle
        (D.booleanFlipStageSequenceIndexCastSucc k i) =
      (D.stageEntry (prefixBandChoice k.castSucc)).system.circle i :=
  D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
    |>.extendedSystem_circle_of_le k.isLt.le i

/-- Pointwise circle transport from the native stage entry to natural stage `k + 1`. -/
theorem booleanFlipStageSequence_circle_succ
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (i : Fin (D.stageEntry (prefixBandChoice k.succ)).circleCount) :
    (D.booleanFlipStageSequence.system (k + 1)).circle
        (D.booleanFlipStageSequenceIndexSucc k i) =
      (D.stageEntry (prefixBandChoice k.succ)).system.circle i :=
  D.toBooleanChoiceRegularStageData.toFiniteRegularSphereSurgeryStageFamily
    |>.extendedSystem_circle_of_le k.isLt i

section BooleanFlipEndpointCircles

variable {F : G.CutCircleTransverseCyclicOrderFamily}
  {b : Fin F.toPairedSeamEnumeration.bandCount}
  {T : F.LiftedGlobalBandTubularChartData b}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData
    T.toGlobalBandTubularChartData.toPairedSeamBandChart pre post}
  {circles : FourPortRawCircleData raw}
  {presentation : FourPortRawSixEdgeBandPresentation circles}

/-- Native endpoint indices at two adjacent Boolean decorations transport to the exact systems
stored by the natural-indexed flip sequence. -/
def endpointSystemCircleDataOfBooleanFlip
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (E : FourPortRawSixEdgeBandPresentation.EndpointSystemCircleData presentation
      (D.stageEntry (prefixBandChoice k.castSucc)).system
      (D.stageEntry (prefixBandChoice k.succ)).system) :
    FourPortRawSixEdgeBandPresentation.EndpointSystemCircleData presentation
      (D.booleanFlipStageSequence.system k)
      (D.booleanFlipStageSequence.system (k + 1)) :=
  E.transport
    (D.booleanFlipStageSequenceIndexCastSucc k)
    (D.booleanFlipStageSequenceIndexSucc k)
    (D.booleanFlipStageSequence_circle_castSucc k)
    (D.booleanFlipStageSequence_circle_succ k)

/-- Native decoration indices construct endpoint-circle data directly on the audited Boolean
flip sequence. -/
def decorationEndpointCircleDataOfBooleanFlip
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount)
    (E :
      letI := D.circleIndex_fintype (prefixBandChoice k.castSucc)
      letI := D.circleIndex_fintype (prefixBandChoice k.succ)
      FourPortRawSixEdgeBandPresentation.DecorationEndpointCircleData presentation
        (D.decoration (prefixBandChoice k.castSucc))
        (D.decoration (prefixBandChoice k.succ))) :
    FourPortRawSixEdgeBandPresentation.EndpointSystemCircleData presentation
      (D.booleanFlipStageSequence.system k)
      (D.booleanFlipStageSequence.system (k + 1)) := by
  letI := D.circleIndex_fintype (prefixBandChoice k.castSucc)
  letI := D.circleIndex_fintype (prefixBandChoice k.succ)
  let native : FourPortRawSixEdgeBandPresentation.EndpointSystemCircleData presentation
      (D.stageEntry (prefixBandChoice k.castSucc)).system
      (D.stageEntry (prefixBandChoice k.succ)).system :=
    E.toEndpointSystemCircleData
      (D.isOpen_insideCell (prefixBandChoice k.castSucc))
      (D.isOpen_insideCell (prefixBandChoice k.succ))
  exact endpointSystemCircleDataOfBooleanFlip D k native

end BooleanFlipEndpointCircles

/-- The parity stage at `k` is the parity stage of the corresponding native decoration. -/
theorem booleanFlipStageSequence_parityStage_castSucc
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    D.booleanFlipStageSequence.parityStage k =
      (D.stageEntry (prefixBandChoice k.castSucc)).parityStage := by
  rw [booleanFlipStageSequence,
    FiniteRegularSphereSurgeryStageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage
      _ k.isLt.le]
  rfl

/-- The parity stage at `k + 1` is the parity stage after flipping band `k`. -/
theorem booleanFlipStageSequence_parityStage_succ
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (k : Fin pairing.bandCount) :
    D.booleanFlipStageSequence.parityStage (k + 1) =
      (D.stageEntry (prefixBandChoice k.succ)).parityStage := by
  have hk : k.1 + 1 ≤ pairing.bandCount := k.isLt
  rw [booleanFlipStageSequence,
    FiniteRegularSphereSurgeryStageFamily.toFiniteRegularSphereSurgeryStageSequence_parityStage
      _ hk]
  rfl

/-- Honest geometric and native-index data for one adjacent flip in the canonical Boolean
sequence.  The corresponding natural-stage endpoint indices are derived rather than assumed. -/
structure BooleanFlipIndexedQuadraticStageSideCoverData
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (hzero : D.booleanFlipStageSequence.AllInessential)
    (k : Fin pairing.bandCount) where
  order : G.CutCircleTransverseCyclicOrderFamily
  band : Fin order.toPairedSeamEnumeration.bandCount
  chart : order.LiftedGlobalBandTubularChartData band
  raw : FourPortRawEndpointData chart.toGlobalBandTubularChartData.toPairedSeamBandChart
    (D.booleanFlipStageSequence.parityStage k)
    (D.booleanFlipStageSequence.parityStage (k + 1))
  circles : FourPortRawCircleData raw
  presentation : FourPortRawSixEdgeBandPresentation circles
  endpointDecoration :
    letI := D.circleIndex_fintype (prefixBandChoice k.castSucc)
    letI := D.circleIndex_fintype (prefixBandChoice k.succ)
    FourPortRawSixEdgeBandPresentation.DecorationEndpointCircleData presentation
      (D.decoration (prefixBandChoice k.castSucc))
      (D.decoration (prefixBandChoice k.succ))
  endpointLabels : FourPortRawSixEdgeBandPresentation.QuadraticEndpointLabelData
    (pre := D.booleanFlipStageSequence.parityStage k)
    (post := D.booleanFlipStageSequence.parityStage (k + 1)) chart

namespace BooleanFlipIndexedQuadraticStageSideCoverData

variable {D : BooleanChoicePairedBandRegularStageData (C := realization)}
  {hzero : D.booleanFlipStageSequence.AllInessential}
  {k : Fin pairing.bandCount}

/-- One native Boolean-flip package constructs the indexed quadratic package for the exact
natural-numbered transition. -/
def toIndexedQuadraticFourPortStageSideCoverData
    (M : BooleanFlipIndexedQuadraticStageSideCoverData D hzero k) :
    IndexedQuadraticFourPortStageSideCoverData D.booleanFlipStageSequence hzero k k.isLt := by
  letI := D.circleIndex_fintype (prefixBandChoice k.castSucc)
  letI := D.circleIndex_fintype (prefixBandChoice k.succ)
  exact {
    frame := frame
    center := c
    outerScale := R
    cutHeight := d
    outerIndex := outerIndex
    cutIndex := cutIndex
    barrier := G
    order := M.order
    band := M.band
    chart := M.chart
    raw := M.raw
    circles := M.circles
    presentation := M.presentation
    endpointCircles := decorationEndpointCircleDataOfBooleanFlip D k M.endpointDecoration
    endpointLabels := M.endpointLabels }

end BooleanFlipIndexedQuadraticStageSideCoverData

/-- Native indexed quadratic geometry at every flip of the canonical Boolean sequence. -/
structure FiniteBooleanFlipIndexedQuadraticStageSideCoverData
    (D : BooleanChoicePairedBandRegularStageData (C := realization))
    (hzero : D.booleanFlipStageSequence.AllInessential) : Prop where
  move : ∀ k : Fin pairing.bandCount,
    Nonempty (BooleanFlipIndexedQuadraticStageSideCoverData D hzero k)

namespace FiniteBooleanFlipIndexedQuadraticStageSideCoverData

variable {D : BooleanChoicePairedBandRegularStageData (C := realization)}
  {hzero : D.booleanFlipStageSequence.AllInessential}

/-- The native per-flip packages assemble into the finite indexed quadratic family. -/
theorem toFiniteIndexedQuadraticFourPortStageSideCoverData
    (M : FiniteBooleanFlipIndexedQuadraticStageSideCoverData D hzero) :
    FiniteIndexedQuadraticFourPortStageSideCoverData D.booleanFlipStageSequence hzero where
  move n hn := by
    let k : Fin pairing.bandCount := ⟨n, by simpa using hn⟩
    simpa [k] using (M.move k).map fun X ↦
      X.toIndexedQuadraticFourPortStageSideCoverData

/-- The native per-flip packages provide the quadratic family consumed by the global axis
integration. -/
theorem toFiniteQuadraticFourPortStageSideCoverData
    (M : FiniteBooleanFlipIndexedQuadraticStageSideCoverData D hzero) :
    FiniteQuadraticFourPortStageSideCoverData D.booleanFlipStageSequence hzero :=
  M.toFiniteIndexedQuadraticFourPortStageSideCoverData
    |>.toFiniteQuadraticFourPortStageSideCoverData

end FiniteBooleanFlipIndexedQuadraticStageSideCoverData

end PairedBandMovingSphereCollarData.BooleanChoicePairedBandRegularStageData
end Submission.Topology
