import Submission.Topology.TransportedTorusRegularLevels
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.LocallyConnected

open Set Topology
open scoped Topology

namespace Submission
namespace SurfaceRegularValue

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Components of compact regular levels

Mathlib supplies the component theory needed after a level is known to be
locally modelled on a line: local connectedness, openness of components, and
finiteness of the component space under compactness.  It does not currently
supply the classification of a compact connected one-manifold as a circle.

There is a second genuine interface boundary here.  A `fundamentalLevelSet` is
cut out using a closed square.  The plane regular-level charts do not by
themselves say that the cuts along the four sides glue to boundaryless line
charts.  Consequently `IsLocallyLineModeled` is recorded explicitly below.
For a torus quotient it is exactly the seam-compatibility statement still
needed; for the literal closed-square intersection it need not hold.
-/

/-- A neighborhood of `x` homeomorphic to an open subset of the real line. -/
structure LocalLineChart (X : Type*) [TopologicalSpace X] (x : X) where
  source : Set X
  target : Set ℝ
  source_open : IsOpen source
  target_open : IsOpen target
  mem_source : x ∈ source
  equiv : source ≃ₜ target

/-- Every point has a neighborhood homeomorphic to an open subset of `ℝ`.
This is the boundaryless topological one-manifold condition used here. -/
def IsLocallyLineModeled (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, Nonempty (LocalLineChart X x)

/-- A space locally modelled on the real line is locally connected. -/
theorem locallyConnectedSpace_of_isLocallyLineModeled
    {X : Type*} [TopologicalSpace X] (hX : IsLocallyLineModeled X) :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hxU
  obtain ⟨C⟩ := hX x
  let _ : LocallyConnectedSpace C.target := C.target_open.locallyConnectedSpace
  let _ : LocallyConnectedSpace C.source := C.equiv.locallyConnectedSpace
  let xC : C.source := ⟨x, C.mem_source⟩
  have hpre : Subtype.val ⁻¹' U ∈ 𝓝 xC :=
    continuousAt_subtype_val.preimage_mem_nhds hxU
  obtain ⟨V, hVU, hVopen, hxV, hVconnected⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (show LocallyConnectedSpace C.source from inferInstance) xC _ hpre
  refine ⟨Subtype.val '' V, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨w, hwV, rfl⟩
    exact hVU hwV
  · exact C.source_open.isOpenEmbedding_subtypeVal.isOpenMap V hVopen
  · exact ⟨xC, hxV, rfl⟩
  · exact hVconnected.image _ continuous_subtype_val.continuousOn

/-- A selected compact level together with the seam-compatible local line
models needed to regard its closed fundamental-domain representative as a
boundaryless one-manifold. -/
structure CompactLocallyLineLevelSelection (f : Plane → ℝ) (a b : ℝ)
    extends CompactRegularLevelSelection f a b where
  locallyLineModeled : IsLocallyLineModeled
    (fundamentalLevelSet f level)

/-- The simultaneous six-face version of `CompactLocallyLineLevelSelection`. -/
structure CompactFacewiseLocallyLineLevelSelection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (a b : ℝ) extends
      CompactFacewiseRegularLevelSelection Phi frame c a b where
  locallyLineModeled : ∀ face : Fin 3 × Bool,
    IsLocallyLineModeled (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) level)

/-- Attach an explicitly proved seam-compatible local-line model to an
existing compact regular-level selection. -/
def CompactRegularLevelSelection.withLocalLineModel
    {f : Plane → ℝ} {a b : ℝ} (S : CompactRegularLevelSelection f a b)
    (hlocal : IsLocallyLineModeled (fundamentalLevelSet f S.level)) :
    CompactLocallyLineLevelSelection f a b where
  __ := S
  locallyLineModeled := hlocal

/-- Attach facewise seam-compatible local-line models to an existing
simultaneous six-face selection. -/
def CompactFacewiseRegularLevelSelection.withLocalLineModels
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
    {a b : ℝ}
    (S : CompactFacewiseRegularLevelSelection Phi frame c a b)
    (hlocal : ∀ face : Fin 3 × Bool,
      IsLocallyLineModeled (fundamentalLevelSet
        (signedOrientedFaceLift Phi frame c face) S.level)) :
    CompactFacewiseLocallyLineLevelSelection Phi frame c a b where
  __ := S
  locallyLineModeled := hlocal

/-- The compact selected level is a compact space in its subtype topology. -/
theorem CompactLocallyLineLevelSelection.compactSpace
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b) :
    CompactSpace (fundamentalLevelSet f S.level) :=
  isCompact_iff_compactSpace.mp S.isCompact

/-- The local line charts give the selected level a locally connected subtype
topology. -/
theorem CompactLocallyLineLevelSelection.locallyConnectedSpace
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b) :
    LocallyConnectedSpace (fundamentalLevelSet f S.level) :=
  locallyConnectedSpace_of_isLocallyLineModeled S.locallyLineModeled

/-- A compact, locally line-modelled selected level has finitely many connected
components. -/
theorem CompactLocallyLineLevelSelection.finite_connectedComponents
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b) :
    Finite (ConnectedComponents (fundamentalLevelSet f S.level)) := by
  let _ : CompactSpace (fundamentalLevelSet f S.level) := S.compactSpace
  let _ : LocallyConnectedSpace (fundamentalLevelSet f S.level) :=
    S.locallyConnectedSpace
  infer_instance

/-- Every connected component of such a selected level is clopen. -/
theorem CompactLocallyLineLevelSelection.isClopen_connectedComponent
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b)
    (x : fundamentalLevelSet f S.level) :
    IsClopen (connectedComponent x) := by
  let _ : LocallyConnectedSpace (fundamentalLevelSet f S.level) :=
    S.locallyConnectedSpace
  exact _root_.isClopen_connectedComponent

/-- Every connected component of such a selected level is compact. -/
theorem CompactLocallyLineLevelSelection.isCompact_connectedComponent
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b)
    (x : fundamentalLevelSet f S.level) :
    IsCompact (connectedComponent x) := by
  let _ : CompactSpace (fundamentalLevelSet f S.level) := S.compactSpace
  exact isClosed_connectedComponent.isCompact

/-- The component represented by a point of the connected-component quotient. -/
def componentPiece {X : Type*} [TopologicalSpace X]
    (c : ConnectedComponents X) : Set X :=
  ConnectedComponents.mk ⁻¹' {c}

/-- The component pieces cover the entire space. -/
theorem iUnion_componentPiece {X : Type*} [TopologicalSpace X] :
    ⋃ c : ConnectedComponents X, componentPiece c = Set.univ := by
  ext x
  simp [componentPiece]

/-- Distinct component pieces are disjoint. -/
theorem pairwise_disjoint_componentPiece
    {X : Type*} [TopologicalSpace X] :
    Pairwise (Function.onFun Disjoint (componentPiece (X := X))) := by
  intro c d hcd
  change Disjoint (componentPiece c) (componentPiece d)
  rw [Set.disjoint_left]
  intro x hxc hxd
  apply hcd
  change ConnectedComponents.mk x = c at hxc
  change ConnectedComponents.mk x = d at hxd
  exact hxc.symm.trans hxd

/-- In a locally connected space, each quotient-indexed component piece is
clopen. -/
theorem isClopen_componentPiece
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (c : ConnectedComponents X) :
    IsClopen (componentPiece c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentPiece, connectedComponents_preimage_singleton]
  exact isClopen_connectedComponent

/-- Each quotient-indexed component piece is connected. -/
theorem isConnected_componentPiece
    {X : Type*} [TopologicalSpace X] (c : ConnectedComponents X) :
    IsConnected (componentPiece c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentPiece, connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- The fully proved finite clopen connected-component decomposition. -/
structure FiniteComponentDecomposition (X : Type*) [TopologicalSpace X] where
  index : Type*
  finite_index : Finite index
  piece : index → Set X
  pairwise_disjoint : Pairwise (Function.onFun Disjoint piece)
  cover : ⋃ i, piece i = Set.univ
  isClopen : ∀ i, IsClopen (piece i)
  isConnected : ∀ i, IsConnected (piece i)

/-- Compact locally connected spaces have their canonical finite clopen
connected-component decomposition. -/
def finiteComponentDecompositionOfCompactLocallyConnected
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] : FiniteComponentDecomposition X where
  index := ConnectedComponents X
  finite_index := inferInstance
  piece := componentPiece
  pairwise_disjoint := pairwise_disjoint_componentPiece
  cover := iUnion_componentPiece
  isClopen := isClopen_componentPiece
  isConnected := isConnected_componentPiece

/-- The canonical finite component decomposition of a compact locally
line-modelled selected level. -/
def CompactLocallyLineLevelSelection.componentDecomposition
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b) :
    FiniteComponentDecomposition (fundamentalLevelSet f S.level) := by
  let _ : CompactSpace (fundamentalLevelSet f S.level) := S.compactSpace
  let _ : LocallyConnectedSpace (fundamentalLevelSet f S.level) :=
    S.locallyConnectedSpace
  exact finiteComponentDecompositionOfCompactLocallyConnected _

/-- The precise remaining global classification input: every connected
component of `X` is homeomorphic to the circle.  This is deliberately data,
not a proposition with a theorem-like name. -/
structure ComponentCircleClassification
    (X : Type*) [TopologicalSpace X] where
  circleEquiv : ∀ c : ConnectedComponents X, Circle ≃ₜ componentPiece c

/-- A finite disjoint union decomposition whose pieces are embedded circles. -/
structure FiniteCircleDecomposition (X : Type*) [TopologicalSpace X]
    extends FiniteComponentDecomposition X where
  circleEquiv : ∀ i, Circle ≃ₜ piece i

/-- The explicit classification input upgrades the canonical component
decomposition to a finite circle decomposition. -/
def finiteCircleDecompositionOfClassification
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] (hcircle : ComponentCircleClassification X) :
    FiniteCircleDecomposition X where
  __ := finiteComponentDecompositionOfCompactLocallyConnected X
  circleEquiv := hcircle.circleEquiv

/-- Once the explicit global circle-classification input is supplied, a
compact locally line-modelled selected level is a finite disjoint union of
circle components. -/
def CompactLocallyLineLevelSelection.circleDecomposition
    {f : Plane → ℝ} {a b : ℝ}
    (S : CompactLocallyLineLevelSelection f a b)
    (hcircle : ComponentCircleClassification
      (fundamentalLevelSet f S.level)) :
    FiniteCircleDecomposition (fundamentalLevelSet f S.level) := by
  let _ : CompactSpace (fundamentalLevelSet f S.level) := S.compactSpace
  let _ : LocallyConnectedSpace (fundamentalLevelSet f S.level) :=
    S.locallyConnectedSpace
  exact finiteCircleDecompositionOfClassification _ hcircle

/-- Each circle parametrization in the classified decomposition is an
embedding into the ambient level subtype. -/
theorem ComponentCircleClassification.isEmbedding
    {X : Type*} [TopologicalSpace X]
    (hcircle : ComponentCircleClassification X)
    (c : ConnectedComponents X) :
    IsEmbedding (fun z : Circle ↦
      ((hcircle.circleEquiv c z : componentPiece c) : X)) :=
  Topology.IsEmbedding.subtypeVal.comp (hcircle.circleEquiv c).isEmbedding

/-- Facewise local-line data yields finite component spaces for every one of
the six selected face levels. -/
theorem CompactFacewiseLocallyLineLevelSelection.finite_connectedComponents
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
    {a b : ℝ}
    (S : CompactFacewiseLocallyLineLevelSelection Phi frame c a b)
    (face : Fin 3 × Bool) :
    Finite (ConnectedComponents (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level)) := by
  let _ : CompactSpace (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level) :=
    isCompact_iff_compactSpace.mp (S.isCompact face)
  let _ : LocallyConnectedSpace (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level) :=
    locallyConnectedSpace_of_isLocallyLineModeled
      (S.locallyLineModeled face)
  infer_instance

/-- Each selected face level has its canonical finite clopen connected
component decomposition. -/
def CompactFacewiseLocallyLineLevelSelection.componentDecomposition
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
    {a b : ℝ}
    (S : CompactFacewiseLocallyLineLevelSelection Phi frame c a b)
    (face : Fin 3 × Bool) :
    FiniteComponentDecomposition (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level) := by
  let _ : CompactSpace (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level) :=
    isCompact_iff_compactSpace.mp (S.isCompact face)
  let _ : LocallyConnectedSpace (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) S.level) :=
    locallyConnectedSpace_of_isLocallyLineModeled
      (S.locallyLineModeled face)
  exact finiteComponentDecompositionOfCompactLocallyConnected _

end
end SurfaceRegularValue
end Submission
