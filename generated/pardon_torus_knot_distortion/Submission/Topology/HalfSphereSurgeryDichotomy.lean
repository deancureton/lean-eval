import Submission.Topology.FinitePunctureCarrierPushout
import Submission.Topology.FinitePunctureConnectivity
import Submission.Topology.InessentialTorusCircleDisk
import Submission.Topology.InnermostCircleSurgery
import Submission.Topology.TorusDiskPuncture

/-!
# The abstract topology of a half-sphere surgery

This module isolates the honest topological data used when an outer sphere is changed, through
Pardon's two-surgery, into the two sphere boundaries of a double bubble.  It intentionally does
not replace the one-parameter surgery by two disjoint rounded endpoint spheres: doing so creates
a third thin region in which the genus-bearing component could lie.

At one elementary surgery event the transported torus meets the moving sphere in finitely many
pairwise-disjoint circles.  An essential circle feeds the existing innermost-circle surgery
contract.  If every circle is inessential, maximal torus-side filling disks are disjoint.  The
finite radial pushout gives a based rank-two carrier in their complement, and connectedness of
that complement locates the whole carrier component in one cell of the exact surgery partition.
The exterior cell is ruled out by the incoming based carrier: otherwise both incoming loops are
contained in inessential torus disks and hence have zero winding.

The genuinely geometric input left in the structures below is explicit: the topological sphere,
the exact cell partition, maximal disk nesting, a surjective connected finite pushout, and the
embedded surgery disks.  No carrier alternative is a structure field.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-! ## Embedded sphere boundaries and finite intersection systems -/

/-- A topological two-sphere embedded in ambient three-space. -/
structure EmbeddedTopologicalSphereInR3 where
  parametrization : Metric.sphere (0 : R3) 1 → R3
  isEmbedding : IsEmbedding parametrization

namespace EmbeddedTopologicalSphereInR3

/-- The ambient carrier of an embedded topological sphere. -/
def carrier (S : EmbeddedTopologicalSphereInR3) : Set R3 :=
  Set.range S.parametrization

theorem isCompact_carrier (S : EmbeddedTopologicalSphereInR3) :
    IsCompact S.carrier :=
  isCompact_range S.isEmbedding.continuous

theorem isClosed_carrier (S : EmbeddedTopologicalSphereInR3) :
    IsClosed S.carrier :=
  S.isCompact_carrier.isClosed

end EmbeddedTopologicalSphereInR3

/-- Finite circle data at one regular time of the genuine sphere-surgery family.

`insideCell` is the parity-selected side of the moving sphere.  The `eventRegion` contains every
intersection circle, so an essential compression retaining one of these parametrized boundaries
is automatically covered by the selected outer/cutting events. -/
structure FiniteSphereSurgeryIntersectionSystem
    (Phi : AmbientIsotopy) (ι : Type*) [Fintype ι] where
  sphere : EmbeddedTopologicalSphereInR3
  insideCell : Set R3
  sphere_is_boundary : sphere.carrier = frontier insideCell
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  intersection_exact : sphere.carrier ∩ transportedTorus Phi =
    ⋃ i, Set.range (circle i).circle
  sphereDisk : ι → BoundaryParametrizedEmbeddedDiskInR3
  sphereDisk_mem : ∀ i, Set.range (sphereDisk i).disk ⊆ sphere.carrier
  sphereDisk_boundary : ∀ i t,
    (sphereDisk i).disk (unitDiskBoundary t) = (circle i).windingLoop.curve t
  eventRegion : Set R3
  circle_mem_event : ∀ i t, ((circle i).windingLoop.curve t : R3) ∈ eventRegion

namespace FiniteSphereSurgeryIntersectionSystem

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]

/-- All regular intersection circles at a stage are inessential on the transported torus. -/
def AllInessential (S : FiniteSphereSurgeryIntersectionSystem Phi ι) : Prop :=
  ∀ i, (S.circle i).windingLoop.windingPair = (0, 0)

/-- The torus-side Schoenflies disk selected for an inessential stage circle. -/
def torusDisk (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    InessentialTorusCircleDisk Phi (S.circle i) :=
  inessentialTorusCircleDisk (S.circle i) (hzero i)

/-- The chosen torus-side disk as a map into the transported-torus subtype. -/
def torusDiskMap (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) (z : ClosedUnitDisk) :
    transportedTorus Phi :=
  ⟨(S.torusDisk hzero i).disk z,
    (S.torusDisk hzero i).range_subset ⟨z, rfl⟩⟩

theorem continuous_torusDiskMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    Continuous (S.torusDiskMap hzero i) :=
  (S.torusDisk hzero i).isEmbedding.continuous.subtype_mk _

theorem injective_torusDiskMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    Function.Injective (S.torusDiskMap hzero i) := by
  intro z w hzw
  exact (S.torusDisk hzero i).isEmbedding.injective (congrArg Subtype.val hzw)

theorem isEmbedding_torusDiskMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    IsEmbedding (S.torusDiskMap hzero i) :=
  ((S.continuous_torusDiskMap hzero i).isClosedEmbedding
    (S.injective_torusDiskMap hzero i)).isEmbedding

/-- The boundary circle lies in its chosen torus-side filling disk. -/
theorem circle_range_subset_torusDiskMap_range
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    Set.range (fun t ↦ (S.circle i).windingLoop.curve t) ⊆
      Set.range (S.torusDiskMap hzero i) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨unitDiskBoundary t, ?_⟩
  apply Subtype.ext
  exact (S.torusDisk hzero i).boundary t

end FiniteSphereSurgeryIntersectionSystem

/-! ## Essential-circle surgery with retained event coverage -/

/-- The existing finite innermost-circle surgery contract, tied to a specified circle of a
sphere-surgery stage.  Equality of parametrized loops ensures that event coverage survives every
replacement surgery. -/
structure EssentialSphereCircleSurgeryData
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι) (i : ι) where
  system : FinitePlaneDiskTorusCircleSystem Phi ι
  innermost : system.InnermostEssential i
  boundary_eq : (system.circle i).windingLoop = (S.circle i).windingLoop
  surgery : FiniteInnermostCircleSurgeryContract Phi ι system

/-- A compression whose retained boundary lies in the selected geometric event region. -/
structure EventCoveredCompressingDisk
    {Phi : AmbientIsotopy} (eventRegion : Set R3) where
  disk : GeneralCompressingDiskWitness Phi
  boundary_mem_event : ∀ t, (disk.boundaryLoop.curve t : R3) ∈ eventRegion

namespace EssentialSphereCircleSurgeryData

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι} {i : ι}

/-- An essential stage circle and its explicit innermost-surgery data produce an event-covered
general compression. -/
theorem exists_eventCoveredCompressingDisk
    (G : EssentialSphereCircleSurgeryData S i) :
    Nonempty (EventCoveredCompressingDisk (Phi := Phi) S.eventRegion) := by
  obtain ⟨D, hD⟩ :=
    G.surgery.exists_generalCompressingDiskWitness_with_boundary i G.innermost
  refine ⟨⟨D, ?_⟩⟩
  intro t
  rw [hD, G.boundary_eq]
  exact S.circle_mem_event i t

end EssentialSphereCircleSurgeryData

/-! ## Maximal inessential torus disks and the exact elementary cell partition -/

/-- Maximal disjoint torus-side disks at an all-inessential surgery stage.

Every nonmaximal disk is nested in a selected maximal disk.  The complement is required to be
connected; in the concrete construction this follows from the finite sequential radial pushout
being onto and from connectedness of the finite-point complement. -/
structure MaximalInessentialTorusDiskFamily
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) where
  maximal : Finset ι
  disks_pairwise_disjoint : ∀ {i}, i ∈ maximal → ∀ {j}, j ∈ maximal → i ≠ j →
    Disjoint (Set.range (S.torusDiskMap hzero i))
      (Set.range (S.torusDiskMap hzero j))
  every_disk_nested : ∀ i, ∃ j ∈ maximal,
    Set.range (S.torusDiskMap hzero i) ⊆
      Set.range (S.torusDiskMap hzero j)

namespace MaximalInessentialTorusDiskFamily

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}

/-- Union of the selected maximal torus-side disks. -/
def diskUnion (M : MaximalInessentialTorusDiskFamily S hzero) :
    Set (transportedTorus Phi) :=
  ⋃ i ∈ M.maximal, Set.range (S.torusDiskMap hzero i)

/-- Complement of the selected maximal disk union. -/
def diskComplement (M : MaximalInessentialTorusDiskFamily S hzero) :
    Set (transportedTorus Phi) :=
  M.diskUnionᶜ

/-- Product-torus coordinates of the canonical center of each selected maximal disk. -/
def centers (M : MaximalInessentialTorusDiskFamily S hzero)
    (i : M.maximal) : Circle × Circle :=
  (transportedTorusHomeomorph Phi).symm
    ((S.circle i.1).zeroWindingTorusDiskCenter (hzero i.1))

/-- A finite radial pushout onto the maximal-disk complement.  Connectedness of the finite-point
source is unconditional by `transportedFinitePointComplement_isConnected`, so surjectivity is
the only extra field needed to prove connectedness of the disk complement. -/
structure ConnectedPushoutData
    (M : MaximalInessentialTorusDiskFamily S hzero) where
  pushout : FinitePuncturePushoutData Phi M.centers M.diskComplement
  push_surjective : ∀ y : M.diskComplement, ∃ x,
    pushout.push x = y.1

namespace ConnectedPushoutData

/-- The pushout, bundled with its target-membership proof. -/
def targetPush (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData)
    (x : transportedFinitePointComplement Phi M.centers) : M.diskComplement :=
  ⟨P.pushout.push x, P.pushout.push_mem x⟩

theorem continuous_targetPush (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData) : Continuous (targetPush M P) :=
  P.pushout.continuous_push.subtype_mk _

theorem surjective_targetPush (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData) : Function.Surjective (targetPush M P) := by
  intro y
  obtain ⟨x, hx⟩ := P.push_surjective y
  exact ⟨x, Subtype.ext hx⟩

/-- Surjectivity transports finite-point connectedness to the maximal-disk complement. -/
theorem complement_isConnected (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData) : IsConnected M.diskComplement := by
  have hrange : Set.range (targetPush M P) =
      (Set.univ : Set M.diskComplement) :=
    Set.range_eq_univ.mpr (surjective_targetPush M P)
  have htarget : IsConnected (Set.univ : Set M.diskComplement) := by
    rw [← hrange]
    exact (transportedFinitePointComplement_isConnected M.centers).image (targetPush M P)
      (continuous_targetPush M P).continuousOn
  simpa using htarget.image ((↑) : M.diskComplement → transportedTorus Phi)
    continuous_subtype_val.continuousOn

end ConnectedPushoutData

theorem circle_range_subset_diskUnion
    (M : MaximalInessentialTorusDiskFamily S hzero) (i : ι) :
    Set.range (fun t ↦ (S.circle i).windingLoop.curve t) ⊆ M.diskUnion := by
  obtain ⟨j, hj, hij⟩ := M.every_disk_nested i
  exact (S.circle_range_subset_torusDiskMap_range hzero i).trans <|
    hij.trans (Set.subset_iUnion_of_subset j <|
      Set.subset_iUnion_of_subset hj Subset.rfl)

end MaximalInessentialTorusDiskFamily

/-! ## The elementary one-parameter surgery event -/

/-- Exact surface-cell data for one elementary event in the genuine sphere-surgery family.

The three open surface cells are the two parity-interior children and the exterior.  Their union
together with the moving-sphere barrier is all of the transported torus.  This exact partition,
rather than two independently rounded endpoint spheres, rules out an unaccounted thin gap. -/
structure ElementaryHalfSphereSurgeryEvent
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι) where
  parentPart : Set (transportedTorus Phi)
  lowerPart : Set (transportedTorus Phi)
  upperPart : Set (transportedTorus Phi)
  exteriorPart : Set (transportedTorus Phi)
  isOpen_lowerPart : IsOpen lowerPart
  isOpen_upperPart : IsOpen upperPart
  isOpen_exteriorPart : IsOpen exteriorPart
  lower_disjoint_upper : Disjoint lowerPart upperPart
  lower_disjoint_exterior : Disjoint lowerPart exteriorPart
  upper_disjoint_exterior : Disjoint upperPart exteriorPart
  lower_subset_parent : lowerPart ⊆ parentPart
  upper_subset_parent : upperPart ⊆ parentPart
  parent_disjoint_exterior : Disjoint parentPart exteriorPart
  surface_partition : Set.univ =
    lowerPart ∪ upperPart ∪ exteriorPart ∪
      ⋃ i, Set.range (fun t ↦ (S.circle i).windingLoop.curve t)

/-- Endpoint geometry of the literal double bubble, tied to one elementary event of the genuine
two-surgery trace.  The lower and upper boundaries are kept separate; no false cross-family
disjointness is imposed along their common cutting disk. -/
structure LiteralHalfSphereSplitGeometry
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (E : ElementaryHalfSphereSurgeryEvent S) where
  outerBody : Set R3
  lowerBody : Set R3
  upperBody : Set R3
  cuttingDisk : Set R3
  outerBoundary : EmbeddedTopologicalSphereInR3
  lowerBoundary : EmbeddedTopologicalSphereInR3
  upperBoundary : EmbeddedTopologicalSphereInR3
  outerBoundary_exact : outerBoundary.carrier = frontier outerBody
  lowerBoundary_exact : lowerBoundary.carrier = frontier lowerBody
  upperBoundary_exact : upperBoundary.carrier = frontier upperBody
  body_split_exact : outerBody = lowerBody ∪ upperBody
  body_overlap_exact : lowerBody ∩ upperBody = cuttingDisk
  parentPart_eq : E.parentPart = transportedTorusPart Phi outerBody
  lowerPart_eq : E.lowerPart = transportedTorusPart Phi (interior lowerBody)
  upperPart_eq : E.upperPart = transportedTorusPart Phi (interior upperBody)
  exteriorPart_eq : E.exteriorPart = transportedTorusPart Phi outerBodyᶜ

/-! ## Connected sets in finite disjoint closed families -/

private theorem IsPreconnected.subset_or_subset_closed
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v)
    (huv : Disjoint u v) (hsub : s ⊆ u ∪ v) :
    s ⊆ u ∨ s ⊆ v := by
  by_contra h
  push_neg at h
  obtain ⟨x, hxs, hxu⟩ := h.1
  obtain ⟨y, hys, hyv⟩ := h.2
  have hxv : x ∈ v := (hsub hxs).resolve_left hxu
  have hyu : y ∈ u := (hsub hys).resolve_right hyv
  obtain ⟨z, hzs, hzu, hzv⟩ :=
    isPreconnected_closed_iff.mp hs u v hu hv hsub
      ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  exact Set.disjoint_left.mp huv hzu hzv

/-- A connected nonempty set covered by finitely many pairwise-disjoint closed sets is contained
in one member of the family. -/
private theorem IsConnected.subset_one_of_subset_biUnion_pairwise_disjoint_closed
    {X κ : Type*} [TopologicalSpace X] [DecidableEq κ]
    {s : Set X} (hs : IsConnected s) (I : Finset κ) (u : κ → Set X)
    (hclosed : ∀ i ∈ I, IsClosed (u i))
    (hdisjoint : ∀ {i}, i ∈ I → ∀ {j}, j ∈ I → i ≠ j →
      Disjoint (u i) (u j))
    (hsub : s ⊆ ⋃ i ∈ I, u i) :
    ∃ i ∈ I, s ⊆ u i := by
  induction I using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hs.nonempty
      simpa using hsub hx
  | @insert i I hi ih =>
      let rest : Set X := ⋃ j ∈ I, u j
      have hrestClosed : IsClosed rest :=
        isClosed_biUnion_finset fun j hj ↦ hclosed j (Finset.mem_insert_of_mem hj)
      have hiClosed : IsClosed (u i) := hclosed i (Finset.mem_insert_self i I)
      have hiRest : Disjoint (u i) rest := by
        rw [Set.disjoint_left]
        intro x hxi hxrest
        simp only [rest, Set.mem_iUnion] at hxrest
        obtain ⟨j, hxrest⟩ := hxrest
        obtain ⟨hj, hxj⟩ := hxrest
        exact Set.disjoint_left.mp
          (hdisjoint (Finset.mem_insert_self i I)
            (Finset.mem_insert_of_mem hj) (Ne.symm <| fun hji ↦ hi (hji ▸ hj))) hxi hxj
      have hcover : s ⊆ u i ∪ rest := by
        simpa only [Finset.set_biUnion_insert] using hsub
      rcases hs.isPreconnected.subset_or_subset_closed hiClosed hrestClosed hiRest hcover with
        hsi | hsrest
      · exact ⟨i, Finset.mem_insert_self i I, hsi⟩
      · obtain ⟨j, hj, hsj⟩ := ih
          (fun j hj ↦ hclosed j (Finset.mem_insert_of_mem hj))
          (fun hj hk hjk ↦ hdisjoint
            (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk)
          hsrest
        exact ⟨j, Finset.mem_insert_of_mem hj, hsj⟩

/-! ## Loops contained in an embedded torus disk have zero winding -/

namespace FiniteSphereSurgeryIntersectionSystem

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}

/-- A loop bundled in the range of one chosen torus-side disk. -/
def torusDiskRangeCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    ℝ → Set.range (S.torusDiskMap hzero i) :=
  fun t ↦ ⟨L.curve t, hsub ⟨t, rfl⟩⟩

theorem continuous_torusDiskRangeCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Continuous (S.torusDiskRangeCurve i L hsub) :=
  L.continuous_curve.subtype_mk _

theorem periodic_torusDiskRangeCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Function.Periodic (S.torusDiskRangeCurve i L hsub) (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  exact L.periodic_curve t

/-- The unique disk coordinate of a loop contained in an embedded torus-side disk. -/
def torusDiskFactorCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    ℝ → ClosedUnitDisk :=
  fun t ↦ (S.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm
    (S.torusDiskRangeCurve i L hsub t)

theorem continuous_torusDiskFactorCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Continuous (S.torusDiskFactorCurve i L hsub) :=
  (S.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm.continuous.comp
    (S.continuous_torusDiskRangeCurve i L hsub)

theorem periodic_torusDiskFactorCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Function.Periodic (S.torusDiskFactorCurve i L hsub) (2 * Real.pi) := by
  intro t
  exact congrArg (S.isEmbedding_torusDiskMap hzero i).toHomeomorph.symm
    (S.periodic_torusDiskRangeCurve i L hsub t)

theorem torusDiskMap_factorCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) (t : ℝ) :
    S.torusDiskMap hzero i (S.torusDiskFactorCurve i L hsub t) = L.curve t :=
  congrArg Subtype.val <|
    (S.isEmbedding_torusDiskMap hzero i).toHomeomorph.apply_symm_apply
      (S.torusDiskRangeCurve i L hsub t)

/-- Clamp a real homotopy parameter to the unit interval. -/
def diskContractionParameter (s : ℝ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one s

/-- Radially contract the factored loop to the center of its torus-side disk. -/
def contractedDiskPoint {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i))
    (a t : ℝ) : ClosedUnitDisk := by
  let r : ℝ := S.diskContractionParameter a
  let z : ℂ := (1 - r) • (S.torusDiskFactorCurve i L hsub t : ℂ)
  refine ⟨z, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hr0 : 0 ≤ 1 - r := by
    exact sub_nonneg.mpr (S.diskContractionParameter a).property.2
  have hr1 : 1 - r ≤ 1 := by
    linarith [(S.diskContractionParameter a).property.1]
  have hz := (S.torusDiskFactorCurve i L hsub t).property
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  change ‖(1 - r) • (S.torusDiskFactorCurve i L hsub t : ℂ)‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left hz hr0).trans <| by simpa using hr1

theorem continuous_contractedDiskPoint {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Continuous (Function.uncurry (S.contractedDiskPoint i L hsub)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst))).smul
    ((continuous_subtype_val.comp (S.continuous_torusDiskFactorCurve i L hsub)).comp
      continuous_snd))

/-- The contraction, mapped back into the transported torus. -/
def contractedTorusDiskCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i))
    (a t : ℝ) : transportedTorus Phi :=
  S.torusDiskMap hzero i (S.contractedDiskPoint i L hsub a t)

theorem continuous_contractedTorusDiskCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    Continuous (Function.uncurry (S.contractedTorusDiskCurve i L hsub)) :=
  (S.continuous_torusDiskMap hzero i).comp
    (S.continuous_contractedDiskPoint i L hsub)

theorem periodic_contractedTorusDiskCurve {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) (a : ℝ) :
    Function.Periodic (S.contractedTorusDiskCurve i L hsub a) (2 * Real.pi) := by
  intro t
  apply congrArg (S.torusDiskMap hzero i)
  apply Subtype.ext
  exact congrArg (fun z : ClosedUnitDisk ↦
    (1 - (S.diskContractionParameter a : ℝ)) • (z : ℂ))
    (S.periodic_torusDiskFactorCurve i L hsub t)

theorem contractedTorusDiskCurve_zero {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) (t : ℝ) :
    S.contractedTorusDiskCurve i L hsub 0 t = L.curve t := by
  rw [contractedTorusDiskCurve]
  have hparameter : S.diskContractionParameter 0 =
      ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ := Set.projIcc_left
  rw [contractedDiskPoint, hparameter]
  simp only [Set.Icc.coe_zero, sub_zero, one_smul]
  exact S.torusDiskMap_factorCurve i L hsub t

theorem contractedTorusDiskCurve_one {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) (t : ℝ) :
    S.contractedTorusDiskCurve i L hsub 1 t = S.torusDiskMap hzero i 0 := by
  rw [contractedTorusDiskCurve]
  have hparameter : S.diskContractionParameter 1 =
      ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ := Set.projIcc_right
  rw [contractedDiskPoint, hparameter]
  simp

/-- The explicit zero-winding lift of a constant transported-torus loop. -/
def constantTransportedTorusLoopLift (x : transportedTorus Phi) :
    TorusLoopLift (transportedLoopCoordinates Phi (fun _ ↦ x)) where
  first := {
    angle := fun _ ↦ (((transportedTorusHomeomorph Phi).symm x).1 : ℂ).arg
    continuous_angle := continuous_const
    exp_angle := fun _ ↦ by
      simp [transportedLoopCoordinates, Circle.exp_arg]
    winding := 0
    angle_add_period := fun _ ↦ by simp
  }
  second := {
    angle := fun _ ↦ (((transportedTorusHomeomorph Phi).symm x).2 : ℂ).arg
    continuous_angle := continuous_const
    exp_angle := fun _ ↦ by
      simp [transportedLoopCoordinates, Circle.exp_arg]
    winding := 0
    angle_add_period := fun _ ↦ by simp
  }

/-- A loop lying in one embedded torus-side disk has winding pair `(0, 0)`. -/
theorem windingPair_eq_zero_of_range_subset_torusDisk {s : Set (transportedTorus Phi)}
    (i : ι) (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i)) :
    L.windingPair = (0, 0) := by
  let x := S.torusDiskMap hzero i 0
  have hhomotopy : PeriodicTorusLoopHomotopy
      (transportedLoopCoordinates Phi L.curve)
      (transportedLoopCoordinates Phi (fun _ ↦ x)) := {
    homotopy := fun a t ↦ transportedLoopCoordinates Phi
      (S.contractedTorusDiskCurve i L hsub a) t
    continuous_homotopy :=
      (transportedTorusHomeomorph Phi).symm.continuous.comp
        (S.continuous_contractedTorusDiskCurve i L hsub)
    periodic_homotopy := fun a t ↦ congrArg
      (transportedTorusHomeomorph Phi).symm
      (S.periodic_contractedTorusDiskCurve i L hsub a t)
    homotopy_zero := by
      funext t
      exact congrArg (transportedTorusHomeomorph Phi).symm
        (S.contractedTorusDiskCurve_zero i L hsub t)
    homotopy_one := by
      funext t
      exact congrArg (transportedTorusHomeomorph Phi).symm
        (S.contractedTorusDiskCurve_one i L hsub t)
  }
  have heq := TorusLoopLift.windingPair_eq_of_periodicHomotopy hhomotopy L.lift
    (constantTransportedTorusLoopLift x)
  simpa [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair,
    constantTransportedTorusLoopLift] using heq

end FiniteSphereSurgeryIntersectionSystem

/-! ## Carrier propagation through one elementary inessential event -/

namespace MaximalInessentialTorusDiskFamily

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}

theorem isClosed_torusDiskMap_range
    (M : MaximalInessentialTorusDiskFamily S hzero) (i : ι) :
    IsClosed (Set.range (S.torusDiskMap hzero i)) :=
  (isCompact_range (S.continuous_torusDiskMap hzero i)).isClosed

/-- A connected loop range covered by maximal disjoint torus disks lies in one of those disks. -/
theorem connected_range_subset_one_maximalDisk
    (M : MaximalInessentialTorusDiskFamily S hzero)
    {s : Set (transportedTorus Phi)} (L : TransportedWindingLoop Phi s)
    (hsub : Set.range L.curve ⊆ M.diskUnion) :
    ∃ i ∈ M.maximal,
      Set.range L.curve ⊆ Set.range (S.torusDiskMap hzero i) := by
  exact (isConnected_range L.continuous_curve)
    .subset_one_of_subset_biUnion_pairwise_disjoint_closed
      M.maximal (fun i ↦ Set.range (S.torusDiskMap hzero i))
      (fun i _ ↦ M.isClosed_torusDiskMap_range i)
      M.disks_pairwise_disjoint hsub

end MaximalInessentialTorusDiskFamily

namespace ElementaryHalfSphereSurgeryEvent

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}

/-- Removing all maximal inessential torus disks removes the entire moving-sphere barrier, so
the remaining surface lies in the two child cells or the exterior cell. -/
theorem diskComplement_subset_cells
    (E : ElementaryHalfSphereSurgeryEvent S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    M.diskComplement ⊆ E.lowerPart ∪ E.upperPart ∪ E.exteriorPart := by
  intro x hx
  have hxuniv : x ∈ (Set.univ : Set (transportedTorus Phi)) := Set.mem_univ x
  rw [E.surface_partition] at hxuniv
  rcases hxuniv with hxcell | hxbarrier
  · exact hxcell
  · simp only [Set.mem_iUnion] at hxbarrier
    obtain ⟨i, hxbarrier⟩ := hxbarrier
    exact False.elim <| hx <| M.circle_range_subset_diskUnion i hxbarrier

private theorem lower_disjoint_upper_union_exterior
    (E : ElementaryHalfSphereSurgeryEvent S) :
    Disjoint E.lowerPart (E.upperPart ∪ E.exteriorPart) := by
  rw [Set.disjoint_left]
  intro x hxl hx
  rcases hx with hxu | hxe
  · exact Set.disjoint_left.mp E.lower_disjoint_upper hxl hxu
  · exact Set.disjoint_left.mp E.lower_disjoint_exterior hxl hxe

/-- Connectedness locates the maximal-disk complement in exactly one of the three surgery
cells. -/
theorem diskComplement_subset_lower_or_upper_or_exterior
    (E : ElementaryHalfSphereSurgeryEvent S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hconnected : IsConnected M.diskComplement) :
    M.diskComplement ⊆ E.lowerPart ∨
      M.diskComplement ⊆ E.upperPart ∨
        M.diskComplement ⊆ E.exteriorPart := by
  have hfirst := hconnected.isPreconnected.subset_or_subset
    E.isOpen_lowerPart (E.isOpen_upperPart.union E.isOpen_exteriorPart)
    E.lower_disjoint_upper_union_exterior (E.diskComplement_subset_cells M)
  rcases hfirst with hlower | hrest
  · exact Or.inl hlower
  · exact Or.inr <| hconnected.isPreconnected.subset_or_subset
      E.isOpen_upperPart E.isOpen_exteriorPart E.upper_disjoint_exterior hrest

/-- If the connected maximal-disk complement were exterior, every incoming-parent point would
lie in a maximal torus disk. -/
theorem parentPart_subset_diskUnion_of_diskComplement_subset_exterior
    (E : ElementaryHalfSphereSurgeryEvent S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hexterior : M.diskComplement ⊆ E.exteriorPart) :
    E.parentPart ⊆ M.diskUnion := by
  intro x hxparent
  by_contra hxdisk
  have hxcomplement : x ∈ M.diskComplement := hxdisk
  exact Set.disjoint_left.mp E.parent_disjoint_exterior hxparent
    (hexterior hxcomplement)

/-- The based rank-two incoming carrier rules out the exterior location.  Both incoming loops
would otherwise be trapped in (possibly different) maximal inessential disks, making both
winding pairs zero and contradicting their nonzero determinant. -/
theorem not_diskComplement_subset_exterior_of_parent_carrier
    (E : ElementaryHalfSphereSurgeryEvent S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart) :
    ¬ M.diskComplement ⊆ E.exteriorPart := by
  intro hexterior
  obtain ⟨W⟩ := hparent
  have hparentDisk := E.parentPart_subset_diskUnion_of_diskComplement_subset_exterior
    M hexterior
  have hfirstRange : Set.range W.first.curve ⊆ M.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hparentDisk (W.first.curve_mem t)
  have hsecondRange : Set.range W.second.curve ⊆ M.diskUnion := by
    rintro _ ⟨t, rfl⟩
    exact hparentDisk (W.second.curve_mem t)
  obtain ⟨i, _hi, hfirstDisk⟩ :=
    M.connected_range_subset_one_maximalDisk W.first hfirstRange
  obtain ⟨j, _hj, hsecondDisk⟩ :=
    M.connected_range_subset_one_maximalDisk W.second hsecondRange
  have hfirstZero := S.windingPair_eq_zero_of_range_subset_torusDisk
    i W.first hfirstDisk
  have hsecondZero := S.windingPair_eq_zero_of_range_subset_torusDisk
    j W.second hsecondDisk
  rw [hfirstZero, hsecondZero] at W.independent
  exact W.independent (by simp [windingDet])

/-- The all-inessential elementary sphere surgery propagates the incoming based carrier into one
of the two parity-interior child cells.  This is the logical heart of the half-sphere argument. -/
theorem carries_lower_or_upper_of_allInessential
    (E : ElementaryHalfSphereSurgeryEvent S)
    (hzero : S.AllInessential)
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart) :
    CarriesBasedLoopTorusGenus Phi E.lowerPart ∨
      CarriesBasedLoopTorusGenus Phi E.upperPart := by
  have hcomplement : CarriesBasedLoopTorusGenus Phi M.diskComplement :=
    carriesBasedLoopTorusGenus_of_finitePuncturePushout P.pushout
  rcases E.diskComplement_subset_lower_or_upper_or_exterior M
      (ConnectedPushoutData.complement_isConnected M P) with
      hlower | hupper | hexterior
  · exact Or.inl (hcomplement.mono hlower)
  · exact Or.inr (hcomplement.mono hupper)
  · exact False.elim <|
      E.not_diskComplement_subset_exterior_of_parent_carrier M hparent hexterior

end ElementaryHalfSphereSurgeryEvent

/-! ## Essential-or-child-carrier dichotomy -/

/-- One regular elementary sphere-surgery event has the exact Pardon alternative.  An essential
circle yields an event-covered compression through the supplied geometric surgery construction;
if all circles are inessential, the connected finite pushout propagates based genus to a child.
The alternative itself is proved here and is not a field of any contract. -/
theorem eventCoveredCompression_or_carries_child
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (E : ElementaryHalfSphereSurgeryEvent S)
    (essentialSurgery : ∀ i, (S.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData S i))
    (inessentialData : ∀ hzero : S.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily S hzero,
        Nonempty M.ConnectedPushoutData)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart) :
    Nonempty (EventCoveredCompressingDisk (Phi := Phi) S.eventRegion) ∨
      CarriesBasedLoopTorusGenus Phi E.lowerPart ∨
        CarriesBasedLoopTorusGenus Phi E.upperPart := by
  by_cases hessential : ∃ i, (S.circle i).Essential
  · obtain ⟨i, hi⟩ := hessential
    obtain ⟨G⟩ := essentialSurgery i hi
    exact Or.inl G.exists_eventCoveredCompressingDisk
  · have hzero : S.AllInessential := by
      intro i
      have hi : ¬ (S.circle i).Essential := fun hi ↦ hessential ⟨i, hi⟩
      exact not_ne_iff.mp (show
        ¬ (S.circle i).windingLoop.windingPair ≠ (0, 0) from hi)
    obtain ⟨M, ⟨P⟩⟩ := inessentialData hzero
    exact Or.inr (E.carries_lower_or_upper_of_allInessential hzero M P hparent)

/-- Adapter to the concrete charged-compression object used by a quantitative application.
Supplying the analytic certificate and finite event injection for every event-covered disk turns
the topological alternative into the exact charged-or-child alternative. -/
theorem chargedCompression_or_carries_child
    {Phi : AmbientIsotopy} {ι Charge : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (E : ElementaryHalfSphereSurgeryEvent S)
    (essentialSurgery : ∀ i, (S.circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData S i))
    (inessentialData : ∀ hzero : S.AllInessential,
      ∃ M : MaximalInessentialTorusDiskFamily S hzero,
        Nonempty M.ConnectedPushoutData)
    (charge : EventCoveredCompressingDisk (Phi := Phi) S.eventRegion → Charge)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart) :
    Nonempty Charge ∨ CarriesBasedLoopTorusGenus Phi E.lowerPart ∨
      CarriesBasedLoopTorusGenus Phi E.upperPart := by
  rcases eventCoveredCompression_or_carries_child S E essentialSurgery
      inessentialData hparent with hcompression | hchild
  · exact Or.inl ⟨charge hcompression.some⟩
  · exact Or.inr hchild

end Submission.Topology
