import Submission.Topology.PairedBandMovingSphere
import Submission.Topology.ResolvedStageLogicalAdapters
import Submission.Topology.SuperellipsoidConvexSpheres

/-!
# Global attachment for the singular superellipsoid three-page

The convex superellipsoid supplies one outer sphere and two literal truncated-frontier spheres.
The latter meet along the cutting disk, so they describe the singular three-page limit rather
than a regular pairwise-disjoint sphere family.

This file isolates the honest global regularization input.  Two rounded child spheres bound
disjoint open child regions and agree with the outer body away from one global neck-pinch
support.  That support is deliberately independent of the local torus-band supports used to
change four-port pairings.  Consequently the induced parity transition is constructed directly;
it uses neither a common singular source parametrization nor a `sourceImage_eq` premise.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus
open PairedBandMovingSphereCollarData

/-! ## Regular parity stages from open ambient regions -/

namespace FiniteEmbeddedTopologicalSphereFamilyInR3

/-- Regard one embedded sphere as a one-component sphere family. -/
def singleton (S : EmbeddedTopologicalSphereInR3) :
    FiniteEmbeddedTopologicalSphereFamilyInR3 where
  count := 1
  sphere := fun _ ↦ S
  pairwise_disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))

@[simp] theorem singleton_carrier (S : EmbeddedTopologicalSphereInR3) :
    (singleton S).carrier = S.carrier := by
  unfold carrier singleton
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, hx⟩ := hx
    exact hx
  · intro hx
    exact Set.mem_iUnion.mpr ⟨0, hx⟩

end FiniteEmbeddedTopologicalSphereFamilyInR3

namespace RegularSphereFamilyParityStage

/-- An open ambient region whose frontier is a finite embedded sphere family gives an honest
parity stage on the transported torus.  The exterior is the complement of the closure, so the
frontier accounts for every remaining point. -/
def ofOpenRegion (Phi : AmbientIsotopy)
    (family : FiniteEmbeddedTopologicalSphereFamilyInR3) (region : Set R3)
    (isOpen_region : IsOpen region)
    (family_is_boundary : family.carrier = frontier region) :
    RegularSphereFamilyParityStage Phi where
  sphereFamily := family
  ambientInside := region
  family_is_boundary := family_is_boundary
  inside := transportedTorusPart Phi region
  outside := transportedTorusPart Phi (closure region)ᶜ
  isOpen_inside := isOpen_region.preimage continuous_subtype_val
  isOpen_outside := isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  inside_disjoint_outside := by
    rw [Set.disjoint_left]
    intro x hxInside hxOutside
    change (x : R3) ∈ region at hxInside
    change (x : R3) ∉ closure region at hxOutside
    exact hxOutside (subset_closure hxInside)
  surface_partition := by
    rw [family_is_boundary]
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_union, transportedTorusPart,
      Set.mem_preimage, Set.mem_compl_iff]
    by_cases hxRegion : (x : R3) ∈ region
    · exact Or.inl (Or.inl hxRegion)
    · by_cases hxClosure : (x : R3) ∈ closure region
      · right
        rw [isOpen_region.frontier_eq]
        exact ⟨hxClosure, hxRegion⟩
      · exact Or.inl (Or.inr hxClosure)

end RegularSphereFamilyParityStage

namespace MaximalInessentialTorusDiskFamily

variable {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota] [DecidableEq iota]
  {system : FiniteSphereSurgeryIntersectionSystem Phi iota}
  {allInessential : system.AllInessential}

/-- Exact intersection by the stage circles implies that every transported-torus point on the
sphere-family boundary lies in the union of the maximal inessential disks. -/
theorem sphereFamilyPart_subset_diskUnion
    (M : MaximalInessentialTorusDiskFamily system allInessential) :
    transportedTorusPart Phi system.sphereFamily.carrier ⊆ M.diskUnion := by
  intro x hx
  have hxIntersection : (x : R3) ∈
      system.sphereFamily.carrier ∩ transportedTorus Phi :=
    ⟨hx, x.property⟩
  rw [system.intersection_exact] at hxIntersection
  simp only [Set.mem_iUnion] at hxIntersection
  obtain ⟨i, hi⟩ := hxIntersection
  obtain ⟨z, hz⟩ := hi
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  have hxValue : (x : R3) =
      ((system.circle i).windingLoop.curve t : R3) := by
    rw [← (system.circle i).parametrization t, ht]
    exact hz.symm
  have hxCurve : x = (system.circle i).windingLoop.curve t :=
    Subtype.ext hxValue
  rw [hxCurve]
  exact M.circle_range_subset_diskUnion i ⟨t, rfl⟩

end MaximalInessentialTorusDiskFamily

/-! ## The convex outer stage and the literal three-page limit -/

private theorem frontier_interior_eq_of_convex {s : Set R3}
    (hconvex : Convex ℝ s) (hnonempty : (interior s).Nonempty) :
    frontier (interior s) = frontier s := by
  calc
    frontier (interior s) = closure (interior s) \ interior (interior s) := rfl
    _ = closure s \ interior s := by
      rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hnonempty,
        interior_interior]
    _ = frontier s := closure_sdiff_interior s

/-- The convex outer superellipsoid sphere, bundled as a one-component family. -/
def outerSuperellipsoidSphereFamily
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    FiniteEmbeddedTopologicalSphereFamilyInR3 :=
  .singleton (outerSuperellipsoidSphereData frame c hR).sphere

theorem outerSuperellipsoidSphereFamily_carrier
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    (outerSuperellipsoidSphereFamily frame c hR).carrier =
      frontier (closedSuperellipsoidBody frame c R) := by
  rw [outerSuperellipsoidSphereFamily,
    FiniteEmbeddedTopologicalSphereFamilyInR3.singleton_carrier]
  exact ConvexBodySphereData.sphere_carrier_eq_frontier _

/-- The outer sphere is also the frontier of the interior of the closed convex body. -/
theorem outerSuperellipsoidSphereFamily_is_boundary
    (frame : Equiv.Perm (Fin 3)) (c : R3) {R : ℝ} (hR : 0 < R) :
    (outerSuperellipsoidSphereFamily frame c hR).carrier =
      frontier (interior (closedSuperellipsoidBody frame c R)) := by
  rw [outerSuperellipsoidSphereFamily_carrier frame c hR,
    frontier_interior_eq_of_convex
      (convex_closedSuperellipsoidBody frame c R)
      (nonempty_interior_closedSuperellipsoidBody frame c hR)]

/-- The initial regular stage is the convex outer sphere, with parity-inside equal to the
interior of the closed superellipsoid. -/
def initialOuterSuperellipsoidParityStage
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R) : RegularSphereFamilyParityStage Phi :=
  RegularSphereFamilyParityStage.ofOpenRegion Phi
    (outerSuperellipsoidSphereFamily frame c hR)
    (interior (closedSuperellipsoidBody frame c R)) isOpen_interior
    (outerSuperellipsoidSphereFamily_is_boundary frame c hR)

@[simp] theorem initialOuterSuperellipsoidParityStage_inside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R) :
    (initialOuterSuperellipsoidParityStage Phi frame c hR).inside =
      transportedTorusPart Phi (interior (closedSuperellipsoidBody frame c R)) :=
  rfl

/-- The selected open superellipsoid lies in the parity-inside region of the convex outer
stage.  Thus an incoming carrier in the usual strict-gauge body remains a carrier here. -/
theorem superellipsoidBody_subset_interior_closedSuperellipsoidBody
    (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) :
    superellipsoidBody frame c R ⊆
      interior (closedSuperellipsoidBody frame c R) := by
  apply interior_maximal
  · intro x hx
    change superellipsoidGauge frame c x ≤ R
    exact hx.le
  · exact isOpen_superellipsoidBody_convexSphere frame c R

theorem transportedSuperellipsoidBody_subset_initialOuterInside
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {R : ℝ} (hR : 0 < R) :
    transportedTorusPart Phi (superellipsoidBody frame c R) ⊆
      (initialOuterSuperellipsoidParityStage Phi frame c hR).inside :=
  preimage_mono (superellipsoidBody_subset_interior_closedSuperellipsoidBody frame c R)

namespace SingularSuperellipsoidSphereData

/-- The singular three-page carrier is the union of the two literal truncated frontiers.  The
two spheres are not bundled as a regular family because they share the cutting disk. -/
def threePageCarrier
    {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    (D : SingularSuperellipsoidSphereData frame c R d) : Set R3 :=
  D.lower.sphere.carrier ∪ D.upper.sphere.carrier

theorem threePageCarrier_eq_frontiers
    {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    (D : SingularSuperellipsoidSphereData frame c R d) :
    D.threePageCarrier =
      frontier (closedLowerSuperellipsoidTruncation frame c R d) ∪
        frontier (closedUpperSuperellipsoidTruncation frame c R d) := by
  rw [threePageCarrier, ConvexBodySphereData.sphere_carrier_eq_frontier,
    ConvexBodySphereData.sphere_carrier_eq_frontier]

end SingularSuperellipsoidSphereData

/-! ## Honest rounded children and their global neck support -/

/-- The remaining geometric input for resolving the singular three-page into two disjoint
regular child spheres.

The exact frontier and component-count fields are the rounding/separation construction.  The two
off-neck fields say that the rounding changes neither the boundary nor the parity label outside
one global neck-pinch support.  No relation to the local four-port band supports is imposed. -/
structure SuperellipsoidGlobalNeckPinchRoundingData
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    (R d : ℝ) (hR : 0 < R) where
  lowerInside : Set R3
  upperInside : Set R3
  isOpen_lowerInside : IsOpen lowerInside
  isOpen_upperInside : IsOpen upperInside
  lower_disjoint_upper : Disjoint lowerInside upperInside
  childFamily : FiniteEmbeddedTopologicalSphereFamilyInR3
  child_count : childFamily.count = 2
  childFamily_is_boundary :
    childFamily.carrier = frontier (lowerInside ∪ upperInside)
  lowerInside_subset_halfBody : lowerInside ⊆
    superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d}
  upperInside_subset_halfBody : upperInside ⊆
    superellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)}
  neckSupport : Set R3
  isOpen_neckSupport : IsOpen neckSupport
  postBoundary_off_neck_subset_outer :
    childFamily.carrier \ neckSupport ⊆
      (outerSuperellipsoidSphereFamily frame c hR).carrier
  inside_agree_off_neck : ∀ x : R3, x ∉ neckSupport →
    (x ∈ interior (closedSuperellipsoidBody frame c R) ↔
      x ∈ lowerInside ∪ upperInside)

namespace SuperellipsoidGlobalNeckPinchRoundingData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
  {R d : ℝ} {hR : 0 < R}

/-- The honest regular two-sphere stage supplied by the rounded children. -/
def postStage
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) :
    RegularSphereFamilyParityStage Phi :=
  RegularSphereFamilyParityStage.ofOpenRegion Phi D.childFamily
    (D.lowerInside ∪ D.upperInside)
    (D.isOpen_lowerInside.union D.isOpen_upperInside)
    D.childFamily_is_boundary

/-- The terminal parity cells are exactly the two disjoint open rounded-child interiors. -/
def terminalStage
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) :
    TerminalTwoComponentSphereStage (D.postStage (Phi := Phi)) where
  lower := transportedTorusPart Phi D.lowerInside
  upper := transportedTorusPart Phi D.upperInside
  isOpen_lower := D.isOpen_lowerInside.preimage continuous_subtype_val
  isOpen_upper := D.isOpen_upperInside.preimage continuous_subtype_val
  lower_disjoint_upper := by
    rw [Set.disjoint_left]
    intro x hxLower hxUpper
    exact Set.disjoint_left.mp D.lower_disjoint_upper hxLower hxUpper
  inside_eq := by
    ext x
    rfl
  sphere_count := D.child_count

theorem terminalLower_subset_halfBody
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) :
    (D.terminalStage (Phi := Phi)).lower ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c R ∩ {x | x.ofLp (frame 2) ≤ d}) :=
  preimage_mono D.lowerInside_subset_halfBody

theorem terminalUpper_subset_halfBody
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) :
    (D.terminalStage (Phi := Phi)).upper ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c R ∩ {x | d ≤ x.ofLp (frame 2)}) :=
  preimage_mono D.upperInside_subset_halfBody

/-- Ambient support for the global transition.  The old boundary is included so that the
rank-two core is disjoint from both endpoint barriers. -/
def transitionSupport
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) : Set R3 :=
  D.neckSupport ∪ (outerSuperellipsoidSphereFamily frame c hR).carrier

theorem postBoundary_subset_transitionSupport
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) :
    transportedTorusPart Phi (D.postStage (Phi := Phi)).sphereFamily.carrier ⊆
      transportedTorusPart Phi D.transitionSupport := by
  intro x hxPost
  by_cases hxNeck : (x : R3) ∈ D.neckSupport
  · exact Or.inl hxNeck
  · exact Or.inr (D.postBoundary_off_neck_subset_outer ⟨hxPost, hxNeck⟩)

theorem preInside_iff_postInside_of_not_mem_neck
    (D : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR)
    (x : transportedTorus Phi) (hx : (x : R3) ∉ D.neckSupport) :
    (x ∈ (initialOuterSuperellipsoidParityStage Phi frame c hR).inside ↔
      x ∈ (D.postStage (Phi := Phi)).inside) :=
  D.inside_agree_off_neck x hx

end SuperellipsoidGlobalNeckPinchRoundingData

/-! ## Direct inessential transition, with no common source image -/

/-- Topological disk-cover data for the global neck pinch.  Canonical maximal disks and their
connected pushout are derived from the finite all-inessential outer-stage system.  Exact circle
intersection covers the old boundary automatically, so the sole remaining cover premise concerns
the genuinely changed neck patch. -/
structure SuperellipsoidGlobalNeckPinchInessentialData
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
    {R d : ℝ} {hR : 0 < R}
    (rounding : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR) where
  coreCircleCount : ℕ
  coreSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin coreCircleCount)
  coreAllInessential : coreSystem.AllInessential
  coreSphereFamily_eq : coreSystem.sphereFamily =
    (initialOuterSuperellipsoidParityStage Phi frame c hR).sphereFamily
  neckPart_subset_diskUnion :
    transportedTorusPart Phi rounding.neckSupport ⊆
      (coreSystem.canonicalMaximalInessentialTorusDiskFamily
        coreAllInessential).diskUnion

namespace SuperellipsoidGlobalNeckPinchInessentialData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3}
  {R d : ℝ} {hR : 0 < R}
  {rounding : SuperellipsoidGlobalNeckPinchRoundingData frame c R d hR}

theorem supportPart_subset_diskUnion
    (D : SuperellipsoidGlobalNeckPinchInessentialData (Phi := Phi) rounding) :
    transportedTorusPart Phi rounding.transitionSupport ⊆
      (D.coreSystem.canonicalMaximalInessentialTorusDiskFamily
        D.coreAllInessential).diskUnion := by
  intro x hxSupport
  rcases hxSupport with hxNeck | hxOuter
  · exact D.neckPart_subset_diskUnion hxNeck
  · apply MaximalInessentialTorusDiskFamily.sphereFamilyPart_subset_diskUnion
    rw [D.coreSphereFamily_eq]
    change (x : R3) ∈ (outerSuperellipsoidSphereFamily frame c hR).carrier
    exact hxOuter

/-- The global neck-pinch data gives the direct parity transition between the convex outer
sphere and the rounded two-child family.  This construction bypasses the band-collar
`sourceImage_eq` route entirely. -/
def toInessentialParityTransition
    (D : SuperellipsoidGlobalNeckPinchInessentialData (Phi := Phi) rounding) :
    InessentialParityTransition
      (initialOuterSuperellipsoidParityStage Phi frame c hR)
      (rounding.postStage (Phi := Phi)) where
  coreCircleCount := D.coreCircleCount
  coreSystem := D.coreSystem
  coreAllInessential := D.coreAllInessential
  maximal := D.coreSystem.canonicalMaximalInessentialTorusDiskFamily D.coreAllInessential
  pushout := MaximalInessentialTorusDiskFamily.canonicalConnectedPushoutData
    D.coreSystem D.coreAllInessential
  support := rounding.transitionSupport
  diskCover := InessentialBandDiskCover.ofSubsetDiskUnion
    D.supportPart_subset_diskUnion
  boundaries_subset_support := by
    intro x hxBoundary
    rcases hxBoundary with hxPre | hxPost
    · exact Or.inr hxPre
    · exact rounding.postBoundary_subset_transitionSupport hxPost
  labelChange_subset_support := by
    intro x hxChange
    by_cases hxNeck : (x : R3) ∈ rounding.neckSupport
    · exact Or.inl hxNeck
    · exact False.elim (hxChange <|
        propext (rounding.preInside_iff_postInside_of_not_mem_neck x hxNeck))

end SuperellipsoidGlobalNeckPinchInessentialData

end Submission.Topology
