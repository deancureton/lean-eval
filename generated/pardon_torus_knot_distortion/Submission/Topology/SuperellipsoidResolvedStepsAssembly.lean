import Submission.Topology.ResolvedStageLogicalAdapters
import Submission.Topology.SuperellipsoidFiniteStageRawCharging
import Submission.Topology.SuperellipsoidOuterCircleSection
import Submission.Topology.SuperellipsoidPairedBandInstantiation

/-!
# Charge-free assembly of the finite superellipsoid surgery stages

This module records the purely logical end of the superellipsoid argument.  Regularity of the
selected outer and cutting levels gives both finite circle families.  Canonical maximal disks give
the connected pushout needed at every all-inessential stage.  The remaining finite-stage package
retains the raw regularity of every essential stage circle and feeds the quantitative charging
adapter without an abstract conversion from event-covered disks.

No moving-sphere, collar, parity, or quantitative certificate is asserted here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## The two regular circle families -/

namespace FiniteCoordinatePlaneTorusCircleFamily

/-- A specified regular cutting height has its complete finite family of embedded torus circles.
This is the cutting-level analogue of the regular outer-level constructor. -/
def ofRegularValue
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d) :
    FiniteCoordinatePlaneTorusCircleFamily Phi frame d := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := orientedCoordinateLift_contDiff Phi frame 2
  let selection : CompactRegularLevelSelection f (d - 1) (d + 1) := {
    level := d
    level_mem := by constructor <;> linarith
    isCompact := isCompact_fundamentalLevelSet hf.continuous d
    localCharts := regularValue_has_local_charts hf hd
  }
  let S : RegularCoordinateTorusLevel Phi frame (d - 1) (d + 1) := {
    selection := selection
    quotientLocallyLineModeled :=
      isLocallyLineModeled_coordinateTorusLevel_of_regularValue Phi frame hd
  }
  exact ofClassification S (componentCircleClassification_regularCoordinateLevel Phi frame hd)

end FiniteCoordinatePlaneTorusCircleFamily

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology

namespace SuperellipsoidDoubleBubbleSelection

/-- The outer regularity retained by the double-bubble selector supplies its finite outer circle
family without any additional classification premise. -/
def outerCircleFamily
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) (hr : 0 < r) :
    FiniteSuperellipsoidOuterTorusCircleFamily Phi frame c S.outer.scale :=
  FiniteSuperellipsoidOuterTorusCircleFamily.ofRegularValue
    (S.outer.scale_pos hr).le S.outer.surfaceRegular

/-- The cutting regularity retained by the double-bubble selector supplies its finite cutting
circle family without any additional classification premise. -/
def cutCircleFamily
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    FiniteCoordinatePlaneTorusCircleFamily Phi frame S.cut.height :=
  FiniteCoordinatePlaneTorusCircleFamily.ofRegularValue Phi frame S.cut.surfaceRegular

end SuperellipsoidDoubleBubbleSelection

end Submission.PardonDistortion

namespace Submission.Topology

open Submission.Torus

/-! ## Canonical connected cores for paired-band transitions -/

namespace PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex vertex edge : Type*}
  [Fintype outerIndex] [Fintype cutIndex] [Fintype vertex] [Fintype edge]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  {A : FiniteBarrierArcPresentation G vertex edge}
  {P : FiniteBarrierExcursionPairing A}
  {C : BarrierExcursionBandChartRealization P}

namespace PairedBandInessentialTransitionData

/-- The canonical maximal disk family and its connected pushout remove those two choices from a
paired-band inessential transition.  The remaining premises are exactly the geometric support and
parity-agreement statements for the two collars. -/
def ofCanonicalCore
    {coreCircleCount : ℕ}
    {preChoice postChoice : Fin P.bandCount → Bool}
    (preCollar : PairedBandMovingSphereCollarData C preChoice)
    (postCollar : PairedBandMovingSphereCollarData C postChoice)
    (pre post : RegularSphereFamilyParityStage Phi)
    (preCarrier_eq : pre.sphereFamily.carrier = preCollar.family.patchedFamily.carrier)
    (postCarrier_eq : post.sphereFamily.carrier = postCollar.family.patchedFamily.carrier)
    (sourceImage_eq : preCollar.family.sourceImage = postCollar.family.sourceImage)
    (inside_agree_off_bands : ∀ (x : transportedTorus Phi),
      (x : R3) ∉ ⋃ b, P.bandNeighborhood b → (x ∈ pre.inside ↔ x ∈ post.inside))
    (coreSystem : FiniteSphereSurgeryIntersectionSystem Phi (Fin coreCircleCount))
    (coreAllInessential : coreSystem.AllInessential)
    (bandPart_subset_diskUnion : transportedTorusPart Phi (⋃ b, P.bandNeighborhood b) ⊆
      (coreSystem.canonicalMaximalInessentialTorusDiskFamily
        coreAllInessential).diskUnion)
    (preBoundary_subset_diskUnion : transportedTorusPart Phi pre.sphereFamily.carrier ⊆
      (coreSystem.canonicalMaximalInessentialTorusDiskFamily
        coreAllInessential).diskUnion) :
    PairedBandInessentialTransitionData preChoice postChoice preCollar postCollar pre post where
  preCarrier_eq := preCarrier_eq
  postCarrier_eq := postCarrier_eq
  sourceImage_eq := sourceImage_eq
  inside_agree_off_bands := inside_agree_off_bands
  coreCircleCount := coreCircleCount
  coreSystem := coreSystem
  coreAllInessential := coreAllInessential
  maximal := coreSystem.canonicalMaximalInessentialTorusDiskFamily coreAllInessential
  pushout := MaximalInessentialTorusDiskFamily.canonicalConnectedPushoutData
    coreSystem coreAllInessential
  bandPart_subset_diskUnion := bandPart_subset_diskUnion
  preBoundary_subset_diskUnion := preBoundary_subset_diskUnion

end PairedBandInessentialTransitionData

end PairedBandMovingSphereCollarData

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Torus

/-! ## Exact charge-free final finite-stage package -/

/-- The geometric output still needed for one selected double bubble after regular outer and cut
circle classification and canonical inessential pushouts have been discharged.  Raw regularity
is retained stagewise, so the quantitative compression is constructed from the actual essential
circle rather than supplied by an abstract charging function. -/
structure SuperellipsoidFiniteStageResolutionData
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness) where
  stageSequence : FiniteRegularSphereSurgeryStageSequence Phi
  lower : Set (transportedTorus Phi)
  upper : Set (transportedTorus Phi)
  initialInside_eq : (stageSequence.parityStage 0).inside = transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale)
  lower_subset : lower ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | x.ofLp (frame 2) ≤ selection.cut.height})
  upper_subset : upper ⊆ transportedTorusPart Phi
    (superellipsoidBody frame c selection.outer.scale ∩
      {x | selection.cut.height ≤ x.ofLp (frame 2)})
  essentialSurgery : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      Nonempty (EssentialSphereCircleSurgeryData (stageSequence.system k) i)
  rawRegular : ∀ k, k ≤ stageSequence.length → ∀ i,
    ((stageSequence.system k).circle i).Essential →
      RawRegularTorusCircleData ((stageSequence.system k).circle i) p q
  inessentialResolution : stageSequence.AllInessential →
    Nonempty (AllInessentialFiniteBandResolution stageSequence lower upper)
  commonEvent_subset : stageSequence.commonEventRegion ⊆
    superellipsoidBoundary frame c selection.outer.scale ∪ selection.cutDisk

namespace SuperellipsoidFiniteStageResolutionData

variable {p q : ℕ} {K : Knot} {Phi : AmbientIsotopy}
  {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r)}
  {selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
    WB.toSmoothLoopCarrierWitness}

/-- The assembly package is exactly the raw-resolution record consumed by the quantitative
finite-stage adapter. -/
def toRawResolutionData
    (D : SuperellipsoidFiniteStageResolutionData p q K Phi frame c r WB selection) :
    SuperellipsoidFiniteStageRawResolutionData p q K Phi frame c r WB selection where
  stageSequence := D.stageSequence
  lower := D.lower
  upper := D.upper
  initialInside_eq := D.initialInside_eq
  lower_subset := D.lower_subset
  upper_subset := D.upper_subset
  essentialSurgery := D.essentialSurgery
  rawRegular := D.rawRegular
  inessentialResolution := D.inessentialResolution
  commonEvent_subset := D.commonEvent_subset

/-- The exact charge-free finite-stage package constructs the resolved alternative for one
selection. -/
theorem toResolvedDoubleBubbleStep
    (D : SuperellipsoidFiniteStageResolutionData p q K Phi frame c r WB selection)
    (hc : p.Coprime q) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t))
    (hr : 0 < r) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection :=
  SuperellipsoidFiniteStageRawResolutionData.toResolvedDoubleBubbleStep
    D.toRawResolutionData hc sigma hclass hr

end SuperellipsoidFiniteStageResolutionData

/-- Pointwise construction of the remaining finite-stage geometry is precisely sufficient for
the global resolved-double-bubble hypothesis used by Pardon's iteration. -/
theorem hasSuperellipsoidResolvedDoubleBubbleSteps_of_finiteStageResolution
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (resolution : ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
      ∀ WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r),
      ∀ selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
        WB.toSmoothLoopCarrierWitness,
        Nonempty (SuperellipsoidFiniteStageResolutionData
          p q K Phi frame c r WB selection)) :
    HasSuperellipsoidResolvedDoubleBubbleSteps p q hp hq hc K Phi sigma hclass := by
  intro frame c r hr hcarrier WB selection
  obtain ⟨D⟩ := resolution frame c r hr hcarrier WB selection
  exact ⟨D.toResolvedDoubleBubbleStep hc sigma hclass hr⟩

end Submission.PardonDistortion
