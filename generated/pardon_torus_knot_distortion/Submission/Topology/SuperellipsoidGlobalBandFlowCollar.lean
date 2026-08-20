import Submission.Topology.RegularBandFlowHomeomorph
import Submission.Topology.SuperellipsoidGlobalBandTubularChart
import Submission.Topology.SuperellipsoidSeamStandardTChart

/-!
# Flow collars of the canonical superellipsoid cutting bands

The canonical extended band path is a lift of one regular cutting-circle arc.  Hence its
oriented height is exactly the selected cutting height.  Flowing it for a small time in the
normalized-gradient field changes height by precisely that time.  Equality of two collar points
therefore first forces equality of their times; the fixed-time flow homeomorphism then forces
equality of their arc parameters.

This gives the injective product collar needed before the endpoint outer branches are straightened
by the standard seam charts.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle

namespace FiniteSuperellipsoidBarrierGraph
namespace CutCircleTransverseCyclicOrderFamily

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
  (F : CutCircleTransverseCyclicOrderFamily G)
  (b : Fin F.toPairedSeamEnumeration.bandCount)

/-- The extended cutting-circle lift, written in the product-plane coordinates used by the
normalized-gradient flow. -/
def globalBandFlowBasePoint (u : unitInterval) : Plane :=
  coveringPlaneCoordinates (F.globalBandExtendedPlanePath b u)

/-- The covering-plane base arc projects to the canonical inward cutting excursion. -/
theorem transportedTorusPlaneMap_globalBandFlowBasePoint (u : unitInterval) :
    transportedTorusPlaneMap Phi (F.globalBandFlowBasePoint b u) =
      ((F.globalBandCircle b).windingLoop.curve
        (F.globalBandExtensionParameter b u) : R3) := by
  let t := F.globalBandExtensionParameter b u
  calc
    transportedTorusPlaneMap Phi (F.globalBandFlowBasePoint b u) =
        ((torusCoveringProjectionToTorus Phi
          (F.globalBandExtendedPlanePath b u) : transportedTorus Phi) : R3) := by
      rw [coe_torusCoveringProjectionToTorus,
        transportedTorusPlaneMap_eq_expPair]
      rfl
    _ = ((F.globalBandCircle b).windingLoop.curve t : R3) := by
      exact congrArg Subtype.val (F.globalBandExtendedPlanePath_projection b u)

/-- The base arc is contained in the cutting-plane torus section. -/
theorem transportedTorusPlaneMap_globalBandFlowBasePoint_mem_cutSection
    (u : unitInterval) :
    transportedTorusPlaneMap Phi (F.globalBandFlowBasePoint b u) ∈
      superellipsoidCutTorusSection Phi frame d := by
  let t := F.globalBandExtensionParameter b u
  rw [F.transportedTorusPlaneMap_globalBandFlowBasePoint b u]
  exact G.cut.circle_mem_section (F.globalGapOfBand b).1.1
    ⟨Circle.exp t, (F.globalBandCircle b).parametrization t⟩

/-- Every point of the extended band lift lies exactly on the selected cutting level. -/
theorem orientedCoordinateLift_globalBandFlowBasePoint (u : unitInterval) :
    orientedCoordinateLift Phi frame 2 (F.globalBandFlowBasePoint b u) = d := by
  have hcut := F.transportedTorusPlaneMap_globalBandFlowBasePoint_mem_cutSection b u
  change ambientCoordinate (frame 2)
    (transportedTorusPlaneMap Phi (F.globalBandFlowBasePoint b u)) = d
  simpa [superellipsoidCutTorusSection, coordinateCuttingPlane] using hcut.2

/-! ## The two canonical seam lifts -/

/-- Covering-plane lift of the left seam endpoint inside the extended base arc. -/
def globalBandLeftFlowSeamLift : Plane :=
  F.globalBandFlowBasePoint b (F.globalBandCoreLeft b)

/-- Covering-plane lift of the right seam endpoint inside the extended base arc. -/
def globalBandRightFlowSeamLift : Plane :=
  F.globalBandFlowBasePoint b (F.globalBandCoreRight b)

theorem transportedTorusPlaneMap_globalBandLeftFlowSeamLift :
    transportedTorusPlaneMap Phi (F.globalBandLeftFlowSeamLift b) =
      (F.toPairedSeamEnumeration.firstVertex b).1 := by
  rw [globalBandLeftFlowSeamLift,
    F.transportedTorusPlaneMap_globalBandFlowBasePoint b,
    F.globalBandExtensionParameter_coreLeft b]
  calc
    ((F.globalBandCircle b).windingLoop.curve
        (F.globalBandLeftParameter b) : R3) =
        ((F.globalBandPath b (0 : unitInterval) : transportedTorus Phi) : R3) := by
      simp [globalBandPath, globalBandLeftParameter, globalBandCircle]
    _ = (F.toPairedSeamEnumeration.firstVertex b).1 := by
      unfold PairedSeamEnumeration.firstVertex
      simpa only [finTwoUnitInterval_zero] using
        (F.globalBandPath_endpoint_val b (0 : Fin 2)).symm

theorem transportedTorusPlaneMap_globalBandRightFlowSeamLift :
    transportedTorusPlaneMap Phi (F.globalBandRightFlowSeamLift b) =
      (F.toPairedSeamEnumeration.secondVertex b).1 := by
  rw [globalBandRightFlowSeamLift,
    F.transportedTorusPlaneMap_globalBandFlowBasePoint b,
    F.globalBandExtensionParameter_coreRight b]
  calc
    ((F.globalBandCircle b).windingLoop.curve
        (F.globalBandRightParameter b) : R3) =
        ((F.globalBandPath b (1 : unitInterval) : transportedTorus Phi) : R3) := by
      simp [globalBandPath, globalBandRightParameter, globalBandCircle]
    _ = (F.toPairedSeamEnumeration.secondVertex b).1 := by
      unfold PairedSeamEnumeration.secondVertex
      simpa only [finTwoUnitInterval_one] using
        (F.globalBandPath_endpoint_val b (1 : Fin 2)).symm

/-- The left collar endpoint is a lift of the exact analytic seam fiber. -/
theorem globalBandLeftFlowSeamLift_mem_seamFiber (hR : 0 < R) :
    F.globalBandLeftFlowSeamLift b ∈
      (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)} := by
  have hseam := (F.toPairedSeamEnumeration.firstVertex b).2
  rw [← F.transportedTorusPlaneMap_globalBandLeftFlowSeamLift b] at hseam
  apply Prod.ext
  · exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp hseam.1.2
  · exact F.orientedCoordinateLift_globalBandFlowBasePoint b (F.globalBandCoreLeft b)

/-- The right collar endpoint is a lift of the exact analytic seam fiber. -/
theorem globalBandRightFlowSeamLift_mem_seamFiber (hR : 0 < R) :
    F.globalBandRightFlowSeamLift b ∈
      (superellipsoidSeamMap Phi frame c) ⁻¹' {(R ^ 256, d)} := by
  have hseam := (F.toPairedSeamEnumeration.secondVertex b).2
  rw [← F.transportedTorusPlaneMap_globalBandRightFlowSeamLift b] at hseam
  apply Prod.ext
  · exact (mem_superellipsoidBoundary_iff_polynomial_eq_pow frame c _ hR.le).mp hseam.1.2
  · exact F.orientedCoordinateLift_globalBandFlowBasePoint b (F.globalBandCoreRight b)

/-- The normalized left inverse-function chart centered at the collar's actual seam lift. -/
def globalBandLeftStandardSeamLocalHomeomorph
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    OpenPartialHomeomorph Plane Plane :=
  leftStandardSeamLocalHomeomorph Phi frame c R d hseam
    (F.globalBandLeftFlowSeamLift b) (F.globalBandLeftFlowSeamLift_mem_seamFiber b hR)

/-- The normalized right inverse-function chart centered at the collar's actual seam lift. -/
def globalBandRightStandardSeamLocalHomeomorph
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    OpenPartialHomeomorph Plane Plane :=
  rightStandardSeamLocalHomeomorph Phi frame c R d hseam
    (F.globalBandRightFlowSeamLift b) (F.globalBandRightFlowSeamLift_mem_seamFiber b hR)

theorem globalBandLeftFlowSeamLift_mem_standardChartSource
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    F.globalBandLeftFlowSeamLift b ∈
      (F.globalBandLeftStandardSeamLocalHomeomorph b hR hseam).source := by
  exact mem_source_leftStandardSeamLocalHomeomorph Phi frame c R d hseam
    (F.globalBandLeftFlowSeamLift b) (F.globalBandLeftFlowSeamLift_mem_seamFiber b hR)

theorem globalBandRightFlowSeamLift_mem_standardChartSource
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    F.globalBandRightFlowSeamLift b ∈
      (F.globalBandRightStandardSeamLocalHomeomorph b hR hseam).source := by
  exact mem_source_rightStandardSeamLocalHomeomorph Phi frame c R d hseam
    (F.globalBandRightFlowSeamLift b) (F.globalBandRightFlowSeamLift_mem_seamFiber b hR)

@[simp]
theorem globalBandLeftStandardSeamLocalHomeomorph_apply_center
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    F.globalBandLeftStandardSeamLocalHomeomorph b hR hseam
        (F.globalBandLeftFlowSeamLift b) = (-1, 0) := by
  exact leftStandardSeamLocalHomeomorph_apply_center Phi frame c R d hseam
    (F.globalBandLeftFlowSeamLift b) (F.globalBandLeftFlowSeamLift_mem_seamFiber b hR)

@[simp]
theorem globalBandRightStandardSeamLocalHomeomorph_apply_center
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d) :
    F.globalBandRightStandardSeamLocalHomeomorph b hR hseam
        (F.globalBandRightFlowSeamLift b) = (1, 0) := by
  exact rightStandardSeamLocalHomeomorph_apply_center Phi frame c R d hseam
    (F.globalBandRightFlowSeamLift b) (F.globalBandRightFlowSeamLift_mem_seamFiber b hR)

/-- At the collar's actual left endpoint, the normalized analytic chart gives the exact
left half-`T` barrier equation. -/
theorem globalBandLeftStandardSeamLocalHomeomorph_mem_carrier_iff
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (z : Plane) :
    transportedTorusPlaneMap Phi z ∈ G.carrier ↔
      (F.globalBandLeftStandardSeamLocalHomeomorph b hR hseam z).1 = -1 ∨
        (-1 < (F.globalBandLeftStandardSeamLocalHomeomorph b hR hseam z).1 ∧
          (F.globalBandLeftStandardSeamLocalHomeomorph b hR hseam z).2 = 0) := by
  exact leftStandardSeamLocalHomeomorph_mem_barrier_iff G hR hseam
    (F.globalBandLeftFlowSeamLift b) (F.globalBandLeftFlowSeamLift_mem_seamFiber b hR) z

/-- At the collar's actual right endpoint, the normalized analytic chart gives the exact
right half-`T` barrier equation. -/
theorem globalBandRightStandardSeamLocalHomeomorph_mem_carrier_iff
    (hR : 0 < R) (hseam : IsRegularSuperellipsoidSeamHeight Phi frame c R d)
    (z : Plane) :
    transportedTorusPlaneMap Phi z ∈ G.carrier ↔
      (F.globalBandRightStandardSeamLocalHomeomorph b hR hseam z).1 = 1 ∨
        ((F.globalBandRightStandardSeamLocalHomeomorph b hR hseam z).1 < 1 ∧
          (F.globalBandRightStandardSeamLocalHomeomorph b hR hseam z).2 = 0) := by
  exact rightStandardSeamLocalHomeomorph_mem_barrier_iff G hR hseam
    (F.globalBandRightFlowSeamLift b) (F.globalBandRightFlowSeamLift_mem_seamFiber b hR) z

variable (B : OrientedCoordinateRegularBandData Phi frame d)

/-- Closed transverse times used for the compact collar. -/
def globalBandFlowCollarTimes : Set ℝ := Set.Icc (-B.ε) B.ε

/-- Compact parameter rectangle for one canonical band flow collar. -/
abbrev GlobalBandFlowCollarDomain :=
  unitInterval × globalBandFlowCollarTimes B

/-- Flow the extended cutting arc through the regular height band. -/
def globalBandPlaneFlowCollarMap
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) : Plane :=
  H.flow.flow (F.globalBandFlowBasePoint b p.1) p.2.1

/-- Pair the extended cutting arc with the retained time coordinate before applying the skew
flow homeomorphism. -/
def globalBandBaseTimeMap (p : GlobalBandFlowCollarDomain B) : Plane × ℝ :=
  (F.globalBandFlowBasePoint b p.1, p.2.1)

/-- Forget the subtype bounds and regard the compact collar domain as its literal rectangle in
the ordinary parameter plane. -/
def globalBandFlowParameterCoordinates (p : GlobalBandFlowCollarDomain B) : Plane :=
  (p.1.1, p.2.1)

/-- The compact collar domain is closed-embedded as its literal planar rectangle. -/
theorem globalBandFlowParameterCoordinates_isClosedEmbedding :
    IsClosedEmbedding (globalBandFlowParameterCoordinates B) := by
  exact (isClosed_Icc.isClosedEmbedding_subtypeVal.prodMap <|
    (show IsClosedEmbedding (fun t : globalBandFlowCollarTimes B ↦ (t : ℝ)) from
      (by
        have hclosed : IsClosed (globalBandFlowCollarTimes B) := by
          simpa only [globalBandFlowCollarTimes] using
            (isClosed_Icc : IsClosed (Set.Icc (-B.ε) B.ε))
        exact hclosed.isClosedEmbedding_subtypeVal)))

/-- The straight horizontal extension in parameter space whose selected core is the canonical
band-parameter interval. -/
def globalBandFlowParameterExtensionPath : Path
    (coveringPlaneCoordinates.symm ((0 : ℝ), 0))
    (coveringPlaneCoordinates.symm ((1 : ℝ), 0)) where
  toFun := fun u ↦ coveringPlaneCoordinates.symm ((u : ℝ), 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The canonical parameter interval is strictly internal to a straight injective extension. -/
def globalBandFlowParameterExtendiblePath : Schoenflies.ExtendibleInjectivePath where
  extensionSource := coveringPlaneCoordinates.symm ((0 : ℝ), 0)
  extensionTarget := coveringPlaneCoordinates.symm ((1 : ℝ), 0)
  extension := globalBandFlowParameterExtensionPath
  coreLeft := F.globalBandCoreLeft b
  coreRight := F.globalBandCoreRight b
  coreLeft_pos := F.globalBandCoreLeft_pos b
  coreLeft_lt_coreRight := F.globalBandCoreLeft_lt_coreRight b
  coreRight_lt_one := F.globalBandCoreRight_lt_one b
  extension_injective := by
    intro u v huv
    have hcoordinates := congrArg coveringPlaneCoordinates huv
    apply Subtype.ext
    exact congrArg Prod.fst hcoordinates

/-- In ordinary product coordinates, the selected parameter core is the expected horizontal
affine interval at time zero. -/
theorem globalBandFlowParameterExtendible_corePath_coordinates (u : unitInterval) :
    coveringPlaneCoordinates ((F.globalBandFlowParameterExtendiblePath b).corePath u) =
      (((Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u :
        unitInterval) : ℝ), 0) := by
  rfl

/-- The open interior of the compact parameter rectangle. -/
def globalBandFlowParameterInterior : Set Plane :=
  Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-B.ε) B.ε

theorem isOpen_globalBandFlowParameterInterior :
    IsOpen (globalBandFlowParameterInterior B) :=
  isOpen_Ioo.prod isOpen_Ioo

/-- Reinsert an interior planar parameter into the closed collar rectangle. -/
def globalBandFlowInteriorParameter
    (z : globalBandFlowParameterInterior B) : GlobalBandFlowCollarDomain B :=
  (⟨z.1.1, z.2.1.1.le, z.2.1.2.le⟩,
    ⟨z.1.2, z.2.2.1.le, z.2.2.2.le⟩)

@[simp]
theorem globalBandFlowParameterCoordinates_interiorParameter
    (z : globalBandFlowParameterInterior B) :
    globalBandFlowParameterCoordinates B (globalBandFlowInteriorParameter B z) = z :=
  rfl

theorem continuous_globalBandFlowInteriorParameter :
    Continuous (globalBandFlowInteriorParameter B) := by
  unfold globalBandFlowInteriorParameter
  fun_prop

/-- The inclusion of the open parameter rectangle into the closed collar rectangle is an
embedding. -/
theorem globalBandFlowInteriorParameter_isEmbedding :
    IsEmbedding (globalBandFlowInteriorParameter B) := by
  rw [← (globalBandFlowParameterCoordinates_isClosedEmbedding B).isEmbedding.of_comp_iff]
  change IsEmbedding (fun z : globalBandFlowParameterInterior B ↦ (z : Plane))
  exact IsEmbedding.subtypeVal

/-- Every point of the canonical horizontal core lies in the open parameter rectangle. -/
theorem globalBandFlowCoreCoordinates_mem_parameterInterior (u : unitInterval) :
    (((Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u :
      unitInterval) : ℝ), 0) ∈ globalBandFlowParameterInterior B := by
  rw [globalBandFlowParameterInterior, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
  constructor
  · simp only [Icc.coe_convexComb]
    have hgap : 0 ≤ (F.globalBandCoreRight b : ℝ) - F.globalBandCoreLeft b :=
      sub_nonneg.mpr (F.globalBandCoreLeft_lt_coreRight b).le
    have hleftTerm : 0 ≤ (u : ℝ) *
        ((F.globalBandCoreRight b : ℝ) - F.globalBandCoreLeft b) :=
      mul_nonneg u.2.1 hgap
    have hrightTerm : 0 ≤ (1 - (u : ℝ)) *
        ((F.globalBandCoreRight b : ℝ) - F.globalBandCoreLeft b) :=
      mul_nonneg (sub_nonneg.mpr u.2.2) hgap
    constructor
    · rw [show (1 - (u : ℝ)) * F.globalBandCoreLeft b +
          u * F.globalBandCoreRight b = F.globalBandCoreLeft b +
            u * (F.globalBandCoreRight b - F.globalBandCoreLeft b) by ring]
      exact add_pos_of_pos_of_nonneg (F.globalBandCoreLeft_pos b) hleftTerm
    · rw [show (1 - (u : ℝ)) * F.globalBandCoreLeft b +
          u * F.globalBandCoreRight b = F.globalBandCoreRight b -
            (1 - u) * (F.globalBandCoreRight b - F.globalBandCoreLeft b) by ring]
      exact lt_of_le_of_lt (sub_le_self _ hrightTerm) (F.globalBandCoreRight_lt_one b)
  · constructor <;> linarith [B.ε_pos]

/-- The lifted extended cutting arc is a closed embedding in the covering plane. -/
theorem globalBandFlowBasePoint_isClosedEmbedding :
    IsClosedEmbedding (F.globalBandFlowBasePoint b) := by
  exact coveringPlaneCoordinates.isClosedEmbedding.comp <|
    (F.globalBandExtendedPlanePath b).continuous.isClosedEmbedding
      (F.globalBandExtendedPlanePath_injective b)

/-- Adding the closed time interval preserves the closed embedding. -/
theorem globalBandBaseTimeMap_isClosedEmbedding :
    IsClosedEmbedding (globalBandBaseTimeMap F b B) := by
  have hclosed : IsClosed (globalBandFlowCollarTimes B) := by
    simpa only [globalBandFlowCollarTimes] using
      (isClosed_Icc : IsClosed (Set.Icc (-B.ε) B.ε))
  exact (F.globalBandFlowBasePoint_isClosedEmbedding b).prodMap
    (show IsClosedEmbedding (fun t : globalBandFlowCollarTimes B ↦ (t : ℝ)) from
      hclosed.isClosedEmbedding_subtypeVal)

private theorem globalBandFlowCollarTime_abs_le_two_mul
    (t : globalBandFlowCollarTimes B) : |(t : ℝ)| ≤ 2 * B.ε := by
  rw [abs_le]
  constructor <;> linarith [t.2.1, t.2.2, B.ε_pos]

/-- The collar's height coordinate is exactly its flow-time coordinate. -/
theorem orientedCoordinateLift_globalBandPlaneFlowCollarMap
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    orientedCoordinateLift Phi frame 2 (globalBandPlaneFlowCollarMap F b B H p) =
      d + p.2.1 := by
  exact H.height_planeFlow_eq_add (F.globalBandFlowBasePoint b p.1)
    (F.orientedCoordinateLift_globalBandFlowBasePoint b p.1) p.2.1
    (globalBandFlowCollarTime_abs_le_two_mul B p.2)

/-- The skew-flow homeomorphism sends the embedded base arc times interval to the graph of the
flow collar together with its time coordinate. -/
theorem planeFlowSkewHomeomorph_globalBandBaseTimeMap
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    H.planeFlowSkewHomeomorph (globalBandBaseTimeMap F b B p) =
      (globalBandPlaneFlowCollarMap F b B H p, p.2.1) :=
  rfl

/-- The collar is an embedding independently of compactness.  Its graph factors through the
global skew-flow homeomorphism, while height continuously recovers the time coordinate. -/
theorem globalBandPlaneFlowCollarMap_isEmbedding
    (H : RegularBandNormalizedGradientFlowData B) :
    IsEmbedding (globalBandPlaneFlowCollarMap F b B H) := by
  let heightGraph : Plane → Plane × ℝ := fun z ↦
    (z, orientedCoordinateLift Phi frame 2 z - d)
  have hheightGraph : IsEmbedding heightGraph := by
    exact isEmbedding_graph <|
      (orientedCoordinateLift_contDiff Phi frame 2).continuous.sub continuous_const
  rw [← hheightGraph.of_comp_iff]
  have hfactor : heightGraph ∘ globalBandPlaneFlowCollarMap F b B H =
      H.planeFlowSkewHomeomorph ∘ globalBandBaseTimeMap F b B := by
    funext p
    apply Prod.ext
    · rfl
    · change orientedCoordinateLift Phi frame 2
          (globalBandPlaneFlowCollarMap F b B H p) - d = p.2.1
      rw [F.orientedCoordinateLift_globalBandPlaneFlowCollarMap b B H p]
      ring
  rw [hfactor]
  exact H.planeFlowSkewHomeomorph.isEmbedding.comp
    (F.globalBandBaseTimeMap_isClosedEmbedding b B).isEmbedding

/-- The flow collar depends continuously on the arc and time parameters. -/
theorem continuous_globalBandPlaneFlowCollarMap
    (H : RegularBandNormalizedGradientFlowData B) :
    Continuous (globalBandPlaneFlowCollarMap F b B H) := by
  have hinput : Continuous (fun p : GlobalBandFlowCollarDomain B ↦
      (F.globalBandFlowBasePoint b p.1, (p.2 : ℝ))) :=
    ((coveringPlaneCoordinates.continuous.comp
        ((F.globalBandExtendedPlanePath b).continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  unfold globalBandPlaneFlowCollarMap
  change Continuous (Function.uncurry H.flow.flow ∘
    fun p : GlobalBandFlowCollarDomain B ↦
      (F.globalBandFlowBasePoint b p.1, (p.2 : ℝ)))
  exact H.continuous_planeFlow.comp hinput

/-- The canonical arc-time collar is injective.  Height recovers time, and the inverse
fixed-time flow recovers the point of the embedded extended arc. -/
theorem globalBandPlaneFlowCollarMap_injective
    (H : RegularBandNormalizedGradientFlowData B) :
    Function.Injective (globalBandPlaneFlowCollarMap F b B H) := by
  intro x y hxy
  have hheight := congrArg (orientedCoordinateLift Phi frame 2) hxy
  rw [F.orientedCoordinateLift_globalBandPlaneFlowCollarMap b B H x,
    F.orientedCoordinateLift_globalBandPlaneFlowCollarMap b B H y] at hheight
  have htime : (x.2 : ℝ) = y.2 := by linarith
  have hbase : F.globalBandFlowBasePoint b x.1 = F.globalBandFlowBasePoint b y.1 := by
    apply (H.planeTimeHomeomorph (x.2 : ℝ)).injective
    change H.flow.flow (F.globalBandFlowBasePoint b x.1) x.2 =
      H.flow.flow (F.globalBandFlowBasePoint b y.1) x.2
    rw [htime]
    unfold globalBandPlaneFlowCollarMap at hxy
    rw [htime] at hxy
    change H.flow.flow (F.globalBandFlowBasePoint b x.1) y.2 =
      H.flow.flow (F.globalBandFlowBasePoint b y.1) y.2 at hxy
    exact hxy
  have harc : x.1 = y.1 := by
    apply F.globalBandExtendedPlanePath_injective b
    exact coveringPlaneCoordinates.injective hbase
  apply Prod.ext
  · exact harc
  · exact Subtype.ext htime

/-- The compact flow collar is a closed embedding in the covering plane. -/
theorem globalBandPlaneFlowCollarMap_isClosedEmbedding
    (H : RegularBandNormalizedGradientFlowData B) :
    IsClosedEmbedding (globalBandPlaneFlowCollarMap F b B H) := by
  let _ : CompactSpace (globalBandFlowCollarTimes B) :=
    isCompact_iff_compactSpace.mp <| by
      simpa only [globalBandFlowCollarTimes] using
        (isCompact_Icc : IsCompact (Set.Icc (-B.ε) B.ε))
  exact (F.continuous_globalBandPlaneFlowCollarMap b B H).isClosedEmbedding
    (F.globalBandPlaneFlowCollarMap_injective b B H)

/-- The canonical compact parameter rectangle is homeomorphic to its image under the
normalized-gradient flow. -/
def globalBandPlaneFlowCollarHomeomorph
    (H : RegularBandNormalizedGradientFlowData B) :
    GlobalBandFlowCollarDomain B ≃ₜ Set.range (globalBandPlaneFlowCollarMap F b B H) :=
  (F.globalBandPlaneFlowCollarMap_isClosedEmbedding b B H).isEmbedding.toHomeomorph

@[simp]
theorem globalBandPlaneFlowCollarHomeomorph_apply_coe
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    ((F.globalBandPlaneFlowCollarHomeomorph b B H p :
      Set.range (globalBandPlaneFlowCollarMap F b B H)) : Plane) =
        globalBandPlaneFlowCollarMap F b B H p :=
  rfl

/-- The zero element of the closed flow-time interval. -/
def globalBandFlowCollarZeroTime : globalBandFlowCollarTimes B :=
  ⟨0, by constructor <;> linarith [B.ε_pos]⟩

/-- The original inward excursion, placed as the zero-time core of the extended flow collar. -/
def globalBandFlowCoreParameter (u : unitInterval) : GlobalBandFlowCollarDomain B :=
  (Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u,
    globalBandFlowCollarZeroTime B)

theorem continuous_globalBandFlowCoreParameter :
    Continuous (globalBandFlowCoreParameter F b B) := by
  unfold globalBandFlowCoreParameter
  fun_prop

/-- The parameterized zero-time core is compact. -/
theorem isCompact_range_globalBandFlowCoreParameter :
    IsCompact (Set.range (globalBandFlowCoreParameter F b B)) :=
  by
    simpa only [Set.image_univ] using
      isCompact_univ.image (F.continuous_globalBandFlowCoreParameter b B)

/-- The zero-time core range is literally the closed horizontal core interval times the
singleton zero time. -/
theorem range_globalBandFlowCoreParameter :
    Set.range (globalBandFlowCoreParameter F b B) =
      Set.Icc (F.globalBandCoreLeft b) (F.globalBandCoreRight b) ×ˢ
        {globalBandFlowCollarZeroTime B} := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    constructor
    · rw [← uIcc_of_le (F.globalBandCoreLeft_lt_coreRight b).le,
        ← Path.range_subpathAux]
      exact Set.mem_range_self u
    · rfl
  · rintro ⟨hp, ht⟩
    have hpRange : p.1 ∈ Set.range
        (Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b)) := by
      rw [Path.range_subpathAux,
        uIcc_of_le (F.globalBandCoreLeft_lt_coreRight b).le]
      exact hp
    obtain ⟨u, hu⟩ := hpRange
    refine ⟨u, Prod.ext hu ?_⟩
    exact (Set.mem_singleton_iff.mp ht).symm

@[simp]
theorem globalBandPlaneFlowCollarMap_zeroTime
    (H : RegularBandNormalizedGradientFlowData B) (u : unitInterval) :
    globalBandPlaneFlowCollarMap F b B H (u, globalBandFlowCollarZeroTime B) =
      F.globalBandFlowBasePoint b u := by
  unfold globalBandPlaneFlowCollarMap globalBandFlowCollarZeroTime
  exact H.flow.flow_zero _

/-- Projecting the zero-time core recovers the canonical global inward excursion pointwise. -/
theorem transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_core
    (H : RegularBandNormalizedGradientFlowData B) (u : unitInterval) :
    transportedTorusPlaneMap Phi
        (globalBandPlaneFlowCollarMap F b B H (globalBandFlowCoreParameter F b B u)) =
      ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
  rw [globalBandFlowCoreParameter, F.globalBandPlaneFlowCollarMap_zeroTime b B H]
  have hcore := F.globalBandExtendible_corePath_apply b u
  have hprojection := congrArg
    (fun z ↦ ((torusCoveringProjectionToTorus Phi z : transportedTorus Phi) : R3)) hcore
  rw [show F.globalBandFlowBasePoint b
      (Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u) =
        coveringPlaneCoordinates
          ((F.globalBandExtendibleInjectivePath b).corePath u) by
      rfl,
    transportedTorusPlaneMap_eq_expPair]
  change ((torusCoveringProjectionToTorus Phi
      ((F.globalBandExtendibleInjectivePath b).corePath u) : transportedTorus Phi) : R3) = _
  calc
    ((torusCoveringProjectionToTorus Phi
        ((F.globalBandExtendibleInjectivePath b).corePath u) : transportedTorus Phi) : R3) =
        ((torusCoveringProjectionToTorus Phi
          ((F.globalBandCircle b).zeroWindingPlaneLift
            (F.globalInwardExcursionParameter (F.globalGapOfBand b) u)) :
              transportedTorus Phi) : R3) := hprojection
    _ = ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
      rw [F.torusCoveringProjection_globalBandCircle_planeLift]
      rfl

/-- The actual universal-cover point represented by one flow-collar parameter. -/
def globalBandFlowCoveringPoint
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) : TorusCoveringPlane :=
  coveringPlaneCoordinates.symm (globalBandPlaneFlowCollarMap F b B H p)

theorem continuous_globalBandFlowCoveringPoint
    (H : RegularBandNormalizedGradientFlowData B) :
    Continuous (globalBandFlowCoveringPoint F b B H) :=
  coveringPlaneCoordinates.symm.continuous.comp
    (F.continuous_globalBandPlaneFlowCollarMap b B H)

@[simp]
theorem coe_torusCoveringProjection_globalBandFlowCoveringPoint
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    ((torusCoveringProjectionToTorus Phi (globalBandFlowCoveringPoint F b B H p) :
      transportedTorus Phi) : R3) =
        transportedTorusPlaneMap Phi (globalBandPlaneFlowCollarMap F b B H p) := by
  rw [coe_torusCoveringProjectionToTorus, globalBandFlowCoveringPoint,
    transportedTorusPlaneMap_eq_expPair]
  unfold torusCoveringProjection planeExpPair
  have hcoordinates := coveringPlaneCoordinates.apply_symm_apply
    (globalBandPlaneFlowCollarMap F b B H p)
  change ((coveringPlaneCoordinates.symm
      (globalBandPlaneFlowCollarMap F b B H p)) 0,
    (coveringPlaneCoordinates.symm
      (globalBandPlaneFlowCollarMap F b B H p)) 1) =
        globalBandPlaneFlowCollarMap F b B H p at hcoordinates
  have hfirst := congrArg Prod.fst hcoordinates
  have hsecond := congrArg Prod.snd hcoordinates
  change (coveringPlaneCoordinates.symm
      (globalBandPlaneFlowCollarMap F b B H p)) 0 =
        (globalBandPlaneFlowCollarMap F b B H p).1 at hfirst
  change (coveringPlaneCoordinates.symm
      (globalBandPlaneFlowCollarMap F b B H p)) 1 =
        (globalBandPlaneFlowCollarMap F b B H p).2 at hsecond
  rw [hfirst, hsecond]

/-- On the zero-time core, the covering point is the original extended plane path at the
selected affine parameter. -/
theorem globalBandFlowCoveringPoint_core
    (H : RegularBandNormalizedGradientFlowData B) (u : unitInterval) :
    globalBandFlowCoveringPoint F b B H (globalBandFlowCoreParameter F b B u) =
      (F.globalBandExtendibleInjectivePath b).corePath u := by
  unfold globalBandFlowCoveringPoint globalBandFlowCoreParameter
  rw [F.globalBandPlaneFlowCollarMap_zeroTime b B H]
  rfl

/-- Parameters whose lifted collar points lie in a specified covering-injective neighborhood. -/
def globalBandFlowCoveringParameters
    (H : RegularBandNormalizedGradientFlowData B) (U : Set TorusCoveringPlane) :
    Set (GlobalBandFlowCollarDomain B) :=
  globalBandFlowCoveringPoint F b B H ⁻¹' U

theorem isOpen_globalBandFlowCoveringParameters
    (H : RegularBandNormalizedGradientFlowData B) {U : Set TorusCoveringPlane}
    (hU : IsOpen U) : IsOpen (globalBandFlowCoveringParameters F b B H U) :=
  hU.preimage (F.continuous_globalBandFlowCoveringPoint b B H)

/-- Parameters whose collar points project into the canonically separated ambient band. -/
def globalBandFlowGoodParameters
    (H : RegularBandNormalizedGradientFlowData B) : Set (GlobalBandFlowCollarDomain B) :=
  {p | transportedTorusPlaneMap Phi (globalBandPlaneFlowCollarMap F b B H p) ∈
    F.globalBandOpenNeighborhood b}

/-- The good parameter locus is open in the compact collar domain. -/
theorem isOpen_globalBandFlowGoodParameters
    (H : RegularBandNormalizedGradientFlowData B) :
    IsOpen (globalBandFlowGoodParameters F b B H) := by
  exact (F.globalBandOpenNeighborhood_spec.1 b).1.preimage <|
    (transportedTorusPlaneMap_contDiff Phi).continuous.comp
      (F.continuous_globalBandPlaneFlowCollarMap b B H)

/-- Simultaneously impose ambient-band control and injectivity of the covering projection. -/
def globalBandFlowChartGoodParameters
    (H : RegularBandNormalizedGradientFlowData B) (U : Set TorusCoveringPlane) :
    Set (GlobalBandFlowCollarDomain B) :=
  globalBandFlowGoodParameters F b B H ∩ globalBandFlowCoveringParameters F b B H U

theorem isOpen_globalBandFlowChartGoodParameters
    (H : RegularBandNormalizedGradientFlowData B) {U : Set TorusCoveringPlane}
    (hU : IsOpen U) : IsOpen (globalBandFlowChartGoodParameters F b B H U) :=
  (F.isOpen_globalBandFlowGoodParameters b B H).inter
    (F.isOpen_globalBandFlowCoveringParameters b B H hU)

/-- The entire canonical inward excursion lies in the good parameter locus. -/
theorem range_globalBandFlowCoreParameter_subset_goodParameters
    (H : RegularBandNormalizedGradientFlowData B) :
    Set.range (globalBandFlowCoreParameter F b B) ⊆
      globalBandFlowGoodParameters F b B H := by
  rintro _ ⟨u, rfl⟩
  rw [globalBandFlowGoodParameters, mem_ofPred_eq,
    F.transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_core b B H u]
  exact (F.globalBandOpenNeighborhood_spec.1 b).2 ⟨u, rfl⟩

/-- Compactness supplies one positive uniform parameter thickening whose entire flow image stays
inside the canonically separated ambient band neighborhood. -/
theorem exists_globalBandFlowCoreThickening_subset_goodParameters
    (H : RegularBandNormalizedGradientFlowData B) :
    ∃ δ > 0, Metric.thickening δ (Set.range (globalBandFlowCoreParameter F b B)) ⊆
      globalBandFlowGoodParameters F b B H := by
  exact (F.isCompact_range_globalBandFlowCoreParameter b B).exists_thickening_subset_open
    (F.isOpen_globalBandFlowGoodParameters b B H)
    (F.range_globalBandFlowCoreParameter_subset_goodParameters b B H)

/-- Independent open horizontal and time neighborhoods whose product remains in the good
parameter locus. -/
structure GlobalBandFlowProductNeighborhood
    (H : RegularBandNormalizedGradientFlowData B) where
  horizontal : Set unitInterval
  time : Set (globalBandFlowCollarTimes B)
  horizontal_open : IsOpen horizontal
  time_open : IsOpen time
  core_subset_horizontal :
    Set.Icc (F.globalBandCoreLeft b) (F.globalBandCoreRight b) ⊆ horizontal
  zero_mem_time : globalBandFlowCollarZeroTime B ∈ time
  product_subset_good : horizontal ×ˢ time ⊆ globalBandFlowGoodParameters F b B H

/-- The tube lemma separates the compact core neighborhood into independent horizontal and time
factors. -/
theorem exists_globalBandFlowProductNeighborhood
    (H : RegularBandNormalizedGradientFlowData B) :
    Nonempty (GlobalBandFlowProductNeighborhood F b B H) := by
  have hproduct : Set.Icc (F.globalBandCoreLeft b) (F.globalBandCoreRight b) ×ˢ
      {globalBandFlowCollarZeroTime B} ⊆ globalBandFlowGoodParameters F b B H := by
    rw [← F.range_globalBandFlowCoreParameter b B]
    exact F.range_globalBandFlowCoreParameter_subset_goodParameters b B H
  obtain ⟨U, V, hUopen, hVopen, hcoreU, hzeroV, hUV⟩ :=
    generalized_tube_lemma
      (isCompact_Icc : IsCompact
        (Set.Icc (F.globalBandCoreLeft b) (F.globalBandCoreRight b)))
      (isCompact_singleton : IsCompact ({globalBandFlowCollarZeroTime B} :
        Set (globalBandFlowCollarTimes B)))
      (F.isOpen_globalBandFlowGoodParameters b B H) hproduct
  exact ⟨{
    horizontal := U
    time := V
    horizontal_open := hUopen
    time_open := hVopen
    core_subset_horizontal := hcoreU
    zero_mem_time := hzeroV (Set.mem_singleton _)
    product_subset_good := hUV }⟩

/-- Relative openness of the good parameter locus is represented by an ambient-open subset of
the ordinary parameter plane. -/
theorem exists_open_parameterPlane_preimage_eq_goodParameters
    (H : RegularBandNormalizedGradientFlowData B) :
    ∃ U : Set Plane, IsOpen U ∧
      globalBandFlowParameterCoordinates B ⁻¹' U = globalBandFlowGoodParameters F b B H := by
  exact (globalBandFlowParameterCoordinates_isClosedEmbedding B).isInducing.isOpen_iff.mp
    (F.isOpen_globalBandFlowGoodParameters b B H)

/-- The canonical horizontal core has an open planar tubular strip wholly inside both the
ambient-good locus and the interior of the compact flow-parameter rectangle.  Its source seam
retains the original unit-interval parameter exactly. -/
theorem exists_globalBandFlowParameterTubularStrip
    (H : RegularBandNormalizedGradientFlowData B) :
    ∃ U : Set Plane, IsOpen U ∧
      globalBandFlowParameterCoordinates B ⁻¹' U =
        globalBandFlowGoodParameters F b B H ∧
      ∃ V : Set TorusCoveringPlane, IsOpen V ∧
        V ⊆ coveringPlaneCoordinates ⁻¹'
          (U ∩ globalBandFlowParameterInterior B) ∧
        ∃ e : Plane ≃ₜ V, ∀ u : unitInterval,
          coveringPlaneCoordinates (e (bandSeamPath u)) =
            globalBandFlowParameterCoordinates B (globalBandFlowCoreParameter F b B u) := by
  obtain ⟨U, hUopen, hUpreimage⟩ :=
    F.exists_open_parameterPlane_preimage_eq_goodParameters b B H
  let E := F.globalBandFlowParameterExtendiblePath b
  let W : Set TorusCoveringPlane :=
    coveringPlaneCoordinates ⁻¹' (U ∩ globalBandFlowParameterInterior B)
  have hWopen : IsOpen W :=
    (hUopen.inter (isOpen_globalBandFlowParameterInterior B)).preimage
      coveringPlaneCoordinates.continuous
  have hcoreW : E.coreRange ⊆ W := by
    intro z hz
    rw [← E.range_corePath] at hz
    obtain ⟨u, rfl⟩ := hz
    change coveringPlaneCoordinates (E.corePath u) ∈
      U ∩ globalBandFlowParameterInterior B
    rw [F.globalBandFlowParameterExtendible_corePath_coordinates b]
    constructor
    · have hgood : globalBandFlowCoreParameter F b B u ∈
          globalBandFlowGoodParameters F b B H := by
        apply F.range_globalBandFlowCoreParameter_subset_goodParameters b B H
        exact Set.mem_range_self u
      rw [← hUpreimage] at hgood
      simpa [globalBandFlowParameterCoordinates, globalBandFlowCoreParameter,
        globalBandFlowCollarZeroTime] using hgood
    · exact F.globalBandFlowCoreCoordinates_mem_parameterInterior b B u
  obtain ⟨V, hVopen, hVW, e, heCore⟩ :=
    E.exists_tubularStrip_of_extendible hWopen hcoreW
  let ep : Plane ≃ₜ V := coveringPlaneCoordinates.symm.trans e
  refine ⟨U, hUopen, hUpreimage, V, hVopen, hVW, ep, ?_⟩
  intro u
  change coveringPlaneCoordinates
      (e (coveringPlaneCoordinates.symm (bandSeamPath u))) = _
  rw [coveringPlaneCoordinates_symm_bandSeamPath, heCore,
    F.globalBandFlowParameterExtendible_corePath_coordinates b]
  rfl

/-- A stronger parameter strip that also lies over one open neighborhood on which the torus
covering projection is injective. -/
theorem exists_globalBandFlowCoveringInjectiveParameterTubularStrip
    (H : RegularBandNormalizedGradientFlowData B) :
    ∃ Uinj : Set TorusCoveringPlane, IsOpen Uinj ∧
      Set.range (F.globalBandExtendedPlanePath b) ⊆ Uinj ∧
      Set.InjOn (torusCoveringProjectionToTorus Phi) Uinj ∧
      ∃ U : Set Plane, IsOpen U ∧
        globalBandFlowParameterCoordinates B ⁻¹' U =
          globalBandFlowChartGoodParameters F b B H Uinj ∧
        ∃ V : Set TorusCoveringPlane, IsOpen V ∧
          V ⊆ coveringPlaneCoordinates ⁻¹'
            (U ∩ globalBandFlowParameterInterior B) ∧
          ∃ e : Plane ≃ₜ V, ∀ u : unitInterval,
            coveringPlaneCoordinates (e (bandSeamPath u)) =
              globalBandFlowParameterCoordinates B
                (globalBandFlowCoreParameter F b B u) := by
  obtain ⟨Uinj, hUinjOpen, hpathUinj, hUinjInjective⟩ :=
    F.exists_open_injOn_globalBandExtendedPlanePath b
  have hchartOpen : IsOpen (globalBandFlowChartGoodParameters F b B H Uinj) :=
    F.isOpen_globalBandFlowChartGoodParameters b B H hUinjOpen
  obtain ⟨U, hUopen, hUpreimage⟩ :=
    (globalBandFlowParameterCoordinates_isClosedEmbedding B).isInducing.isOpen_iff.mp hchartOpen
  let E := F.globalBandFlowParameterExtendiblePath b
  let W : Set TorusCoveringPlane :=
    coveringPlaneCoordinates ⁻¹' (U ∩ globalBandFlowParameterInterior B)
  have hWopen : IsOpen W :=
    (hUopen.inter (isOpen_globalBandFlowParameterInterior B)).preimage
      coveringPlaneCoordinates.continuous
  have hcoreW : E.coreRange ⊆ W := by
    intro z hz
    rw [← E.range_corePath] at hz
    obtain ⟨u, rfl⟩ := hz
    change coveringPlaneCoordinates (E.corePath u) ∈
      U ∩ globalBandFlowParameterInterior B
    rw [F.globalBandFlowParameterExtendible_corePath_coordinates b]
    constructor
    · have hchart : globalBandFlowCoreParameter F b B u ∈
          globalBandFlowChartGoodParameters F b B H Uinj := by
        constructor
        · apply F.range_globalBandFlowCoreParameter_subset_goodParameters b B H
          exact Set.mem_range_self u
        · change globalBandFlowCoveringPoint F b B H
            (globalBandFlowCoreParameter F b B u) ∈ Uinj
          rw [F.globalBandFlowCoveringPoint_core b B H]
          apply hpathUinj
          exact ⟨Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u, rfl⟩
      rw [← hUpreimage] at hchart
      simpa [globalBandFlowParameterCoordinates, globalBandFlowCoreParameter,
        globalBandFlowCollarZeroTime] using hchart
    · exact F.globalBandFlowCoreCoordinates_mem_parameterInterior b B u
  obtain ⟨V, hVopen, hVW, e, heCore⟩ :=
    E.exists_tubularStrip_of_extendible hWopen hcoreW
  let ep : Plane ≃ₜ V := coveringPlaneCoordinates.symm.trans e
  refine ⟨Uinj, hUinjOpen, hpathUinj, hUinjInjective,
    U, hUopen, hUpreimage, V, hVopen, hVW, ep, ?_⟩
  intro u
  change coveringPlaneCoordinates
      (e (coveringPlaneCoordinates.symm (bandSeamPath u))) = _
  rw [coveringPlaneCoordinates_symm_bandSeamPath, heCore,
    F.globalBandFlowParameterExtendible_corePath_coordinates b]
  rfl

/-- The flow collar and the covering-injective parameter strip assemble into the actual global
transported-torus tubular chart required by the paired-band API. -/
theorem exists_globalBandFlowTubularChartData
    (H : RegularBandNormalizedGradientFlowData B) :
    Nonempty (GlobalBandTubularChartData F b) := by
  obtain ⟨Uinj, hUinjOpen, _, hUinjInjective, U, _, hUpreimage,
    V, hVopen, hVW, e, heCore⟩ :=
    F.exists_globalBandFlowCoveringInjectiveParameterTubularStrip b B H
  let qV : V → globalBandFlowParameterInterior B := fun z ↦
    ⟨coveringPlaneCoordinates z, (hVW z.2).2⟩
  have hqVEmbedding : IsEmbedding qV := by
    apply IsEmbedding.codRestrict
    exact coveringPlaneCoordinates.isEmbedding.comp IsEmbedding.subtypeVal
  let pV : V → GlobalBandFlowCollarDomain B :=
    globalBandFlowInteriorParameter B ∘ qV
  have hpVEmbedding : IsEmbedding pV :=
    (globalBandFlowInteriorParameter_isEmbedding B).comp hqVEmbedding
  have hpVGood (z : V) :
      pV z ∈ globalBandFlowChartGoodParameters F b B H Uinj := by
    rw [← hUpreimage]
    change globalBandFlowParameterCoordinates B (pV z) ∈ U
    simpa [pV, qV] using (hVW z.2).1
  let liftV : V → TorusCoveringPlane :=
    globalBandFlowCoveringPoint F b B H ∘ pV
  have hliftVEmbedding : IsEmbedding liftV := by
    exact coveringPlaneCoordinates.symm.isEmbedding.comp <|
      (F.globalBandPlaneFlowCollarMap_isEmbedding b B H).comp hpVEmbedding
  have hliftVU (z : V) : liftV z ∈ Uinj := by
    exact (hpVGood z).2
  let liftVU : V → Uinj := fun z ↦ ⟨liftV z, hliftVU z⟩
  have hliftVUEmbedding : IsEmbedding liftVU := by
    exact hliftVEmbedding.codRestrict Uinj hliftVU
  let projU : Uinj → transportedTorus Phi := fun z ↦
    torusCoveringProjectionToTorus Phi z
  have hprojULocal : IsLocalHomeomorph projU := by
    change IsLocalHomeomorph
      (torusCoveringProjectionToTorus Phi ∘ (fun z : Uinj ↦ (z : TorusCoveringPlane)))
    exact (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).comp
      hUinjOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hprojUInjective : Function.Injective projU := by
    intro x y hxy
    apply Subtype.ext
    exact hUinjInjective x.2 y.2 hxy
  have hprojUEmbedding : IsEmbedding projU :=
    (hprojULocal.isOpenEmbedding_of_injective hprojUInjective).isEmbedding
  let torusV : V → transportedTorus Phi := projU ∘ liftVU
  have htorusVEmbedding : IsEmbedding torusV :=
    hprojUEmbedding.comp hliftVUEmbedding
  let ep : V ≃ₜ Set.range torusV := htorusVEmbedding.toHomeomorph
  let strip : Plane ≃ₜ Set.range torusV := e.trans ep
  refine ⟨GlobalBandTubularChartData.ofStrip (Set.range torusV) strip ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    change ((torusV (e z) : transportedTorus Phi) : R3) ∈
      F.globalBandOpenNeighborhood b
    have hgood := (hpVGood (e z)).1
    change transportedTorusPlaneMap Phi
        (globalBandPlaneFlowCollarMap F b B H (pV (e z))) ∈
      F.globalBandOpenNeighborhood b at hgood
    simpa only [torusV, projU, liftVU, liftV, Function.comp_apply,
      F.coe_torusCoveringProjection_globalBandFlowCoveringPoint b B H] using
        hgood
  · intro u
    change ((torusV (e (bandSeamPath u)) : transportedTorus Phi) : R3) =
      ((F.globalBandPath b u : transportedTorus Phi) : R3)
    have hpVCore : pV (e (bandSeamPath u)) = globalBandFlowCoreParameter F b B u := by
      apply (globalBandFlowParameterCoordinates_isClosedEmbedding B).injective
      calc
        globalBandFlowParameterCoordinates B (pV (e (bandSeamPath u))) =
            coveringPlaneCoordinates (e (bandSeamPath u)) := by
          simp [pV, qV]
        _ = globalBandFlowParameterCoordinates B
            (globalBandFlowCoreParameter F b B u) := heCore u
    rw [show torusV (e (bandSeamPath u)) =
        torusCoveringProjectionToTorus Phi
          (globalBandFlowCoveringPoint F b B H (pV (e (bandSeamPath u)))) by rfl,
      hpVCore]
    simpa only [F.coe_torusCoveringProjection_globalBandFlowCoveringPoint b B H] using
      F.transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_core b B H u

/-- Choose the normalized-gradient-flow tubular chart simultaneously for every canonical inward
excursion. -/
noncomputable def globalBandFlowTubularChartFamily
    (H : RegularBandNormalizedGradientFlowData B) : GlobalBandTubularChartFamily F where
  band b := Classical.choice (F.exists_globalBandFlowTubularChartData b B H)

theorem globalBandFlowTubularChartFamily_core_alignment
    (H : RegularBandNormalizedGradientFlowData B)
    (b : Fin F.toPairedSeamEnumeration.bandCount) (u : unitInterval) :
    (((F.globalBandFlowTubularChartFamily B H).chart b).chart (bandSeamPath u) : R3) =
      ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
  exact (F.globalBandFlowTubularChartFamily B H).band b |>.core_alignment u

/-- In flow coordinates, the cutting-plane torus section is exactly the horizontal zero-time
slice of the compact collar. -/
theorem transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_mem_cutSection_iff
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    transportedTorusPlaneMap Phi (globalBandPlaneFlowCollarMap F b B H p) ∈
        superellipsoidCutTorusSection Phi frame d ↔
      (p.2 : ℝ) = 0 := by
  constructor
  · intro hp
    have hheight :
        orientedCoordinateLift Phi frame 2 (globalBandPlaneFlowCollarMap F b B H p) = d := by
      change ambientCoordinate (frame 2)
        (transportedTorusPlaneMap Phi (globalBandPlaneFlowCollarMap F b B H p)) = d
      simpa [superellipsoidCutTorusSection, coordinateCuttingPlane] using hp.2
    rw [F.orientedCoordinateLift_globalBandPlaneFlowCollarMap b B H p] at hheight
    linarith
  · intro hp
    have hmap : globalBandPlaneFlowCollarMap F b B H p =
        F.globalBandFlowBasePoint b p.1 := by
      unfold globalBandPlaneFlowCollarMap
      rw [hp, H.flow.flow_zero]
    rw [hmap]
    exact F.transportedTorusPlaneMap_globalBandFlowBasePoint_mem_cutSection b p.1

/-- Set-level form of the exact horizontal cutting slice. -/
theorem preimage_transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_cutSection
    (H : RegularBandNormalizedGradientFlowData B) :
    (transportedTorusPlaneMap Phi ∘ globalBandPlaneFlowCollarMap F b B H) ⁻¹'
        superellipsoidCutTorusSection Phi frame d =
      {p : GlobalBandFlowCollarDomain B | (p.2 : ℝ) = 0} := by
  ext p
  exact F.transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_mem_cutSection_iff b B H p

/-- The signed outer-polynomial coordinate on the compact flow collar. -/
def globalBandFlowOuterDefect
    (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) : ℝ :=
  superellipsoidPolynomialLift Phi frame c
      (globalBandPlaneFlowCollarMap F b B H p) - R ^ 256

/-- The signed outer-polynomial coordinate varies continuously on the flow collar. -/
theorem continuous_globalBandFlowOuterDefect
    (H : RegularBandNormalizedGradientFlowData B) :
    Continuous (globalBandFlowOuterDefect F b B H) := by
  exact ((contDiff_superellipsoidPolynomialLift Phi frame c).continuous.comp
    (F.continuous_globalBandPlaneFlowCollarMap b B H)).sub continuous_const

/-- Complete pointwise barrier equation in flow coordinates.  The horizontal arm is already
straight; the remaining outer arms are the zero locus of one continuous scalar function. -/
theorem transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_mem_carrier_iff
    (hR : 0 < R) (H : RegularBandNormalizedGradientFlowData B)
    (p : GlobalBandFlowCollarDomain B) :
    transportedTorusPlaneMap Phi (globalBandPlaneFlowCollarMap F b B H p) ∈ G.carrier ↔
      globalBandFlowOuterDefect F b B H p = 0 ∨
        (globalBandFlowOuterDefect F b B H p < 0 ∧ (p.2 : ℝ) = 0) := by
  rw [transportedTorusPlaneMap_mem_barrier_iff G hR]
  rw [F.orientedCoordinateLift_globalBandPlaneFlowCollarMap b B H p]
  unfold globalBandFlowOuterDefect
  constructor
  · rintro (houter | ⟨houter, hheight⟩)
    · exact Or.inl (sub_eq_zero.mpr houter)
    · exact Or.inr ⟨sub_neg.mpr houter, by linarith⟩
  · rintro (houter | ⟨houter, htime⟩)
    · exact Or.inl (sub_eq_zero.mp houter)
    · exact Or.inr ⟨sub_neg.mp houter, by linarith⟩

end CutCircleTransverseCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
