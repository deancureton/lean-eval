import Submission.Topology.SuperellipsoidPairedBandInstantiation
import Submission.PlaneSchoenflies.Schoenflies.ExtendibleArcTubularStrip
import Submission.Topology.TorusDiskPuncture

/-!
# Tubular charts for the global superellipsoid excursion bands

This file lifts each closed inward excursion to the universal covering plane of the transported
torus, extends it slightly along its embedded cutting circle, applies the planar extendible-arc
tubular-strip theorem, and descends the resulting strip through an injective neighborhood of the
covering projection.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open EmbeddedTorusIntersectionCircle

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace CutCircleTransverseCyclicOrderFamily

variable (F : CutCircleTransverseCyclicOrderFamily G)
  (b : Fin F.toPairedSeamEnumeration.bandCount)

/-- The cutting circle containing the band indexed by `b`. -/
noncomputable def globalBandCircle : EmbeddedTorusIntersectionCircle Phi :=
  G.cut.circle (F.globalGapOfBand b).1.1

/-- Left and right real parameters of the selected cyclic inward gap. -/
noncomputable def globalBandLeftParameter : ℝ :=
  G.cutCircleSortedCrossing (F.globalGapOfBand b).1.1
    (F.globalGapFinIndex (F.globalGapOfBand b))

noncomputable def globalBandRightParameter : ℝ :=
  G.cutCircleCyclicRight (F.globalGapOfBand b).1.1
    (F.order (F.globalGapOfBand b).1).crossings_nonempty
    (F.globalGapFinIndex (F.globalGapOfBand b))

theorem globalBandLeftParameter_lt_rightParameter :
    F.globalBandLeftParameter b < F.globalBandRightParameter b := by
  exact G.cutCircleSortedCrossing_lt_cyclicRight (F.globalGapOfBand b).1.1
    (F.order (F.globalGapOfBand b).1).crossings_nonempty
    (F.globalGapFinIndex (F.globalGapOfBand b))

/-- The cyclic gap is strictly shorter than a full period.  Equality would identify its two
globally enumerated seam endpoints. -/
theorem globalBandRightParameter_lt_add_period :
    F.globalBandRightParameter b < F.globalBandLeftParameter b + 2 * Real.pi := by
  have hle := G.cutCircleCyclicRight_le_add_period (F.globalGapOfBand b).1.1
    (F.order (F.globalGapOfBand b).1).crossings_nonempty
    (F.globalGapFinIndex (F.globalGapOfBand b))
  apply lt_of_le_of_ne hle
  intro heq
  have hpath :
      ((F.globalBandPath b (0 : unitInterval) : transportedTorus Phi) : R3) =
        ((F.globalBandPath b (1 : unitInterval) : transportedTorus Phi) : R3) := by
    change (((F.globalBandCircle b).windingLoop.curve
        (F.globalBandLeftParameter b + (0 : ℝ) *
          (F.globalBandRightParameter b - F.globalBandLeftParameter b)) :
          transportedTorus Phi) : R3) =
      (((F.globalBandCircle b).windingLoop.curve
        (F.globalBandLeftParameter b + (1 : ℝ) *
          (F.globalBandRightParameter b - F.globalBandLeftParameter b)) :
          transportedTorus Phi) : R3)
    simp only [zero_mul, add_zero, one_mul]
    rw [show F.globalBandRightParameter b =
        F.globalBandLeftParameter b + 2 * Real.pi by
      simpa [globalBandLeftParameter, globalBandRightParameter] using heq]
    apply congrArg Subtype.val
    convert ((F.globalBandCircle b).windingLoop.periodic_curve
      (F.globalBandLeftParameter b)).symm using 1
    ring_nf
  have hp : (F.globalGapOfBand b, (0 : Fin 2)) =
      (F.globalGapOfBand b, (1 : Fin 2)) :=
    F.global_path_endpoint_injective (by simpa using hpath)
  have he : (0 : Fin 2) = 1 := congrArg Prod.snd hp
  norm_num at he

/-- Projecting the chosen real coordinate lift recovers the transported-torus loop point. -/
theorem torusCoveringProjection_globalBandCircle_planeLift (t : ℝ) :
    torusCoveringProjectionToTorus Phi ((F.globalBandCircle b).zeroWindingPlaneLift t) =
      (F.globalBandCircle b).windingLoop.curve t := by
  change transportedTorusHomeomorph Phi
      (Circle.exp ((F.globalBandCircle b).windingLoop.lift.first.angle t),
        Circle.exp ((F.globalBandCircle b).windingLoop.lift.second.angle t)) =
    (F.globalBandCircle b).windingLoop.curve t
  rw [(F.globalBandCircle b).windingLoop.lift.first.exp_angle,
    (F.globalBandCircle b).windingLoop.lift.second.exp_angle]
  exact (transportedTorusHomeomorph Phi).apply_symm_apply _

/-- A positive margin leaving the extended real parameter interval shorter than one period. -/
noncomputable def globalBandExtensionMargin : ℝ :=
  (F.globalBandLeftParameter b + 2 * Real.pi - F.globalBandRightParameter b) / 4

theorem globalBandExtensionMargin_pos : 0 < F.globalBandExtensionMargin b := by
  unfold globalBandExtensionMargin
  linarith [F.globalBandRightParameter_lt_add_period b]

/-- Endpoints and length of the slightly extended lifted arc. -/
noncomputable def globalBandExtensionSourceParameter : ℝ :=
  F.globalBandLeftParameter b - F.globalBandExtensionMargin b

noncomputable def globalBandExtensionTargetParameter : ℝ :=
  F.globalBandRightParameter b + F.globalBandExtensionMargin b

noncomputable def globalBandExtensionSpan : ℝ :=
  F.globalBandExtensionTargetParameter b - F.globalBandExtensionSourceParameter b

theorem globalBandExtensionSpan_pos : 0 < F.globalBandExtensionSpan b := by
  unfold globalBandExtensionSpan globalBandExtensionTargetParameter
    globalBandExtensionSourceParameter
  linarith [F.globalBandExtensionMargin_pos b,
    F.globalBandLeftParameter_lt_rightParameter b]

theorem globalBandExtensionSpan_lt_period :
    F.globalBandExtensionSpan b < 2 * Real.pi := by
  unfold globalBandExtensionSpan globalBandExtensionTargetParameter
    globalBandExtensionSourceParameter globalBandExtensionMargin
  linarith [F.globalBandRightParameter_lt_add_period b]

/-- Affine real parameter of the extended lifted arc. -/
noncomputable def globalBandExtensionParameter (u : unitInterval) : ℝ :=
  F.globalBandExtensionSourceParameter b +
    (u : ℝ) * F.globalBandExtensionSpan b

/-- The selected circle arc, extended a positive distance past both seam endpoints and lifted to
the universal covering plane. -/
noncomputable def globalBandExtendedPlanePath :
    Path
      ((F.globalBandCircle b).zeroWindingPlaneLift
        (F.globalBandExtensionSourceParameter b))
      ((F.globalBandCircle b).zeroWindingPlaneLift
        (F.globalBandExtensionTargetParameter b)) where
  toContinuousMap :=
    ⟨fun u ↦ (F.globalBandCircle b).zeroWindingPlaneLift
      (F.globalBandExtensionParameter b u),
      (F.globalBandCircle b).continuous_zeroWindingPlaneLift.comp
        (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩
  source' := by simp [globalBandExtensionParameter]
  target' := by
    change (F.globalBandCircle b).zeroWindingPlaneLift
        (F.globalBandExtensionParameter b 1) = _
    congr 1
    change F.globalBandExtensionSourceParameter b +
      1 * F.globalBandExtensionSpan b = F.globalBandExtensionTargetParameter b
    unfold globalBandExtensionSpan
    ring

/-- The normalized location of the original left endpoint inside the extended interval. -/
noncomputable def globalBandCoreLeft : unitInterval :=
  ⟨F.globalBandExtensionMargin b / F.globalBandExtensionSpan b, by
    have hm := F.globalBandExtensionMargin_pos b
    have hs := F.globalBandExtensionSpan_pos b
    have hgap := F.globalBandLeftParameter_lt_rightParameter b
    constructor
    · exact (div_pos hm hs).le
    · rw [div_le_one hs]
      unfold globalBandExtensionSpan globalBandExtensionTargetParameter
        globalBandExtensionSourceParameter
      linarith⟩

/-- The normalized location of the original right endpoint inside the extended interval. -/
noncomputable def globalBandCoreRight : unitInterval :=
  ⟨(F.globalBandExtensionMargin b +
      (F.globalBandRightParameter b - F.globalBandLeftParameter b)) /
      F.globalBandExtensionSpan b, by
    have hm := F.globalBandExtensionMargin_pos b
    have hs := F.globalBandExtensionSpan_pos b
    have hgap := F.globalBandLeftParameter_lt_rightParameter b
    constructor
    · exact (div_pos (by linarith) hs).le
    · rw [div_le_one hs]
      unfold globalBandExtensionSpan globalBandExtensionTargetParameter
        globalBandExtensionSourceParameter
      linarith⟩

theorem globalBandCoreLeft_pos :
    (0 : unitInterval) < F.globalBandCoreLeft b := by
  change (0 : ℝ) < F.globalBandExtensionMargin b / F.globalBandExtensionSpan b
  exact div_pos (F.globalBandExtensionMargin_pos b)
    (F.globalBandExtensionSpan_pos b)

theorem globalBandCoreLeft_lt_coreRight :
    F.globalBandCoreLeft b < F.globalBandCoreRight b := by
  change F.globalBandExtensionMargin b / F.globalBandExtensionSpan b <
    (F.globalBandExtensionMargin b +
      (F.globalBandRightParameter b - F.globalBandLeftParameter b)) /
        F.globalBandExtensionSpan b
  exact div_lt_div_of_pos_right (by
    linarith [F.globalBandLeftParameter_lt_rightParameter b])
    (F.globalBandExtensionSpan_pos b)

theorem globalBandCoreRight_lt_one :
    F.globalBandCoreRight b < (1 : unitInterval) := by
  change (F.globalBandExtensionMargin b +
      (F.globalBandRightParameter b - F.globalBandLeftParameter b)) /
        F.globalBandExtensionSpan b < 1
  rw [div_lt_one (F.globalBandExtensionSpan_pos b)]
  unfold globalBandExtensionSpan globalBandExtensionTargetParameter
    globalBandExtensionSourceParameter
  linarith [F.globalBandExtensionMargin_pos b]

theorem globalBandExtensionParameter_coreLeft :
    F.globalBandExtensionParameter b (F.globalBandCoreLeft b) =
      F.globalBandLeftParameter b := by
  unfold globalBandExtensionParameter globalBandCoreLeft globalBandExtensionSourceParameter
  field_simp [ne_of_gt (F.globalBandExtensionSpan_pos b)]
  ring

theorem globalBandExtensionParameter_coreRight :
    F.globalBandExtensionParameter b (F.globalBandCoreRight b) =
      F.globalBandRightParameter b := by
  unfold globalBandExtensionParameter globalBandCoreRight globalBandExtensionSourceParameter
  field_simp [ne_of_gt (F.globalBandExtensionSpan_pos b)]
  ring

theorem globalBandExtensionParameter_mem_interval (u : unitInterval) :
    F.globalBandExtensionParameter b u ∈
      Icc (F.globalBandExtensionSourceParameter b)
        (F.globalBandExtensionTargetParameter b) := by
  unfold globalBandExtensionParameter globalBandExtensionSpan
  have hspan := F.globalBandExtensionSpan_pos b
  unfold globalBandExtensionSpan at hspan
  constructor <;> nlinarith [u.2.1, u.2.2]

theorem globalBandExtendedPlanePath_injective :
    Function.Injective (F.globalBandExtendedPlanePath b) := by
  intro u v huv
  let su := F.globalBandExtensionParameter b u
  let sv := F.globalBandExtensionParameter b v
  have hsu := F.globalBandExtensionParameter_mem_interval b u
  have hsv := F.globalBandExtensionParameter_mem_interval b v
  change F.globalBandExtensionSourceParameter b ≤ su ∧
    su ≤ F.globalBandExtensionTargetParameter b at hsu
  change F.globalBandExtensionSourceParameter b ≤ sv ∧
    sv ≤ F.globalBandExtensionTargetParameter b at hsv
  have hexp : Circle.exp su = Circle.exp sv := by
    apply (F.globalBandCircle b).isEmbedding.injective
    rw [(F.globalBandCircle b).parametrization,
      (F.globalBandCircle b).parametrization]
    have hprojected := congrArg (torusCoveringProjectionToTorus Phi) huv
    change torusCoveringProjectionToTorus Phi
        ((F.globalBandCircle b).zeroWindingPlaneLift su) =
      torusCoveringProjectionToTorus Phi
        ((F.globalBandCircle b).zeroWindingPlaneLift sv) at hprojected
    rw [F.torusCoveringProjection_globalBandCircle_planeLift b,
      F.torusCoveringProjection_globalBandCircle_planeLift b] at hprojected
    exact congrArg Subtype.val hprojected
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hnzero : n = 0 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · have hnleInt : n ≤ -1 := by omega
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast hnleInt
      have hshift : (n : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by
        simpa only [neg_mul, one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      have hperiod := F.globalBandExtensionSpan_lt_period b
      unfold globalBandExtensionSpan at hperiod
      linarith
    · exact hnzero
    · have hnleInt : 1 ≤ n := by omega
      have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hnleInt
      have hshift : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      have hperiod := F.globalBandExtensionSpan_lt_period b
      unfold globalBandExtensionSpan at hperiod
      linarith
  rw [hnzero, Int.cast_zero, zero_mul, add_zero] at hn
  apply Subtype.ext
  change F.globalBandExtensionSourceParameter b +
      (u : ℝ) * F.globalBandExtensionSpan b =
    F.globalBandExtensionSourceParameter b +
      (v : ℝ) * F.globalBandExtensionSpan b at hn
  nlinarith [F.globalBandExtensionSpan_pos b]

/-- The globally selected excursion, with a genuine injective extension in the covering plane. -/
noncomputable def globalBandExtendibleInjectivePath : Schoenflies.ExtendibleInjectivePath where
  extensionSource := (F.globalBandCircle b).zeroWindingPlaneLift
    (F.globalBandExtensionSourceParameter b)
  extensionTarget := (F.globalBandCircle b).zeroWindingPlaneLift
    (F.globalBandExtensionTargetParameter b)
  extension := F.globalBandExtendedPlanePath b
  coreLeft := F.globalBandCoreLeft b
  coreRight := F.globalBandCoreRight b
  coreLeft_pos := F.globalBandCoreLeft_pos b
  coreLeft_lt_coreRight := F.globalBandCoreLeft_lt_coreRight b
  coreRight_lt_one := F.globalBandCoreRight_lt_one b
  extension_injective := F.globalBandExtendedPlanePath_injective b

theorem globalBandExtendible_corePath_apply (u : unitInterval) :
    (F.globalBandExtendibleInjectivePath b).corePath u =
      (F.globalBandCircle b).zeroWindingPlaneLift
        (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) := by
  change (F.globalBandCircle b).zeroWindingPlaneLift
      (F.globalBandExtensionParameter b
        (Icc.convexComb (F.globalBandCoreLeft b) (F.globalBandCoreRight b) u)) = _
  congr 1
  unfold globalBandExtensionParameter globalInwardExcursionParameter
  simp only [Icc.coe_convexComb]
  dsimp [globalBandCoreLeft, globalBandCoreRight]
  field_simp [ne_of_gt (F.globalBandExtensionSpan_pos b)]
  unfold globalBandExtensionSourceParameter
  dsimp [globalBandLeftParameter, globalBandRightParameter]
  ring

theorem globalBandExtendedPlanePath_projection (u : unitInterval) :
    torusCoveringProjectionToTorus Phi (F.globalBandExtendedPlanePath b u) =
      (F.globalBandCircle b).windingLoop.curve
        (F.globalBandExtensionParameter b u) := by
  exact F.torusCoveringProjection_globalBandCircle_planeLift b _

theorem globalBandExtendedPlanePath_projection_injective :
    Function.Injective (fun u ↦
      torusCoveringProjectionToTorus Phi (F.globalBandExtendedPlanePath b u)) := by
  intro u v huv
  let su := F.globalBandExtensionParameter b u
  let sv := F.globalBandExtensionParameter b v
  have hsu := F.globalBandExtensionParameter_mem_interval b u
  have hsv := F.globalBandExtensionParameter_mem_interval b v
  change F.globalBandExtensionSourceParameter b ≤ su ∧
    su ≤ F.globalBandExtensionTargetParameter b at hsu
  change F.globalBandExtensionSourceParameter b ≤ sv ∧
    sv ≤ F.globalBandExtensionTargetParameter b at hsv
  have hexp : Circle.exp su = Circle.exp sv := by
    apply (F.globalBandCircle b).isEmbedding.injective
    rw [(F.globalBandCircle b).parametrization,
      (F.globalBandCircle b).parametrization]
    exact congrArg Subtype.val <| by
      simpa [su, sv, F.globalBandExtendedPlanePath_projection b] using huv
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hnzero : n = 0 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · have hnleInt : n ≤ -1 := by omega
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast hnleInt
      have hshift : (n : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by
        simpa only [neg_mul, one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      have hperiod := F.globalBandExtensionSpan_lt_period b
      unfold globalBandExtensionSpan at hperiod
      linarith
    · exact hnzero
    · have hnleInt : 1 ≤ n := by omega
      have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hnleInt
      have hshift : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
      have hperiod := F.globalBandExtensionSpan_lt_period b
      unfold globalBandExtensionSpan at hperiod
      linarith
  rw [hnzero, Int.cast_zero, zero_mul, add_zero] at hn
  apply Subtype.ext
  change F.globalBandExtensionSourceParameter b +
      (u : ℝ) * F.globalBandExtensionSpan b =
    F.globalBandExtensionSourceParameter b +
      (v : ℝ) * F.globalBandExtensionSpan b at hn
  nlinarith [F.globalBandExtensionSpan_pos b]

/-- An open neighborhood of the entire extended lift on which the covering projection is
injective.  Compactness upgrades pointwise local injectivity of the covering map. -/
theorem exists_open_injOn_globalBandExtendedPlanePath :
    ∃ U : Set TorusCoveringPlane,
      IsOpen U ∧ Set.range (F.globalBandExtendedPlanePath b) ⊆ U ∧
        Set.InjOn (torusCoveringProjectionToTorus Phi) U := by
  have hinj : Set.InjOn (torusCoveringProjectionToTorus Phi)
      (Set.range (F.globalBandExtendedPlanePath b)) := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ huv
    exact congrArg (F.globalBandExtendedPlanePath b)
      (F.globalBandExtendedPlanePath_projection_injective b huv)
  have hcompact : IsCompact (Set.range (F.globalBandExtendedPlanePath b)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image (F.globalBandExtendedPlanePath b).continuous
  have hlocal :=
    (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).isLocallyInjective
  exact hinj.exists_isOpen_superset hcompact
    (fun _ _ ↦ (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.continuousAt)
    (fun x _ ↦ (isLocallyInjective_iff_nhds.mp hlocal x))

/-- The two standard seam parametrizations agree through the covering-plane coordinate
homeomorphism. -/
theorem coveringPlaneCoordinates_symm_bandSeamPath (u : unitInterval) :
    coveringPlaneCoordinates.symm (bandSeamPath u) =
      Schoenflies.ExtendibleInjectivePath.bandSeamPath u := by
  apply coveringPlaneCoordinates.injective
  rw [coveringPlaneCoordinates.apply_symm_apply,
    Schoenflies.ExtendibleInjectivePath.bandSeamPath_eq_planePoint]
  change bandSeamPath u = (2 * (u : ℝ) - 1, 0)
  change Path.segment bandLeftVertex bandRightVertex u = _
  rw [Path.segment_apply]
  apply Prod.ext
  · simp [bandLeftVertex, bandRightVertex, AffineMap.lineMap_apply_module]
    ring
  · simp [bandLeftVertex, bandRightVertex, AffineMap.lineMap_apply_module]

/-- A global band chart whose surface patch is retained as an open subset of the transported
torus. -/
structure OpenGlobalBandTubularChartData where
  data : GlobalBandTubularChartData F b
  surfacePatch_open : IsOpen data.surfacePatch

/-- The planar extendible-arc strip descends through an injective covering neighborhood to the
desired transported-torus band chart. -/
theorem exists_openGlobalBandTubularChartData :
    Nonempty (OpenGlobalBandTubularChartData F b) := by
  let E := F.globalBandExtendibleInjectivePath b
  obtain ⟨Uinj, hUinjOpen, hpathUinj, hinj⟩ :=
    F.exists_open_injOn_globalBandExtendedPlanePath b
  let ambientBand : Set (transportedTorus Phi) :=
    {x | (x : R3) ∈ F.globalBandOpenNeighborhood b}
  have hambientBandOpen : IsOpen ambientBand :=
    (F.globalBandOpenNeighborhood_spec.1 b).1.preimage continuous_subtype_val
  let U : Set TorusCoveringPlane := Uinj ∩
    torusCoveringProjectionToTorus Phi ⁻¹' ambientBand
  have hUopen : IsOpen U := hUinjOpen.inter <|
    hambientBandOpen.preimage
      (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous
  have hcoreU : E.coreRange ⊆ U := by
    intro x hx
    rw [← E.range_corePath] at hx
    obtain ⟨u, rfl⟩ := hx
    constructor
    · apply hpathUinj
      exact ⟨Icc.convexComb E.coreLeft E.coreRight u, rfl⟩
    · change ((torusCoveringProjectionToTorus Phi (E.corePath u) :
          transportedTorus Phi) : R3) ∈ F.globalBandOpenNeighborhood b
      rw [show E.corePath u =
          (F.globalBandCircle b).zeroWindingPlaneLift
            (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) from
        F.globalBandExtendible_corePath_apply b u,
        F.torusCoveringProjection_globalBandCircle_planeLift]
      exact F.globalBandOpenNeighborhood_spec.1 b |>.2 ⟨u, rfl⟩
  obtain ⟨V, hVopen, hVU, e, heCore⟩ :=
    E.exists_tubularStrip_of_extendible hUopen hcoreU
  let pV : V → transportedTorus Phi :=
    fun x ↦ torusCoveringProjectionToTorus Phi x
  have hpVlocal : IsLocalHomeomorph pV := by
    change IsLocalHomeomorph
      (torusCoveringProjectionToTorus Phi ∘ (fun x : V ↦ (x : TorusCoveringPlane)))
    exact (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).comp
      hVopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hpVinj : Function.Injective pV := by
    intro x y hxy
    apply Subtype.ext
    apply hinj (hVU x.2).1 (hVU y.2).1 hxy
  have hpVopen : IsOpenEmbedding pV :=
    hpVlocal.isOpenEmbedding_of_injective hpVinj
  let ep : V ≃ₜ Set.range pV :=
    hpVopen.isEmbedding.toHomeomorph
  let strip : Submission.SurfaceRegularValue.Plane ≃ₜ Set.range pV :=
    coveringPlaneCoordinates.symm.trans (e.trans ep)
  have hstrip : Set.range (fun z ↦
      (((strip z : Set.range pV) : transportedTorus Phi) : R3)) ⊆
      F.globalBandOpenNeighborhood b := by
    rintro _ ⟨z, rfl⟩
    change ((pV (e (coveringPlaneCoordinates.symm z)) : transportedTorus Phi) : R3) ∈
      F.globalBandOpenNeighborhood b
    exact (hVU (e (coveringPlaneCoordinates.symm z)).2).2
  have halign : ∀ u : unitInterval,
      (((strip (bandSeamPath u) : Set.range pV) : transportedTorus Phi) : R3) =
        ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
    intro u
    change ((pV (e (coveringPlaneCoordinates.symm (bandSeamPath u))) :
      transportedTorus Phi) : R3) =
      ((F.globalBandPath b u : transportedTorus Phi) : R3)
    rw [coveringPlaneCoordinates_symm_bandSeamPath]
    calc
      ((pV (e (Schoenflies.ExtendibleInjectivePath.bandSeamPath u)) :
          transportedTorus Phi) : R3) =
          ((torusCoveringProjectionToTorus Phi (E.corePath u) :
            transportedTorus Phi) : R3) :=
        congrArg Subtype.val <| congrArg (torusCoveringProjectionToTorus Phi) (heCore u)
      _ = (((F.globalBandCircle b).windingLoop.curve
          (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) :
            transportedTorus Phi) : R3) := by
        rw [show E.corePath u =
            (F.globalBandCircle b).zeroWindingPlaneLift
              (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) from
          F.globalBandExtendible_corePath_apply b u,
          F.torusCoveringProjection_globalBandCircle_planeLift]
      _ = ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
        rfl
  let T := GlobalBandTubularChartData.ofStrip (Set.range pV) strip hstrip halign
  refine ⟨⟨T, ?_⟩⟩
  change IsOpen (Set.range pV)
  exact hpVopen.isOpen_range

/-- The open global band chart supplies the original chart data after forgetting openness. -/
theorem exists_globalBandTubularChartData :
    Nonempty (GlobalBandTubularChartData F b) :=
  ⟨(Classical.choice (F.exists_openGlobalBandTubularChartData b)).data⟩

/-- Choose an open transported-torus chart for the band indexed by `b`. -/
noncomputable def globalBandOpenTubularChartData :
    OpenGlobalBandTubularChartData F b :=
  Classical.choice (F.exists_openGlobalBandTubularChartData b)

/-- Choose the validated open tubular strip simultaneously for every canonical inward
excursion. -/
noncomputable def globalBandOpenTubularChartFamily
    (F : CutCircleTransverseCyclicOrderFamily G) :
    GlobalBandTubularChartFamily F where
  band b := (F.globalBandOpenTubularChartData b).data

theorem globalBandOpenTubularChartFamily_surfacePatch_open
    (F : CutCircleTransverseCyclicOrderFamily G)
    (b : Fin F.toPairedSeamEnumeration.bandCount) :
    IsOpen ((F.globalBandOpenTubularChartFamily).band b).surfacePatch :=
  (F.globalBandOpenTubularChartData b).surfacePatch_open

/-- Choose the validated tubular strip simultaneously for every canonical inward excursion. -/
noncomputable def globalBandTubularChartFamily
    (F : CutCircleTransverseCyclicOrderFamily G) :
    GlobalBandTubularChartFamily F where
  band b := Classical.choice (F.exists_globalBandTubularChartData b)

end CutCircleTransverseCyclicOrderFamily

end FiniteSuperellipsoidBarrierGraph

end Submission.Topology
