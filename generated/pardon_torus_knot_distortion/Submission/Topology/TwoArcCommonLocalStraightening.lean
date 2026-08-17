import Submission.PlaneSchoenflies.Schoenflies.ExtendibleArcTubularStrip
import Submission.Topology.CoherentThetaCanonicalCircles

/-!
# Local straightening along a shared two-arc edge

An injective arc in a two-arc Jordan presentation is automatically the core of a strictly
longer injective path: use short, disjoint terminal pieces of the return arc as its two tails.
This supplies the exact hypothesis consumed by the planar tubular-strip construction.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

variable {a b : Schoenflies.Plane}

namespace TwoArcStrictExtension

private def quarter : unitInterval :=
  ⟨(1 : ℝ) / 4, by constructor <;> norm_num⟩

private def half : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

private def threeQuarter : unitInterval :=
  ⟨(3 : ℝ) / 4, by constructor <;> norm_num⟩

private theorem subpath_injective_of_lt {x y : Schoenflies.Plane} (q : Path x y)
    (hq : Function.Injective q) {u v : unitInterval} (huv : u < v) :
    Function.Injective (q.subpath u v) := by
  intro s t hst
  apply Subtype.ext
  have hparameter := hq hst
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  have huv' : (u : ℝ) < v := huv
  nlinarith

/-- The initial short return tail, ending at the source of the shared arc. -/
def initialTail (q : Path b a) : Path (q threeQuarter) a :=
  (q.subpath threeQuarter 1).cast rfl q.target.symm

/-- The final short return tail, starting at the target of the shared arc. -/
def finalTail (q : Path b a) : Path b (q quarter) :=
  (q.subpath 0 quarter).cast q.source.symm rfl

/-- The return-tail extension in which `p` occupies the parameter interval `[1/4,1/2]`. -/
def extension (p : Path a b) (q : Path b a) :
    Path (q threeQuarter) (q quarter) :=
  ((initialTail q).trans p).trans (finalTail q)

private theorem initialTail_injective (q : Path b a) (hq : Function.Injective q) :
    Function.Injective (initialTail q) := by
  simpa only [initialTail, Path.cast_coe] using
    subpath_injective_of_lt q hq
      (show threeQuarter < 1 by
        change (3 / 4 : ℝ) < 1
        norm_num)

private theorem finalTail_injective (q : Path b a) (hq : Function.Injective q) :
    Function.Injective (finalTail q) := by
  simpa only [finalTail, Path.cast_coe] using
    subpath_injective_of_lt q hq
      (show (0 : unitInterval) < quarter by
        change (0 : ℝ) < 1 / 4
        norm_num)

private theorem initialTail_inter_shared
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Set.range (initialTail q) ∩ Set.range p = {a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨u, hu⟩, ⟨v, hvx⟩⟩
    change q (Icc.convexComb threeQuarter 1 u) = x at hu
    have hmem : p v ∈ Set.range p ∩ Set.range q := by
      refine ⟨⟨v, rfl⟩, ?_⟩
      refine ⟨Icc.convexComb threeQuarter 1 u, ?_⟩
      exact hu.trans hvx.symm
    rw [D.range_inter] at hmem
    rcases hmem with hva | hvb
    · exact Set.mem_singleton_iff.mpr (hvx.symm.trans hva)
    · rw [Set.mem_singleton_iff] at hvb
      have hv : v = 1 := D.first_injective (hvb.trans p.target.symm)
      subst v
      have hqzero : Icc.convexComb threeQuarter 1 u = 0 := by
        apply D.second_injective
        simpa only [q.source] using hu.trans (hvx.symm.trans hvb)
      have hvalue := congrArg Subtype.val hqzero
      simp only [Icc.coe_convexComb] at hvalue
      norm_num [threeQuarter] at hvalue
      nlinarith [u.2.1, u.2.2]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, by simp [initialTail]⟩, ⟨0, p.source⟩⟩

private theorem shared_inter_finalTail
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Set.range p ∩ Set.range (finalTail q) = {b} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨v, hvx⟩, ⟨u, hu⟩⟩
    change q (Icc.convexComb 0 quarter u) = x at hu
    have hmem : p v ∈ Set.range p ∩ Set.range q := by
      refine ⟨⟨v, rfl⟩, ?_⟩
      refine ⟨Icc.convexComb 0 quarter u, ?_⟩
      exact hu.trans hvx.symm
    rw [D.range_inter] at hmem
    rcases hmem with hva | hvb
    · have hv : v = 0 := D.first_injective (hva.trans p.source.symm)
      subst v
      have hqone : Icc.convexComb 0 quarter u = 1 := by
        apply D.second_injective
        simpa only [q.target] using hu.trans (hvx.symm.trans hva)
      have hvalue := congrArg Subtype.val hqone
      simp only [Icc.coe_convexComb] at hvalue
      norm_num [quarter] at hvalue
      nlinarith [u.2.1, u.2.2]
    · exact Set.mem_singleton_iff.mpr (hvx.symm.trans hvb)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, p.target⟩, ⟨0, by simp [finalTail]⟩⟩

private theorem initialTail_disjoint_finalTail
    (q : Path b a) (hq : Function.Injective q) :
    Disjoint (Set.range (initialTail q)) (Set.range (finalTail q)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, huv⟩
  change q (Icc.convexComb 0 quarter v) =
      q (Icc.convexComb threeQuarter 1 u) at huv
  have hparameter : Icc.convexComb threeQuarter 1 u =
      Icc.convexComb 0 quarter v := by
    apply hq
    exact huv.symm
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  norm_num [threeQuarter, quarter] at hvalue
  nlinarith [u.2.1, u.2.2, v.2.1, v.2.2]

private theorem initialTransShared_injective
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Function.Injective ((initialTail q).trans p) :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter _ _
    (initialTail_injective q D.second_injective) D.first_injective
    (initialTail_inter_shared p q D)

private theorem initialTransShared_inter_finalTail
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Set.range ((initialTail q).trans p) ∩ Set.range (finalTail q) = {b} := by
  rw [Path.trans_range, Set.union_inter_distrib_right,
    Set.disjoint_iff_inter_eq_empty.mp
      (initialTail_disjoint_finalTail q D.second_injective),
    shared_inter_finalTail p q D, Set.empty_union]

theorem extension_injective
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Function.Injective (extension p q) :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter _ _
    (initialTransShared_injective p q D)
    (finalTail_injective q D.second_injective)
    (initialTransShared_inter_finalTail p q D)

/-- The canonical strict extension of the first arc in a two-arc Jordan presentation. -/
def data (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    ExtendibleInjectivePath where
  extensionSource := q threeQuarter
  extensionTarget := q quarter
  extension := extension p q
  coreLeft := quarter
  coreRight := half
  coreLeft_pos := by change (0 : ℝ) < 1 / 4; norm_num
  coreLeft_lt_coreRight := by norm_num [quarter, half]
  coreRight_lt_one := by change (1 / 2 : ℝ) < 1; norm_num
  extension_injective := extension_injective p q D

theorem corePath_apply
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q)
    (t : unitInterval) :
    (data p q D).corePath t = p t := by
  rw [ExtendibleInjectivePath.corePath, Path.subpath]
  change extension p q (Icc.convexComb quarter half t) = p t
  rw [extension, Path.trans_apply]
  have houter : ((Icc.convexComb quarter half t : unitInterval) : ℝ) ≤ 1 / 2 := by
    simp only [Icc.coe_convexComb, quarter, half]
    nlinarith [t.2.1, t.2.2]
  simp only [dif_pos houter]
  rw [Path.trans_apply]
  split_ifs with hinner
  · have htzero : t = 0 := by
      apply Subtype.ext
      change 2 * (Icc.convexComb quarter half t : ℝ) ≤ 1 / 2 at hinner
      simp only [Icc.coe_convexComb, quarter, half] at hinner
      dsimp
      nlinarith [t.2.1]
    subst t
    calc
      (initialTail q) _ = (initialTail q) 1 := by
        congr 1
        apply Subtype.ext
        norm_num [Icc.coe_convexComb, quarter, half]
      _ = p 0 := by rw [(initialTail q).target, p.source]
  ·
    apply congrArg p
    apply Subtype.ext
    simp only [Icc.coe_convexComb, quarter, half]
    ring

theorem range_corePath
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    Set.range (data p q D).corePath = Set.range p := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, (corePath_apply p q D t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, corePath_apply p q D t⟩

end TwoArcStrictExtension

namespace TwoArcCommonLocalStraightening

open ExtendibleInjectivePath

private theorem bandSeamPath_eq_segmentPath (t : unitInterval) :
    bandSeamPath t = Path.segment (bandSeamPath 0) (bandSeamPath 1) t := by
  simp only [bandSeamPath_eq_planePoint, Path.segment_apply,
    AffineMap.lineMap_apply_module]
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.plane_ext
  · simp only [LeanEval.Topology.ClassificationOfSurfaces.Moise.planePoint_apply_zero,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    norm_num
    ring
  · simp only [
      LeanEval.Topology.ClassificationOfSurfaces.Moise.planePoint_apply_one,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_zero, add_zero]

private theorem range_bandSeamPath :
    Set.range bandSeamPath = segment ℝ (bandSeamPath 0) (bandSeamPath 1) := by
  rw [← Path.range_segment]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, (bandSeamPath_eq_segmentPath t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, bandSeamPath_eq_segmentPath t⟩

private theorem bandSeamPath_mem_openSegment (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) :
    bandSeamPath t ∈ openSegment ℝ (bandSeamPath 0) (bandSeamPath 1) := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨(t : ℝ), ?_, ?_⟩
  · exact ⟨ht.1, ht.2⟩
  · exact (bandSeamPath_eq_segmentPath t).symm

private theorem bandSeamPath_endpoints_ne :
    bandSeamPath (0 : unitInterval) ≠ bandSeamPath 1 := by
  intro h
  rw [bandSeamPath_eq_planePoint, bandSeamPath_eq_planePoint] at h
  have hcoord := congrArg (fun z : Plane ↦ z 0) h
  norm_num [LeanEval.Topology.ClassificationOfSurfaces.Moise.planePoint] at hcoord

private def straightener
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) : Plane ≃ₜ Plane :=
  (TwoArcStrictExtension.data p q D).ambientCoreStraightener.symm

private theorem straightener_apply_shared
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q)
    (t : unitInterval) :
    straightener p q D (p t) = bandSeamPath t := by
  change (TwoArcStrictExtension.data p q D).ambientCoreStraightener.symm (p t) = _
  apply (TwoArcStrictExtension.data p q D).ambientCoreStraightener.injective
  rw [Homeomorph.apply_symm_apply,
    ExtendibleInjectivePath.ambientCoreStraightener_apply_bandSeamPath,
    TwoArcStrictExtension.corePath_apply]

private theorem image_range_shared
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q) :
    straightener p q D '' Set.range p = Set.range bandSeamPath := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (straightener_apply_shared p q D t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨p t, ⟨t, rfl⟩, straightener_apply_shared p q D t⟩

private theorem shared_point_not_mem_return
    (p : Path a b) (q : Path b a) (D : TwoArcCircle.Data p q)
    (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
    p t ∉ Set.range q := by
  rintro ⟨u, hu⟩
  have hmem : p t ∈ Set.range p ∩ Set.range q :=
    ⟨⟨t, rfl⟩, ⟨u, hu⟩⟩
  rw [D.range_inter] at hmem
  rcases hmem with hsource | htarget
  · have : t = 0 := D.first_injective (hsource.trans p.source.symm)
    exact ht.1.ne this.symm
  · have : t = 1 := D.first_injective (htarget.trans p.target.symm)
    exact ht.2.ne this

private theorem straightened_point_not_mem_return
    (p : Path a b) (q₀ q₁ : Path b a)
    (D₀ : TwoArcCircle.Data p q₀) (D₁ : TwoArcCircle.Data p q₁)
    (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
    bandSeamPath t ∉
      straightener p q₀ D₀ '' (Set.range q₀ ∪ Set.range q₁) := by
  rintro ⟨x, hx, hmap⟩
  have hxEq : x = p t := by
    apply (straightener p q₀ D₀).injective
    rw [hmap, straightener_apply_shared]
  rcases hx with hx₀ | hx₁
  · exact shared_point_not_mem_return p q₀ D₀ t ht (hxEq ▸ hx₀)
  · exact shared_point_not_mem_return p q₁ D₁ t ht (hxEq ▸ hx₁)

private theorem straightened_return_isCompact
    (p : Path a b) (q₀ q₁ : Path b a) (D₀ : TwoArcCircle.Data p q₀) :
    IsCompact (straightener p q₀ D₀ '' (Set.range q₀ ∪ Set.range q₁)) := by
  apply IsCompact.image (isCompact_range q₀.continuous |>.union
    (isCompact_range q₁.continuous))
  exact (straightener p q₀ D₀).continuous

private theorem range_bandSeamPath_subset_determinantLine (t : unitInterval) :
    Set.range bandSeamPath ⊆
      determinantLine (bandSeamPath t) (bandSeamPath 1 - bandSeamPath 0) := by
  rintro _ ⟨u, rfl⟩
  simp only [determinantLine, mem_ofPred_eq, bandSeamPath_eq_planePoint]
  simp [planeDet,
    LeanEval.Topology.ClassificationOfSurfaces.Moise.planePoint]

private theorem mapped_twoArc_carrier
    (p : Path a b) (q₀ q : Path b a)
    (D₀ : TwoArcCircle.Data p q₀) (D : TwoArcCircle.Data p q) :
    ((twoArcJordanCircle p q D.first_injective D.second_injective D.range_inter).mapHomeomorph
      (straightener p q₀ D₀)).carrier =
      Set.range bandSeamPath ∪ straightener p q₀ D₀ '' Set.range q := by
  rw [Schoenflies.JordanCircle.carrier_mapHomeomorph,
    carrier_twoArcJordanCircle, Set.image_union, image_range_shared]

private theorem local_mapped_twoArc_carrier
    (p : Path a b) (q₀ q₁ q : Path b a)
    (D₀ : TwoArcCircle.Data p q₀) (D : TwoArcCircle.Data p q)
    (t : unitInterval) (r rLine : ℝ)
    (hrLine : r ≤ rLine)
    (hline : Metric.ball (bandSeamPath t) rLine ∩
        determinantLine (bandSeamPath t) (bandSeamPath 1 - bandSeamPath 0) ⊆
      segment ℝ (bandSeamPath 0) (bandSeamPath 1))
    (hballAway : Metric.ball (bandSeamPath t) r ⊆
      (straightener p q₀ D₀ '' (Set.range q₀ ∪ Set.range q₁))ᶜ)
    (hq : Set.range q ⊆ Set.range q₀ ∪ Set.range q₁) :
    Metric.ball (bandSeamPath t) r ∩
        ((twoArcJordanCircle p q D.first_injective D.second_injective
          D.range_inter).mapHomeomorph (straightener p q₀ D₀)).carrier =
      Metric.ball (bandSeamPath t) r ∩
        determinantLine (bandSeamPath t) (bandSeamPath 1 - bandSeamPath 0) := by
  rw [mapped_twoArc_carrier p q₀ q D₀ D]
  ext x
  constructor
  · rintro ⟨hxBall, hxSeam | hxReturn⟩
    · exact ⟨hxBall, range_bandSeamPath_subset_determinantLine t hxSeam⟩
    · exfalso
      rcases hxReturn with ⟨y, hy, rfl⟩
      exact hballAway hxBall ⟨y, hq hy, rfl⟩
  · rintro ⟨hxBall, hxLine⟩
    have hxBigBall : x ∈ Metric.ball (bandSeamPath t) rLine := by
      exact Metric.ball_subset_ball hrLine hxBall
    have hxSegment := hline ⟨hxBigBall, hxLine⟩
    rw [← range_bandSeamPath] at hxSegment
    exact ⟨hxBall, Or.inl hxSegment⟩

/-- Two Jordan circles sharing an injective first arc have the same straight local germ at every
relative-interior point of that arc. -/
noncomputable def commonLocalStraighteningData
    (p : Path a b) (q₀ q₁ : Path b a)
    (D₀ : TwoArcCircle.Data p q₀) (D₁ : TwoArcCircle.Data p q₁)
    (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
    CommonLocalStraighteningData
      (twoArcJordanCircle p q₀ D₀.first_injective D₀.second_injective D₀.range_inter)
      (twoArcJordanCircle p q₁ D₁.first_injective D₁.second_injective D₁.range_inter)
      (p t) := by
  let lineExists :=
    exists_ball_inter_determinantLine_subset_segment bandSeamPath_endpoints_ne
      (bandSeamPath_mem_openSegment t ht)
  let rLine := Classical.choose lineExists
  have hrLine := (Classical.choose_spec lineExists).1
  have hline := (Classical.choose_spec lineExists).2
  let returnCarrier :=
    straightener p q₀ D₀ '' (Set.range q₀ ∪ Set.range q₁)
  have hreturnCompact : IsCompact returnCarrier :=
    straightened_return_isCompact p q₀ q₁ D₀
  have hpointAway : bandSeamPath t ∈ returnCarrierᶜ :=
    straightened_point_not_mem_return p q₀ q₁ D₀ D₁ t ht
  let awayExists :=
    Metric.isOpen_iff.mp hreturnCompact.isClosed.isOpen_compl _ hpointAway
  let rAway := Classical.choose awayExists
  have hrAway := (Classical.choose_spec awayExists).1
  have hballAwayLarge := (Classical.choose_spec awayExists).2
  let r := min rLine rAway
  have hr : 0 < r := lt_min hrLine hrAway
  have hballAway : Metric.ball (bandSeamPath t) r ⊆ returnCarrierᶜ := by
    exact (Metric.ball_subset_ball (min_le_right rLine rAway)).trans hballAwayLarge
  refine
    { imagePoint := bandSeamPath t
      direction := bandSeamPath 1 - bandSeamPath 0
      radius := r
      homeomorph := straightener p q₀ D₀
      map_point := straightener_apply_shared p q₀ D₀ t
      radius_pos := hr
      point_mem_first := ?_
      local_first := ?_
      local_second := ?_ }
  · rw [carrier_twoArcJordanCircle]
    exact Or.inl ⟨t, rfl⟩
  · exact local_mapped_twoArc_carrier p q₀ q₁ q₀ D₀ D₀ t r rLine
      (min_le_left _ _) hline hballAway Set.subset_union_left
  · exact local_mapped_twoArc_carrier p q₀ q₁ q₁ D₀ D₁ t r rLine
      (min_le_left _ _) hline hballAway Set.subset_union_right

end TwoArcCommonLocalStraightening

namespace CommonLocalStraighteningData

/-- Local straightening depends only on the two Jordan carriers, not their parametrizations. -/
noncomputable def of_carrier_eq
    {J₀ J₁ K₀ K₁ : JordanCircle} {p : Plane}
    (D : CommonLocalStraighteningData J₀ J₁ p)
    (h₀ : K₀.carrier = J₀.carrier) (h₁ : K₁.carrier = J₁.carrier) :
    CommonLocalStraighteningData K₀ K₁ p where
  imagePoint := D.imagePoint
  direction := D.direction
  radius := D.radius
  homeomorph := D.homeomorph
  map_point := D.map_point
  radius_pos := D.radius_pos
  point_mem_first := by simpa only [h₀] using D.point_mem_first
  local_first := by
    simpa only [JordanCircle.carrier_mapHomeomorph, h₀] using D.local_first
  local_second := by
    simpa only [JordanCircle.carrier_mapHomeomorph, h₁] using D.local_second

end CommonLocalStraighteningData

namespace TorusThetaPathSystem.CoherentPlaneLiftData

open LeanEval.KnotTheory.PardonDistortion
open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {T : TorusThetaPathSystem Phi}

private theorem edgePairData (L : T.CoherentPlaneLiftData) (i j : Fin 3) (hij : i ≠ j) :
    TwoArcCircle.Data (L.edgeLift i) (L.edgeLift j).symm where
  first_injective := L.edgeLift_injective i
  second_injective := by
    intro u v huv
    apply unitInterval.symm_bijective.injective
    apply L.edgeLift_injective j
    simpa only [Path.symm_apply, Function.comp_apply] using huv
  range_inter := by
    rw [Path.symm_range]
    exact L.edgeLift_range_inter hij

private theorem parameter_mem_Ioo_of_not_endpoints
    (L : T.CoherentPlaneLiftData) (i : Fin 3) (t : unitInterval)
    (hprivate : L.edgeLift i t ∉ ({L.sourceLift, L.targetLift} : Set Plane)) :
    t ∈ Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro ht
    apply hprivate
    subst t
    exact Or.inl (L.edgeLift i).source
  have ht1 : t ≠ 1 := by
    intro ht
    apply hprivate
    subst t
    exact Or.inr (L.edgeLift i).target
  exact ⟨lt_of_le_of_ne t.2.1 ht0.symm, lt_of_le_of_ne t.2.2 ht1⟩

private noncomputable def localAlongEdge
    (L : T.CoherentPlaneLiftData) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k)
    (K₀ K₁ : JordanCircle)
    (hK₀ : K₀.carrier = Set.range (L.edgeLift i) ∪ Set.range (L.edgeLift j))
    (hK₁ : K₁.carrier = Set.range (L.edgeLift i) ∪ Set.range (L.edgeLift k)) :
    ∀ x ∈ Set.range (L.edgeLift i) \ ({L.sourceLift, L.targetLift} : Set Plane),
      CommonLocalStraighteningData K₀ K₁ x := by
  intro x hx
  let t := Classical.choose hx.1
  have htValue : L.edgeLift i t = x := Classical.choose_spec hx.1
  have htPrivate : L.edgeLift i t ∉ ({L.sourceLift, L.targetLift} : Set Plane) := by
    simpa only [htValue] using hx.2
  let D₀ := edgePairData L i j hij
  let D₁ := edgePairData L i k hik
  let raw := TwoArcCommonLocalStraightening.commonLocalStraighteningData
    (L.edgeLift i) (L.edgeLift j).symm (L.edgeLift k).symm D₀ D₁ t
      (parameter_mem_Ioo_of_not_endpoints L i t htPrivate)
  have result : CommonLocalStraighteningData K₀ K₁ (L.edgeLift i t) :=
    CommonLocalStraighteningData.of_carrier_eq raw
      (by rw [hK₀, carrier_twoArcJordanCircle, Path.symm_range])
      (by rw [hK₁, carrier_twoArcJordanCircle, Path.symm_range])
  simpa only [htValue] using result

/-- Every coherent lifted theta graph has canonical common local straightenings; only its two
vertices need to be excluded. -/
noncomputable def canonicalLocalStraighteningData (L : T.CoherentPlaneLiftData) :
    L.CanonicalLocalStraighteningData where
  exceptional := {L.sourceLift, L.targetLift}
  exceptional_finite := Set.Finite.insert _ (Set.finite_singleton _)
  local0 := localAlongEdge L 0 1 2 (by decide) (by decide)
    L.circle01 L.circle02 L.carrier_circle01 L.carrier_circle02
  local1 := localAlongEdge L 1 0 2 (by decide) (by decide)
    L.circle01 L.circle12 (by rw [L.carrier_circle01, Set.union_comm])
      L.carrier_circle12
  local2 := localAlongEdge L 2 0 1 (by decide) (by decide)
    L.circle02 L.circle12 (by rw [L.carrier_circle02, Set.union_comm])
      (by rw [L.carrier_circle12, Set.union_comm])

/-- The canonical invariant planar theta package associated to any coherent plane lift. -/
noncomputable def topologicalPlanarJordanThetaData (L : T.CoherentPlaneLiftData) :
    TopologicalPlanarJordanThetaData :=
  L.canonicalLocalStraighteningData.toJordanLocalStraighteningData
    |>.toTopologicalPlanarJordanThetaData

/-- A coherent plane theta lift has an outer cycle without any additional local-flatness input. -/
theorem exists_outer_cycle_decomposition (L : T.CoherentPlaneLiftData) :
    closure L.circle01.inside = closure L.circle02.inside ∪ closure L.circle12.inside ∨
      closure L.circle02.inside = closure L.circle01.inside ∪ closure L.circle12.inside ∨
      closure L.circle12.inside = closure L.circle01.inside ∪ closure L.circle02.inside := by
  exact L.topologicalPlanarJordanThetaData.exists_outer_cycle_decomposition

end TorusThetaPathSystem.CoherentPlaneLiftData

end Submission.Topology
