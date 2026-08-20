import Submission.Topology.SuperellipsoidCanonicalSeamFlowChartInclusion
import Submission.PlaneSchoenflies.Schoenflies.PolyhedralDiskNeighborhoods

/-!
# The canonical embedded four-port tree in strip coordinates

The narrowed seam-flow arms are reparametrized from bottom to top by the unit interval.  Together
with the fixed horizontal seam path they give the finite embedded tree whose relative planar
straightening upgrades the global band chart to the exact standard `T` chart.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev BandIndex := Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private def armMidParameter : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Affine reparametrization of the narrowed flow interval from bottom to top. -/
def centralOuterArmTime (u : unitInterval) :
    globalBandFlowCollarTimes D.openChartNarrowedData.heightData.band :=
  ⟨-D.openChartNarrowedData.heightData.band.ε +
      (u : ℝ) * (2 * D.openChartNarrowedData.heightData.band.ε), by
    constructor <;> nlinarith [u.2.1, u.2.2,
      D.openChartNarrowedData.heightData.band.ε_pos]⟩

theorem continuous_centralOuterArmTime : Continuous D.centralOuterArmTime := by
  apply Continuous.subtype_mk
  fun_prop

theorem centralOuterArmTime_injective : Function.Injective D.centralOuterArmTime := by
  intro u v huv
  apply Subtype.ext
  have hvalue := congrArg Subtype.val huv
  change -D.openChartNarrowedData.heightData.band.ε +
      (u : ℝ) * (2 * D.openChartNarrowedData.heightData.band.ε) =
    -D.openChartNarrowedData.heightData.band.ε +
      (v : ℝ) * (2 * D.openChartNarrowedData.heightData.band.ε) at hvalue
  nlinarith [D.openChartNarrowedData.heightData.band.ε_pos]

private theorem centralOuterArmTime_mid :
    D.centralOuterArmTime armMidParameter =
      globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band := by
  apply Subtype.ext
  change -D.openChartNarrowedData.heightData.band.ε +
      (1 / 2 : ℝ) * (2 * D.openChartNarrowedData.heightData.band.ε) = 0
  ring

/-- The complete left outer port inside the canonical strip. -/
def centralLeftOuterArmPath (b : D.BandIndex) : Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0))
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1)) where
  toFun := fun u ↦ D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime u)
  continuous_toFun := (D.continuous_centralLeftOuterArmCoordinate b).comp
    D.continuous_centralOuterArmTime
  source' := rfl
  target' := rfl

/-- The complete right outer port inside the canonical strip. -/
def centralRightOuterArmPath (b : D.BandIndex) : Path
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0))
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)) where
  toFun := fun u ↦ D.centralRightOuterArmCoordinate b (D.centralOuterArmTime u)
  continuous_toFun := (D.continuous_centralRightOuterArmCoordinate b).comp
    D.continuous_centralOuterArmTime
  source' := rfl
  target' := rfl

theorem centralLeftOuterArmPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralLeftOuterArmPath b) :=
  (D.centralLeftOuterArmCoordinate_injective b).comp D.centralOuterArmTime_injective

theorem centralRightOuterArmPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralRightOuterArmPath b) :=
  (D.centralRightOuterArmCoordinate_injective b).comp D.centralOuterArmTime_injective

theorem centralLeftOuterArmPath_disjoint_centralRightOuterArmPath (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftOuterArmPath b))
      (Set.range (D.centralRightOuterArmPath b)) := by
  apply (D.centralLeftOuterArmCoordinate_disjoint_centralRightOuterArmCoordinate b).mono
  · rintro _ ⟨u, rfl⟩
    exact ⟨D.centralOuterArmTime u, rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨D.centralOuterArmTime u, rfl⟩

theorem centralLeftOuterArmPath_mid (b : D.BandIndex) :
    D.centralLeftOuterArmPath b armMidParameter = bandLeftVertex := by
  change D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime armMidParameter) = _
  rw [D.centralOuterArmTime_mid, D.centralLeftOuterArmCoordinate_zero]

theorem centralRightOuterArmPath_mid (b : D.BandIndex) :
    D.centralRightOuterArmPath b armMidParameter = bandRightVertex := by
  change D.centralRightOuterArmCoordinate b (D.centralOuterArmTime armMidParameter) = _
  rw [D.centralOuterArmTime_mid, D.centralRightOuterArmCoordinate_zero]

/-- The lower half of the left outer arm, ending at the left seam vertex. -/
def centralLeftLowerBranchPath (b : D.BandIndex) : Path
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 0)) bandLeftVertex :=
  ((D.centralLeftOuterArmPath b).subpath 0 armMidParameter).cast
    rfl (D.centralLeftOuterArmPath_mid b).symm

/-- The upper half of the left outer arm, starting at the left seam vertex. -/
def centralLeftUpperBranchPath (b : D.BandIndex) : Path bandLeftVertex
    (D.centralLeftOuterArmCoordinate b (D.centralOuterArmTime 1)) :=
  ((D.centralLeftOuterArmPath b).subpath armMidParameter 1).cast
    (D.centralLeftOuterArmPath_mid b).symm rfl

/-- The lower half of the right outer arm, ending at the right seam vertex. -/
def centralRightLowerBranchPath (b : D.BandIndex) : Path
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 0)) bandRightVertex :=
  ((D.centralRightOuterArmPath b).subpath 0 armMidParameter).cast
    rfl (D.centralRightOuterArmPath_mid b).symm

/-- The upper half of the right outer arm, starting at the right seam vertex. -/
def centralRightUpperBranchPath (b : D.BandIndex) : Path bandRightVertex
    (D.centralRightOuterArmCoordinate b (D.centralOuterArmTime 1)) :=
  ((D.centralRightOuterArmPath b).subpath armMidParameter 1).cast
    (D.centralRightOuterArmPath_mid b).symm rfl

private theorem subpath_injective_of_lt {x y : Plane} (p : Path x y)
    (hp : Function.Injective p) {u v : unitInterval} (huv : u < v) :
    Function.Injective (p.subpath u v) := by
  intro s t hst
  apply Subtype.ext
  have hparameter := hp hst
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  have huv' : (u : ℝ) < v := huv
  nlinarith

theorem centralLeftLowerBranchPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralLeftLowerBranchPath b) := by
  intro u v huv
  apply subpath_injective_of_lt (D.centralLeftOuterArmPath b)
    (D.centralLeftOuterArmPath_injective b)
    (show (0 : unitInterval) < armMidParameter by
      change (0 : ℝ) < 1 / 2
      norm_num)
  change (D.centralLeftOuterArmPath b).subpath 0 armMidParameter u =
    (D.centralLeftOuterArmPath b).subpath 0 armMidParameter v at huv
  exact huv

theorem centralLeftUpperBranchPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralLeftUpperBranchPath b) := by
  intro u v huv
  apply subpath_injective_of_lt (D.centralLeftOuterArmPath b)
    (D.centralLeftOuterArmPath_injective b)
    (show armMidParameter < (1 : unitInterval) by
      change (1 / 2 : ℝ) < 1
      norm_num)
  change (D.centralLeftOuterArmPath b).subpath armMidParameter 1 u =
    (D.centralLeftOuterArmPath b).subpath armMidParameter 1 v at huv
  exact huv

theorem centralRightLowerBranchPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralRightLowerBranchPath b) := by
  intro u v huv
  apply subpath_injective_of_lt (D.centralRightOuterArmPath b)
    (D.centralRightOuterArmPath_injective b)
    (show (0 : unitInterval) < armMidParameter by
      change (0 : ℝ) < 1 / 2
      norm_num)
  change (D.centralRightOuterArmPath b).subpath 0 armMidParameter u =
    (D.centralRightOuterArmPath b).subpath 0 armMidParameter v at huv
  exact huv

theorem centralRightUpperBranchPath_injective (b : D.BandIndex) :
    Function.Injective (D.centralRightUpperBranchPath b) := by
  intro u v huv
  apply subpath_injective_of_lt (D.centralRightOuterArmPath b)
    (D.centralRightOuterArmPath_injective b)
    (show armMidParameter < (1 : unitInterval) by
      change (1 / 2 : ℝ) < 1
      norm_num)
  change (D.centralRightOuterArmPath b).subpath armMidParameter 1 u =
    (D.centralRightOuterArmPath b).subpath armMidParameter 1 v at huv
  exact huv

private theorem range_subpath_zero_mid_union_subpath_mid_one {x y : Plane}
    (p : Path x y) (m : unitInterval) :
    Set.range (p.subpath 0 m) ∪ Set.range (p.subpath m 1) = Set.range p := by
  rw [Path.range_subpath_of_le p 0 m bot_le,
    Path.range_subpath_of_le p m 1 le_top]
  ext z
  constructor
  · rintro (⟨u, _, rfl⟩ | ⟨u, _, rfl⟩)
    · exact ⟨u, rfl⟩
    · exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    by_cases hu : u ≤ m
    · exact Or.inl ⟨u, ⟨bot_le, hu⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨le_of_not_ge hu, le_top⟩, rfl⟩

theorem centralLeftBranchPaths_range_union (b : D.BandIndex) :
    Set.range (D.centralLeftLowerBranchPath b) ∪
        Set.range (D.centralLeftUpperBranchPath b) =
      Set.range (D.centralLeftOuterArmPath b) := by
  change Set.range ((D.centralLeftOuterArmPath b).subpath 0 armMidParameter) ∪
      Set.range ((D.centralLeftOuterArmPath b).subpath armMidParameter 1) = _
  exact range_subpath_zero_mid_union_subpath_mid_one
    (D.centralLeftOuterArmPath b) armMidParameter

theorem centralRightBranchPaths_range_union (b : D.BandIndex) :
    Set.range (D.centralRightLowerBranchPath b) ∪
        Set.range (D.centralRightUpperBranchPath b) =
      Set.range (D.centralRightOuterArmPath b) := by
  change Set.range ((D.centralRightOuterArmPath b).subpath 0 armMidParameter) ∪
      Set.range ((D.centralRightOuterArmPath b).subpath armMidParameter 1) = _
  exact range_subpath_zero_mid_union_subpath_mid_one
    (D.centralRightOuterArmPath b) armMidParameter

private theorem range_subpath_zero_mid_inter_subpath_mid_one {x y : Plane}
    (p : Path x y) (hp : Function.Injective p) (m : unitInterval) :
    Set.range (p.subpath 0 m) ∩ Set.range (p.subpath m 1) = {p m} := by
  rw [Path.range_subpath_of_le p 0 m bot_le,
    Path.range_subpath_of_le p m 1 le_top]
  ext z
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have huv : u = v := hp hvu.symm
    subst v
    have hum : u = m := le_antisymm hu.2 hv.1
    subst u
    rfl
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨⟨m, ⟨bot_le, le_rfl⟩, rfl⟩,
      ⟨m, ⟨le_rfl, le_top⟩, rfl⟩⟩

theorem centralLeftBranchPaths_range_inter (b : D.BandIndex) :
    Set.range (D.centralLeftLowerBranchPath b) ∩
        Set.range (D.centralLeftUpperBranchPath b) =
      {bandLeftVertex} := by
  change Set.range ((D.centralLeftOuterArmPath b).subpath 0 armMidParameter) ∩
      Set.range ((D.centralLeftOuterArmPath b).subpath armMidParameter 1) = _
  rw [← D.centralLeftOuterArmPath_mid b]
  exact range_subpath_zero_mid_inter_subpath_mid_one
    (D.centralLeftOuterArmPath b) (D.centralLeftOuterArmPath_injective b)
    armMidParameter

theorem centralRightBranchPaths_range_inter (b : D.BandIndex) :
    Set.range (D.centralRightLowerBranchPath b) ∩
        Set.range (D.centralRightUpperBranchPath b) =
      {bandRightVertex} := by
  change Set.range ((D.centralRightOuterArmPath b).subpath 0 armMidParameter) ∩
      Set.range ((D.centralRightOuterArmPath b).subpath armMidParameter 1) = _
  rw [← D.centralRightOuterArmPath_mid b]
  exact range_subpath_zero_mid_inter_subpath_mid_one
    (D.centralRightOuterArmPath b) (D.centralRightOuterArmPath_injective b)
    armMidParameter

theorem centralLeftLowerBranchPath_range_subset_outerArm (b : D.BandIndex) :
    Set.range (D.centralLeftLowerBranchPath b) ⊆
      Set.range (D.centralLeftOuterArmPath b) := by
  rw [← D.centralLeftBranchPaths_range_union b]
  exact Set.subset_union_left

theorem centralLeftUpperBranchPath_range_subset_outerArm (b : D.BandIndex) :
    Set.range (D.centralLeftUpperBranchPath b) ⊆
      Set.range (D.centralLeftOuterArmPath b) := by
  rw [← D.centralLeftBranchPaths_range_union b]
  exact Set.subset_union_right

theorem centralRightLowerBranchPath_range_subset_outerArm (b : D.BandIndex) :
    Set.range (D.centralRightLowerBranchPath b) ⊆
      Set.range (D.centralRightOuterArmPath b) := by
  rw [← D.centralRightBranchPaths_range_union b]
  exact Set.subset_union_left

theorem centralRightUpperBranchPath_range_subset_outerArm (b : D.BandIndex) :
    Set.range (D.centralRightUpperBranchPath b) ⊆
      Set.range (D.centralRightOuterArmPath b) := by
  rw [← D.centralRightBranchPaths_range_union b]
  exact Set.subset_union_right

theorem centralLeftLowerBranchPath_disjoint_centralRightLowerBranchPath
    (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftLowerBranchPath b))
      (Set.range (D.centralRightLowerBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftLowerBranchPath_range_subset_outerArm b)
    (D.centralRightLowerBranchPath_range_subset_outerArm b)

theorem centralLeftLowerBranchPath_disjoint_centralRightUpperBranchPath
    (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftLowerBranchPath b))
      (Set.range (D.centralRightUpperBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftLowerBranchPath_range_subset_outerArm b)
    (D.centralRightUpperBranchPath_range_subset_outerArm b)

theorem centralLeftUpperBranchPath_disjoint_centralRightLowerBranchPath
    (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftUpperBranchPath b))
      (Set.range (D.centralRightLowerBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftUpperBranchPath_range_subset_outerArm b)
    (D.centralRightLowerBranchPath_range_subset_outerArm b)

theorem centralLeftUpperBranchPath_disjoint_centralRightUpperBranchPath
    (b : D.BandIndex) :
    Disjoint (Set.range (D.centralLeftUpperBranchPath b))
      (Set.range (D.centralRightUpperBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftUpperBranchPath_range_subset_outerArm b)
    (D.centralRightUpperBranchPath_range_subset_outerArm b)

private theorem ambientCoordinate_globalBandPath (b : D.BandIndex) (u : unitInterval) :
    ambientCoordinate (frame 2)
        ((D.centralCutOrder.globalBandPath b u : transportedTorus Phi) : R3) =
      S.cut.height := by
  have hcircle := D.centralCutOrder.globalInwardExcursionPath_mem_cutCircle
    (D.centralCutOrder.globalGapOfBand b) u
  have hsection := D.centralGraph.cut.circle_mem_section
    (D.centralCutOrder.globalGapOfBand b).1.1 hcircle
  change ambientCoordinate (frame 2)
      (((D.centralCutOrder.globalInwardExcursionPath
        (D.centralCutOrder.globalGapOfBand b)) u : transportedTorus Phi) : R3) =
    S.cut.height
  simpa [superellipsoidCutTorusSection, coordinateCuttingPlane] using hsection.2

theorem centralLeftOuterArmPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralLeftOuterArmPath b) ∩ Set.range bandSeamPath =
      {bandLeftVertex} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    rw [Set.mem_singleton_iff]
    let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
    have hcoord : D.centralLeftOuterArmPath b u = bandSeamPath v := hu.trans hv.symm
    have hsurface :
        (⟨D.centralLeftOuterArmPoint b
            (D.openChartNarrowedTime (D.centralOuterArmTime u)),
          (D.centralOuterArmPoint_mem_openChart_of_narrowed b
            (D.centralOuterArmTime u)).1⟩ : T.surfacePatch) =
          T.strip (bandSeamPath v) := by
      rw [← hcoord]
      change _ = T.strip (T.strip.symm _)
      exact (T.strip.apply_symm_apply _).symm
    have hpoint : D.centralLeftOuterArmPoint b
        (D.openChartNarrowedTime (D.centralOuterArmTime u)) =
          (T.strip (bandSeamPath v) : transportedTorus Phi) :=
      congrArg Subtype.val hsurface
    have hheight := congrArg (ambientCoordinate (frame 2))
      (congrArg Subtype.val hpoint)
    change orientedCoordinateLift Phi frame 2
        (D.centralLeftOuterArmLift b
          (D.openChartNarrowedTime (D.centralOuterArmTime u))) =
      ambientCoordinate (frame 2)
        (((T.strip (bandSeamPath v) : T.surfacePatch) : transportedTorus Phi) : R3)
        at hheight
    rw [D.centralLeftOuterArmLift_height b,
      T.core_alignment v, D.ambientCoordinate_globalBandPath b v] at hheight
    have htime : D.centralOuterArmTime u =
        globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band := by
      apply Subtype.ext
      change (D.centralOuterArmTime u : ℝ) = 0
      change S.cut.height + (D.centralOuterArmTime u : ℝ) = S.cut.height at hheight
      linarith
    have huMid : u = armMidParameter := by
      apply D.centralOuterArmTime_injective
      exact htime.trans D.centralOuterArmTime_mid.symm
    calc
      x = D.centralLeftOuterArmPath b u := hu.symm
      _ = D.centralLeftOuterArmPath b armMidParameter := congrArg _ huMid
      _ = bandLeftVertex := D.centralLeftOuterArmPath_mid b
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨armMidParameter, D.centralLeftOuterArmPath_mid b⟩,
      ⟨0, bandSeamPath.source⟩⟩

theorem centralRightOuterArmPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralRightOuterArmPath b) ∩ Set.range bandSeamPath =
      {bandRightVertex} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    rw [Set.mem_singleton_iff]
    let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
    have hcoord : D.centralRightOuterArmPath b u = bandSeamPath v := hu.trans hv.symm
    have hsurface :
        (⟨D.centralRightOuterArmPoint b
            (D.openChartNarrowedTime (D.centralOuterArmTime u)),
          (D.centralOuterArmPoint_mem_openChart_of_narrowed b
            (D.centralOuterArmTime u)).2⟩ : T.surfacePatch) =
          T.strip (bandSeamPath v) := by
      rw [← hcoord]
      change _ = T.strip (T.strip.symm _)
      exact (T.strip.apply_symm_apply _).symm
    have hpoint : D.centralRightOuterArmPoint b
        (D.openChartNarrowedTime (D.centralOuterArmTime u)) =
          (T.strip (bandSeamPath v) : transportedTorus Phi) :=
      congrArg Subtype.val hsurface
    have hheight := congrArg (ambientCoordinate (frame 2))
      (congrArg Subtype.val hpoint)
    change orientedCoordinateLift Phi frame 2
        (D.centralRightOuterArmLift b
          (D.openChartNarrowedTime (D.centralOuterArmTime u))) =
      ambientCoordinate (frame 2)
        (((T.strip (bandSeamPath v) : T.surfacePatch) : transportedTorus Phi) : R3)
        at hheight
    rw [D.centralRightOuterArmLift_height b,
      T.core_alignment v, D.ambientCoordinate_globalBandPath b v] at hheight
    have htime : D.centralOuterArmTime u =
        globalBandFlowCollarZeroTime D.openChartNarrowedData.heightData.band := by
      apply Subtype.ext
      change (D.centralOuterArmTime u : ℝ) = 0
      change S.cut.height + (D.centralOuterArmTime u : ℝ) = S.cut.height at hheight
      linarith
    have huMid : u = armMidParameter := by
      apply D.centralOuterArmTime_injective
      exact htime.trans D.centralOuterArmTime_mid.symm
    calc
      x = D.centralRightOuterArmPath b u := hu.symm
      _ = D.centralRightOuterArmPath b armMidParameter := congrArg _ huMid
      _ = bandRightVertex := D.centralRightOuterArmPath_mid b
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨armMidParameter, D.centralRightOuterArmPath_mid b⟩,
      ⟨1, bandSeamPath.target⟩⟩

private theorem inter_eq_singleton_of_subset_left {X : Type*}
    {s t u : Set X} {p : X} (hs : s ⊆ t) (htu : t ∩ u = {p})
    (hps : p ∈ s) (hpu : p ∈ u) : s ∩ u = {p} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ t ∩ u := ⟨hs hx.1, hx.2⟩
    rw [htu] at hx'
    exact hx'
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨hps, hpu⟩

theorem centralLeftLowerBranchPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralLeftLowerBranchPath b) ∩ Set.range bandSeamPath =
      {bandLeftVertex} := by
  apply inter_eq_singleton_of_subset_left
    (D.centralLeftLowerBranchPath_range_subset_outerArm b)
    (D.centralLeftOuterArmPath_inter_bandSeamPath b)
  · exact ⟨1, (D.centralLeftLowerBranchPath b).target⟩
  · exact ⟨0, bandSeamPath.source⟩

theorem centralLeftUpperBranchPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralLeftUpperBranchPath b) ∩ Set.range bandSeamPath =
      {bandLeftVertex} := by
  apply inter_eq_singleton_of_subset_left
    (D.centralLeftUpperBranchPath_range_subset_outerArm b)
    (D.centralLeftOuterArmPath_inter_bandSeamPath b)
  · exact ⟨0, (D.centralLeftUpperBranchPath b).source⟩
  · exact ⟨0, bandSeamPath.source⟩

theorem centralRightLowerBranchPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralRightLowerBranchPath b) ∩ Set.range bandSeamPath =
      {bandRightVertex} := by
  apply inter_eq_singleton_of_subset_left
    (D.centralRightLowerBranchPath_range_subset_outerArm b)
    (D.centralRightOuterArmPath_inter_bandSeamPath b)
  · exact ⟨1, (D.centralRightLowerBranchPath b).target⟩
  · exact ⟨1, bandSeamPath.target⟩

theorem centralRightUpperBranchPath_inter_bandSeamPath (b : D.BandIndex) :
    Set.range (D.centralRightUpperBranchPath b) ∩ Set.range bandSeamPath =
      {bandRightVertex} := by
  apply inter_eq_singleton_of_subset_left
    (D.centralRightUpperBranchPath_range_subset_outerArm b)
    (D.centralRightOuterArmPath_inter_bandSeamPath b)
  · exact ⟨0, (D.centralRightUpperBranchPath b).source⟩
  · exact ⟨1, bandSeamPath.target⟩

/-- The complete compact four-port tree in the canonical strip coordinates. -/
def centralFourPortTreeCarrier (b : D.BandIndex) : Set Plane :=
  Set.range (D.centralLeftOuterArmPath b) ∪
    Set.range bandSeamPath ∪ Set.range (D.centralRightOuterArmPath b)

theorem isCompact_centralFourPortTreeCarrier (b : D.BandIndex) :
    IsCompact (D.centralFourPortTreeCarrier b) := by
  exact ((isCompact_range (D.centralLeftOuterArmPath b).continuous).union
    (isCompact_range bandSeamPath.continuous)).union
      (isCompact_range (D.centralRightOuterArmPath b).continuous)

theorem isConnected_centralFourPortTreeCarrier (b : D.BandIndex) :
    IsConnected (D.centralFourPortTreeCarrier b) := by
  have hleft : IsConnected (Set.range (D.centralLeftOuterArmPath b)) :=
    isConnected_range (D.centralLeftOuterArmPath b).continuous
  have hseam : IsConnected (Set.range bandSeamPath) :=
    isConnected_range bandSeamPath.continuous
  have hright : IsConnected (Set.range (D.centralRightOuterArmPath b)) :=
    isConnected_range (D.centralRightOuterArmPath b).continuous
  have hleftSeam : IsConnected
      (Set.range (D.centralLeftOuterArmPath b) ∪ Set.range bandSeamPath) := by
    apply IsConnected.union
    · exact ⟨bandLeftVertex,
        ⟨armMidParameter, D.centralLeftOuterArmPath_mid b⟩,
        ⟨0, bandSeamPath.source⟩⟩
    · exact hleft
    · exact hseam
  unfold centralFourPortTreeCarrier
  apply IsConnected.union
  · exact ⟨bandRightVertex, Or.inr ⟨1, bandSeamPath.target⟩,
      ⟨armMidParameter, D.centralRightOuterArmPath_mid b⟩⟩
  · exact hleftSeam
  · exact hright

/-- The canonical four-port tree lies strictly inside a polygonal disk whose boundary avoids
the tree. -/
theorem exists_polygonalDiskNeighborhood_centralFourPortTreeCarrier (b : D.BandIndex) :
    ∃ P : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle,
      Schoenflies.planeCoordinates.symm ''
          D.centralFourPortTreeCarrier b ⊆ P.interiorRegion ∧
        Disjoint P.carrier
          (Schoenflies.planeCoordinates.symm ''
            D.centralFourPortTreeCarrier b) := by
  let C := D.centralFourPortTreeCarrier b
  let e := Schoenflies.planeCoordinates.symm
  let C' := e '' C
  have hcompact : IsCompact C' :=
    (D.isCompact_centralFourPortTreeCarrier b).image e.continuous
  have hconnected : IsConnected C' :=
    (D.isConnected_centralFourPortTreeCarrier b).image e e.continuous.continuousOn
  let N : Schoenflies.JordanCircle.FinitePolyhedralNeighborhood C' Set.univ :=
    Classical.choice <| Schoenflies.JordanCircle.exists_finitePolyhedralNeighborhood
      hcompact isOpen_univ (Set.subset_univ C')
  obtain ⟨P, _, _, hcomponent, _⟩ :=
    N.exists_outerBoundaryPolygonalCircle_of_connected hconnected
  have htree : C' ⊆ P.interiorRegion :=
    (N.core_subset_coreComponent hconnected).trans hcomponent
  exact ⟨P, htree,
    (Schoenflies.PolygonalCircle.carrier_disjoint_interiorRegion P).mono
      Set.Subset.rfl htree⟩

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
