import Submission.Topology.JordanThetaThreePathExtension
import Submission.Topology.FourPortQuadraticLabelChange
import Submission.Topology.StandardFourPortRectangle
import Submission.PlaneSchoenflies.Schoenflies.JordanConvexHull

/-!
# The standard four-port theta

The horizontal seam and the two three-piece routes around the lower and upper halves of the
standard rectangle share exactly the parametrization used by the canonical source connectors.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies
open EmbeddedTorusIntersectionCircle

/-- The lower-left branch, oriented away from the seam. -/
def standardLeftLowerBranchPath : Path bandLeftVertex bandLeftBottom :=
  Path.segment bandLeftVertex bandLeftBottom

/-- The lower-right branch, oriented toward the seam. -/
def standardRightLowerBranchPath : Path bandRightBottom bandRightVertex :=
  Path.segment bandRightBottom bandRightVertex

/-- The upper-left branch, oriented away from the seam. -/
def standardLeftUpperBranchPath : Path bandLeftVertex bandLeftTop :=
  Path.segment bandLeftVertex bandLeftTop

/-- The upper-right branch, oriented toward the seam. -/
def standardRightUpperBranchPath : Path bandRightTop bandRightVertex :=
  Path.segment bandRightTop bandRightVertex

/-- The lower return route from the left seam vertex to the right seam vertex. -/
def standardLowerThetaPath : Path bandLeftVertex bandRightVertex :=
  (standardLeftLowerBranchPath.trans bandBottomPath).trans
    standardRightLowerBranchPath

/-- The upper return route from the left seam vertex to the right seam vertex. -/
def standardUpperThetaPath : Path bandLeftVertex bandRightVertex :=
  (standardLeftUpperBranchPath.trans bandTopPath).trans
    standardRightUpperBranchPath

private theorem standardLeftLowerBranchPath_apply (u : unitInterval) :
    standardLeftLowerBranchPath u = (-1, -(u : ℝ)) := by
  rw [standardLeftLowerBranchPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftVertex, bandLeftBottom] <;> ring

private theorem standardRightLowerBranchPath_apply (u : unitInterval) :
    standardRightLowerBranchPath u = (1, (u : ℝ) - 1) := by
  rw [standardRightLowerBranchPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandRightBottom, bandRightVertex] <;> ring

private theorem standardLeftUpperBranchPath_apply (u : unitInterval) :
    standardLeftUpperBranchPath u = (-1, (u : ℝ)) := by
  rw [standardLeftUpperBranchPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftVertex, bandLeftTop] <;> ring

private theorem standardRightUpperBranchPath_apply (u : unitInterval) :
    standardRightUpperBranchPath u = (1, 1 - (u : ℝ)) := by
  rw [standardRightUpperBranchPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandRightTop, bandRightVertex] <;> ring

theorem standardLeftLowerBranchPath_injective :
    Function.Injective standardLeftLowerBranchPath :=
  Path.segment_injective_of_ne (by norm_num [bandLeftVertex, bandLeftBottom])

theorem standardRightLowerBranchPath_injective :
    Function.Injective standardRightLowerBranchPath :=
  Path.segment_injective_of_ne (by norm_num [bandRightBottom, bandRightVertex])

theorem standardLeftUpperBranchPath_injective :
    Function.Injective standardLeftUpperBranchPath :=
  Path.segment_injective_of_ne (by norm_num [bandLeftVertex, bandLeftTop])

theorem standardRightUpperBranchPath_injective :
    Function.Injective standardRightUpperBranchPath :=
  Path.segment_injective_of_ne (by norm_num [bandRightTop, bandRightVertex])

private theorem standardBandBottomPath_apply (u : unitInterval) :
    bandBottomPath u = (2 * (u : ℝ) - 1, -1) := by
  rw [bandBottomPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftBottom, bandRightBottom] <;> ring

private theorem standardBandTopPath_apply (u : unitInterval) :
    bandTopPath u = (2 * (u : ℝ) - 1, 1) := by
  rw [bandTopPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftTop, bandRightTop] <;> ring

private theorem standardBandLeftPath_apply (u : unitInterval) :
    bandLeftPath u = (-1, 2 * (u : ℝ) - 1) := by
  rw [bandLeftPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftBottom, bandLeftTop] <;> ring

private theorem standardBandRightPath_apply (u : unitInterval) :
    bandRightPath u = (1, 2 * (u : ℝ) - 1) := by
  rw [bandRightPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandRightBottom, bandRightTop] <;> ring

private theorem standardBandSeamPath_apply (u : unitInterval) :
    bandSeamPath u = (2 * (u : ℝ) - 1, 0) := by
  rw [bandSeamPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftVertex, bandRightVertex] <;> ring

theorem bandBottomPath_mem_standardSingularUnion_iff (u : unitInterval) :
    bandBottomPath u ∈
        (Set.range bandLeftPath ∪ Set.range bandRightPath) ∪ Set.range bandSeamPath ↔
      u = 0 ∨ u = 1 := by
  constructor
  · rintro ((⟨v, hv⟩ | ⟨v, hv⟩) | ⟨v, hv⟩)
    · rw [standardBandLeftPath_apply, standardBandBottomPath_apply] at hv
      left
      have hx := congrArg Prod.fst hv
      apply Subtype.ext
      change (u : ℝ) = 0
      linarith
    · rw [standardBandRightPath_apply, standardBandBottomPath_apply] at hv
      right
      have hx := congrArg Prod.fst hv
      apply Subtype.ext
      change (u : ℝ) = 1
      linarith
    · rw [standardBandSeamPath_apply, standardBandBottomPath_apply] at hv
      have hy := congrArg Prod.snd hv
      norm_num at hy
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl ⟨0, by simp⟩)
    · exact Or.inl (Or.inr ⟨0, by simp⟩)

theorem bandTopPath_mem_standardSingularUnion_iff (u : unitInterval) :
    bandTopPath u ∈
        (Set.range bandLeftPath ∪ Set.range bandRightPath) ∪ Set.range bandSeamPath ↔
      u = 0 ∨ u = 1 := by
  constructor
  · rintro ((⟨v, hv⟩ | ⟨v, hv⟩) | ⟨v, hv⟩)
    · rw [standardBandLeftPath_apply, standardBandTopPath_apply] at hv
      left
      have hx := congrArg Prod.fst hv
      apply Subtype.ext
      change (u : ℝ) = 0
      linarith
    · rw [standardBandRightPath_apply, standardBandTopPath_apply] at hv
      right
      have hx := congrArg Prod.fst hv
      apply Subtype.ext
      change (u : ℝ) = 1
      linarith
    · rw [standardBandSeamPath_apply, standardBandTopPath_apply] at hv
      have hy := congrArg Prod.snd hv
      norm_num at hy
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl ⟨1, by simp⟩)
    · exact Or.inl (Or.inr ⟨1, by simp⟩)

theorem range_bandLeftPath_eq_standardHalves :
    Set.range bandLeftPath =
      Set.range standardLeftLowerBranchPath ∪
        Set.range standardLeftUpperBranchPath := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · left
      let v : unitInterval := ⟨1 - 2 * (u : ℝ), by
        constructor <;> linarith [u.2.1]⟩
      refine ⟨v, ?_⟩
      rw [standardBandLeftPath_apply, standardLeftLowerBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [v]
        ring
    · right
      let v : unitInterval := ⟨2 * (u : ℝ) - 1, by
        constructor <;> linarith [u.2.2]⟩
      refine ⟨v, ?_⟩
      rw [standardBandLeftPath_apply, standardLeftUpperBranchPath_apply]
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · let u : unitInterval := ⟨(1 - (v : ℝ)) / 2, by
        constructor <;> linarith [v.2.1, v.2.2]⟩
      refine ⟨u, ?_⟩
      rw [standardBandLeftPath_apply, standardLeftLowerBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [u]
        ring
    · let u : unitInterval := ⟨((v : ℝ) + 1) / 2, by
        constructor <;> linarith [v.2.1, v.2.2]⟩
      refine ⟨u, ?_⟩
      rw [standardBandLeftPath_apply, standardLeftUpperBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [u]
        ring

theorem range_bandRightPath_eq_standardHalves :
    Set.range bandRightPath =
      Set.range standardRightLowerBranchPath ∪
        Set.range standardRightUpperBranchPath := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · left
      let v : unitInterval := ⟨2 * (u : ℝ), by
        constructor <;> linarith [u.2.1]⟩
      refine ⟨v, ?_⟩
      rw [standardBandRightPath_apply, standardRightLowerBranchPath_apply]
    · right
      let v : unitInterval := ⟨2 - 2 * (u : ℝ), by
        constructor <;> linarith [u.2.2]⟩
      refine ⟨v, ?_⟩
      rw [standardBandRightPath_apply, standardRightUpperBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [v]
        ring
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · let u : unitInterval := ⟨(v : ℝ) / 2, by
        constructor <;> linarith [v.2.1, v.2.2]⟩
      refine ⟨u, ?_⟩
      rw [standardBandRightPath_apply, standardRightLowerBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [u]
        ring
    · let u : unitInterval := ⟨1 - (v : ℝ) / 2, by
        constructor <;> linarith [v.2.1, v.2.2]⟩
      refine ⟨u, ?_⟩
      rw [standardBandRightPath_apply, standardRightUpperBranchPath_apply]
      apply Prod.ext
      · rfl
      · dsimp [u]
        ring

private theorem range_standardLeftLowerBranchPath_inter_bandBottomPath :
    Set.range standardLeftLowerBranchPath ∩ Set.range bandBottomPath =
      {bandLeftBottom} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : standardLeftLowerBranchPath s = bandBottomPath t :=
      hs.trans ht.symm
    rw [standardLeftLowerBranchPath_apply, standardBandBottomPath_apply] at heq
    have hsval := congrArg Prod.snd heq
    have hsone : s = 1 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans standardLeftLowerBranchPath.target)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, standardLeftLowerBranchPath.target⟩, ⟨0, bandBottomPath.source⟩⟩

private theorem range_bandBottomPath_inter_standardRightLowerBranchPath :
    Set.range bandBottomPath ∩ Set.range standardRightLowerBranchPath =
      {bandRightBottom} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandBottomPath s = standardRightLowerBranchPath t :=
      hs.trans ht.symm
    rw [standardBandBottomPath_apply, standardRightLowerBranchPath_apply] at heq
    have hsval := congrArg Prod.fst heq
    have hsone : s = 1 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans bandBottomPath.target)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, bandBottomPath.target⟩, ⟨0, standardRightLowerBranchPath.source⟩⟩

private theorem range_standardLeftUpperBranchPath_inter_bandTopPath :
    Set.range standardLeftUpperBranchPath ∩ Set.range bandTopPath =
      {bandLeftTop} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : standardLeftUpperBranchPath s = bandTopPath t := hs.trans ht.symm
    rw [standardLeftUpperBranchPath_apply, standardBandTopPath_apply] at heq
    have hsval := congrArg Prod.snd heq
    have hsone : s = 1 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans standardLeftUpperBranchPath.target)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, standardLeftUpperBranchPath.target⟩, ⟨0, bandTopPath.source⟩⟩

private theorem range_bandTopPath_inter_standardRightUpperBranchPath :
    Set.range bandTopPath ∩ Set.range standardRightUpperBranchPath =
      {bandRightTop} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandTopPath s = standardRightUpperBranchPath t := hs.trans ht.symm
    rw [standardBandTopPath_apply, standardRightUpperBranchPath_apply] at heq
    have hsval := congrArg Prod.fst heq
    have hsone : s = 1 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans bandTopPath.target)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, bandTopPath.target⟩, ⟨0, standardRightUpperBranchPath.source⟩⟩

private theorem standardLowerBranchPaths_disjoint :
    Disjoint (Set.range standardLeftLowerBranchPath)
      (Set.range standardRightLowerBranchPath) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs⟩ ⟨t, ht⟩
  have heq : standardLeftLowerBranchPath s = standardRightLowerBranchPath t :=
    hs.trans ht.symm
  rw [standardLeftLowerBranchPath_apply, standardRightLowerBranchPath_apply] at heq
  norm_num at heq

private theorem standardUpperBranchPaths_disjoint :
    Disjoint (Set.range standardLeftUpperBranchPath)
      (Set.range standardRightUpperBranchPath) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs⟩ ⟨t, ht⟩
  have heq : standardLeftUpperBranchPath s = standardRightUpperBranchPath t :=
    hs.trans ht.symm
  rw [standardLeftUpperBranchPath_apply, standardRightUpperBranchPath_apply] at heq
  norm_num at heq

theorem standardLowerThetaPath_injective : Function.Injective standardLowerThetaPath := by
  have hleftBottom : Function.Injective
      (standardLeftLowerBranchPath.trans bandBottomPath) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      standardLeftLowerBranchPath bandBottomPath
      standardLeftLowerBranchPath_injective bandBottomPath_injective
      range_standardLeftLowerBranchPath_inter_bandBottomPath
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    (standardLeftLowerBranchPath.trans bandBottomPath)
      standardRightLowerBranchPath hleftBottom standardRightLowerBranchPath_injective
  rw [Path.trans_range, Set.union_inter_distrib_right,
    Set.disjoint_iff_inter_eq_empty.mp standardLowerBranchPaths_disjoint,
    range_bandBottomPath_inter_standardRightLowerBranchPath, Set.empty_union]

theorem standardUpperThetaPath_injective : Function.Injective standardUpperThetaPath := by
  have hleftTop : Function.Injective
      (standardLeftUpperBranchPath.trans bandTopPath) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      standardLeftUpperBranchPath bandTopPath
      standardLeftUpperBranchPath_injective bandTopPath_injective
      range_standardLeftUpperBranchPath_inter_bandTopPath
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    (standardLeftUpperBranchPath.trans bandTopPath)
      standardRightUpperBranchPath hleftTop standardRightUpperBranchPath_injective
  rw [Path.trans_range, Set.union_inter_distrib_right,
    Set.disjoint_iff_inter_eq_empty.mp standardUpperBranchPaths_disjoint,
    range_bandTopPath_inter_standardRightUpperBranchPath, Set.empty_union]

/-- The three standard theta paths, with the seam as the distinguished shared path. -/
def standardFourPortThetaPath : Fin 3 → Path bandLeftVertex bandRightVertex
  | 0 => bandSeamPath
  | 1 => standardLowerThetaPath
  | 2 => standardUpperThetaPath

@[simp] theorem standardFourPortThetaPath_zero :
    standardFourPortThetaPath 0 = bandSeamPath := rfl

@[simp] theorem standardFourPortThetaPath_one :
    standardFourPortThetaPath 1 = standardLowerThetaPath := rfl

@[simp] theorem standardFourPortThetaPath_two :
    standardFourPortThetaPath 2 = standardUpperThetaPath := rfl

theorem standardLowerThetaPath_firstCoordinate (u : unitInterval) :
    standardLowerThetaPath (ThreePiecePath.firstCoordinate u) =
      standardLeftLowerBranchPath u := by
  exact ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

theorem standardLowerThetaPath_middleCoordinate (u : unitInterval) :
    standardLowerThetaPath (ThreePiecePath.middleCoordinate u) = bandBottomPath u := by
  exact ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

theorem standardLowerThetaPath_thirdCoordinate (u : unitInterval) :
    standardLowerThetaPath (ThreePiecePath.thirdCoordinate u) =
      standardRightLowerBranchPath u := by
  exact ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

theorem standardUpperThetaPath_firstCoordinate (u : unitInterval) :
    standardUpperThetaPath (ThreePiecePath.firstCoordinate u) =
      standardLeftUpperBranchPath u := by
  exact ThreePiecePath.trans_trans_firstCoordinate _ _ _ u

theorem standardUpperThetaPath_middleCoordinate (u : unitInterval) :
    standardUpperThetaPath (ThreePiecePath.middleCoordinate u) = bandTopPath u := by
  exact ThreePiecePath.trans_trans_middleCoordinate _ _ _ u

theorem standardUpperThetaPath_thirdCoordinate (u : unitInterval) :
    standardUpperThetaPath (ThreePiecePath.thirdCoordinate u) =
      standardRightUpperBranchPath u := by
  exact ThreePiecePath.trans_trans_thirdCoordinate _ _ _ u

theorem range_standardLowerThetaPath :
    Set.range standardLowerThetaPath =
      Set.range standardLeftLowerBranchPath ∪ Set.range bandBottomPath ∪
        Set.range standardRightLowerBranchPath := by
  rw [standardLowerThetaPath, Path.trans_range, Path.trans_range]

theorem range_standardUpperThetaPath :
    Set.range standardUpperThetaPath =
      Set.range standardLeftUpperBranchPath ∪ Set.range bandTopPath ∪
        Set.range standardRightUpperBranchPath := by
  rw [standardUpperThetaPath, Path.trans_range, Path.trans_range]

private theorem exists_standardBandParameter {x : ℝ}
    (hx : x ∈ Icc (-(1 : ℝ)) 1) :
    ∃ u : unitInterval, 2 * (u : ℝ) - 1 = x := by
  let u : unitInterval := ⟨(x + 1) / 2, by
    constructor <;> linarith [hx.1, hx.2]⟩
  exact ⟨u, by dsimp [u]; ring⟩

private theorem standardVerticalCarrier_eq_pathRanges :
    fourPortVerticalCarrier = Set.range bandLeftPath ∪ Set.range bandRightPath := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨u, hu⟩ := exists_standardBandParameter hy
    rcases hx with hx | hx
    · right
      refine ⟨u, ?_⟩
      rw [standardBandRightPath_apply]
      exact Prod.ext hx.symm hu
    · left
      refine ⟨u, ?_⟩
      rw [standardBandLeftPath_apply]
      exact Prod.ext hx.symm hu
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · rw [standardBandLeftPath_apply]
      refine ⟨Or.inr rfl, ?_⟩
      constructor <;> linarith [u.2.1, u.2.2]
    · rw [standardBandRightPath_apply]
      refine ⟨Or.inl rfl, ?_⟩
      constructor <;> linarith [u.2.1, u.2.2]

private theorem standardHorizontalCarrier_eq_pathRanges :
    fourPortHorizontalCarrier = Set.range bandBottomPath ∪ Set.range bandTopPath := by
  ext x
  constructor
  · rintro ⟨hy, hx⟩
    obtain ⟨u, hu⟩ := exists_standardBandParameter hx
    rcases hy with hy | hy
    · right
      refine ⟨u, ?_⟩
      rw [standardBandTopPath_apply]
      exact Prod.ext hu hy.symm
    · left
      refine ⟨u, ?_⟩
      rw [standardBandBottomPath_apply]
      exact Prod.ext hu hy.symm
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · rw [standardBandBottomPath_apply]
      refine ⟨Or.inr rfl, ?_⟩
      constructor <;> linarith [u.2.1, u.2.2]
    · rw [standardBandTopPath_apply]
      refine ⟨Or.inl rfl, ?_⟩
      constructor <;> linarith [u.2.1, u.2.2]

theorem standardOuterThetaCarrier_eq :
    Set.range standardLowerThetaPath ∪ Set.range standardUpperThetaPath =
      fourPortVerticalCarrier ∪ fourPortHorizontalCarrier := by
  rw [range_standardLowerThetaPath, range_standardUpperThetaPath,
    standardVerticalCarrier_eq_pathRanges,
    standardHorizontalCarrier_eq_pathRanges,
    range_bandLeftPath_eq_standardHalves,
    range_bandRightPath_eq_standardHalves]
  ac_rfl

/-- The lower closed half of the standard four-port rectangle. -/
def standardLowerClosedRectangle : Set Submission.SurfaceRegularValue.Plane :=
  Icc (-(1 : ℝ)) 1 ×ˢ Icc (-(1 : ℝ)) 0

/-- The upper closed half of the standard four-port rectangle. -/
def standardUpperClosedRectangle : Set Submission.SurfaceRegularValue.Plane :=
  Icc (-(1 : ℝ)) 1 ×ˢ Icc 0 1

theorem isCompact_standardLowerClosedRectangle : IsCompact standardLowerClosedRectangle :=
  isCompact_Icc.prod isCompact_Icc

theorem isCompact_standardUpperClosedRectangle : IsCompact standardUpperClosedRectangle :=
  isCompact_Icc.prod isCompact_Icc

theorem interior_standardLowerClosedRectangle_nonempty :
    (interior standardLowerClosedRectangle).Nonempty := by
  refine ⟨(0, -(1 : ℝ) / 2), ?_⟩
  simp only [standardLowerClosedRectangle, interior_prod_eq, interior_Icc,
    Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem interior_standardUpperClosedRectangle_nonempty :
    (interior standardUpperClosedRectangle).Nonempty := by
  refine ⟨(0, (1 : ℝ) / 2), ?_⟩
  simp only [standardUpperClosedRectangle, interior_prod_eq, interior_Icc,
    Set.mem_prod, Set.mem_Ioo]
  norm_num

/-- The lower standard half-rectangle in the Euclidean Schoenflies plane. -/
def standardLowerClosedRectangleInPlane : Set Schoenflies.Plane :=
  coveringPlaneCoordinates.symm '' standardLowerClosedRectangle

/-- The upper standard half-rectangle in the Euclidean Schoenflies plane. -/
def standardUpperClosedRectangleInPlane : Set Schoenflies.Plane :=
  coveringPlaneCoordinates.symm '' standardUpperClosedRectangle

theorem isCompact_standardLowerClosedRectangleInPlane :
    IsCompact standardLowerClosedRectangleInPlane :=
  isCompact_standardLowerClosedRectangle.image coveringPlaneCoordinates.symm.continuous

theorem isCompact_standardUpperClosedRectangleInPlane :
    IsCompact standardUpperClosedRectangleInPlane :=
  isCompact_standardUpperClosedRectangle.image coveringPlaneCoordinates.symm.continuous

theorem interior_standardLowerClosedRectangleInPlane_nonempty :
    (interior standardLowerClosedRectangleInPlane).Nonempty := by
  rw [standardLowerClosedRectangleInPlane, ← coveringPlaneCoordinates.symm.image_interior]
  exact interior_standardLowerClosedRectangle_nonempty.image coveringPlaneCoordinates.symm

theorem interior_standardUpperClosedRectangleInPlane_nonempty :
    (interior standardUpperClosedRectangleInPlane).Nonempty := by
  rw [standardUpperClosedRectangleInPlane, ← coveringPlaneCoordinates.symm.image_interior]
  exact interior_standardUpperClosedRectangle_nonempty.image coveringPlaneCoordinates.symm

private theorem standardLowerThetaPath_snd_nonpos
    {z : Submission.SurfaceRegularValue.Plane}
    (hz : z ∈ Set.range standardLowerThetaPath) : z.2 ≤ 0 := by
  rw [range_standardLowerThetaPath] at hz
  rcases hz with (⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩
  · rw [standardLeftLowerBranchPath_apply]
    exact neg_nonpos.mpr u.2.1
  · rw [standardBandBottomPath_apply]
    norm_num
  · rw [standardRightLowerBranchPath_apply]
    linarith [u.2.2]

private theorem standardUpperThetaPath_snd_nonneg
    {z : Submission.SurfaceRegularValue.Plane}
    (hz : z ∈ Set.range standardUpperThetaPath) : 0 ≤ z.2 := by
  rw [range_standardUpperThetaPath] at hz
  rcases hz with (⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩
  · rw [standardLeftUpperBranchPath_apply]
    exact u.2.1
  · rw [standardBandTopPath_apply]
    norm_num
  · rw [standardRightUpperBranchPath_apply]
    linarith [u.2.2]

private theorem standardLowerThetaPath_eq_endpoint_of_snd_eq_zero
    {z : Submission.SurfaceRegularValue.Plane}
    (hz : z ∈ Set.range standardLowerThetaPath) (hzero : z.2 = 0) :
    z = bandLeftVertex ∨ z = bandRightVertex := by
  rw [range_standardLowerThetaPath] at hz
  rcases hz with (⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩
  · rw [standardLeftLowerBranchPath_apply] at hzero
    have hu : u = 0 := by
      apply Subtype.ext
      dsimp at hzero ⊢
      linarith
    subst u
    exact Or.inl standardLeftLowerBranchPath.source
  · rw [standardBandBottomPath_apply] at hzero
    norm_num at hzero
  · rw [standardRightLowerBranchPath_apply] at hzero
    have hu : u = 1 := by
      apply Subtype.ext
      dsimp at hzero ⊢
      linarith
    subst u
    exact Or.inr standardRightLowerBranchPath.target

private theorem standardUpperThetaPath_eq_endpoint_of_snd_eq_zero
    {z : Submission.SurfaceRegularValue.Plane}
    (hz : z ∈ Set.range standardUpperThetaPath) (hzero : z.2 = 0) :
    z = bandLeftVertex ∨ z = bandRightVertex := by
  rw [range_standardUpperThetaPath] at hz
  rcases hz with (⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩
  · rw [standardLeftUpperBranchPath_apply] at hzero
    have hu : u = 0 := by
      apply Subtype.ext
      dsimp at hzero ⊢
      linarith
    subst u
    exact Or.inl standardLeftUpperBranchPath.source
  · rw [standardBandTopPath_apply] at hzero
    norm_num at hzero
  · rw [standardRightUpperBranchPath_apply] at hzero
    have hu : u = 1 := by
      apply Subtype.ext
      dsimp at hzero ⊢
      linarith
    subst u
    exact Or.inr standardRightUpperBranchPath.target

private theorem bandSeamPath_snd_eq_zero (u : unitInterval) :
    (bandSeamPath u).2 = 0 := by
  rw [bandSeamPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  dsimp [bandLeftVertex, bandRightVertex]
  ring

private theorem range_bandSeamPath_inter_standardLowerThetaPath :
    Set.range bandSeamPath ∩ Set.range standardLowerThetaPath =
      {bandLeftVertex, bandRightVertex} := by
  ext z
  constructor
  · rintro ⟨⟨u, rfl⟩, hzLower⟩
    rcases standardLowerThetaPath_eq_endpoint_of_snd_eq_zero hzLower
        (bandSeamPath_snd_eq_zero u) with h | h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inl h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨⟨0, bandSeamPath.source⟩, ⟨0, standardLowerThetaPath.source⟩⟩
    · exact ⟨⟨1, bandSeamPath.target⟩, ⟨1, standardLowerThetaPath.target⟩⟩

private theorem range_bandSeamPath_inter_standardUpperThetaPath :
    Set.range bandSeamPath ∩ Set.range standardUpperThetaPath =
      {bandLeftVertex, bandRightVertex} := by
  ext z
  constructor
  · rintro ⟨⟨u, rfl⟩, hzUpper⟩
    rcases standardUpperThetaPath_eq_endpoint_of_snd_eq_zero hzUpper
        (bandSeamPath_snd_eq_zero u) with h | h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inl h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨⟨0, bandSeamPath.source⟩, ⟨0, standardUpperThetaPath.source⟩⟩
    · exact ⟨⟨1, bandSeamPath.target⟩, ⟨1, standardUpperThetaPath.target⟩⟩

private theorem range_standardLowerThetaPath_inter_standardUpperThetaPath :
    Set.range standardLowerThetaPath ∩ Set.range standardUpperThetaPath =
      {bandLeftVertex, bandRightVertex} := by
  ext z
  constructor
  · rintro ⟨hzLower, hzUpper⟩
    have hzero : z.2 = 0 := by
      exact le_antisymm (standardLowerThetaPath_snd_nonpos hzLower)
        (standardUpperThetaPath_snd_nonneg hzUpper)
    rcases standardLowerThetaPath_eq_endpoint_of_snd_eq_zero hzLower hzero with h | h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inl h
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨⟨0, standardLowerThetaPath.source⟩,
        ⟨0, standardUpperThetaPath.source⟩⟩
    · exact ⟨⟨1, standardLowerThetaPath.target⟩,
        ⟨1, standardUpperThetaPath.target⟩⟩

private theorem mappedStandardPath_injective
    {a b : Submission.SurfaceRegularValue.Plane} (p : Path a b)
    (hp : Function.Injective p) :
    Function.Injective (p.map coveringPlaneCoordinates.symm.continuous) := by
  intro s t hst
  apply hp
  apply coveringPlaneCoordinates.symm.injective
  simpa only [Path.map_coe, Function.comp_apply] using hst

private theorem range_mappedStandardPath
    {a b : Submission.SurfaceRegularValue.Plane} (p : Path a b) :
    Set.range (p.map coveringPlaneCoordinates.symm.continuous) =
      coveringPlaneCoordinates.symm '' Set.range p := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨p u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

private theorem mappedStandardPath_range_inter
    {a b : Submission.SurfaceRegularValue.Plane} (p q : Path a b)
    (hinter : Set.range p ∩ Set.range q = {a, b}) :
    Set.range (p.map coveringPlaneCoordinates.symm.continuous) ∩
        Set.range (q.map coveringPlaneCoordinates.symm.continuous) =
      {coveringPlaneCoordinates.symm a, coveringPlaneCoordinates.symm b} := by
  ext z
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    change coveringPlaneCoordinates.symm (p u) = z at hu
    change coveringPlaneCoordinates.symm (q v) = z at hv
    have hpq : p u = q v := coveringPlaneCoordinates.symm.injective
      (hu.trans hv.symm)
    have horig : p u ∈ Set.range p ∩ Set.range q :=
      ⟨⟨u, rfl⟩, ⟨v, hpq.symm⟩⟩
    rw [hinter] at horig
    rcases horig with ha | hb
    · exact Or.inl (hu.symm.trans (congrArg coveringPlaneCoordinates.symm ha))
    · exact Or.inr (hu.symm.trans (congrArg coveringPlaneCoordinates.symm hb))
  · rintro (rfl | rfl)
    · exact ⟨⟨0, (p.map coveringPlaneCoordinates.symm.continuous).source⟩,
        ⟨0, (q.map coveringPlaneCoordinates.symm.continuous).source⟩⟩
    · exact ⟨⟨1, (p.map coveringPlaneCoordinates.symm.continuous).target⟩,
        ⟨1, (q.map coveringPlaneCoordinates.symm.continuous).target⟩⟩

/-- The standard theta transported to the Euclidean plane used by Schoenflies. -/
def standardPlaneFourPortThetaPath : Fin 3 → Path
    (coveringPlaneCoordinates.symm bandLeftVertex)
      (coveringPlaneCoordinates.symm bandRightVertex) :=
  fun i ↦ (standardFourPortThetaPath i).map
    coveringPlaneCoordinates.symm.continuous

/-- The literal square boundary split by its horizontal seam is a planar three-path system. -/
theorem standardPlaneFourPortThetaSystem : ThreePathSystem standardPlaneFourPortThetaPath where
  injective := by
    intro i
    fin_cases i
    · exact mappedStandardPath_injective bandSeamPath bandSeamPath_injective
    · exact mappedStandardPath_injective standardLowerThetaPath
        standardLowerThetaPath_injective
    · exact mappedStandardPath_injective standardUpperThetaPath
        standardUpperThetaPath_injective
  range_inter := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact mappedStandardPath_range_inter bandSeamPath standardLowerThetaPath
        range_bandSeamPath_inter_standardLowerThetaPath
    · exact mappedStandardPath_range_inter bandSeamPath standardUpperThetaPath
        range_bandSeamPath_inter_standardUpperThetaPath
    · rw [Set.inter_comm]
      exact mappedStandardPath_range_inter bandSeamPath standardLowerThetaPath
        range_bandSeamPath_inter_standardLowerThetaPath
    · exact (hij rfl).elim
    · exact mappedStandardPath_range_inter standardLowerThetaPath standardUpperThetaPath
        range_standardLowerThetaPath_inter_standardUpperThetaPath
    · rw [Set.inter_comm]
      exact mappedStandardPath_range_inter bandSeamPath standardUpperThetaPath
        range_bandSeamPath_inter_standardUpperThetaPath
    · rw [Set.inter_comm]
      exact mappedStandardPath_range_inter standardLowerThetaPath standardUpperThetaPath
        range_standardLowerThetaPath_inter_standardUpperThetaPath
    · exact (hij rfl).elim

theorem standardPlaneOuterThetaCarrier_eq_frontier :
    standardPlaneFourPortThetaSystem.circle12.carrier =
      frontier fourPortClosedRectangleInCoveringPlane := by
  rw [ThreePathSystem.carrier_circle12,
    frontier_fourPortClosedRectangleInCoveringPlane]
  change Set.range (standardLowerThetaPath.map coveringPlaneCoordinates.symm.continuous) ∪
      Set.range (standardUpperThetaPath.map coveringPlaneCoordinates.symm.continuous) = _
  rw [range_mappedStandardPath, range_mappedStandardPath, ← Set.image_union,
    standardOuterThetaCarrier_eq]

private theorem isCompact_fourPortClosedRectangleInCoveringPlane :
    IsCompact fourPortClosedRectangleInCoveringPlane :=
  isCompact_fourPortClosedRectangle.image coveringPlaneCoordinates.symm.continuous

private theorem interior_fourPortClosedRectangleInCoveringPlane_nonempty :
    (interior fourPortClosedRectangleInCoveringPlane).Nonempty := by
  rw [fourPortClosedRectangleInCoveringPlane,
    ← coveringPlaneCoordinates.symm.image_interior]
  refine Set.Nonempty.image coveringPlaneCoordinates.symm ⟨(0, 0), ?_⟩
  simp only [fourPortClosedRectangle, interior_prod_eq, interior_Icc,
    Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem standardOuterRectangle_eq_closure_inside :
    fourPortClosedRectangleInCoveringPlane =
      closure standardPlaneFourPortThetaSystem.circle12.inside := by
  apply Schoenflies.JordanCircle.eq_closure_inside_of_isCompact_frontier_eq
    standardPlaneFourPortThetaSystem.circle12
    isCompact_fourPortClosedRectangleInCoveringPlane
  · exact standardPlaneOuterThetaCarrier_eq_frontier.symm
  · exact interior_fourPortClosedRectangleInCoveringPlane_nonempty

private def standardLowerHalfPlane : Set Schoenflies.Plane :=
  {z | z 1 ≤ 0}

private def standardUpperHalfPlane : Set Schoenflies.Plane :=
  {z | 0 ≤ z 1}

private theorem isClosed_standardLowerHalfPlane : IsClosed standardLowerHalfPlane := by
  exact isClosed_le
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 1) continuous_const

private theorem isClosed_standardUpperHalfPlane : IsClosed standardUpperHalfPlane := by
  exact isClosed_le continuous_const
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) 1)

private theorem convex_standardLowerHalfPlane : Convex ℝ standardLowerHalfPlane := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y) 1 ≤ 0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change x 1 ≤ 0 at hx
  change y 1 ≤ 0 at hy
  nlinarith

private theorem convex_standardUpperHalfPlane : Convex ℝ standardUpperHalfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ (a • x + b • y) 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change 0 ≤ x 1 at hx
  change 0 ≤ y 1 at hy
  nlinarith

private theorem coveringPlaneCoordinates_symm_second
    (z : Submission.SurfaceRegularValue.Plane) :
    (coveringPlaneCoordinates.symm z) 1 = z.2 := by
  have h := congrArg Prod.snd
    (coveringPlaneCoordinates.apply_symm_apply z)
  simpa only [coveringPlaneCoordinates_apply] using h

private theorem mappedPath_secondCoordinate
    {a b : Submission.SurfaceRegularValue.Plane} (p : Path a b)
    (u : unitInterval) :
    (coveringPlaneCoordinates.symm (p u)) 1 = (p u).2 :=
  coveringPlaneCoordinates_symm_second (p u)

private theorem standardCircle01_carrier_subset_lowerHalfPlane :
    standardPlaneFourPortThetaSystem.circle01.carrier ⊆ standardLowerHalfPlane := by
  rw [ThreePathSystem.carrier_circle01]
  rintro z (hz | hz)
  · rcases hz with ⟨u, rfl⟩
    change (coveringPlaneCoordinates.symm (bandSeamPath u)) 1 ≤ 0
    rw [mappedPath_secondCoordinate, bandSeamPath_snd_eq_zero]
  · rcases hz with ⟨u, rfl⟩
    change (coveringPlaneCoordinates.symm (standardLowerThetaPath u)) 1 ≤ 0
    rw [mappedPath_secondCoordinate]
    exact standardLowerThetaPath_snd_nonpos ⟨u, rfl⟩

private theorem standardCircle02_carrier_subset_upperHalfPlane :
    standardPlaneFourPortThetaSystem.circle02.carrier ⊆ standardUpperHalfPlane := by
  rw [ThreePathSystem.carrier_circle02]
  rintro z (hz | hz)
  · rcases hz with ⟨u, rfl⟩
    change 0 ≤ (coveringPlaneCoordinates.symm (bandSeamPath u)) 1
    rw [mappedPath_secondCoordinate, bandSeamPath_snd_eq_zero]
  · rcases hz with ⟨u, rfl⟩
    change 0 ≤ (coveringPlaneCoordinates.symm (standardUpperThetaPath u)) 1
    rw [mappedPath_secondCoordinate]
    exact standardUpperThetaPath_snd_nonneg ⟨u, rfl⟩

private theorem standardCircle01_closure_inside_subset_lowerHalfPlane :
    closure standardPlaneFourPortThetaSystem.circle01.inside ⊆
      standardLowerHalfPlane := by
  apply (closure_minimal
    standardPlaneFourPortThetaSystem.circle01.inside_subset_closedConvexHull_carrier
      isClosed_closedConvexHull).trans
  exact closedConvexHull_min standardCircle01_carrier_subset_lowerHalfPlane
    convex_standardLowerHalfPlane isClosed_standardLowerHalfPlane

private theorem standardCircle02_closure_inside_subset_upperHalfPlane :
    closure standardPlaneFourPortThetaSystem.circle02.inside ⊆
      standardUpperHalfPlane := by
  apply (closure_minimal
    standardPlaneFourPortThetaSystem.circle02.inside_subset_closedConvexHull_carrier
      isClosed_closedConvexHull).trans
  exact closedConvexHull_min standardCircle02_carrier_subset_upperHalfPlane
    convex_standardUpperHalfPlane isClosed_standardUpperHalfPlane

theorem standardPlaneFourPortTheta_outer_decomposition :
    closure standardPlaneFourPortThetaSystem.circle12.inside =
      closure standardPlaneFourPortThetaSystem.circle01.inside ∪
        closure standardPlaneFourPortThetaSystem.circle02.inside := by
  rcases standardPlaneFourPortThetaSystem.exists_outer_cycle_decomposition with
      h01 | h02 | h12
  · have hp : coveringPlaneCoordinates.symm (0, 1) ∈
        closure standardPlaneFourPortThetaSystem.circle01.inside := by
      rw [h01]
      right
      rw [← standardOuterRectangle_eq_closure_inside]
      exact ⟨(0, 1), by simp [fourPortClosedRectangle], rfl⟩
    have := standardCircle01_closure_inside_subset_lowerHalfPlane hp
    change (coveringPlaneCoordinates.symm (0, 1)) 1 ≤ 0 at this
    rw [coveringPlaneCoordinates_symm_second] at this
    norm_num at this
  · have hp : coveringPlaneCoordinates.symm (0, -1) ∈
        closure standardPlaneFourPortThetaSystem.circle02.inside := by
      rw [h02]
      right
      rw [← standardOuterRectangle_eq_closure_inside]
      exact ⟨(0, -1), by simp [fourPortClosedRectangle], rfl⟩
    have := standardCircle02_closure_inside_subset_upperHalfPlane hp
    change 0 ≤ (coveringPlaneCoordinates.symm (0, -1)) 1 at this
    rw [coveringPlaneCoordinates_symm_second] at this
    norm_num at this
  · exact h12

end Submission.Topology
