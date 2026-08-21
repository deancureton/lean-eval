import Submission.Topology.FourPortSixEdgeFaces
import Submission.Topology.PairedSeamBandSmoothing

/-!
# The standard four-port rectangle is an embedded cycle

The four segment paths of `PairedSeamBandSmoothing` form the local rectangular face.  This file
proves the exact two-arc data directly from their affine coordinates.  A later covering-plane
band alignment can transport this package without assuming local rectangle embeddedness.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

private theorem bandLeftPath_apply_formula (t : unitInterval) :
    bandLeftPath t = (-1, 2 * (t : ℝ) - 1) := by
  rw [bandLeftPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftBottom, bandLeftTop] <;> ring

private theorem bandRightPath_apply_formula (t : unitInterval) :
    bandRightPath t = (1, 2 * (t : ℝ) - 1) := by
  rw [bandRightPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandRightBottom, bandRightTop] <;> ring

private theorem bandBottomPath_apply_formula (t : unitInterval) :
    bandBottomPath t = (2 * (t : ℝ) - 1, -1) := by
  rw [bandBottomPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftBottom, bandRightBottom] <;> ring

private theorem bandTopPath_apply_formula (t : unitInterval) :
    bandTopPath t = (2 * (t : ℝ) - 1, 1) := by
  rw [bandTopPath, Path.segment_apply, AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [bandLeftTop, bandRightTop] <;> ring

private theorem range_bandLeftPath_inter_bandTopPath :
    Set.range bandLeftPath ∩ Set.range bandTopPath = {bandLeftTop} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandLeftPath s = bandTopPath t := hs.trans ht.symm
    rw [bandLeftPath_apply_formula, bandTopPath_apply_formula] at heq
    have hsval := congrArg Prod.snd heq
    have hsone : s = 1 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans bandLeftPath.target)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, bandLeftPath.target⟩, ⟨0, bandTopPath.source⟩⟩

private theorem range_bandTopPath_inter_bandRightPath :
    Set.range bandTopPath ∩ Set.range bandRightPath = {bandRightTop} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandTopPath s = bandRightPath t := hs.trans ht.symm
    rw [bandTopPath_apply_formula, bandRightPath_apply_formula] at heq
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
    exact ⟨⟨1, bandTopPath.target⟩, ⟨1, bandRightPath.target⟩⟩

private theorem range_bandLeftPath_inter_bandBottomPath :
    Set.range bandLeftPath ∩ Set.range bandBottomPath = {bandLeftBottom} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandLeftPath s = bandBottomPath t := hs.trans ht.symm
    rw [bandLeftPath_apply_formula, bandBottomPath_apply_formula] at heq
    have hsval := congrArg Prod.snd heq
    have hszero : s = 0 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans bandLeftPath.source)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, bandLeftPath.source⟩, ⟨0, bandBottomPath.source⟩⟩

private theorem range_bandRightPath_inter_bandBottomPath :
    Set.range bandRightPath ∩ Set.range bandBottomPath = {bandRightBottom} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : bandRightPath s = bandBottomPath t := hs.trans ht.symm
    rw [bandRightPath_apply_formula, bandBottomPath_apply_formula] at heq
    have hsval := congrArg Prod.snd heq
    have hszero : s = 0 := by
      apply Subtype.ext
      dsimp at hsval ⊢
      linarith
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans bandRightPath.source)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, bandRightPath.source⟩, ⟨1, bandBottomPath.target⟩⟩

theorem range_bandLeftPath_inter_bandTopPath_eq :
    Set.range bandLeftPath ∩ Set.range bandTopPath = {bandLeftTop} :=
  range_bandLeftPath_inter_bandTopPath

theorem range_bandTopPath_inter_bandRightPath_eq :
    Set.range bandTopPath ∩ Set.range bandRightPath = {bandRightTop} :=
  range_bandTopPath_inter_bandRightPath

theorem range_bandLeftPath_inter_bandBottomPath_eq :
    Set.range bandLeftPath ∩ Set.range bandBottomPath = {bandLeftBottom} :=
  range_bandLeftPath_inter_bandBottomPath

theorem range_bandRightPath_inter_bandBottomPath_eq :
    Set.range bandRightPath ∩ Set.range bandBottomPath = {bandRightBottom} :=
  range_bandRightPath_inter_bandBottomPath

private theorem bandRightPath_symm_injective :
    Function.Injective bandRightPath.symm := by
  intro s t hst
  apply unitInterval.symm_bijective.injective
  apply bandRightPath_injective
  simpa only [Path.symm_apply, Function.comp_apply] using hst

/-- The three upper sides of the standard rectangle form one embedded path. -/
theorem standardLocalRectangleUpperPath_injective : Function.Injective
    ((bandLeftPath.trans bandTopPath).trans bandRightPath.symm) := by
  have hleftTop : Function.Injective (bandLeftPath.trans bandTopPath) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      bandLeftPath bandTopPath bandLeftPath_injective bandTopPath_injective
      range_bandLeftPath_inter_bandTopPath
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    (bandLeftPath.trans bandTopPath) bandRightPath.symm hleftTop
      bandRightPath_symm_injective
  rw [Path.trans_range, Path.symm_range, union_inter_distrib_right,
    range_bandTopPath_inter_bandRightPath]
  have hdisjoint : Set.range bandLeftPath ∩ Set.range bandRightPath = ∅ := by
    exact Set.disjoint_iff_inter_eq_empty.mp <| by
      rw [Set.disjoint_left]
      rintro x ⟨s, hs⟩ ⟨t, ht⟩
      have heq : bandLeftPath s = bandRightPath t := hs.trans ht.symm
      rw [bandLeftPath_apply_formula, bandRightPath_apply_formula] at heq
      norm_num at heq
  rw [hdisjoint, empty_union]

/-- The upper route meets the bottom side exactly at the two lower ports. -/
theorem standardLocalRectangleUpper_inter_bottom :
    Set.range ((bandLeftPath.trans bandTopPath).trans bandRightPath.symm) ∩
        Set.range bandBottomPath =
      {bandLeftBottom, bandRightBottom} := by
  rw [Path.trans_range, Path.trans_range, Path.symm_range,
    union_inter_distrib_right, union_inter_distrib_right,
    range_bandLeftPath_inter_bandBottomPath,
    range_bandRightPath_inter_bandBottomPath]
  have htop : Set.range bandTopPath ∩ Set.range bandBottomPath = ∅ := by
    ext x
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have heq : bandTopPath s = bandBottomPath t := hs.trans ht.symm
      rw [bandTopPath_apply_formula, bandBottomPath_apply_formula] at heq
      have := congrArg Prod.snd heq
      norm_num at this
    · intro hx
      exact hx.elim
  rw [htop, union_empty]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- Exact two-arc data for the standard local rectangle. -/
theorem standardLocalRectangleData : TwoArcCircle.Data
    ((bandLeftPath.trans bandTopPath).trans bandRightPath.symm)
      bandBottomPath.symm where
  first_injective := standardLocalRectangleUpperPath_injective
  second_injective := by
    intro s t hst
    apply unitInterval.symm_bijective.injective
    apply bandBottomPath_injective
    simpa only [Path.symm_apply, Function.comp_apply] using hst
  range_inter := by
    simpa only [Path.symm_range] using standardLocalRectangleUpper_inter_bottom

end Submission.Topology
