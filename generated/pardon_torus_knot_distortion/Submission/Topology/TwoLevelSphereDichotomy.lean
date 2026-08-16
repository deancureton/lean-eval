import Submission.Topology.HalfSphereSurgeryDichotomy

/-!
# A four-cell alternative for two separated cutting levels

Two disjoint endpoint spheres cut the transported torus into lower, middle, upper, and exterior
cells.  After all inessential boundary circles are filled by their maximal torus disks, the
remaining connected carrier core lies in one cell.  An incoming parent carrier excludes the
exterior cell, while a separate rank-one theorem for the middle band excludes the middle cell.
Thus one child carries based torus genus.

This file proves only that logical implication.  It does not assert the geometric construction of
the two sphere boundaries or the rank-one property of a regular middle band.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-- Exact four-cell surface partition produced by two disjoint endpoint sphere boundaries. -/
structure TwoLevelSpherePartition
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι) where
  parentPart : Set (transportedTorus Phi)
  lowerPart : Set (transportedTorus Phi)
  middlePart : Set (transportedTorus Phi)
  upperPart : Set (transportedTorus Phi)
  exteriorPart : Set (transportedTorus Phi)
  isOpen_lowerPart : IsOpen lowerPart
  isOpen_middlePart : IsOpen middlePart
  isOpen_upperPart : IsOpen upperPart
  isOpen_exteriorPart : IsOpen exteriorPart
  lower_disjoint_middle : Disjoint lowerPart middlePart
  lower_disjoint_upper : Disjoint lowerPart upperPart
  lower_disjoint_exterior : Disjoint lowerPart exteriorPart
  middle_disjoint_upper : Disjoint middlePart upperPart
  middle_disjoint_exterior : Disjoint middlePart exteriorPart
  upper_disjoint_exterior : Disjoint upperPart exteriorPart
  lower_subset_parent : lowerPart ⊆ parentPart
  middle_subset_parent : middlePart ⊆ parentPart
  upper_subset_parent : upperPart ⊆ parentPart
  parent_disjoint_exterior : Disjoint parentPart exteriorPart
  surface_partition : Set.univ =
    lowerPart ∪ middlePart ∪ upperPart ∪ exteriorPart ∪
      ⋃ i, Set.range (fun t ↦ (S.circle i).windingLoop.curve t)

namespace TwoLevelSpherePartition

variable {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}

/-- Removing all maximal disks removes the boundary barrier from the four-cell partition. -/
theorem diskComplement_subset_cells
    (E : TwoLevelSpherePartition S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    M.diskComplement ⊆
      E.lowerPart ∪ E.middlePart ∪ E.upperPart ∪ E.exteriorPart := by
  intro x hx
  have hxuniv : x ∈ (Set.univ : Set (transportedTorus Phi)) := Set.mem_univ x
  rw [E.surface_partition] at hxuniv
  rcases hxuniv with hxcell | hxbarrier
  · exact hxcell
  · simp only [Set.mem_iUnion] at hxbarrier
    obtain ⟨i, hi⟩ := hxbarrier
    exact False.elim <| hx <| M.circle_range_subset_diskUnion i hi

private theorem lower_disjoint_rest (E : TwoLevelSpherePartition S) :
    Disjoint E.lowerPart
      (E.middlePart ∪ (E.upperPart ∪ E.exteriorPart)) := by
  rw [Set.disjoint_left]
  intro x hxl hx
  rcases hx with hxm | hxu | hxe
  · exact Set.disjoint_left.mp E.lower_disjoint_middle hxl hxm
  · exact Set.disjoint_left.mp E.lower_disjoint_upper hxl hxu
  · exact Set.disjoint_left.mp E.lower_disjoint_exterior hxl hxe

private theorem middle_disjoint_rest (E : TwoLevelSpherePartition S) :
    Disjoint E.middlePart (E.upperPart ∪ E.exteriorPart) := by
  rw [Set.disjoint_left]
  intro x hxm hx
  rcases hx with hxu | hxe
  · exact Set.disjoint_left.mp E.middle_disjoint_upper hxm hxu
  · exact Set.disjoint_left.mp E.middle_disjoint_exterior hxm hxe

/-- Connectedness locates the maximal-disk complement in one of the four cells. -/
theorem diskComplement_subset_one_cell
    (E : TwoLevelSpherePartition S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hconnected : IsConnected M.diskComplement) :
    M.diskComplement ⊆ E.lowerPart ∨
      M.diskComplement ⊆ E.middlePart ∨
        M.diskComplement ⊆ E.upperPart ∨
          M.diskComplement ⊆ E.exteriorPart := by
  have hfirst := hconnected.isPreconnected.subset_or_subset
    E.isOpen_lowerPart
    (E.isOpen_middlePart.union <| E.isOpen_upperPart.union E.isOpen_exteriorPart)
    E.lower_disjoint_rest (by
      simpa only [Set.union_assoc] using E.diskComplement_subset_cells M)
  rcases hfirst with hlower | hrest
  · exact Or.inl hlower
  · right
    have hsecond := hconnected.isPreconnected.subset_or_subset
      E.isOpen_middlePart (E.isOpen_upperPart.union E.isOpen_exteriorPart)
      E.middle_disjoint_rest hrest
    rcases hsecond with hmiddle | hrest
    · exact Or.inl hmiddle
    · exact Or.inr <| hconnected.isPreconnected.subset_or_subset
        E.isOpen_upperPart E.isOpen_exteriorPart E.upper_disjoint_exterior hrest

/-- Exterior location would force the whole incoming parent part into the maximal disk union. -/
theorem parentPart_subset_diskUnion_of_diskComplement_subset_exterior
    (E : TwoLevelSpherePartition S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hexterior : M.diskComplement ⊆ E.exteriorPart) :
    E.parentPart ⊆ M.diskUnion := by
  intro x hxparent
  by_contra hxdisk
  have hxcomplement : x ∈ M.diskComplement := hxdisk
  exact Set.disjoint_left.mp E.parent_disjoint_exterior hxparent
    (hexterior hxcomplement)

/-- An incoming based rank-two carrier rules out the exterior cell. -/
theorem not_diskComplement_subset_exterior_of_parent_carrier
    (E : TwoLevelSpherePartition S)
    {hzero : S.AllInessential}
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart) :
    ¬ M.diskComplement ⊆ E.exteriorPart := by
  intro hexterior
  obtain ⟨W⟩ := hparent
  have hparentDisk :=
    E.parentPart_subset_diskUnion_of_diskComplement_subset_exterior M hexterior
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
  apply W.independent
  simp [windingDet, hfirstZero, hsecondZero]

/-- If the middle band cannot carry rank two, every all-inessential two-level partition sends the
incoming carrier into the lower or upper child. -/
theorem carries_lower_or_upper_of_allInessential
    (E : TwoLevelSpherePartition S)
    (hzero : S.AllInessential)
    (M : MaximalInessentialTorusDiskFamily S hzero)
    (P : M.ConnectedPushoutData)
    (hparent : CarriesBasedLoopTorusGenus Phi E.parentPart)
    (hmiddle : ¬ CarriesBasedLoopTorusGenus Phi E.middlePart) :
    CarriesBasedLoopTorusGenus Phi E.lowerPart ∨
      CarriesBasedLoopTorusGenus Phi E.upperPart := by
  have hcomplement : CarriesBasedLoopTorusGenus Phi M.diskComplement :=
    carriesBasedLoopTorusGenus_of_finitePuncturePushout P.pushout
  rcases E.diskComplement_subset_one_cell M
      (MaximalInessentialTorusDiskFamily.ConnectedPushoutData.complement_isConnected M P) with
      hlower | hmiddleCell | hupper | hexterior
  · exact Or.inl (hcomplement.mono hlower)
  · exact False.elim <| hmiddle (hcomplement.mono hmiddleCell)
  · exact Or.inr (hcomplement.mono hupper)
  · exact False.elim <|
      E.not_diskComplement_subset_exterior_of_parent_carrier M hparent hexterior

end TwoLevelSpherePartition

end Submission.Topology
