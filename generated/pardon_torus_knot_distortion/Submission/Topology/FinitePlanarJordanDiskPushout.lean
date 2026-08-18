import Submission.Topology.MaximalDiskSeparatedSupports
import Submission.Topology.PlanarJordanDiskPushout

/-!
# Separated supports for finite planar Jordan-disk pushouts

A finite pairwise-disjoint family of closed Jordan disks lying in one outer Jordan region has
pairwise-disjoint Schoenflies radial supports, still contained in that outer region.  This is the
geometric separation input needed to compose the corresponding one-disk planar pushouts.
-/

open Metric Set Topology

noncomputable section

namespace Schoenflies.JordanCircle

open Submission.Topology

variable {ι : Type*}

/-- The closed disk used by the planar pushout is closed. -/
theorem isClosed_diskPushClosedDisk (J : JordanCircle) :
    IsClosed J.diskPushClosedDisk := by
  exact isClosed_closure

/-- A radial support of radius at least one contains the closed Jordan disk. -/
theorem diskPushClosedDisk_subset_support (J : JordanCircle) {R : ℝ} (hR : 1 ≤ R) :
    J.diskPushClosedDisk ⊆ J.diskPushSupport R := by
  intro x hx
  refine ⟨J.diskPushAmbientHomeomorph x, ?_, J.diskPushAmbientHomeomorph.symm_apply_apply x⟩
  have hxball : J.diskPushAmbientHomeomorph x ∈ closedBall (0 : Plane) 1 :=
    (J.diskPushAmbientHomeomorph_mem_closedBall_iff x).2 hx
  simpa only [mem_closedBall, dist_zero_right] using
    (le_trans (by simpa only [mem_closedBall, dist_zero_right] using hxball) hR)

/-- Every open neighborhood of a closed planar Jordan disk contains a radial support of radius
strictly larger than one. -/
theorem exists_radius_diskPushSupport_subset_open
    (J : JordanCircle) {U : Set Plane} (hUopen : IsOpen U)
    (hKU : J.diskPushClosedDisk ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ J.diskPushSupport R ⊆ U := by
  let e := J.diskPushAmbientHomeomorph
  have hballU : closedBall (0 : Plane) 1 ⊆ e '' U := by
    rw [← J.diskPushAmbientHomeomorph_image_closedDisk]
    exact image_mono hKU
  have heUopen : IsOpen (e '' U) := e.isOpenMap U hUopen
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : Plane) 1).exists_cthickening_subset_open heUopen hballU
  have hlarge : closedBall (0 : Plane) (1 + δ) ⊆ e '' U := by
    simpa only [cthickening_closedBall hδ.le (show (0 : ℝ) ≤ 1 by norm_num), add_comm]
      using hthick
  refine ⟨1 + δ, by linarith, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨u, hu, heu⟩ := hlarge hy
  rw [← heu, e.symm_apply_apply]
  exact hu

/-- Pairwise-disjoint radial supports for a finite family of inner planar Jordan disks. -/
structure SeparatedPlanarJordanDiskSupports [Fintype ι]
    (outer : JordanCircle) (inner : ι → JordanCircle) where
  radius : ι → ℝ
  one_lt_radius : ∀ i, 1 < radius i
  support_subset_outer : ∀ i, (inner i).diskPushSupport (radius i) ⊆ outer.inside
  pairwise_disjoint_support : Pairwise fun i j ↦
    Disjoint ((inner i).diskPushSupport (radius i))
      ((inner j).diskPushSupport (radius j))

/-- Pairwise-disjoint closed inner disks inside one outer Jordan region have separated radial
supports inside that region. -/
theorem exists_separatedPlanarJordanDiskSupports [Fintype ι]
    (outer : JordanCircle) (inner : ι → JordanCircle)
    (hinside : ∀ i, (inner i).diskPushClosedDisk ⊆ outer.inside)
    (hdisjoint : Pairwise fun i j ↦
      Disjoint ((inner i).diskPushClosedDisk) ((inner j).diskPushClosedDisk)) :
    Nonempty (SeparatedPlanarJordanDiskSupports outer inner) := by
  let K : ι → Set Plane := fun i ↦ (inner i).diskPushClosedDisk
  obtain ⟨U, hU, hUpairwise⟩ :=
    Submission.Topology.exists_pairwise_disjoint_open_supersets K
      (fun i ↦ (inner i).isClosed_diskPushClosedDisk) hdisjoint
  let V : ι → Set Plane := fun i ↦ U i ∩ outer.inside
  have hVopen : ∀ i, IsOpen (V i) := fun i ↦ (hU i).1.inter outer.inside_isOpen
  have hKV : ∀ i, K i ⊆ V i := by
    intro i x hx
    exact ⟨(hU i).2 hx, hinside i hx⟩
  have hVpairwise : Pairwise fun i j ↦ Disjoint (V i) (V j) := by
    intro i j hij
    exact (hUpairwise hij).mono inter_subset_left inter_subset_left
  have hradius : ∀ i, ∃ R : ℝ, 1 < R ∧ (inner i).diskPushSupport R ⊆ V i := by
    intro i
    exact (inner i).exists_radius_diskPushSupport_subset_open (hVopen i) (hKV i)
  choose R hR hsupport using hradius
  refine ⟨{
    radius := R
    one_lt_radius := hR
    support_subset_outer := fun i ↦ (hsupport i).trans inter_subset_right
    pairwise_disjoint_support := ?_
  }⟩
  intro i j hij
  exact (hVpairwise hij).mono (hsupport i) (hsupport j)

/-- The distinguished Schoenflies centers of a finite family of Jordan disks. -/
def finiteDiskCenters [Fintype ι] (inner : ι → JordanCircle) : ι → Plane :=
  fun i ↦ (inner i).diskPushCenter

/-- The common finite-point source for the simultaneous planar disk pushout. -/
def finiteDiskCenterComplement [Fintype ι] (inner : ι → JordanCircle) : Set Plane :=
  {x | ∀ i, x ≠ finiteDiskCenters inner i}

namespace SeparatedPlanarJordanDiskSupports

variable [Fintype ι] {outer : JordanCircle} {inner : ι → JordanCircle}
  (D : SeparatedPlanarJordanDiskSupports outer inner)

/-- Regard a point missing every center as a point missing the selected center. -/
def localPuncture (_D : SeparatedPlanarJordanDiskSupports outer inner)
    (i : ι) (x : finiteDiskCenterComplement inner) :
    (inner i).diskPushPuncture :=
  ⟨x, x.2 i⟩

/-- The ambient value of the `i`-th one-disk pushout on the common finite-point source. -/
def localPushedValue (i : ι) (x : finiteDiskCenterComplement inner) : Plane :=
  (inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)
    (D.localPuncture i x)

/-- A local pushout preserves membership in its own radial support. -/
theorem localPushedValue_mem_support_iff (i : ι)
    (x : finiteDiskCenterComplement inner) :
    D.localPushedValue i x ∈ (inner i).diskPushSupport (D.radius i) ↔
      (x : Plane) ∈ (inner i).diskPushSupport (D.radius i) := by
  exact (inner i).punctureToDiskComplement_mem_support_iff
    (D.radius i) (D.one_lt_radius i) (D.localPuncture i x)

/-- A local pushout avoids its own closed Jordan disk. -/
theorem localPushedValue_not_mem_disk (i : ι)
    (x : finiteDiskCenterComplement inner) :
    D.localPushedValue i x ∉ (inner i).diskPushClosedDisk := by
  exact ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)
    (D.localPuncture i x)).2

/-- A local pushout cannot hit any distinguished center. -/
theorem localPushedValue_ne_center (i j : ι)
    (x : finiteDiskCenterComplement inner) :
    D.localPushedValue i x ≠ finiteDiskCenters inner j := by
  by_cases hij : i = j
  · subst j
    intro hcenter
    exact D.localPushedValue_not_mem_disk i x
      (hcenter.symm ▸ (inner i).diskPushCenter_mem_closedDisk)
  · by_cases hx : (x : Plane) ∈ (inner i).diskPushSupport (D.radius i)
    · intro hcenter
      have hout : D.localPushedValue i x ∈
          (inner i).diskPushSupport (D.radius i) :=
        (D.localPushedValue_mem_support_iff i x).2 hx
      have hj : finiteDiskCenters inner j ∈
          (inner j).diskPushSupport (D.radius j) :=
        (inner j).diskPushClosedDisk_subset_support (D.one_lt_radius j).le
          (inner j).diskPushCenter_mem_closedDisk
      exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij)) hout (hcenter ▸ hj)
    · change ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)
        (D.localPuncture i x) : Plane) ≠ _
      rw [(inner i).punctureToDiskComplement_apply_of_not_mem_support
        (D.radius i) (D.one_lt_radius i) (D.localPuncture i x) hx]
      exact x.2 j

/-- The `i`-th planar pushout as an endomorphism of the common finite-point source. -/
def stage (i : ι) (x : finiteDiskCenterComplement inner) :
    finiteDiskCenterComplement inner :=
  ⟨D.localPushedValue i x, fun j ↦ D.localPushedValue_ne_center i j x⟩

theorem continuous_localPuncture (i : ι) : Continuous (D.localPuncture i) := by
  exact Continuous.subtype_mk continuous_subtype_val _

theorem continuous_localPushedValue (i : ι) : Continuous (D.localPushedValue i) := by
  exact continuous_subtype_val.comp <|
    ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)).continuous.comp
      (D.continuous_localPuncture i)

theorem continuous_stage (i : ι) : Continuous (D.stage i) := by
  exact Continuous.subtype_mk (D.continuous_localPushedValue i) _

/-- A local stage is fixed outside its own support. -/
theorem stage_eq_self_of_not_mem_support (i : ι)
    (x : finiteDiskCenterComplement inner)
    (hx : (x : Plane) ∉ (inner i).diskPushSupport (D.radius i)) :
    D.stage i x = x := by
  apply Subtype.ext
  exact (inner i).punctureToDiskComplement_apply_of_not_mem_support
    (D.radius i) (D.one_lt_radius i) (D.localPuncture i x) hx

/-- The `i`-th stage avoids the `i`-th closed disk. -/
theorem stage_not_mem_disk (i : ι) (x : finiteDiskCenterComplement inner) :
    (D.stage i x : Plane) ∉ (inner i).diskPushClosedDisk :=
  D.localPushedValue_not_mem_disk i x

/-- A local stage preserves membership in the complement of every other closed disk. -/
theorem stage_not_mem_other_disk_iff {i j : ι} (hij : i ≠ j)
    (x : finiteDiskCenterComplement inner) :
    (D.stage i x : Plane) ∉ (inner j).diskPushClosedDisk ↔
      (x : Plane) ∉ (inner j).diskPushClosedDisk := by
  by_cases hx : (x : Plane) ∈ (inner i).diskPushSupport (D.radius i)
  · have hout : (D.stage i x : Plane) ∈ (inner i).diskPushSupport (D.radius i) :=
      (D.localPushedValue_mem_support_iff i x).2 hx
    have hdisjoint := Set.disjoint_left.mp (D.pairwise_disjoint_support hij)
    constructor
    · intro _ hxdisk
      exact hdisjoint hx <|
        (inner j).diskPushClosedDisk_subset_support (D.one_lt_radius j).le hxdisk
    · intro _ hstagedisk
      exact hdisjoint hout <|
        (inner j).diskPushClosedDisk_subset_support (D.one_lt_radius j).le hstagedisk
  · rw [D.stage_eq_self_of_not_mem_support i x hx]

/-- Every point outside the selected disk has a preimage under the corresponding local stage. -/
theorem stage_surjective_disk_complement (i : ι)
    (y : finiteDiskCenterComplement inner)
    (hy : (y : Plane) ∉ (inner i).diskPushClosedDisk) :
    ∃ x, D.stage i x = y := by
  let ycomp : (inner i).diskPushComplement := ⟨y, hy⟩
  let xp := ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)).symm ycomp
  have hxp : ∀ j, (xp : Plane) ≠ finiteDiskCenters inner j := by
    intro j
    by_cases hij : i = j
    · subst j
      exact xp.2
    · by_cases hysupport : (y : Plane) ∈ (inner i).diskPushSupport (D.radius i)
      · have hpush :
          ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i) xp : Plane) =
            y := congrArg Subtype.val <|
          ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)).apply_symm_apply
            ycomp
        have hxpsupport : (xp : Plane) ∈ (inner i).diskPushSupport (D.radius i) :=
          ((inner i).punctureToDiskComplement_mem_support_iff
            (D.radius i) (D.one_lt_radius i) xp).1 (hpush.symm ▸ hysupport)
        intro hxcenter
        have hj : finiteDiskCenters inner j ∈
            (inner j).diskPushSupport (D.radius j) :=
          (inner j).diskPushClosedDisk_subset_support (D.one_lt_radius j).le
            (inner j).diskPushCenter_mem_closedDisk
        exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij))
          hxpsupport (hxcenter ▸ hj)
      · have hxpeq : (xp : Plane) = y := congrArg Subtype.val <|
          (inner i).punctureToDiskComplement_symm_apply_of_not_mem_support
            (D.radius i) (D.one_lt_radius i) ycomp hysupport
        exact hxpeq.symm ▸ y.2 j
  let x : finiteDiskCenterComplement inner := ⟨xp, hxp⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i) xp : Plane) = y
  exact congrArg Subtype.val <|
    ((inner i).punctureToDiskComplement (D.radius i) (D.one_lt_radius i)).apply_symm_apply
      ycomp

/-- The `i`-th closed disk, viewed as a forbidden subset of the common source. -/
def sourceDisk (_D : SeparatedPlanarJordanDiskSupports outer inner)
    (i : ι) : Set (finiteDiskCenterComplement inner) :=
  Subtype.val ⁻¹' (inner i).diskPushClosedDisk

/-- The exact simultaneous disk complement inside the common finite-point source. -/
def sourceDiskComplement (_D : SeparatedPlanarJordanDiskSupports outer inner) :
    Set (finiteDiskCenterComplement inner) :=
  {x | ∀ i, (x : Plane) ∉ (inner i).diskPushClosedDisk}

/-- The final finite planar pushout. -/
def finitePush (x : finiteDiskCenterComplement inner) : finiteDiskCenterComplement inner :=
  Submission.Topology.composeStageList D.stage Finset.univ.toList x

theorem continuous_finitePush : Continuous D.finitePush :=
  Submission.Topology.continuous_composeStageList D.stage D.continuous_stage
    Finset.univ.toList

/-- The finite planar pushout has exactly the simultaneous disk complement as its range. -/
theorem range_finitePush : Set.range D.finitePush = D.sourceDiskComplement := by
  unfold finitePush sourceDiskComplement
  have hrange := Submission.Topology.range_composeStageList D.stage D.sourceDisk
    D.stage_not_mem_disk D.stage_surjective_disk_complement
    (fun hij x ↦ D.stage_not_mem_other_disk_iff hij x)
    Finset.univ.toList Finset.univ.nodup_toList
  simpa only [sourceDisk, Submission.Topology.listComplement,
    Submission.Topology.mem_listComplement,
    Finset.mem_toList, Finset.mem_univ, mem_preimage, forall_const] using hrange

/-- Each local stage preserves the chosen outer Jordan inside. -/
theorem stage_mem_outer_inside (i : ι) (x : finiteDiskCenterComplement inner)
    (hxOuter : (x : Plane) ∈ outer.inside) :
    (D.stage i x : Plane) ∈ outer.inside := by
  by_cases hx : (x : Plane) ∈ (inner i).diskPushSupport (D.radius i)
  · exact D.support_subset_outer i ((D.localPushedValue_mem_support_iff i x).2 hx)
  · rw [D.stage_eq_self_of_not_mem_support i x hx]
    exact hxOuter

/-- The complete finite push preserves the chosen outer Jordan inside. -/
theorem finitePush_mem_outer_inside (x : finiteDiskCenterComplement inner)
    (hxOuter : (x : Plane) ∈ outer.inside) :
    (D.finitePush x : Plane) ∈ outer.inside := by
  unfold finitePush
  generalize (Finset.univ : Finset ι).toList = is
  induction is with
  | nil => exact hxOuter
  | cons i is ih =>
      exact D.stage_mem_outer_inside i _ ih

/-- The finite push is fixed at every point outside all selected supports. -/
theorem finitePush_eq_self_of_forall_not_mem_support
    (x : finiteDiskCenterComplement inner)
    (hx : ∀ i, (x : Plane) ∉ (inner i).diskPushSupport (D.radius i)) :
    D.finitePush x = x := by
  exact Submission.Topology.composeStageList_eq_self_of_forall_not_mem
    D.stage (fun i ↦ Subtype.val ⁻¹' (inner i).diskPushSupport (D.radius i))
    (fun i x hxi ↦ D.stage_eq_self_of_not_mem_support i x hxi)
    Finset.univ.toList x fun i _ ↦ hx i

/-- Every selected disk center, regarded as a point of the outer Jordan inside. -/
def diskCenterInOuterInside (i : ι) : outer.inside :=
  ⟨finiteDiskCenters inner i,
    D.support_subset_outer i <|
      (inner i).diskPushClosedDisk_subset_support (D.one_lt_radius i).le
        (inner i).diskPushCenter_mem_closedDisk⟩

/-- The connected source obtained by removing the selected centers from the outer inside. -/
def puncturedOuterInside : Set outer.inside :=
  {x | ∀ i, x ≠ D.diskCenterInOuterInside i}

theorem isConnected_puncturedOuterInside : IsConnected D.puncturedOuterInside :=
  outer.isConnected_inside_avoiding_finite D.diskCenterInOuterInside

/-- Convert a point of the punctured outer inside to the common finite-center source. -/
def puncturedOuterInsideToCenterComplement (x : D.puncturedOuterInside) :
    finiteDiskCenterComplement inner :=
  ⟨x, fun i hi ↦ x.2 i (Subtype.ext hi)⟩

theorem continuous_puncturedOuterInsideToCenterComplement :
    Continuous D.puncturedOuterInsideToCenterComplement := by
  exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The finite push restricted to the connected punctured outer inside. -/
def outerFinitePush (x : D.puncturedOuterInside) : Plane :=
  D.finitePush (D.puncturedOuterInsideToCenterComplement x)

theorem continuous_outerFinitePush : Continuous D.outerFinitePush := by
  exact continuous_subtype_val.comp <|
    D.continuous_finitePush.comp D.continuous_puncturedOuterInsideToCenterComplement

theorem outerFinitePush_mem_outer_inside (x : D.puncturedOuterInside) :
    D.outerFinitePush x ∈ outer.inside := by
  exact D.finitePush_mem_outer_inside _ x.1.2

/-- The union of all selected closed inner Jordan disks. -/
def closedInnerDiskUnion (_D : SeparatedPlanarJordanDiskSupports outer inner) : Set Plane :=
  ⋃ i, (inner i).diskPushClosedDisk

/-- The open planar core between the outer circle and the selected closed inner disks. -/
def outerDiskCore : Set Plane :=
  outer.inside \ D.closedInnerDiskUnion

/-- The restricted finite push has exactly the open planar core as its range. -/
theorem range_outerFinitePush : Set.range D.outerFinitePush = D.outerDiskCore := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨D.outerFinitePush_mem_outer_inside x, ?_⟩
    intro hinner
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hinner
    have hcomplement : D.finitePush (D.puncturedOuterInsideToCenterComplement x) ∈
        D.sourceDiskComplement := by
      rw [← D.range_finitePush]
      exact ⟨D.puncturedOuterInsideToCenterComplement x, rfl⟩
    exact hcomplement i hi
  · rintro y ⟨hyOuter, hyInner⟩
    let ys : finiteDiskCenterComplement inner :=
      ⟨y, fun i hi ↦ hyInner <| Set.mem_iUnion.mpr ⟨i,
        hi.symm ▸ (inner i).diskPushCenter_mem_closedDisk⟩⟩
    have hysComplement : ys ∈ D.sourceDiskComplement := by
      intro i hi
      exact hyInner (Set.mem_iUnion.mpr ⟨i, hi⟩)
    obtain ⟨x, hx⟩ : ∃ x, D.finitePush x = ys := by
      rw [← D.range_finitePush] at hysComplement
      exact hysComplement
    have hxOuter : (x : Plane) ∈ outer.inside := by
      by_contra hxNotOuter
      have hxSupport : ∀ i, (x : Plane) ∉ (inner i).diskPushSupport (D.radius i) := by
        intro i hxi
        exact hxNotOuter (D.support_subset_outer i hxi)
      have hfixed := D.finitePush_eq_self_of_forall_not_mem_support x hxSupport
      have hxy : (x : Plane) = y := by
        rw [← hfixed]
        exact congrArg Subtype.val hx
      exact hxNotOuter (hxy ▸ hyOuter)
    let xo : outer.inside := ⟨x, hxOuter⟩
    let xa : D.puncturedOuterInside :=
      ⟨xo, fun i hi ↦ x.2 i (congrArg Subtype.val hi)⟩
    refine ⟨xa, ?_⟩
    exact congrArg Subtype.val hx

/-- The open planar core between finitely many separated inner disks is connected. -/
theorem isConnected_outerDiskCore : IsConnected D.outerDiskCore := by
  let _ : ConnectedSpace D.puncturedOuterInside :=
    isConnected_iff_connectedSpace.mp D.isConnected_puncturedOuterInside
  rw [← D.range_outerFinitePush]
  exact isConnected_range D.continuous_outerFinitePush

end SeparatedPlanarJordanDiskSupports

end Schoenflies.JordanCircle
