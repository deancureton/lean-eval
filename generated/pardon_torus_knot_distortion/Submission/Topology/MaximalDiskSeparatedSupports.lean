import Submission.Topology.FiniteSequentialTorusPushout
import Submission.Topology.HalfSphereSurgeryDichotomy

/-!
# Separated supports for maximal inessential torus disks

A finite pairwise-disjoint family of closed torus disks admits pairwise-disjoint open
neighborhoods.  Pulling those neighborhoods back to the covering plane and intersecting them
with the covering-injective neighborhoods of the lifted Jordan disks gives the open sets into
which the existing Schoenflies radius lemma shrinks.  Consequently the radial supports needed
by the finite puncture pushout are consequences of maximal-disk disjointness, not extra geometric
data.
-/

open LeanEval.KnotTheory.PardonDistortion
open Filter Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

variable {Phi : AmbientIsotopy} {ι : Type*}

/-- A finite pairwise-disjoint family of closed sets has pairwise-disjoint open supersets. -/
theorem exists_pairwise_disjoint_open_supersets [Fintype ι]
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (K : ι → Set X) (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (K i) (K j)) :
    ∃ U : ι → Set X,
      (∀ i, IsOpen (U i) ∧ K i ⊆ U i) ∧
        Pairwise fun i j ↦ Disjoint (U i) (U j) := by
  have hnhds : Pairwise (Disjoint on fun i ↦ 𝓝ˢ (K i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hclosed i) (hclosed j) (hdisjoint hij)
  obtain ⟨U, hU, hUpairwise⟩ :=
    hnhds.exists_mem_filter_basis_of_disjoint (fun i ↦ hasBasis_nhdsSet (K i))
  exact ⟨U, hU, hUpairwise⟩

namespace EmbeddedTorusIntersectionCircle

/-- A projected closed zero-winding Jordan disk is closed in the transported torus. -/
theorem isClosed_zeroWindingProjectedClosedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    IsClosed (C.zeroWindingProjectedClosedJordanDisk hzero) := by
  exact ((C.zeroWindingJordanCircle hzero).isCompact_closure_inside.image
    (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous).isClosed

/-- Pairwise-disjoint canonical disks have all the separated radial support data needed by the
finite sequential pushout. -/
theorem exists_separatedZeroWindingDiskSupports_of_pairwise_disjoint [Fintype ι]
    (C : ι → EmbeddedTorusIntersectionCircle Phi)
    (hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0))
    (hdisjoint : Pairwise fun i j ↦
      Disjoint ((C i).zeroWindingProjectedClosedJordanDisk (hzero i))
        ((C j).zeroWindingProjectedClosedJordanDisk (hzero j))) :
    Nonempty (SeparatedZeroWindingDiskSupports C hzero) := by
  let K : ι → Set (transportedTorus Phi) :=
    fun i ↦ (C i).zeroWindingProjectedClosedJordanDisk (hzero i)
  obtain ⟨U, hU, hUpairwise⟩ := exists_pairwise_disjoint_open_supersets K
    (fun i ↦ (C i).isClosed_zeroWindingProjectedClosedJordanDisk (hzero i)) hdisjoint
  have hradius : ∀ i, ∃ R : ℝ, 1 < R ∧
      (C i).zeroWindingSchoenfliesSupport (hzero i) R ⊆
        torusCoveringProjectionToTorus Phi ⁻¹' U i ∧
      Set.InjOn (torusCoveringProjectionToTorus Phi)
        ((C i).zeroWindingSchoenfliesSupport (hzero i) R) := by
    intro i
    obtain ⟨V, hVopen, hKV, hinjV⟩ :=
      (C i).exists_open_injOn_torusCoveringProjection_zeroWindingDisk (hzero i)
    let W := torusCoveringProjectionToTorus Phi ⁻¹' U i ∩ V
    have hWopen : IsOpen W :=
      ((hU i).1.preimage
        (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous).inter hVopen
    have hKW : (C i).zeroWindingClosedJordanDisk (hzero i) ⊆ W := by
      intro x hx
      exact ⟨(hU i).2 ⟨x, hx, rfl⟩, hKV hx⟩
    obtain ⟨R, hR, hsupport⟩ :=
      (C i).exists_radius_schoenfliesSupport_subset_open (hzero i) hWopen hKW
    have hsupport' : (C i).zeroWindingSchoenfliesSupport (hzero i) R ⊆ W := by
      simpa only [zeroWindingSchoenfliesSupport] using hsupport
    exact ⟨R, hR, hsupport'.trans inter_subset_left,
      hinjV.mono (hsupport'.trans inter_subset_right)⟩
  choose R hR hsupport hinjective using hradius
  refine ⟨{
    radius := R
    one_lt_radius := hR
    projection_injective := hinjective
    pairwise_disjoint_support := ?_
    disk_subset_support := ?_
    center_mem_disk := fun i ↦
      (C i).zeroWindingTorusDiskCenter_mem_projectedClosedJordanDisk (hzero i)
  }⟩
  · intro i j hij
    apply (hUpairwise hij).mono
    · rintro _ ⟨x, hx, rfl⟩
      exact hsupport i hx
    · rintro _ ⟨x, hx, rfl⟩
      exact hsupport j hx
  · intro i _ hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x,
      (C i).zeroWindingClosedJordanDisk_subset_schoenfliesSupport (hzero i) (hR i).le hx,
      rfl⟩

end EmbeddedTorusIntersectionCircle

namespace FiniteSphereSurgeryIntersectionSystem

variable [Fintype ι]

/-- The stage disk map has exactly the canonical projected closed Jordan disk as its range. -/
theorem range_torusDiskMap_eq_projectedClosedJordanDisk
    (S : FiniteSphereSurgeryIntersectionSystem Phi ι)
    (hzero : S.AllInessential) (i : ι) :
    Set.range (S.torusDiskMap hzero i) =
      (S.circle i).zeroWindingProjectedClosedJordanDisk (hzero i) := by
  rw [(S.circle i).zeroWindingProjectedClosedJordanDisk_eq_range (hzero i)]
  rfl

end FiniteSphereSurgeryIntersectionSystem

namespace MaximalInessentialTorusDiskFamily

variable [Fintype ι] [DecidableEq ι]
  {S : FiniteSphereSurgeryIntersectionSystem Phi ι}
  {hzero : S.AllInessential}

/-- The canonical projected disks indexed by a maximal family are pairwise disjoint. -/
theorem selected_projectedClosedJordanDisks_pairwise_disjoint
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    Pairwise fun i j : M.maximal ↦
      Disjoint ((S.circle i.1).zeroWindingProjectedClosedJordanDisk (hzero i.1))
        ((S.circle j.1).zeroWindingProjectedClosedJordanDisk (hzero j.1)) := by
  intro i j hij
  rw [← S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero i.1,
    ← S.range_torusDiskMap_eq_projectedClosedJordanDisk hzero j.1]
  exact M.disks_pairwise_disjoint i.2 j.2 fun hval ↦ hij (Subtype.ext hval)

/-- The separated radial supports canonically derived from the selected maximal disks. -/
def separatedZeroWindingDiskSupports
    (M : MaximalInessentialTorusDiskFamily S hzero) :
    EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports
      (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1) :=
  Classical.choice <|
    EmbeddedTorusIntersectionCircle.exists_separatedZeroWindingDiskSupports_of_pairwise_disjoint
      (fun i : M.maximal ↦ S.circle i.1) (fun i ↦ hzero i.1)
      M.selected_projectedClosedJordanDisks_pairwise_disjoint

/-- A selected support is contained in the complement of every other selected closed disk. -/
theorem separatedSupport_subset_compl_otherDisk
    (M : MaximalInessentialTorusDiskFamily S hzero)
    {i j : M.maximal} (hij : i ≠ j) :
    (S.circle i.1).zeroWindingProjectedSupport (hzero i.1)
        (M.separatedZeroWindingDiskSupports.radius i) ⊆
      ((S.circle j.1).zeroWindingProjectedClosedJordanDisk (hzero j.1))ᶜ := by
  intro x hxsupport hxdisk
  let D := M.separatedZeroWindingDiskSupports
  exact Set.disjoint_left.mp
    ((D.pairwise_disjoint_support hij).mono_right (D.disk_subset_support j))
      hxsupport hxdisk

end MaximalInessentialTorusDiskFamily

end Submission.Topology
