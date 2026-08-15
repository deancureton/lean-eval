import Submission.Topology.FinitePunctureCarrierPushout
import Submission.Topology.TorusDiskPuncture

/-!
# Finite sequential disk pushouts on a transported torus

This file isolates the finite-composition part of the puncture-to-disk construction.  A local
stage is an endomorphism of the complement of all chosen centers, together with a unit-interval
deformation from the identity and a support outside which both maps are literally the identity.
Composing the stages along `Finset.univ.toList` gives the exact `FinitePuncturePushoutData`
interface used by the finite-puncture carrier argument.

The geometric input is deliberately support-aware.  For pairwise disjoint Schoenflies supports,
the local torus chart obtained from `zeroWindingPlanePunctureToDiskComplement` supplies these
fields: its image remains in its own support, so it misses every other center and every other
closed disk.  The final range equality below is what later localization arguments use to keep a
carrier in the original inner component rather than replacing it by an unrelated puncture
carrier.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*}
  {centers : ι → Circle × Circle} {target : Set (transportedTorus Phi)}

namespace EmbeddedTorusIntersectionCircle

/-- Product-torus coordinates of the chosen Schoenflies center. -/
def zeroWindingDiskCenterCoordinates (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Circle × Circle :=
  (Circle.exp ((C.zeroWindingDiskCenter hzero) 0),
    Circle.exp ((C.zeroWindingDiskCenter hzero) 1))

@[simp]
theorem transported_zeroWindingDiskCenterCoordinates
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    transportedTorusHomeomorph Phi (C.zeroWindingDiskCenterCoordinates hzero) =
      C.zeroWindingTorusDiskCenter hzero :=
  rfl

/-- The projected closed lifted Jordan disk in the transported torus. -/
def zeroWindingProjectedClosedJordanDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) : Set (transportedTorus Phi) :=
  torusCoveringProjectionToTorus Phi '' C.zeroWindingClosedJordanDisk hzero

theorem zeroWindingTorusDiskCenter_mem_projectedClosedJordanDisk
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingTorusDiskCenter hzero ∈
      C.zeroWindingProjectedClosedJordanDisk hzero :=
  ⟨C.zeroWindingDiskCenter hzero,
    C.zeroWindingDiskCenter_mem_closedJordanDisk hzero, rfl⟩

/-- The explicit Schoenflies disk parametrization fills the entire closed lifted Jordan disk. -/
theorem range_zeroWindingPlaneDisk (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Set.range (C.zeroWindingPlaneDisk hzero) = C.zeroWindingClosedJordanDisk hzero := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact C.zeroWindingPlaneDisk_mem_closure_inside hzero z
  · intro x hx
    let E := C.zeroWindingRegionalExtension hzero
    let xb : closure (C.zeroWindingJordanCircle hzero).inside := ⟨x, hx⟩
    let z : ClosedUnitDisk := complexDiskPlaneBall.symm (E.insideHomeomorph xb)
    refine ⟨z, ?_⟩
    change (E.insideHomeomorph.symm (complexDiskPlaneBall z) : TorusCoveringPlane) = x
    rw [show complexDiskPlaneBall z = E.insideHomeomorph xb by
      exact complexDiskPlaneBall.apply_symm_apply (E.insideHomeomorph xb)]
    exact congrArg Subtype.val (E.insideHomeomorph.symm_apply_apply xb)

/-- The projected closed Jordan disk is exactly the range of the canonical torus-side disk map. -/
theorem zeroWindingProjectedClosedJordanDisk_eq_range
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    C.zeroWindingProjectedClosedJordanDisk hzero =
      Set.range (fun z : ClosedUnitDisk ↦
        torusCoveringProjectionToTorus Phi (C.zeroWindingPlaneDisk hzero z)) := by
  rw [zeroWindingProjectedClosedJordanDisk, ← C.range_zeroWindingPlaneDisk hzero]
  ext x
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨C.zeroWindingPlaneDisk hzero z, ⟨z, rfl⟩, rfl⟩

/-- The complement of a finite family of projected zero-winding Jordan disks. -/
def finiteZeroWindingDiskComplement [Fintype ι]
    (C : ι → EmbeddedTorusIntersectionCircle Phi)
    (hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0)) :
    Set (transportedTorus Phi) :=
  {x | ∀ i, x ∉ (C i).zeroWindingProjectedClosedJordanDisk (hzero i)}

/-- Centers used by the finite-point source of the disk pushout. -/
def finiteZeroWindingDiskCenters [Fintype ι]
    (C : ι → EmbeddedTorusIntersectionCircle Phi)
    (hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0)) :
    ι → Circle × Circle :=
  fun i ↦ (C i).zeroWindingDiskCenterCoordinates (hzero i)

/-- Geometric separation data needed to descend every local plane pushout and patch it by the
identity.  The support containment clauses are intentionally explicit: they are the facts that
make all later stages preserve the disks already removed by earlier stages. -/
structure SeparatedZeroWindingDiskSupports [Fintype ι]
    (C : ι → EmbeddedTorusIntersectionCircle Phi)
    (hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0)) where
  radius : ι → ℝ
  one_lt_radius : ∀ i, 1 < radius i
  projection_injective : ∀ i,
    Set.InjOn (torusCoveringProjectionToTorus Phi)
      ((C i).zeroWindingSchoenfliesSupport (hzero i) (radius i))
  pairwise_disjoint_support : Pairwise fun i j ↦
    Disjoint ((C i).zeroWindingProjectedSupport (hzero i) (radius i))
      ((C j).zeroWindingProjectedSupport (hzero j) (radius j))
  disk_subset_support : ∀ i,
    (C i).zeroWindingProjectedClosedJordanDisk (hzero i) ⊆
      (C i).zeroWindingProjectedSupport (hzero i) (radius i)
  center_mem_disk : ∀ i,
    (C i).zeroWindingTorusDiskCenter (hzero i) ∈
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)

namespace SeparatedZeroWindingDiskSupports

variable [Fintype ι]
  {C : ι → EmbeddedTorusIntersectionCircle Phi}
  {hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0)}
  (D : SeparatedZeroWindingDiskSupports C hzero)

/-- The inverse support chart gives the distinguished lift of a torus point in a projected
support. -/
def supportLift (i : ι) (x : transportedTorus Phi)
    (hx : x ∈ (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    (C i).zeroWindingSchoenfliesSupport (hzero i) (D.radius i) :=
  ((C i).zeroWindingSupportProjectionHomeomorph (hzero i) (D.radius i)
    (D.projection_injective i)).symm ⟨x, hx⟩

theorem projection_supportLift (i : ι) (x : transportedTorus Phi)
    (hx : x ∈ (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    torusCoveringProjectionToTorus Phi (D.supportLift i x hx) = x := by
  exact congrArg Subtype.val <|
    ((C i).zeroWindingSupportProjectionHomeomorph (hzero i) (D.radius i)
      (D.projection_injective i)).apply_symm_apply ⟨x, hx⟩

/-- A point of the finite-center complement lying in one projected support has a unique support
lift, and that lift misses the corresponding Schoenflies center. -/
def supportPunctureLift (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    (C i).zeroWindingPlanePuncture (hzero i) :=
  ⟨D.supportLift i x hx, by
    intro hlift
    apply x.2 i
    rw [transported_zeroWindingDiskCenterCoordinates]
    exact (D.projection_supportLift i x hx).symm.trans <|
      congrArg (torusCoveringProjectionToTorus Phi) hlift⟩

/-- The local torus value obtained by lifting through the injective support chart, applying the
Schoenflies radial pushout, and projecting back. -/
def localStageValue (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    transportedTorus Phi :=
  torusCoveringProjectionToTorus Phi <|
    (C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
      (D.radius i) (D.one_lt_radius i) (D.supportPunctureLift i x hx)

/-- A local radial pushout stays in the same projected support. -/
theorem localStageValue_mem_support (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.localStageValue i x hx ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) := by
  refine ⟨(C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
      (D.radius i) (D.one_lt_radius i) (D.supportPunctureLift i x hx), ?_, rfl⟩
  rw [(C i).planePunctureToDiskComplement_mem_support_iff]
  exact (D.supportLift i x hx).2

/-- The local radial value avoids its own projected closed Jordan disk. -/
theorem localStageValue_not_mem_disk (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.localStageValue i x hx ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i) := by
  rintro ⟨z, hz, hprojection⟩
  let pushed := (C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
    (D.radius i) (D.one_lt_radius i) (D.supportPunctureLift i x hx)
  have hpushedSupport : (pushed : TorusCoveringPlane) ∈
      (C i).zeroWindingSchoenfliesSupport (hzero i) (D.radius i) := by
    rw [(C i).planePunctureToDiskComplement_mem_support_iff]
    exact (D.supportLift i x hx).2
  have hzSupport : z ∈
      (C i).zeroWindingSchoenfliesSupport (hzero i) (D.radius i) :=
    (C i).zeroWindingClosedJordanDisk_subset_schoenfliesSupport
      (hzero i) (D.one_lt_radius i).le hz
  have hpushedz : (pushed : TorusCoveringPlane) = z :=
    D.projection_injective i hpushedSupport hzSupport <| by
      simpa only [localStageValue, pushed] using hprojection.symm
  exact pushed.2 (hpushedz.symm ▸ hz)

/-- The local unit-interval deformation, transported through the same support chart. -/
def localDeformationValue (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    transportedTorus Phi :=
  torusCoveringProjectionToTorus Phi <|
    (C i).zeroWindingPlanePunctureDeformation (hzero i)
      (D.radius i) (D.one_lt_radius i) u (D.supportPunctureLift i x hx)

/-- The entire local deformation remains in its projected closed support. -/
theorem localDeformationValue_mem_support (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.localDeformationValue i u x hx ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) := by
  refine ⟨(C i).zeroWindingPlanePunctureDeformation (hzero i)
      (D.radius i) (D.one_lt_radius i) u (D.supportPunctureLift i x hx), ?_, rfl⟩
  rw [(C i).mem_zeroWindingSchoenfliesSupport_iff,
    (C i).zeroWindingAmbientHomeomorph_planePunctureDeformation]
  apply RadialPuncture.planePunctureDeformation_mem_closedBall
  rw [← (C i).mem_zeroWindingSchoenfliesSupport_iff]
  exact (D.supportLift i x hx).2

/-- On the closed/open support seam the local deformation is literally the identity. -/
theorem localDeformationValue_eq_self_of_not_mem_openSupport
    (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hxopen : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedOpenSupport (hzero i) (D.radius i)) :
    D.localDeformationValue i u x hx = x := by
  have hliftOpen : (D.supportLift i x hx : TorusCoveringPlane) ∉
      (C i).zeroWindingSchoenfliesOpenSupport (hzero i) (D.radius i) := by
    intro hlift
    exact hxopen ⟨D.supportLift i x hx, hlift, D.projection_supportLift i x hx⟩
  have hnorm : D.radius i ≤
      ‖(C i).zeroWindingAmbientHomeomorph (hzero i) (D.supportLift i x hx)‖ := by
    rw [zeroWindingSchoenfliesOpenSupport, mem_image] at hliftOpen
    have hnotball : (C i).zeroWindingAmbientHomeomorph (hzero i)
        (D.supportLift i x hx) ∉ ball (0 : TorusCoveringPlane) (D.radius i) := by
      intro hball
      apply hliftOpen
      exact ⟨(C i).zeroWindingAmbientHomeomorph (hzero i)
        (D.supportLift i x hx), hball,
        (C i).zeroWindingAmbientHomeomorph (hzero i) |>.symm_apply_apply _⟩
    simpa only [mem_ball, dist_zero_right, not_lt] using hnotball
  rw [localDeformationValue,
    (C i).zeroWindingPlanePunctureDeformation_apply_of_radius_le
      (hzero i) (D.radius i) (D.one_lt_radius i) _ _ hnorm]
  exact D.projection_supportLift i x hx

theorem localStageValue_eq_self_of_not_mem_openSupport
    (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hxopen : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedOpenSupport (hzero i) (D.radius i)) :
    D.localStageValue i x hx = x := by
  calc
    D.localStageValue i x hx =
        D.localDeformationValue i
          ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x hx := by
      rw [localDeformationValue, localStageValue,
        (C i).zeroWindingPlanePunctureDeformation_one]
    _ = x := D.localDeformationValue_eq_self_of_not_mem_openSupport
      i _ x hx hxopen

/-- The finite-center source restricted to the `i`-th projected closed support. -/
def sourceSupport (i : ι) :
    Set (transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :=
  Subtype.val ⁻¹' (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)

/-- The clean, non-piecewise local stage on its closed support. -/
def localStageOnSupport (i : ι) (x : D.sourceSupport i) : transportedTorus Phi :=
  D.localStageValue i x.1 x.2

theorem continuous_supportPunctureLift (i : ι) :
    Continuous (fun x : D.sourceSupport i ↦
      D.supportPunctureLift i x.1 x.2) := by
  apply Continuous.subtype_mk
  exact ((C i).zeroWindingSupportProjectionHomeomorph (hzero i) (D.radius i)
      (D.projection_injective i)).symm.continuous.comp <|
    Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) _

theorem continuous_localStageOnSupport (i : ι) :
    Continuous (D.localStageOnSupport i) :=
  (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.comp <|
    ((C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
      (D.radius i) (D.one_lt_radius i)).continuous.comp
        (D.continuous_supportPunctureLift i)

/-- The clean local deformation on the product of the unit interval and its closed support. -/
def localDeformationOnSupport (i : ι)
    (z : Set.Icc (0 : ℝ) 1 × D.sourceSupport i) : transportedTorus Phi :=
  D.localDeformationValue i z.1 z.2.1 z.2.2

theorem continuous_localDeformationOnSupport (i : ι) :
    Continuous (D.localDeformationOnSupport i) :=
  (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous.comp <|
    ((C i).continuous_uncurry_zeroWindingPlanePunctureDeformation
      (hzero i) (D.radius i) (D.one_lt_radius i)).comp <|
        continuous_fst.prodMk <|
          (D.continuous_supportPunctureLift i).comp continuous_snd

/-- The total one-disk stage: use the descended radial map on the closed support and the identity
off it.  The two formulas agree on the support seam. -/
def totalStageValue (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) : transportedTorus Phi := by
  classical
  exact if hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) then
    D.localStageValue i x hx
  else x

theorem totalStageValue_eq_local (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.totalStageValue i x = D.localStageValue i x hx := by
  classical
  simp only [totalStageValue, dif_pos hx]

theorem totalStageValue_eq_self (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.totalStageValue i x = x := by
  classical
  simp only [totalStageValue, dif_neg hx]

theorem totalStageValue_mem_support_iff (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalStageValue i x ∈
        (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) ↔
      (x : transportedTorus Phi) ∈
        (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) := by
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalStageValue_eq_local i x hx]
    exact ⟨fun _ ↦ hx, fun _ ↦ D.localStageValue_mem_support i x hx⟩
  · rw [D.totalStageValue_eq_self i x hx]

/-- The closed part of the two-member source cover used for gluing a total stage. -/
theorem isClosed_sourceSupport (i : ι) : IsClosed (D.sourceSupport i) :=
  ((C i).isClosed_zeroWindingProjectedSupport (hzero i) (D.radius i)).preimage
    continuous_subtype_val

/-- The complement of the projected open support, viewed in the finite-center source. -/
def sourceOpenExterior (i : ι) :
    Set (transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :=
  Subtype.val ⁻¹'
    ((C i).zeroWindingProjectedOpenSupport (hzero i) (D.radius i))ᶜ

theorem isClosed_sourceOpenExterior (i : ι) : IsClosed (D.sourceOpenExterior i) :=
  ((C i).isOpen_zeroWindingProjectedOpenSupport (hzero i) (D.radius i)).isClosed_compl
    |>.preimage continuous_subtype_val

theorem sourceSupport_union_sourceOpenExterior (i : ι) :
    D.sourceSupport i ∪ D.sourceOpenExterior i = Set.univ := by
  ext x
  simp only [sourceSupport, sourceOpenExterior, mem_union, mem_preimage,
    mem_compl_iff, mem_univ, iff_true]
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedOpenSupport (hzero i) (D.radius i)
  · exact Or.inl <|
      (C i).zeroWindingProjectedOpenSupport_subset_support
        (hzero i) (D.radius i) hx
  · exact Or.inr hx

theorem totalStageValue_eq_self_of_mem_sourceOpenExterior (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : x ∈ D.sourceOpenExterior i) : D.totalStageValue i x = x := by
  by_cases hsupport : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalStageValue_eq_local i x hsupport]
    exact D.localStageValue_eq_self_of_not_mem_openSupport i x hsupport hx
  · exact D.totalStageValue_eq_self i x hsupport

/-- Continuity of the descended one-disk stage, including the support seam. -/
theorem continuous_totalStageValue (i : ι) :
    Continuous (D.totalStageValue i) := by
  have hsupport : ContinuousOn (D.totalStageValue i) (D.sourceSupport i) := by
    rw [continuousOn_iff_continuous_restrict]
    exact (D.continuous_localStageOnSupport i).congr fun x ↦
      D.totalStageValue_eq_local i x.1 x.2
  have hexterior : ContinuousOn (D.totalStageValue i) (D.sourceOpenExterior i) :=
    continuous_id.continuousOn.congr fun x hx ↦
      (D.totalStageValue_eq_self_of_mem_sourceOpenExterior i x hx).symm
  rw [← continuousOn_univ, ← D.sourceSupport_union_sourceOpenExterior i]
  exact hsupport.union_of_isClosed hexterior
    (D.isClosed_sourceSupport i) (D.isClosed_sourceOpenExterior i)

theorem totalStageValue_not_mem_disk (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalStageValue i x ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i) := by
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalStageValue_eq_local i x hx]
    exact D.localStageValue_not_mem_disk i x hx
  · rw [D.totalStageValue_eq_self i x hx]
    exact fun hxdisk ↦ hx (D.disk_subset_support i hxdisk)

/-- The total stage continues to avoid every chosen puncture center. -/
theorem totalStageValue_ne_center (i j : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalStageValue i x ≠ transportedTorusHomeomorph Phi
      (finiteZeroWindingDiskCenters C hzero j) := by
  rw [transported_zeroWindingDiskCenterCoordinates]
  by_cases hij : i = j
  · subst j
    intro heq
    apply D.totalStageValue_not_mem_disk i x
    exact heq ▸ D.center_mem_disk i
  · by_cases hx : (x : transportedTorus Phi) ∈
        (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
    · intro heq
      have hout : D.totalStageValue i x ∈
          (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) :=
        (D.totalStageValue_mem_support_iff i x).2 hx
      have hcenter : (C j).zeroWindingTorusDiskCenter (hzero j) ∈
          (C j).zeroWindingProjectedSupport (hzero j) (D.radius j) :=
        D.disk_subset_support j (D.center_mem_disk j)
      exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij))
        hout (heq.symm ▸ hcenter)
    · rw [D.totalStageValue_eq_self i x hx]
      exact x.2 j

/-- The total stage bundled as an endomorphism of the simultaneous finite-center complement. -/
def stage (i : ι) :
    transportedFinitePointComplement Phi (finiteZeroWindingDiskCenters C hzero) →
      transportedFinitePointComplement Phi (finiteZeroWindingDiskCenters C hzero) :=
  fun x ↦ ⟨D.totalStageValue i x, fun j ↦ D.totalStageValue_ne_center i j x⟩

theorem coe_stage (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    (D.stage i x : transportedTorus Phi) = D.totalStageValue i x :=
  rfl

theorem continuous_stage (i : ι) : Continuous (D.stage i) :=
  (D.continuous_totalStageValue i).subtype_mk _

/-- Every intermediate local radial value avoids every selected center. -/
theorem localDeformationValue_ne_center (i j : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.localDeformationValue i u x hx ≠
      transportedTorusHomeomorph Phi (finiteZeroWindingDiskCenters C hzero j) := by
  rw [transported_zeroWindingDiskCenterCoordinates]
  by_cases hij : i = j
  · subst j
    intro hprojection
    let moved := (C i).zeroWindingPlanePunctureDeformation (hzero i)
      (D.radius i) (D.one_lt_radius i) u (D.supportPunctureLift i x hx)
    have hmovedSupport : (moved : TorusCoveringPlane) ∈
        (C i).zeroWindingSchoenfliesSupport (hzero i) (D.radius i) := by
      rw [(C i).mem_zeroWindingSchoenfliesSupport_iff,
        (C i).zeroWindingAmbientHomeomorph_planePunctureDeformation]
      apply RadialPuncture.planePunctureDeformation_mem_closedBall
      rw [← (C i).mem_zeroWindingSchoenfliesSupport_iff]
      exact (D.supportLift i x hx).2
    have hcenterSupport := (C i).zeroWindingDiskCenter_mem_schoenfliesSupport
      (hzero i) (D.one_lt_radius i).le
    have hmovedCenter : (moved : TorusCoveringPlane) =
        (C i).zeroWindingDiskCenter (hzero i) :=
      D.projection_injective i hmovedSupport hcenterSupport <| by
        simpa only [localDeformationValue, moved] using hprojection
    exact moved.2 hmovedCenter
  · intro heq
    have hout := D.localDeformationValue_mem_support i u x hx
    have hcenter : (C j).zeroWindingTorusDiskCenter (hzero j) ∈
        (C j).zeroWindingProjectedSupport (hzero j) (D.radius j) :=
      D.disk_subset_support j (D.center_mem_disk j)
    exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij))
      hout (heq.symm ▸ hcenter)

/-- The total deformation is the local descended radial deformation on the support and the
identity elsewhere. -/
def totalDeformationValue (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) : transportedTorus Phi := by
  classical
  exact if hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) then
    D.localDeformationValue i u x hx
  else x

theorem totalDeformationValue_eq_local (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.totalDeformationValue i u x = D.localDeformationValue i u x hx := by
  classical
  simp only [totalDeformationValue, dif_pos hx]

theorem totalDeformationValue_eq_self (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.totalDeformationValue i u x = x := by
  classical
  simp only [totalDeformationValue, dif_neg hx]

theorem totalDeformationValue_ne_center (i j : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalDeformationValue i u x ≠
      transportedTorusHomeomorph Phi (finiteZeroWindingDiskCenters C hzero j) := by
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalDeformationValue_eq_local i u x hx]
    exact D.localDeformationValue_ne_center i j u x hx
  · rw [D.totalDeformationValue_eq_self i u x hx]
    exact x.2 j

theorem totalDeformationValue_eq_self_of_mem_sourceOpenExterior
    (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : x ∈ D.sourceOpenExterior i) : D.totalDeformationValue i u x = x := by
  by_cases hsupport : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalDeformationValue_eq_local i u x hsupport]
    exact D.localDeformationValue_eq_self_of_not_mem_openSupport
      i u x hsupport hx
  · exact D.totalDeformationValue_eq_self i u x hsupport

/-- The closed support part of the product cover for deformation continuity. -/
def deformationSupport (i : ι) : Set
    (Set.Icc (0 : ℝ) 1 × transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :=
  Prod.snd ⁻¹' D.sourceSupport i

/-- The closed exterior part of the product cover for deformation continuity. -/
def deformationOpenExterior (i : ι) : Set
    (Set.Icc (0 : ℝ) 1 × transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :=
  Prod.snd ⁻¹' D.sourceOpenExterior i

theorem deformationSupport_union_openExterior (i : ι) :
    D.deformationSupport i ∪ D.deformationOpenExterior i = Set.univ := by
  ext z
  have hz : z.2 ∈ D.sourceSupport i ∪ D.sourceOpenExterior i := by
    rw [D.sourceSupport_union_sourceOpenExterior i]
    exact Set.mem_univ z.2
  simpa only [deformationSupport, deformationOpenExterior, mem_union, mem_preimage,
    mem_univ, iff_true] using hz

/-- Joint continuity of the total descended deformation, including the support seam. -/
theorem continuous_uncurry_totalDeformationValue (i : ι) :
    Continuous (Function.uncurry (D.totalDeformationValue i)) := by
  have hsupport : ContinuousOn (Function.uncurry (D.totalDeformationValue i))
      (D.deformationSupport i) := by
    rw [continuousOn_iff_continuous_restrict]
    let g : (D.deformationSupport i) → Set.Icc (0 : ℝ) 1 × D.sourceSupport i :=
      fun z ↦ (z.1.1, ⟨z.1.2, z.2⟩)
    have hg : Continuous g :=
      (continuous_fst.comp continuous_subtype_val).prodMk <|
        Continuous.subtype_mk
          (continuous_snd.comp continuous_subtype_val) _
    exact ((D.continuous_localDeformationOnSupport i).comp hg).congr fun z ↦
      D.totalDeformationValue_eq_local i z.1.1 z.1.2 z.2
  have hexterior : ContinuousOn (Function.uncurry (D.totalDeformationValue i))
      (D.deformationOpenExterior i) :=
    continuous_snd.continuousOn.congr fun z hz ↦
      (D.totalDeformationValue_eq_self_of_mem_sourceOpenExterior
        i z.1 z.2 hz).symm
  have hsupportClosed : IsClosed (D.deformationSupport i) :=
    (D.isClosed_sourceSupport i).preimage continuous_snd
  have hexteriorClosed : IsClosed (D.deformationOpenExterior i) :=
    (D.isClosed_sourceOpenExterior i).preimage continuous_snd
  rw [← continuousOn_univ, ← D.deformationSupport_union_openExterior i]
  exact hsupport.union_of_isClosed hexterior hsupportClosed hexteriorClosed

/-- The total deformation bundled in the simultaneous finite-center complement. -/
def deformation (i : ι) (u : Set.Icc (0 : ℝ) 1) :
    transportedFinitePointComplement Phi (finiteZeroWindingDiskCenters C hzero) →
      transportedFinitePointComplement Phi (finiteZeroWindingDiskCenters C hzero) :=
  fun x ↦ ⟨D.totalDeformationValue i u x,
    fun j ↦ D.totalDeformationValue_ne_center i j u x⟩

theorem continuous_uncurry_deformation (i : ι) :
    Continuous (Function.uncurry (D.deformation i)) :=
  (D.continuous_uncurry_totalDeformationValue i).subtype_mk _

theorem totalDeformationValue_zero (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalDeformationValue i ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x := by
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalDeformationValue_eq_local i _ x hx, localDeformationValue,
      (C i).zeroWindingPlanePunctureDeformation_zero]
    exact D.projection_supportLift i x hx
  · exact D.totalDeformationValue_eq_self i _ x hx

theorem totalDeformationValue_one (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.totalDeformationValue i ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x =
      D.totalStageValue i x := by
  by_cases hx : (x : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · rw [D.totalDeformationValue_eq_local i _ x hx,
      D.totalStageValue_eq_local i x hx, localDeformationValue, localStageValue,
      (C i).zeroWindingPlanePunctureDeformation_one]
  · rw [D.totalDeformationValue_eq_self i _ x hx,
      D.totalStageValue_eq_self i x hx]

theorem deformation_zero (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.deformation i ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x := by
  exact Subtype.ext (D.totalDeformationValue_zero i x)

theorem deformation_one (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero)) :
    D.deformation i ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = D.stage i x := by
  exact Subtype.ext (D.totalDeformationValue_one i x)

theorem stage_fixed (i : ι)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.stage i x = x :=
  Subtype.ext (D.totalStageValue_eq_self i x hx)

theorem deformation_fixed (i : ι) (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hx : (x : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)) :
    D.deformation i u x = x :=
  Subtype.ext (D.totalDeformationValue_eq_self i u x hx)

/-- A support lift of a target point outside the projected disk, bundled in the lifted disk
complement. -/
def supportDiskComplementLift (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    (C i).zeroWindingPlaneDiskComplement (hzero i) :=
  ⟨D.supportLift i y hysupport, fun hliftDisk ↦
    hydisk ⟨D.supportLift i y hysupport, hliftDisk,
      D.projection_supportLift i y hysupport⟩⟩

/-- Apply the inverse lifted radial map to a target point in the support. -/
def localPreimagePlane (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    (C i).zeroWindingPlanePuncture (hzero i) :=
  ((C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
    (D.radius i) (D.one_lt_radius i)).symm
      (D.supportDiskComplementLift i y hysupport hydisk)

theorem localPreimagePlane_mem_support (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    (D.localPreimagePlane i y hysupport hydisk : TorusCoveringPlane) ∈
      (C i).zeroWindingSchoenfliesSupport (hzero i) (D.radius i) := by
  apply ((C i).planePunctureToDiskComplement_mem_support_iff
    (hzero i) (D.radius i) (D.one_lt_radius i)
    (D.localPreimagePlane i y hysupport hydisk)).mp
  rw [localPreimagePlane,
    ((C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
      (D.radius i) (D.one_lt_radius i)).apply_symm_apply]
  exact (D.supportLift i y hysupport).2

theorem localPreimagePlane_projection_ne_center (i j : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    torusCoveringProjectionToTorus Phi
        (D.localPreimagePlane i y hysupport hydisk) ≠
      transportedTorusHomeomorph Phi (finiteZeroWindingDiskCenters C hzero j) := by
  rw [transported_zeroWindingDiskCenterCoordinates]
  by_cases hij : i = j
  · subst j
    intro hprojection
    have hcenterSupport := (C i).zeroWindingDiskCenter_mem_schoenfliesSupport
      (hzero i) (D.one_lt_radius i).le
    have hplane := D.projection_injective i
      (D.localPreimagePlane_mem_support i y hysupport hydisk)
      hcenterSupport hprojection
    exact (D.localPreimagePlane i y hysupport hydisk).2 hplane
  · intro hprojection
    have hcenter : (C j).zeroWindingTorusDiskCenter (hzero j) ∈
        (C j).zeroWindingProjectedSupport (hzero j) (D.radius j) :=
      D.disk_subset_support j (D.center_mem_disk j)
    have hpreimage : torusCoveringProjectionToTorus Phi
        (D.localPreimagePlane i y hysupport hydisk) ∈
          (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) :=
      ⟨D.localPreimagePlane i y hysupport hydisk,
        D.localPreimagePlane_mem_support i y hysupport hydisk, rfl⟩
    exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij))
      hpreimage (hprojection.symm ▸ hcenter)

/-- The inverse local plane value, projected and bundled in the finite-center complement. -/
def localPreimage (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    transportedFinitePointComplement Phi (finiteZeroWindingDiskCenters C hzero) :=
  ⟨torusCoveringProjectionToTorus Phi
      (D.localPreimagePlane i y hysupport hydisk),
    fun j ↦ D.localPreimagePlane_projection_ne_center i j y hysupport hydisk⟩

theorem stage_localPreimage (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    D.stage i (D.localPreimage i y hysupport hydisk) = y := by
  apply Subtype.ext
  have hpreimageSupport :
      (D.localPreimage i y hysupport hydisk : transportedTorus Phi) ∈
        (C i).zeroWindingProjectedSupport (hzero i) (D.radius i) :=
    ⟨D.localPreimagePlane i y hysupport hydisk,
      D.localPreimagePlane_mem_support i y hysupport hydisk, rfl⟩
  rw [coe_stage, D.totalStageValue_eq_local i _ hpreimageSupport, localStageValue]
  have hlift : D.supportPunctureLift i (D.localPreimage i y hysupport hydisk)
      hpreimageSupport = D.localPreimagePlane i y hysupport hydisk := by
    apply Subtype.ext
    exact D.projection_injective i
      (D.supportLift i (D.localPreimage i y hysupport hydisk) hpreimageSupport).2
      (D.localPreimagePlane_mem_support i y hysupport hydisk) <| by
        rw [D.projection_supportLift]
  rw [hlift, localPreimagePlane,
    ((C i).zeroWindingPlanePunctureToDiskComplement (hzero i)
      (D.radius i) (D.one_lt_radius i)).apply_symm_apply]
  exact D.projection_supportLift i y hysupport

theorem stage_surjective_disk_complement (i : ι)
    (y : transportedFinitePointComplement Phi
      (finiteZeroWindingDiskCenters C hzero))
    (hydisk : (y : transportedTorus Phi) ∉
      (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) :
    ∃ x, D.stage i x = y := by
  by_cases hysupport : (y : transportedTorus Phi) ∈
      (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  · exact ⟨D.localPreimage i y hysupport hydisk,
      D.stage_localPreimage i y hysupport hydisk⟩
  · exact ⟨y, D.stage_fixed i y hysupport⟩

end SeparatedZeroWindingDiskSupports

end EmbeddedTorusIntersectionCircle

/-- Compose a list of endomorphisms, with the head acting last. -/
def composeStageList {X : Type*} (stage : ι → X → X) : List ι → X → X
  | [], x => x
  | i :: is, x => stage i (composeStageList stage is x)

/-- Compose a list of simultaneous deformations, again with the head acting last. -/
def composeDeformationList {X : Type*} (deformation : ι → Set.Icc (0 : ℝ) 1 → X → X)
    (u : Set.Icc (0 : ℝ) 1) : List ι → X → X
  | [], x => x
  | i :: is, x => deformation i u (composeDeformationList deformation u is x)

theorem continuous_composeStageList {X : Type*} [TopologicalSpace X]
    (stage : ι → X → X) (hstage : ∀ i, Continuous (stage i)) (is : List ι) :
    Continuous (composeStageList stage is) := by
  induction is with
  | nil => exact continuous_id
  | cons i is ih => exact (hstage i).comp ih

theorem continuous_uncurry_composeDeformationList
    {X : Type*} [TopologicalSpace X]
    (deformation : ι → Set.Icc (0 : ℝ) 1 → X → X)
    (hdeformation : ∀ i, Continuous (Function.uncurry (deformation i)))
    (is : List ι) :
    Continuous (Function.uncurry fun u ↦ composeDeformationList deformation u is) := by
  induction is with
  | nil => exact continuous_snd
  | cons i is ih =>
      exact (hdeformation i).comp (continuous_fst.prodMk ih)

theorem composeDeformationList_zero {X : Type*}
    (deformation : ι → Set.Icc (0 : ℝ) 1 → X → X)
    (hzero : ∀ i x, deformation i ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x)
    (is : List ι) (x : X) :
    composeDeformationList deformation ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ is x = x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [composeDeformationList, hzero, ih]

theorem composeDeformationList_one {X : Type*}
    (stage : ι → X → X) (deformation : ι → Set.Icc (0 : ℝ) 1 → X → X)
    (hone : ∀ i x, deformation i ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = stage i x)
    (is : List ι) (x : X) :
    composeDeformationList deformation ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ is x =
      composeStageList stage is x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [composeDeformationList, composeStageList, hone, ih]

theorem composeStageList_eq_self_of_forall_not_mem {X : Type*}
    (stage : ι → X → X) (support : ι → Set X)
    (hfixed : ∀ i x, x ∉ support i → stage i x = x)
    (is : List ι) (x : X) (hx : ∀ i ∈ is, x ∉ support i) :
    composeStageList stage is x = x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [composeStageList, ih (fun j hj ↦ hx j (List.mem_cons_of_mem i hj)),
        hfixed i x (hx i (List.mem_cons_self))]

theorem composeDeformationList_eq_self_of_forall_not_mem {X : Type*}
    (deformation : ι → Set.Icc (0 : ℝ) 1 → X → X) (support : ι → Set X)
    (hfixed : ∀ i u x, x ∉ support i → deformation i u x = x)
    (u : Set.Icc (0 : ℝ) 1) (is : List ι) (x : X)
    (hx : ∀ i ∈ is, x ∉ support i) :
    composeDeformationList deformation u is x = x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [composeDeformationList,
        ih (fun j hj ↦ hx j (List.mem_cons_of_mem i hj)),
        hfixed i u x (hx i List.mem_cons_self)]

/-- The points which avoid every member of a list of forbidden sets. -/
def listComplement {X : Type*} (removed : ι → Set X) (is : List ι) : Set X :=
  {x | ∀ i ∈ is, x ∉ removed i}

@[simp]
theorem mem_listComplement {X : Type*} (removed : ι → Set X)
    (is : List ι) (x : X) :
    x ∈ listComplement removed is ↔ ∀ i ∈ is, x ∉ removed i :=
  Iff.rfl

/-- Local replacements whose supports do not interact remove precisely the sets indexed by a
duplicate-free list.  This statement is the finite algebra behind the geometric construction:
the local Schoenflies map supplies `hown`, `hsurjective`, and `hother`, while this lemma handles
the order of composition. -/
theorem composeStageList_mem_listComplement {X : Type*}
    (stage : ι → X → X) (removed : ι → Set X)
    (hown : ∀ i x, stage i x ∉ removed i)
    (hother : ∀ {i j}, i ≠ j → ∀ x,
      stage i x ∉ removed j ↔ x ∉ removed j)
    (is : List ι) (his : is.Nodup) (x : X) :
    composeStageList stage is x ∈ listComplement removed is := by
  induction is with
  | nil => exact fun _ hi ↦ nomatch hi
  | cons i is ih =>
      rw [List.nodup_cons] at his
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hown i _
      · exact (hother (fun hij ↦ his.1 (hij ▸ hj)) _).2 (ih his.2 x j hj)

/-- Conversely, every point outside the listed removed sets has a preimage under the finite
composition.  Notice that no commutativity of the stages is assumed: preservation of all other
removed sets is exactly the hypothesis needed by the reverse induction. -/
theorem composeStageList_surjective_listComplement {X : Type*}
    (stage : ι → X → X) (removed : ι → Set X)
    (hsurjective : ∀ i y, y ∉ removed i → ∃ x, stage i x = y)
    (hother : ∀ {i j}, i ≠ j → ∀ x,
      stage i x ∉ removed j ↔ x ∉ removed j)
    (is : List ι) (his : is.Nodup) (y : X)
    (hy : y ∈ listComplement removed is) :
    ∃ x, composeStageList stage is x = y := by
  induction is with
  | nil => exact ⟨y, rfl⟩
  | cons i is ih =>
      rw [List.nodup_cons] at his
      obtain ⟨z, hz⟩ := hsurjective i y (hy i List.mem_cons_self)
      have hzremoved : z ∈ listComplement removed is := by
        intro j hj
        apply (hother (fun hij ↦ his.1 (hij ▸ hj)) z).1
        rw [hz]
        exact hy j (List.mem_cons_of_mem i hj)
      obtain ⟨x, hx⟩ := ih his.2 z hzremoved
      exact ⟨x, by rw [composeStageList, hx, hz]⟩

/-- The range of a duplicate-free finite composition is exactly the simultaneous complement of
the removed sets. -/
theorem range_composeStageList {X : Type*}
    (stage : ι → X → X) (removed : ι → Set X)
    (hown : ∀ i x, stage i x ∉ removed i)
    (hsurjective : ∀ i y, y ∉ removed i → ∃ x, stage i x = y)
    (hother : ∀ {i j}, i ≠ j → ∀ x,
      stage i x ∉ removed j ↔ x ∉ removed j)
    (is : List ι) (his : is.Nodup) :
    Set.range (composeStageList stage is) = listComplement removed is := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact composeStageList_mem_listComplement stage removed hown hother is his x
  · intro y hy
    exact composeStageList_surjective_listComplement stage removed
      hsurjective hother is his y hy

/-- Finite local puncture replacements on one fixed finite-point complement.

For separated Schoenflies supports, each local plane pushout descends to such an endomorphism:
outside its support it is the identity; inside, preservation of that support and disjointness from
the other supports show that no other center is hit. -/
structure FiniteSequentialPunctureStages [Fintype ι]
    (Phi : AmbientIsotopy) (centers : ι → Circle × Circle)
    (target : Set (transportedTorus Phi)) where
  support : ι → Set (transportedFinitePointComplement Phi centers)
  stage : ι → transportedFinitePointComplement Phi centers →
    transportedFinitePointComplement Phi centers
  continuous_stage : ∀ i, Continuous (stage i)
  stage_fixed : ∀ i x, x ∉ support i → stage i x = x
  deformation : ι → Set.Icc (0 : ℝ) 1 →
    transportedFinitePointComplement Phi centers →
      transportedFinitePointComplement Phi centers
  continuous_deformation : ∀ i, Continuous (Function.uncurry (deformation i))
  deformation_zero : ∀ i x,
    deformation i ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x
  deformation_one : ∀ i x,
    deformation i ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = stage i x
  deformation_fixed : ∀ i u x, x ∉ support i → deformation i u x = x
  terminal_mem : ∀ x,
    (composeStageList stage Finset.univ.toList x : transportedTorus Phi) ∈ target
  terminal_surjective : ∀ y : target, ∃ x,
    (composeStageList stage Finset.univ.toList x : transportedTorus Phi) = y

/-- Support-aware local disk replacements.  Unlike `FiniteSequentialPunctureStages`, this
structure has only one-disk hypotheses: the exact simultaneous range is proved below.  The
supports and removed disks live in the ambient transported torus so that localization lemmas can
be used without repeatedly changing between nested subtypes. -/
structure FiniteSupportedDiskReplacements [Fintype ι]
    (Phi : AmbientIsotopy) (centers : ι → Circle × Circle)
    (disk : ι → Set (transportedTorus Phi)) where
  support : ι → Set (transportedTorus Phi)
  pairwise_disjoint_support : Pairwise fun i j ↦ Disjoint (support i) (support j)
  disk_subset_support : ∀ i, disk i ⊆ support i
  center_mem_disk : ∀ i, transportedTorusHomeomorph Phi (centers i) ∈ disk i
  stage : ι → transportedFinitePointComplement Phi centers →
    transportedFinitePointComplement Phi centers
  continuous_stage : ∀ i, Continuous (stage i)
  stage_fixed : ∀ i x, (x : transportedTorus Phi) ∉ support i → stage i x = x
  stage_mem_support_iff : ∀ i x,
    (stage i x : transportedTorus Phi) ∈ support i ↔
      (x : transportedTorus Phi) ∈ support i
  stage_avoids_disk : ∀ i x, (stage i x : transportedTorus Phi) ∉ disk i
  stage_surjective_disk_complement : ∀ i y,
    (y : transportedTorus Phi) ∉ disk i → ∃ x, stage i x = y
  deformation : ι → Set.Icc (0 : ℝ) 1 →
    transportedFinitePointComplement Phi centers →
      transportedFinitePointComplement Phi centers
  continuous_deformation : ∀ i, Continuous (Function.uncurry (deformation i))
  deformation_zero : ∀ i x,
    deformation i ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x
  deformation_one : ∀ i x,
    deformation i ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = stage i x
  deformation_fixed : ∀ i u x,
    (x : transportedTorus Phi) ∉ support i → deformation i u x = x

namespace EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports

variable [Fintype ι]
  {C : ι → EmbeddedTorusIntersectionCircle Phi}
  {hzero : ∀ i, (C i).windingLoop.windingPair = (0, 0)}
  (D : EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports C hzero)

/-- Pairwise-separated lifted Schoenflies supports supply every local field required by the
finite exact-range theorem. -/
def toFiniteSupportedDiskReplacements :
    FiniteSupportedDiskReplacements Phi
      (EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskCenters C hzero)
      (fun i ↦ (C i).zeroWindingProjectedClosedJordanDisk (hzero i)) where
  support := fun i ↦ (C i).zeroWindingProjectedSupport (hzero i) (D.radius i)
  pairwise_disjoint_support := D.pairwise_disjoint_support
  disk_subset_support := D.disk_subset_support
  center_mem_disk := by
    intro i
    simpa only [EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskCenters,
      EmbeddedTorusIntersectionCircle.transported_zeroWindingDiskCenterCoordinates] using
        D.center_mem_disk i
  stage := D.stage
  continuous_stage := D.continuous_stage
  stage_fixed := D.stage_fixed
  stage_mem_support_iff := by
    intro i x
    rw [D.coe_stage]
    exact D.totalStageValue_mem_support_iff i x
  stage_avoids_disk := by
    intro i x
    rw [D.coe_stage]
    exact D.totalStageValue_not_mem_disk i x
  stage_surjective_disk_complement := D.stage_surjective_disk_complement
  deformation := D.deformation
  continuous_deformation := D.continuous_uncurry_deformation
  deformation_zero := D.deformation_zero
  deformation_one := D.deformation_one
  deformation_fixed := D.deformation_fixed

end EmbeddedTorusIntersectionCircle.SeparatedZeroWindingDiskSupports

namespace FiniteSupportedDiskReplacements

variable [Fintype ι] {disk : ι → Set (transportedTorus Phi)}
  (D : FiniteSupportedDiskReplacements Phi centers disk)

/-- A point in another removed disk is outside the support of the current stage. -/
theorem not_mem_support_of_mem_disk {i j : ι} (hij : i ≠ j)
    {x : transportedTorus Phi} (hx : x ∈ disk j) : x ∉ D.support i := by
  exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij))
    (D.disk_subset_support j hx)

/-- Every local stage fixes every point of every other removed disk. -/
theorem stage_eq_self_of_mem_other_disk {i j : ι} (hij : i ≠ j)
    (x : transportedFinitePointComplement Phi centers)
    (hx : (x : transportedTorus Phi) ∈ disk j) : D.stage i x = x :=
  D.stage_fixed i x (D.not_mem_support_of_mem_disk hij hx)

/-- The local replacement preserves membership in the complement of every other disk. -/
theorem stage_not_mem_other_disk_iff {i j : ι} (hij : i ≠ j)
    (x : transportedFinitePointComplement Phi centers) :
    (D.stage i x : transportedTorus Phi) ∉ disk j ↔
      (x : transportedTorus Phi) ∉ disk j := by
  by_cases hx : (x : transportedTorus Phi) ∈ D.support i
  · have hout : (D.stage i x : transportedTorus Phi) ∈ D.support i :=
      (D.stage_mem_support_iff i x).2 hx
    have hdisjoint := Set.disjoint_left.mp (D.pairwise_disjoint_support hij)
    constructor
    · intro _ hxdisk
      exact hdisjoint hx (D.disk_subset_support j hxdisk)
    · intro _ hstagedisk
      exact hdisjoint hout (D.disk_subset_support j hstagedisk)
  · rw [D.stage_fixed i x hx]

/-- Pairwise disjoint disk supports force the chosen puncture centers to be pairwise distinct. -/
theorem pairwise_ne_transported_centers : Pairwise fun i j ↦
    transportedTorusHomeomorph Phi (centers i) ≠
      transportedTorusHomeomorph Phi (centers j) := by
  intro i j hij hcenter
  have hi : transportedTorusHomeomorph Phi (centers i) ∈ D.support i :=
    D.disk_subset_support i (D.center_mem_disk i)
  have hj : transportedTorusHomeomorph Phi (centers j) ∈ D.support j :=
    D.disk_subset_support j (D.center_mem_disk j)
  exact (Set.disjoint_left.mp (D.pairwise_disjoint_support hij)) hi (hcenter.symm ▸ hj)

/-- Regard the `i`-th ambient disk as a forbidden set in the finite-point source. -/
def sourceDisk (i : ι) : Set (transportedFinitePointComplement Phi centers) :=
  Subtype.val ⁻¹' disk i

/-- The exact simultaneous closed-disk complement in the transported torus. -/
def diskComplement : Set (transportedTorus Phi) :=
  {x | ∀ i, x ∉ disk i}

/-- The one-disk axioms imply the complete finite sequential pushout contract. -/
def toFiniteSequentialPunctureStages :
    FiniteSequentialPunctureStages Phi centers D.diskComplement where
  support := fun i ↦ Subtype.val ⁻¹' D.support i
  stage := D.stage
  continuous_stage := D.continuous_stage
  stage_fixed := D.stage_fixed
  deformation := D.deformation
  continuous_deformation := D.continuous_deformation
  deformation_zero := D.deformation_zero
  deformation_one := D.deformation_one
  deformation_fixed := D.deformation_fixed
  terminal_mem := by
    intro x
    have hx := composeStageList_mem_listComplement D.stage D.sourceDisk
      D.stage_avoids_disk
      (fun hij x ↦ D.stage_not_mem_other_disk_iff hij x)
      Finset.univ.toList Finset.nodup_toList x
    exact fun i ↦ hx i (Finset.mem_toList.mpr (Finset.mem_univ i))
  terminal_surjective := by
    intro y
    let ysource : transportedFinitePointComplement Phi centers :=
      ⟨y, fun i hcenter ↦ y.2 i (hcenter.symm ▸ D.center_mem_disk i)⟩
    have hy : ysource ∈ listComplement D.sourceDisk Finset.univ.toList := by
      intro i _
      exact y.2 i
    obtain ⟨x, hx⟩ := composeStageList_surjective_listComplement
      D.stage D.sourceDisk D.stage_surjective_disk_complement
      (fun hij z ↦ D.stage_not_mem_other_disk_iff hij z)
      Finset.univ.toList Finset.nodup_toList ysource hy

end FiniteSupportedDiskReplacements

namespace FiniteSequentialPunctureStages

variable [Fintype ι]
  (D : FiniteSequentialPunctureStages Phi centers target)

/-- The final finite composition, with its transported-torus codomain exposed. -/
def push (x : transportedFinitePointComplement Phi centers) : transportedTorus Phi :=
  composeStageList D.stage Finset.univ.toList x

theorem continuous_push : Continuous D.push :=
  continuous_subtype_val.comp <|
    continuous_composeStageList D.stage D.continuous_stage Finset.univ.toList

/-- The simultaneous unit-interval deformation of the finite composition. -/
def unitIntervalDeformation (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi centers) : transportedTorus Phi :=
  composeDeformationList D.deformation u Finset.univ.toList x

theorem continuous_unitIntervalDeformation :
    Continuous (Function.uncurry D.unitIntervalDeformation) :=
  continuous_subtype_val.comp <|
    continuous_uncurry_composeDeformationList D.deformation
      D.continuous_deformation Finset.univ.toList

theorem unitIntervalDeformation_zero
    (x : transportedFinitePointComplement Phi centers) :
    D.unitIntervalDeformation ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x.1 := by
  exact congrArg Subtype.val <|
    composeDeformationList_zero D.deformation D.deformation_zero
      Finset.univ.toList x

theorem unitIntervalDeformation_one
    (x : transportedFinitePointComplement Phi centers) :
    D.unitIntervalDeformation ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = D.push x := by
  exact congrArg Subtype.val <|
    composeDeformationList_one D.stage D.deformation D.deformation_one
      Finset.univ.toList x

/-- The finite sequential construction supplies the exact downstream pushout contract. -/
def toFinitePuncturePushoutData : FinitePuncturePushoutData Phi centers target :=
  FinitePuncturePushoutData.ofUnitInterval D.push D.continuous_push D.terminal_mem
    D.unitIntervalDeformation D.continuous_unitIntervalDeformation
    D.unitIntervalDeformation_zero D.unitIntervalDeformation_one

/-- Points outside all selected supports are fixed by the final push. -/
theorem push_eq_self_of_forall_not_mem
    (x : transportedFinitePointComplement Phi centers)
    (hx : ∀ i, x ∉ D.support i) : D.push x = x.1 := by
  exact congrArg Subtype.val <|
    composeStageList_eq_self_of_forall_not_mem D.stage D.support D.stage_fixed
      Finset.univ.toList x fun i _ ↦ hx i

/-- The whole deformation is fixed outside all selected supports. -/
theorem unitIntervalDeformation_eq_self_of_forall_not_mem
    (u : Set.Icc (0 : ℝ) 1) (x : transportedFinitePointComplement Phi centers)
    (hx : ∀ i, x ∉ D.support i) : D.unitIntervalDeformation u x = x.1 := by
  exact congrArg Subtype.val <|
    composeDeformationList_eq_self_of_forall_not_mem D.deformation D.support
      D.deformation_fixed u Finset.univ.toList x fun i _ ↦ hx i

/-- The final map has exactly the prescribed finite disk complement as its range. -/
theorem range_push : Set.range D.push = target := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact D.terminal_mem x
  · intro y hy
    obtain ⟨x, hx⟩ := D.terminal_surjective ⟨y, hy⟩
    exact ⟨x, hx⟩

/-- Membership in the target is equivalent to having a preimage under the finite push. -/
theorem mem_target_iff_exists_preimage (y : transportedTorus Phi) :
    y ∈ target ↔ ∃ x, D.push x = y := by
  rw [← D.range_push]
  rfl

end FiniteSequentialPunctureStages

namespace FiniteSupportedDiskReplacements

variable [Fintype ι] {disk : ι → Set (transportedTorus Phi)}
  (D : FiniteSupportedDiskReplacements Phi centers disk)

/-- The finite push constructed from local replacements. -/
def push (x : transportedFinitePointComplement Phi centers) : transportedTorus Phi :=
  D.toFiniteSequentialPunctureStages.push x

/-- The finite push is fixed away from all selected support neighborhoods. -/
theorem push_eq_self_of_forall_not_mem
    (x : transportedFinitePointComplement Phi centers)
    (hx : ∀ i, (x : transportedTorus Phi) ∉ D.support i) :
    D.push x = x.1 :=
  D.toFiniteSequentialPunctureStages.push_eq_self_of_forall_not_mem x hx

/-- The whole finite deformation is fixed away from all selected support neighborhoods. -/
theorem unitIntervalDeformation_eq_self_of_forall_not_mem
    (u : Set.Icc (0 : ℝ) 1)
    (x : transportedFinitePointComplement Phi centers)
    (hx : ∀ i, (x : transportedTorus Phi) ∉ D.support i) :
    D.toFiniteSequentialPunctureStages.unitIntervalDeformation u x = x.1 :=
  D.toFiniteSequentialPunctureStages.unitIntervalDeformation_eq_self_of_forall_not_mem u x hx

/-- The exact range of the finite push is the complement of all selected closed disks. -/
theorem range_push : Set.range D.push = D.diskComplement :=
  D.toFiniteSequentialPunctureStages.range_push

/-- The finite disk complement is characterized by exact preimages under the push. -/
theorem mem_diskComplement_iff_exists_preimage (y : transportedTorus Phi) :
    y ∈ D.diskComplement ↔ ∃ x, D.push x = y :=
  D.toFiniteSequentialPunctureStages.mem_target_iff_exists_preimage y

end FiniteSupportedDiskReplacements

end Submission.Topology
