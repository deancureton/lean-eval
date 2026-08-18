import Submission.Topology.FinitePlanarPunctureConnectivity
import Submission.Topology.TorusDiskPuncture

/-!
# Pushing a planar puncture onto a Jordan disk

Schoenflies coordinates carry a planar Jordan disk to the closed unit ball.  Conjugating the
fixed-tail radial puncture map by those coordinates gives a homeomorphism from the complement
of one distinguished interior point to the complement of the whole closed Jordan disk.
-/

open Metric Set Topology

noncomputable section

namespace Schoenflies.JordanCircle

open JordanCurve.Arcs Submission.Topology

/-- The canonical ambient Schoenflies homeomorphism used by the planar disk pushout. -/
def diskPushAmbientHomeomorph (J : JordanCircle) : Plane ≃ₜ Plane :=
  J.regionalExtensionData.diskExtensionData.ambientHomeomorph

/-- The closed Jordan disk removed by the planar pushout. -/
def diskPushClosedDisk (J : JordanCircle) : Set Plane :=
  closure J.inside

/-- The distinguished puncture corresponding to the origin in Schoenflies coordinates. -/
def diskPushCenter (J : JordanCircle) : Plane :=
  J.diskPushAmbientHomeomorph.symm 0

/-- The source of the one-disk planar pushout. -/
def diskPushPuncture (J : JordanCircle) : Set Plane :=
  {J.diskPushCenter}ᶜ

/-- The target of the one-disk planar pushout. -/
def diskPushComplement (J : JordanCircle) : Set Plane :=
  (J.diskPushClosedDisk)ᶜ

/-- A closed fixed-tail support for the planar radial pushout. -/
def diskPushSupport (J : JordanCircle) (R : ℝ) : Set Plane :=
  J.diskPushAmbientHomeomorph.symm '' closedBall (0 : Plane) R

/-- Membership in a radial support can be checked in Schoenflies coordinates. -/
theorem mem_diskPushSupport_iff (J : JordanCircle) (R : ℝ) (x : Plane) :
    x ∈ J.diskPushSupport R ↔
      J.diskPushAmbientHomeomorph x ∈ closedBall (0 : Plane) R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [Homeomorph.apply_symm_apply] using hy
  · intro hx
    exact ⟨J.diskPushAmbientHomeomorph x, hx,
      J.diskPushAmbientHomeomorph.symm_apply_apply x⟩

/-- Schoenflies coordinates carry the closed Jordan disk exactly onto the closed unit ball. -/
theorem diskPushAmbientHomeomorph_image_closedDisk (J : JordanCircle) :
    J.diskPushAmbientHomeomorph '' J.diskPushClosedDisk = closedBall (0 : Plane) 1 := by
  let E := J.regionalExtensionData
  let D := E.diskExtensionData
  change D.ambientHomeomorph '' closure J.inside = _
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    change D.toFun x ∈ closedBall (0 : Plane) 1
    simpa only [Schoenflies.DiskExtensionData.toFun, hx, Set.piecewise, if_true] using
      D.maps_inside hx
  · intro y hy
    refine ⟨D.ambientHomeomorph.symm y, ?_, D.ambientHomeomorph.apply_symm_apply y⟩
    change D.invFun y ∈ closure J.inside
    simpa only [Schoenflies.DiskExtensionData.invFun, hy, Set.piecewise, if_true] using
      D.inv_maps_inside hy

theorem diskPushAmbientHomeomorph_mem_closedBall_iff
    (J : JordanCircle) (x : Plane) :
    J.diskPushAmbientHomeomorph x ∈ closedBall (0 : Plane) 1 ↔
      x ∈ J.diskPushClosedDisk := by
  constructor
  · intro hx
    rw [← J.diskPushAmbientHomeomorph_image_closedDisk] at hx
    obtain ⟨y, hy, hey⟩ := hx
    exact (J.diskPushAmbientHomeomorph.injective hey).symm ▸ hy
  · intro hx
    rw [← J.diskPushAmbientHomeomorph_image_closedDisk]
    exact ⟨x, hx, rfl⟩

/-- The distinguished puncture lies in the closed Jordan disk. -/
theorem diskPushCenter_mem_closedDisk (J : JordanCircle) :
    J.diskPushCenter ∈ J.diskPushClosedDisk := by
  rw [← J.diskPushAmbientHomeomorph_mem_closedBall_iff]
  simp only [diskPushCenter, Homeomorph.apply_symm_apply, mem_closedBall, dist_self]
  norm_num

/-- Schoenflies coordinates identify the distinguished puncture with the origin puncture. -/
def diskPushPunctureToOrigin (J : JordanCircle) :
    J.diskPushPuncture ≃ₜ ({0}ᶜ : Set Plane) :=
  J.diskPushAmbientHomeomorph.subtype fun x ↦ by
    change x ≠ J.diskPushAmbientHomeomorph.symm 0 ↔
      J.diskPushAmbientHomeomorph x ≠ 0
    constructor
    · intro hx heq
      apply hx
      apply J.diskPushAmbientHomeomorph.injective
      simpa only [Homeomorph.apply_symm_apply] using heq
    · intro hx heq
      apply hx
      simp only [heq, Homeomorph.apply_symm_apply]

/-- The one-disk planar radial pushout. -/
def punctureToDiskComplement
    (J : JordanCircle) (R : ℝ) (hR : 1 < R) :
    J.diskPushPuncture ≃ₜ J.diskPushComplement := by
  let e := J.diskPushAmbientHomeomorph
  let exteriorToTarget : ((closedBall (0 : Plane) 1)ᶜ : Set Plane) ≃ₜ
      J.diskPushComplement :=
    e.symm.subtype fun y ↦ by
      change y ∉ closedBall (0 : Plane) 1 ↔
        e.symm y ∉ J.diskPushClosedDisk
      have hmem := not_congr (J.diskPushAmbientHomeomorph_mem_closedBall_iff (e.symm y))
      simpa only [e, Homeomorph.apply_symm_apply] using hmem
  exact J.diskPushPunctureToOrigin.trans <|
    (RadialPuncture.planePunctureToExterior R hR).trans exteriorToTarget

theorem diskPushAmbientHomeomorph_punctureToDiskComplement
    (J : JordanCircle) (R : ℝ) (hR : 1 < R)
    (x : J.diskPushPuncture) :
    J.diskPushAmbientHomeomorph (J.punctureToDiskComplement R hR x) =
      RadialPuncture.planePunctureToExterior R hR
        ⟨J.diskPushAmbientHomeomorph x, by
          intro hx
          apply x.2
          apply J.diskPushAmbientHomeomorph.injective
          simpa only [mem_singleton_iff, diskPushCenter,
            Homeomorph.apply_symm_apply] using hx⟩ := by
  simp only [punctureToDiskComplement, diskPushPunctureToOrigin, Homeomorph.trans_apply]
  change J.diskPushAmbientHomeomorph (J.diskPushAmbientHomeomorph.symm _) = _
  rw [J.diskPushAmbientHomeomorph.apply_symm_apply]
  rfl

/-- The one-disk pushout preserves membership in its chosen closed radial support. -/
theorem punctureToDiskComplement_mem_support_iff
    (J : JordanCircle) (R : ℝ) (hR : 1 < R)
    (x : J.diskPushPuncture) :
    (J.punctureToDiskComplement R hR x : Plane) ∈ J.diskPushSupport R ↔
      (x : Plane) ∈ J.diskPushSupport R := by
  rw [J.mem_diskPushSupport_iff, J.diskPushAmbientHomeomorph_punctureToDiskComplement,
    RadialPuncture.planePunctureToExterior_mem_closedBall_iff,
    ← J.mem_diskPushSupport_iff]

/-- The planar pushout is fixed outside its chosen closed radial support. -/
theorem punctureToDiskComplement_apply_of_not_mem_support
    (J : JordanCircle) (R : ℝ) (hR : 1 < R)
    (x : J.diskPushPuncture) (hx : (x : Plane) ∉ J.diskPushSupport R) :
    (J.punctureToDiskComplement R hR x : Plane) = x := by
  have hxR : R < ‖J.diskPushAmbientHomeomorph x‖ := by
    change (x : Plane) ∉
      J.diskPushAmbientHomeomorph.symm '' closedBall (0 : Plane) R at hx
    have hnot : J.diskPushAmbientHomeomorph x ∉ closedBall (0 : Plane) R := by
      intro hball
      apply hx
      exact ⟨J.diskPushAmbientHomeomorph x, hball,
        J.diskPushAmbientHomeomorph.symm_apply_apply x⟩
    simpa only [mem_closedBall, dist_zero_right, not_le] using hnot
  apply J.diskPushAmbientHomeomorph.injective
  rw [J.diskPushAmbientHomeomorph_punctureToDiskComplement R hR]
  exact RadialPuncture.planePunctureToExterior_apply_of_le R hR _ hxR.le

/-- The inverse one-disk pushout is also fixed outside the chosen support. -/
theorem punctureToDiskComplement_symm_apply_of_not_mem_support
    (J : JordanCircle) (R : ℝ) (hR : 1 < R)
    (y : J.diskPushComplement) (hy : (y : Plane) ∉ J.diskPushSupport R) :
    (J.punctureToDiskComplement R hR).symm y =
      ⟨y, fun hcenter ↦ y.2 (hcenter.symm ▸ J.diskPushCenter_mem_closedDisk)⟩ := by
  let yp : J.diskPushPuncture :=
    ⟨y, fun hcenter ↦ y.2 (hcenter.symm ▸ J.diskPushCenter_mem_closedDisk)⟩
  apply (J.punctureToDiskComplement R hR).injective
  rw [(J.punctureToDiskComplement R hR).apply_symm_apply]
  apply Subtype.ext
  exact (J.punctureToDiskComplement_apply_of_not_mem_support R hR yp hy).symm

end Schoenflies.JordanCircle
