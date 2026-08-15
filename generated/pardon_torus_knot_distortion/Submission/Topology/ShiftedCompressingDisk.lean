import Submission.GeometricEventCharging
import Submission.Topology.ShiftedSL2ZCertificate

/-!
# Rotating a compressing disk with its phase-shifted boundary

Parameter translation of a disk boundary is realized by rotating the closed unit disk.  This
preserves the embedded image, interior disjointness, winding pair, and geometric event coverage.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-- Rotation of the closed complex unit disk through angle `s`. -/
def closedUnitDiskRotation (s : ℝ) : ClosedUnitDisk ≃ₜ ClosedUnitDisk where
  toFun z := ⟨(Circle.exp s : ℂ) * (z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Circle.norm_coe, one_mul]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  invFun z := ⟨(Circle.exp (-s) : ℂ) * (z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Circle.norm_coe, one_mul]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change (Circle.exp (-s) : ℂ) * ((Circle.exp s : ℂ) * (z : ℂ)) = z
    rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    simp
  right_inv z := by
    apply Subtype.ext
    change (Circle.exp s : ℂ) * ((Circle.exp (-s) : ℂ) * (z : ℂ)) = z
    rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    simp
  continuous_toFun := Continuous.subtype_mk
    (continuous_const.mul continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_const.mul continuous_subtype_val) _

theorem closedUnitDiskRotation_coe (s : ℝ) (z : ClosedUnitDisk) :
    ((closedUnitDiskRotation s z : ClosedUnitDisk) : ℂ) =
      (Circle.exp s : ℂ) * (z : ℂ) :=
  rfl

theorem norm_closedUnitDiskRotation (s : ℝ) (z : ClosedUnitDisk) :
    ‖((closedUnitDiskRotation s z : ClosedUnitDisk) : ℂ)‖ = ‖(z : ℂ)‖ := by
  rw [closedUnitDiskRotation_coe, norm_mul, Circle.norm_coe, one_mul]

theorem closedUnitDiskRotation_boundary (s t : ℝ) :
    closedUnitDiskRotation s (unitDiskBoundary t) = unitDiskBoundary (t + s) := by
  apply Subtype.ext
  change (Circle.exp s : ℂ) * unitCircleParam t = unitCircleParam (t + s)
  rw [← circle_exp_coe_eq_unitCircleParam, ← circle_exp_coe_eq_unitCircleParam,
    ← Circle.coe_mul, ← Circle.exp_add]
  congr 2
  ring

end Submission.PardonDistortion

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- Translate a winding-certified transported-torus loop. -/
def TransportedWindingLoop.shifted {Phi : AmbientIsotopy}
    {A : Set (transportedTorus Phi)} (B : TransportedWindingLoop Phi A) (s : ℝ) :
    TransportedWindingLoop Phi A where
  curve := shiftedLoop B.curve s
  continuous_curve := B.continuous_curve.comp (continuous_id.add continuous_const)
  periodic_curve t := by
    change B.curve (t + 2 * Real.pi + s) = B.curve (t + s)
    rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring]
    exact B.periodic_curve (t + s)
  curve_mem t := B.curve_mem (t + s)
  lift := B.lift.shifted s

@[simp] theorem TransportedWindingLoop.shifted_windingPair
    {Phi : AmbientIsotopy} {A : Set (transportedTorus Phi)}
    (B : TransportedWindingLoop Phi A) (s : ℝ) :
    (B.shifted s).windingPair = B.windingPair :=
  rfl

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-- Rotate a compressing disk so that its boundary parametrization is translated by `s`. -/
def GeneralCompressingDiskWitness.shifted {Phi : AmbientIsotopy}
    (D : GeneralCompressingDiskWitness Phi) (s : ℝ) :
    GeneralCompressingDiskWitness Phi where
  boundaryLoop := D.boundaryLoop.shifted s
  disk := D.disk ∘ closedUnitDiskRotation s
  isEmbedding := D.isEmbedding.comp (closedUnitDiskRotation s).isEmbedding
  boundary t := by
    change D.disk (closedUnitDiskRotation s (unitDiskBoundary t)) =
      D.boundaryLoop.curve (t + s)
    rw [closedUnitDiskRotation_boundary, D.boundary]
  interior_disjoint z hz := by
    apply D.interior_disjoint (closedUnitDiskRotation s z)
    rwa [norm_closedUnitDiskRotation]
  essential := by
    simpa only [TransportedWindingLoop.shifted_windingPair] using D.essential

/-- Translation does not change the range of a real-parametrized loop. -/
theorem range_shiftedLoop {X : Type*} (gamma : ℝ → X) (s : ℝ) :
    Set.range (shiftedLoop gamma s) = Set.range gamma := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + s, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - s, ?_⟩
    simp only [shiftedLoop, sub_add_cancel]

theorem torusLoopIntersectionParameters_shifted
    (p q : ℕ) (gamma : ℝ → Circle × Circle) (s : ℝ) :
    torusLoopIntersectionParameters p q (shiftedLoop gamma s) =
      torusLoopIntersectionParameters p q gamma := by
  ext t
  simp only [torusLoopIntersectionParameters, Set.mem_ofPred_eq, range_shiftedLoop]

namespace DoubleBubbleSelection

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
  {Phi : AmbientIsotopy}

/-- Geometric event coverage is unchanged by rotating the disk boundary parametrization. -/
def CompressionBoundaryEventCover.shifted
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (G : CompressionBoundaryEventCover S D p q) (s : ℝ) :
    CompressionBoundaryEventCover S (D.shifted s) p q where
  tag := G.tag
  point_mem_event t ht := by
    apply G.point_mem_event t
    change t ∈ torusLoopIntersectionParameters p q
      (shiftedLoop (transportedLoopCoordinates Phi D.boundaryLoop.curve) s) at ht
    rw [← torusLoopIntersectionParameters_shifted p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve) s]
    exact ht

/-- Exact downstream package: a shifted direct certificate and the unchanged geometric event
cover instantiate `ChargedCompression` for the rotated compressing disk. -/
def CompressionBoundaryEventCover.toShiftedChargedCompression
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q)
    (s : ℝ)
    (C : TransverseIntersectionCertificate p q
      (shiftedLoop (transportedLoopCoordinates Phi D.boundaryLoop.curve) s)
      D.boundaryLoop.lift.first.winding D.boundaryLoop.lift.second.winding) :
    ChargedCompression (Phi := Phi) p q S :=
  (G.shifted S D p q s).toChargedCompression S (D.shifted s) p q hc sigma hclass
    C

/-- Seam-free one-call bridge from raw smooth transverse boundary data and geometric event
coverage to the charged-compression package.  The phase used to rotate the disk is the canonical
non-root phase of the transformed slope coordinate. -/
noncomputable def CompressionBoundaryEventCover.toCanonicallyShiftedChargedCompressionOfRawRegular
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S D p q)
    (hfirst : ContDiff ℝ 1 D.boundaryLoop.lift.first.angle)
    (hsecond : ContDiff ℝ 1 D.boundaryLoop.lift.second.angle)
    (hregular : ∀ t,
      Circle.exp (transformedSlopeAngle p q D.boundaryLoop.lift t) = 1 →
        deriv (transformedSlopeAngle p q D.boundaryLoop.lift) t ≠ 0)
    (hinjective : Set.InjOn
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      (Ico (0 : ℝ) (2 * Real.pi))) :
    ChargedCompression (Phi := Phi) p q S := by
  let H := transformedRegularPeriodicCircleLift p q D.boundaryLoop.lift
    hfirst hsecond hregular
  exact G.toShiftedChargedCompression S D p q hc sigma hclass H.nonrootPhase
    (shiftedTransverseIntersectionCertificateOfRawRegular p q hc
      D.boundaryLoop.lift hfirst hsecond hregular hinjective)

end DoubleBubbleSelection

end Submission.PardonDistortion
