import Submission.SuperellipsoidCompressionExclusion
import Submission.Topology.SuperellipsoidSmoothedChargingTransport

/-!
# Excluding charged coordinate-axis loops

The quantitative part of Pardon's argument only counts intersections of a loop on the
transported torus with the torus knot.  Once one winding coordinate vanishes and the other does
not, the required lower bound follows without retaining a compressing disk.  This module isolates
that stronger interface.

The missing topology in a sphere-surgery application is correspondingly reduced to finding one
nonzero coordinate-axis circle among the finite essential intersection circles.  No disk-surgery
contract is used by the counting argument below.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology Submission.Torus

/-- A nonzero slope supported on one coordinate axis. -/
def IsNonzeroAxisSlope (m n : ℤ) : Prop :=
  (m = 0 ∨ n = 0) ∧ (m, n) ≠ (0, 0)

/-- A nonzero coordinate-axis slope has at least `min p q` intersections with the `(p,q)`
slope.  Primitivity is unnecessary for this lower bound. -/
theorem min_le_slopeIntersectionNumber_of_nonzeroAxis
    (p q : ℕ) (m n : ℤ) (haxis : IsNonzeroAxisSlope m n) :
    min p q ≤ slopeIntersectionNumber p q m n := by
  rcases haxis.1 with hm | hn
  · have hn0 : n ≠ 0 := by
      intro hn
      exact haxis.2 (Prod.ext hm hn)
    rw [slopeIntersectionNumber, slopeIntersectionDet, hm]
    simp only [Int.mul_zero, sub_zero, Int.natAbs_mul, Int.natAbs_natCast]
    exact (min_le_left p q).trans
      (Nat.le_mul_of_pos_right p (Int.natAbs_pos.mpr hn0))
  · have hm0 : m ≠ 0 := by
      intro hm
      exact haxis.2 (Prod.ext hm hn)
    rw [slopeIntersectionNumber, slopeIntersectionDet, hn]
    simp only [Int.mul_zero, zero_sub, Int.natAbs_neg, Int.natAbs_mul,
      Int.natAbs_natCast]
    exact (min_le_right p q).trans
      (Nat.le_mul_of_pos_right q (Int.natAbs_pos.mpr hm0))

/-- A transverse certificate for a nonzero axis loop has at least `min p q` parameters. -/
theorem min_le_intersection_ncard_of_nonzeroAxis
    (p q : ℕ) (gamma : ℝ → Circle × Circle) (m n : ℤ)
    (haxis : IsNonzeroAxisSlope m n)
    (C : TransverseIntersectionCertificate p q gamma m n) :
    min p q ≤ (torusLoopIntersectionParameters p q gamma).ncard :=
  (min_le_slopeIntersectionNumber_of_nonzeroAxis p q m n haxis).trans
    (slopeIntersectionNumber_le_ncard_of_transverseCertificate p q gamma m n C)

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- A transverse, charged torus loop whose winding lies on a nonzero coordinate axis. -/
structure ChargedAxisLoop
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) where
  loop : ℝ → Circle × Circle
  firstWinding : ℤ
  secondWinding : ℤ
  axis : IsNonzeroAxisSlope firstWinding secondWinding
  certificate : TransverseIntersectionCertificate p q loop firstWinding secondWinding
  charging : LoopCharging S p q loop

namespace ChargedAxisLoop

variable {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  {p q : ℕ}

/-- Injective charging of an axis loop forces at least `min p q` counted events. -/
theorem min_le_card_countedEvents (A : ChargedAxisLoop S p q) :
    min p q ≤ S.countedEvents.card := by
  have hparameters : min p q ≤
      (torusLoopIntersectionParameters p q A.loop).ncard :=
    min_le_intersection_ncard_of_nonzeroAxis p q A.loop
      A.firstWinding A.secondWinding A.axis A.certificate
  have hcount := Set.ncard_le_ncard_of_injOn A.charging.encode
    (fun _ ht ↦ by simpa using A.charging.mem_counted _ ht)
    A.charging.injOn S.countedEvents.finite_toSet
  exact hparameters.trans (by simpa using hcount)

end ChargedAxisLoop

/-- The benchmark contrary inequality rules out every charged nonzero axis loop. -/
theorem no_chargedAxisLoop_of_distortion_lt
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ)
    (hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    ¬ Nonempty (ChargedAxisLoop S p q) := by
  rintro ⟨A⟩
  have hcardNat := A.min_le_card_countedEvents
  rw [S.card_countedEvents] at hcardNat
  have hcard : ((Nat.min p q : ℕ) : ℝ) ≤
      (S.outerEventSet_finite.toFinset.card : ℝ) +
        2 * (S.cutEventSet_finite.toFinset.card : ℝ) := by
    exact_mod_cast hcardNat
  exact (not_lt_of_ge hcard) <|
    lt_of_le_of_lt S.weightedEventCount_le_oneSixty hcontra

end SuperellipsoidDoubleBubbleSelection
end Submission.PardonDistortion
