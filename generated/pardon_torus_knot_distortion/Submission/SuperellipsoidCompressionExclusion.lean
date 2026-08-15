import Submission.SuperellipsoidDoubleBubbleSelection
import Submission.Topology.CountedCompression

/-!
# Excluding a compression charged to smooth superellipsoid events

The outer superellipsoid contributes at most `76 D` knot events and the cutting disk contributes
at most `40 D`.  A sphere surgery may use two copies of the disk, so the complete tagged event
set has cardinality at most `156 D`, hence at most the benchmark allowance `160 D`.
-/

open Set

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology

noncomputable section

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- One copy of each outer event and two tagged copies of each cutting-disk event. -/
def countedEvents (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    Finset (Sum ℝ (Bool × ℝ)) :=
  S.outerEventSet_finite.toFinset.disjSum
    (Finset.univ.product S.cutEventSet_finite.toFinset)

@[simp]
theorem card_countedEvents
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) :
    S.countedEvents.card = S.outerEventSet_finite.toFinset.card +
      2 * S.cutEventSet_finite.toFinset.card := by
  simp [countedEvents]

/-- An injective assignment of every knot/compression-boundary intersection to a selected smooth
boundary event. -/
structure CompressionCharging
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) where
  encode : ℝ → Sum ℝ (Bool × ℝ)
  mem_counted : ∀ t ∈ torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve),
      encode t ∈ S.countedEvents
  injOn : Set.InjOn encode (torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve))

/-- A certified essential compression cannot inject into fewer than `min p q` events. -/
theorem no_compressionCharging_of_weightedCount_lt_min
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding D.boundaryLoop.lift.second.winding)
    (hsmall : (S.outerEventSet_finite.toFinset.card : ℝ) +
      2 * (S.cutEventSet_finite.toFinset.card : ℝ) <
        ((Nat.min p q : ℕ) : ℝ)) :
    ¬ Nonempty (CompressionCharging S D p q) := by
  rintro ⟨charge⟩
  have hcard : min p q ≤ S.countedEvents.card := by
    have h := D.min_le_ncard_of_injective_charging p q C
      (S.countedEvents : Set (Sum ℝ (Bool × ℝ)))
      S.countedEvents.finite_toSet charge.encode
      (by
        intro t ht
        simpa using charge.mem_counted t ht)
      charge.injOn
    simpa using h
  rw [card_countedEvents] at hcard
  have hcardReal : ((Nat.min p q : ℕ) : ℝ) ≤
      (S.outerEventSet_finite.toFinset.card : ℝ) +
        2 * (S.cutEventSet_finite.toFinset.card : ℝ) := by
    exact_mod_cast hcard
  exact (not_lt_of_ge hcardReal) hsmall

/-- The benchmark contrary inequality rules out every certified compression charging. -/
theorem no_compressionCharging_of_distortion_lt
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding D.boundaryLoop.lift.second.winding)
    (hcontra : 160 * (distortion K).toReal < ((Nat.min p q : ℕ) : ℝ)) :
    ¬ Nonempty (CompressionCharging S D p q) := by
  apply S.no_compressionCharging_of_weightedCount_lt_min D p q C
  exact lt_of_le_of_lt S.weightedEventCount_le_oneSixty hcontra

end SuperellipsoidDoubleBubbleSelection

/-- A particular compressing disk, its signed intersection certificate, and its injective charge
to the smooth outer/cut event set. -/
structure SuperellipsoidChargedCompression
    (p q : ℕ) {K : Knot} {Phi : AmbientIsotopy}
    {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W) where
  disk : GeneralCompressingDiskWitness Phi
  certificate : TransverseIntersectionCertificate p q
    (transportedLoopCoordinates Phi disk.boundaryLoop.curve)
    disk.boundaryLoop.lift.first.winding disk.boundaryLoop.lift.second.winding
  charging : Nonempty (S.CompressionCharging disk p q)

end

end Submission.PardonDistortion
