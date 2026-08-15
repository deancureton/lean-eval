import Submission.DoubleBubbleSelection
import Submission.Topology.CountedCompression

/-!
# Excluding a charged compression by Pardon's `160D` count

The outer-box crossings are charged once and the cutting-plane crossings
twice.  This file realizes that bookkeeping as one finite disjoint-sum
finset and proves the numerical contradiction used in the double-bubble
step.
-/

open Set

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace DoubleBubbleSelection

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}

/-- A tagged finite set containing one copy of every outer-boundary crossing
and two copies of every cutting-plane crossing. -/
def countedEvents (S : DoubleBubbleSelection K frame c r) :
    Finset (Sum ℝ (Bool × ℝ)) :=
  S.outerFinite.toFinset.disjSum
    (Finset.univ.product S.cutFinite.toFinset)

@[simp]
theorem card_countedEvents (S : DoubleBubbleSelection K frame c r) :
    S.countedEvents.card = S.outerFinite.toFinset.card +
      2 * S.cutFinite.toFinset.card := by
  simp [countedEvents]

/-- An injective charging of every torus-knot/compression-boundary
intersection to the selected outer/cutting-plane events. -/
structure CompressionCharging {Phi : AmbientIsotopy}
    (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ) where
  encode : ℝ → Sum ℝ (Bool × ℝ)
  mem_counted : ∀ t ∈ torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve),
      encode t ∈ S.countedEvents
  injOn : Set.InjOn encode (torusLoopIntersectionParameters p q
    (transportedLoopCoordinates Phi D.boundaryLoop.curve))

/-- A certified essential compression cannot inject into the selected events
when their weighted count is strictly below `min p q`. -/
theorem no_compressionCharging_of_weightedCount_lt_min
    {Phi : AmbientIsotopy} (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding)
    (hsmall : (S.outerFinite.toFinset.card : ℝ) +
      2 * (S.cutFinite.toFinset.card : ℝ) < (min p q : ℝ)) :
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
  have hcardReal : (min p q : ℝ) ≤
      (S.outerFinite.toFinset.card : ℝ) +
        2 * (S.cutFinite.toFinset.card : ℝ) := by
    exact_mod_cast hcard
  exact (not_lt_of_ge hcardReal) hsmall

/-- Under the benchmark contradiction inequality, the coarea-selected event
set admits no certified compression charging. -/
theorem no_compressionCharging_of_distortion_lt
    {Phi : AmbientIsotopy} (S : DoubleBubbleSelection K frame c r)
    (D : GeneralCompressingDiskWitness Phi) (p q : ℕ)
    (C : TransverseIntersectionCertificate p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding
      D.boundaryLoop.lift.second.winding)
    (hcontra : 160 * (distortion K).toReal < (min p q : ℝ)) :
    ¬ Nonempty (CompressionCharging S D p q) :=
  S.no_compressionCharging_of_weightedCount_lt_min D p q C
    (S.weightedCount_lt_min p q hcontra)

end DoubleBubbleSelection

end

end Submission.PardonDistortion
