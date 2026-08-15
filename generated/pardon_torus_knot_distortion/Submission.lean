import ChallengeDeps
import Submission.Helpers
import Submission.ArcLength
import Submission.ArcMeasure
import Submission.ArcCoordinate
import Submission.BoxGeometry
import Submission.Coarea.BoxShell
import Submission.Coarea.FiniteBranches
import Submission.Coarea.General
import Submission.Coarea.PlaneSlice
import Submission.Distortion
import Submission.LocalArc
import Submission.NestedCarrier
import Submission.OrientedBox
import Submission.PardonReduction
import Submission.Shrinking
import Submission.Topology.CircleDegree
import Submission.Topology.Carrier
import Submission.Topology.DiskWinding
import Submission.Topology.LocalFlatness
import Submission.Topology.Representativity
import Submission.Topology.SolidTorus
import Submission.Torus.AmbientTransfer
import Submission.Torus.Standard

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

theorem pardon_torus_knot_distortion (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot)
    (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  sorry

end Submission
