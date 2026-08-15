import ChallengeDeps
import Submission.Helpers
import Submission.ArcLength
import Submission.ArcMeasure
import Submission.ArcCoordinate
import Submission.BoxGeometry
import Submission.CapstoneReduction
import Submission.Coarea.BoxShell
import Submission.Coarea.BoundarySelection
import Submission.Coarea.FiniteBranches
import Submission.Coarea.FacewiseRegularOuterBoundarySelection
import Submission.Coarea.General
import Submission.Coarea.Lipschitz
import Submission.Coarea.OrientedShell
import Submission.Coarea.OrientedBoundarySelection
import Submission.Coarea.PlaneSlice
import Submission.Coarea.SmoothCarrierPlaneSelection
import Submission.CompressionExclusion
import Submission.Distortion
import Submission.DoubleBubbleSelection
import Submission.GeometricEventCharging
import Submission.LocalArc
import Submission.LoopNested
import Submission.NestedCarrier
import Submission.OrientedBox
import Submission.PardonReduction
import Submission.PardonGeometricStep
import Submission.ReparamCharging
import Submission.RegularDoubleBubbleSelection
import Submission.Shrinking
import Submission.SardMoreira
import Submission.Topology.CircleDegree
import Submission.Topology.CircleIntersectionLocalIFT
import Submission.Topology.CountedCompression
import Submission.Topology.Carrier
import Submission.Topology.ArcReplacementConstruction
import Submission.Topology.AffineCircleEndpointBridge
import Submission.Topology.CircleIntersectionCovering
import Submission.Topology.DiskWinding
import Submission.Topology.DoubleBubble
import Submission.Topology.GeneralCompression
import Submission.Topology.HalfspaceCut
import Submission.Topology.IntersectionCertificate
import Submission.Topology.LocalFlatness
import Submission.Topology.LoopCarrier
import Submission.Topology.LoopHalfspaceCut
import Submission.Topology.PlaneSliceComponents
import Submission.Topology.CyclicOrderConstruction
import Submission.Topology.CrossingSignFlip
import Submission.Topology.SortedCrossingConstruction
import Submission.Topology.Representativity
import Submission.Topology.SolidTorus
import Submission.Topology.SlopeNormalization
import Submission.Topology.SurfaceRegularValue
import Submission.Topology.RegularLevelComponents
import Submission.Topology.SmoothWindingApproximation
import Submission.Topology.FourierSmoothApproximation
import Submission.Topology.SmoothLoopCarrier
import Submission.Topology.TransportedTorusRegularLevels
import Submission.Topology.TransverseContinuation
import Submission.Topology.TransverseBranchIFT
import Submission.Topology.WindingSafeSplice
import Submission.Topology.WindingDecompositionCut
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
