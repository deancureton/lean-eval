import Submission.Topology.CoherentThetaCanonicalCircles
import Submission.Topology.FourPortEndpointCollarPush

/-!
# Raw four-port circles as the cycles of a torus theta path system

This is the exact path-level attachment needed to invoke coherent lifting.  It identifies all
three raw circles with the three canonical two-edge cycles; zero winding then constructs the
coherent plane lifts without an additional lifting premise.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}
  {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

/-- Exact identification of the raw circles with all three cycles of a theta path system. -/
structure RawFourPortThetaPathPresentation (R : FourPortRawCircleData raw) where
  theta : TorusThetaPathSystem Phi
  index01 : Fin 3
  index02 : Fin 3
  index12 : Fin 3
  indices_exhaust : ∀ i, i = index01 ∨ i = index02 ∨ i = index12
  circle01_eq : ∀ z,
    (R.circle index01).circle z = (theta.referenceCycleMap 0 z : R3)
  circle02_eq : ∀ z,
    (R.circle index02).circle z = (theta.referenceCycleMap 1 z : R3)
  circle12_eq : ∀ z,
    (R.circle index12).circle z =
      ((TwoArcCircle.circleMap (theta.edge 1) (theta.edge 2).symm z :
        transportedTorus Phi) : R3)

namespace RawFourPortThetaPathPresentation

/-- The two reference raw circles provide the exact zero-winding theta data. -/
noncomputable def toZeroWindingThetaData
    (P : RawFourPortThetaPathPresentation R) : P.theta.ZeroWindingThetaData where
  circle := ![R.circle P.index01, R.circle P.index02]
  circle_eq := by
    intro j z
    fin_cases j
    · exact P.circle01_eq z
    · exact P.circle02_eq z
  zeroWinding := by
    intro j
    fin_cases j
    · exact R.zeroWinding P.index01
    · exact R.zeroWinding P.index02

/-- The path presentation canonically produces coherent plane lifts of all three edges. -/
noncomputable def coherentPlaneLiftData
    (P : RawFourPortThetaPathPresentation R) : P.theta.CoherentPlaneLiftData :=
  P.toZeroWindingThetaData.toCoherentPlaneLiftData

end RawFourPortThetaPathPresentation
end Submission.Topology
