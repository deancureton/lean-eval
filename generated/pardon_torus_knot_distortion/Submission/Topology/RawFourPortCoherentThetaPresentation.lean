import Submission.Topology.CoherentThetaTopologicalPresentation
import Submission.Topology.RawFourPortProjectedFaceDiskSide

/-!
# Raw four-port circles aligned with a coherent lifted theta graph

The three coherent two-edge cycles may differ from the canonical zero-winding plane circles by
independent deck translations.  Exact translated-carrier identities are enough to construct the
projection-invariant topological theta presentation used by the disk-side argument.
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
  {T : TorusThetaPathSystem Phi}
  {L : T.CoherentPlaneLiftData}

/-- Alignment of the three coherent plane cycles with the three raw zero-winding cycles. -/
structure RawFourPortCoherentThetaAlignmentData
    (D : L.JordanLocalStraighteningData)
    (R : FourPortRawCircleData raw) where
  index01 : Fin 3
  index02 : Fin 3
  index12 : Fin 3
  indices_exhaust : ∀ i, i = index01 ∨ i = index02 ∨ i = index12
  shift01 : Fin 2 → ℤ
  shift02 : Fin 2 → ℤ
  shift12 : Fin 2 → ℤ
  carrier01 : D.circle01.carrier =
    (((R.circle index01).zeroWindingJordanCircle
      (R.zeroWinding index01)).translate
        (EmbeddedTorusIntersectionCircle.torusLatticeVector shift01)).carrier
  carrier02 : D.circle02.carrier =
    (((R.circle index02).zeroWindingJordanCircle
      (R.zeroWinding index02)).translate
        (EmbeddedTorusIntersectionCircle.torusLatticeVector shift02)).carrier
  carrier12 : D.circle12.carrier =
    (((R.circle index12).zeroWindingJordanCircle
      (R.zeroWinding index12)).translate
        (EmbeddedTorusIntersectionCircle.torusLatticeVector shift12)).carrier

namespace RawFourPortCoherentThetaAlignmentData

private theorem projection_eq_rawDisk
    (C : Schoenflies.JordanCircle)
    (rawCircle : EmbeddedTorusIntersectionCircle Phi)
    (hzero : rawCircle.windingLoop.windingPair = (0, 0))
    (shift : Fin 2 → ℤ)
    (hcarrier : C.carrier =
      ((rawCircle.zeroWindingJordanCircle hzero).translate
        (EmbeddedTorusIntersectionCircle.torusLatticeVector shift)).carrier) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi ''
        closure C.inside =
      rawCircle.zeroWindingProjectedClosedJordanDisk hzero := by
  rw [projected_closure_inside_eq_of_carrier_eq_translate C
    (rawCircle.zeroWindingJordanCircle hzero)
    (EmbeddedTorusIntersectionCircle.torusLatticeVector shift) hcarrier
    (fun x ↦ EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus_add_lattice
      x shift)]
  rfl

/-- Translated carrier alignment gives the projection-invariant topological presentation. -/
noncomputable def toProjectedTopologicalThetaPresentation
    {D : L.JordanLocalStraighteningData}
    (A : RawFourPortCoherentThetaAlignmentData D R) :
    RawFourPortProjectedTopologicalThetaPresentation R where
  theta := D.toTopologicalPlanarJordanThetaData
  index01 := A.index01
  index02 := A.index02
  index12 := A.index12
  indices_exhaust := A.indices_exhaust
  projection01 := projection_eq_rawDisk D.circle01
    (R.circle A.index01) (R.zeroWinding A.index01) A.shift01 A.carrier01
  projection02 := projection_eq_rawDisk D.circle02
    (R.circle A.index02) (R.zeroWinding A.index02) A.shift02 A.carrier02
  projection12 := projection_eq_rawDisk D.circle12
    (R.circle A.index12) (R.zeroWinding A.index12) A.shift12 A.carrier12

end RawFourPortCoherentThetaAlignmentData
end Submission.Topology
