import Submission.Topology.RawFourPortCoherentThetaPresentation
import Submission.Topology.RawFourPortThetaPathPresentation
import Submission.Topology.TorusPlaneCircleLiftAlignment

/-!
# Automatic deck alignment of raw four-port theta cycles

An exact torus theta path presentation and zero winding determine coherent plane lifts.  Covering
uniqueness then aligns each canonical coherent Jordan circle with the corresponding raw canonical
plane circle by one deck translation.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

private theorem carrier_zeroWindingJordanCircle_eq_range
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    (C.zeroWindingJordanCircle hzero).carrier =
      Set.range (C.zeroWindingPlaneCircle hzero) := by
  change Set.range
      (C.zeroWindingPlaneCircle hzero ∘
        JordanCurve.Arcs.spherePlaneHomeoCircle) = _
  rw [Set.range_comp,
    JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq, Set.image_univ]

private theorem exists_jordanCarrier_eq_translate
    (K J : Schoenflies.JordanCircle)
    (p q : Circle → TorusCoveringPlane)
    (hK : K.carrier = Set.range p)
    (hJ : J.carrier = Set.range q)
    (hp : Continuous p) (hq : Continuous q)
    (hprojection : ∀ z,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p z) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q z)) :
    ∃ k : Fin 2 → ℤ,
      K.carrier =
        (J.translate (EmbeddedTorusIntersectionCircle.torusLatticeVector k)).carrier := by
  obtain ⟨k, hk⟩ := exists_planeCircleLift_eq_add_lattice p q hp hq hprojection
  refine ⟨k, ?_⟩
  rw [hK, Schoenflies.JordanCircle.carrier_translate, hJ]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨q z, ⟨z, rfl⟩, (hk z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, hk z⟩

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}
  {R : FourPortRawCircleData raw}

namespace RawFourPortThetaPathPresentation

variable (P : RawFourPortThetaPathPresentation R)

private theorem projection_circle01 (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (TwoArcCircle.circleMap
          (P.coherentPlaneLiftData.edgeLift 0)
          (P.coherentPlaneLiftData.edgeLift 1).symm z) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        ((R.circle P.index01).zeroWindingPlaneCircle
          (R.zeroWinding P.index01) z) := by
  apply Subtype.ext
  calc
    _ = ((P.theta.referenceCycleMap 0 z : transportedTorus Phi) : R3) :=
      congrArg Subtype.val (P.coherentPlaneLiftData.projection_circleMap_edges 0 1 z)
    _ = (R.circle P.index01).circle z := (P.circle01_eq z).symm
    _ = EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        ((R.circle P.index01).zeroWindingPlaneCircle
          (R.zeroWinding P.index01) z) :=
      ((R.circle P.index01).torusCoveringProjection_zeroWindingPlaneCircle
        (R.zeroWinding P.index01) z).symm

private theorem projection_circle02 (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (TwoArcCircle.circleMap
          (P.coherentPlaneLiftData.edgeLift 0)
          (P.coherentPlaneLiftData.edgeLift 2).symm z) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        ((R.circle P.index02).zeroWindingPlaneCircle
          (R.zeroWinding P.index02) z) := by
  apply Subtype.ext
  calc
    _ = ((P.theta.referenceCycleMap 1 z : transportedTorus Phi) : R3) :=
      congrArg Subtype.val (P.coherentPlaneLiftData.projection_circleMap_edges 0 2 z)
    _ = (R.circle P.index02).circle z := (P.circle02_eq z).symm
    _ = EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        ((R.circle P.index02).zeroWindingPlaneCircle
          (R.zeroWinding P.index02) z) :=
      ((R.circle P.index02).torusCoveringProjection_zeroWindingPlaneCircle
        (R.zeroWinding P.index02) z).symm

private theorem projection_circle12 (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (TwoArcCircle.circleMap
          (P.coherentPlaneLiftData.edgeLift 1)
          (P.coherentPlaneLiftData.edgeLift 2).symm z) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        ((R.circle P.index12).zeroWindingPlaneCircle
          (R.zeroWinding P.index12) z) := by
  apply Subtype.ext
  calc
    _ = ((TwoArcCircle.circleMap (P.theta.edge 1) (P.theta.edge 2).symm z :
        transportedTorus Phi) : R3) :=
      congrArg Subtype.val (P.coherentPlaneLiftData.projection_circleMap_edges 1 2 z)
    _ = (R.circle P.index12).circle z := (P.circle12_eq z).symm
    _ = EmbeddedTorusIntersectionCircle.torusCoveringProjection Phi
        ((R.circle P.index12).zeroWindingPlaneCircle
          (R.zeroWinding P.index12) z) :=
      ((R.circle P.index12).torusCoveringProjection_zeroWindingPlaneCircle
        (R.zeroWinding P.index12) z).symm

private theorem exists_circle01_alignment :
    ∃ k : Fin 2 → ℤ,
      P.coherentPlaneLiftData.circle01.carrier =
        (((R.circle P.index01).zeroWindingJordanCircle
          (R.zeroWinding P.index01)).translate
            (EmbeddedTorusIntersectionCircle.torusLatticeVector k)).carrier := by
  apply exists_jordanCarrier_eq_translate
    P.coherentPlaneLiftData.circle01
    ((R.circle P.index01).zeroWindingJordanCircle (R.zeroWinding P.index01))
    (TwoArcCircle.circleMap (P.coherentPlaneLiftData.edgeLift 0)
      (P.coherentPlaneLiftData.edgeLift 1).symm)
    ((R.circle P.index01).zeroWindingPlaneCircle (R.zeroWinding P.index01))
  · rw [P.coherentPlaneLiftData.carrier_circle01,
      TwoArcCircle.range_circleMap, Path.symm_range]
  · exact carrier_zeroWindingJordanCircle_eq_range _ _
  · exact TwoArcCircle.continuous_circleMap _ _
  · exact (R.circle P.index01).continuous_zeroWindingPlaneCircle _
  · exact P.projection_circle01

private theorem exists_circle02_alignment :
    ∃ k : Fin 2 → ℤ,
      P.coherentPlaneLiftData.circle02.carrier =
        (((R.circle P.index02).zeroWindingJordanCircle
          (R.zeroWinding P.index02)).translate
            (EmbeddedTorusIntersectionCircle.torusLatticeVector k)).carrier := by
  apply exists_jordanCarrier_eq_translate
    P.coherentPlaneLiftData.circle02
    ((R.circle P.index02).zeroWindingJordanCircle (R.zeroWinding P.index02))
    (TwoArcCircle.circleMap (P.coherentPlaneLiftData.edgeLift 0)
      (P.coherentPlaneLiftData.edgeLift 2).symm)
    ((R.circle P.index02).zeroWindingPlaneCircle (R.zeroWinding P.index02))
  · rw [P.coherentPlaneLiftData.carrier_circle02,
      TwoArcCircle.range_circleMap, Path.symm_range]
  · exact carrier_zeroWindingJordanCircle_eq_range _ _
  · exact TwoArcCircle.continuous_circleMap _ _
  · exact (R.circle P.index02).continuous_zeroWindingPlaneCircle _
  · exact P.projection_circle02

private theorem exists_circle12_alignment :
    ∃ k : Fin 2 → ℤ,
      P.coherentPlaneLiftData.circle12.carrier =
        (((R.circle P.index12).zeroWindingJordanCircle
          (R.zeroWinding P.index12)).translate
            (EmbeddedTorusIntersectionCircle.torusLatticeVector k)).carrier := by
  apply exists_jordanCarrier_eq_translate
    P.coherentPlaneLiftData.circle12
    ((R.circle P.index12).zeroWindingJordanCircle (R.zeroWinding P.index12))
    (TwoArcCircle.circleMap (P.coherentPlaneLiftData.edgeLift 1)
      (P.coherentPlaneLiftData.edgeLift 2).symm)
    ((R.circle P.index12).zeroWindingPlaneCircle (R.zeroWinding P.index12))
  · rw [P.coherentPlaneLiftData.carrier_circle12,
      TwoArcCircle.range_circleMap, Path.symm_range]
  · exact carrier_zeroWindingJordanCircle_eq_range _ _
  · exact TwoArcCircle.continuous_circleMap _ _
  · exact (R.circle P.index12).continuous_zeroWindingPlaneCircle _
  · exact P.projection_circle12

/-- All three raw cycle carrier alignments are consequences of the path presentation. -/
noncomputable def coherentThetaAlignmentData
    (D : P.coherentPlaneLiftData.CanonicalLocalStraighteningData) :
    RawFourPortCoherentThetaAlignmentData
      D.toJordanLocalStraighteningData R := by
  let h01 := P.exists_circle01_alignment
  let h02 := P.exists_circle02_alignment
  let h12 := P.exists_circle12_alignment
  exact {
    index01 := P.index01
    index02 := P.index02
    index12 := P.index12
    indices_exhaust := P.indices_exhaust
    shift01 := Classical.choose h01
    shift02 := Classical.choose h02
    shift12 := Classical.choose h12
    carrier01 := Classical.choose_spec h01
    carrier02 := Classical.choose_spec h02
    carrier12 := Classical.choose_spec h12 }

end RawFourPortThetaPathPresentation
end Submission.Topology
