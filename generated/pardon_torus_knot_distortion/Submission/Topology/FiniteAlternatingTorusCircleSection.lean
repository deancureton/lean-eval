import Submission.Topology.SuperellipsoidActiveCycleConcatenation

/-!
# Torus-circle sections from finite alternating arc systems

Exact endpoint incidence turns two finite perfect matchings into embedded cyclic components.  This
file converts those canonical cycles directly into `EmbeddedTorusIntersectionCircle`s and an exact
finite torus-circle section.  The remaining geometry at a Pardon prefix is therefore only the
construction of its fixed outside paths, its chosen local paths, and their incidence equations.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

namespace EmbeddedTorusIntersectionCircle

variable {Phi : AmbientIsotopy}

/-- Bundle an embedded circle in the transported torus with its canonical winding loop. -/
noncomputable def ofTorusEmbedding
    (beta : Circle → transportedTorus Phi) (hbeta : IsEmbedding beta) :
    EmbeddedTorusIntersectionCircle Phi := by
  let coordinates : Circle → Circle × Circle := fun z ↦
    (transportedTorusHomeomorph Phi).symm (beta z)
  have hcoordinates : Continuous coordinates :=
    (transportedTorusHomeomorph Phi).symm.continuous.comp hbeta.continuous
  let loop := FiniteCoordinatePlaneTorusCircleFamily.windingLoopOfCircle
    (Phi := Phi) coordinates hcoordinates
  exact {
    circle := fun z ↦ beta z
    isEmbedding := IsEmbedding.subtypeVal.comp hbeta
    windingLoop := loop
    parametrization := fun t ↦ by
      change (beta (Circle.exp t) : R3) =
        transportedTorusHomeomorph Phi (coordinates (Circle.exp t))
      exact congrArg Subtype.val <|
        ((transportedTorusHomeomorph Phi).apply_symm_apply
          (beta (Circle.exp t))).symm }

@[simp] theorem ofTorusEmbedding_apply
    (beta : Circle → transportedTorus Phi) (hbeta : IsEmbedding beta) (z : Circle) :
    (ofTorusEmbedding beta hbeta).circle z = beta z :=
  rfl

end EmbeddedTorusIntersectionCircle

namespace FiniteAlternatingEndpointSystem.ClosedArcIncidenceData

universe u

variable {Phi : AmbientIsotopy} {vertex : Type u} [Fintype vertex]
  {A : FiniteAlternatingEndpointSystem vertex}
  {point : vertex → transportedTorus Phi}
  {firstPaths : EndpointPathFamily A.first point}
  {secondPaths : EndpointPathFamily A.second point}

/-- The canonical embedded torus circle associated to one quotient cycle. -/
noncomputable def embeddedTorusCircle
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (q : A.CycleIndex) : EmbeddedTorusIntersectionCircle Phi :=
  EmbeddedTorusIntersectionCircle.ofTorusEmbedding
    ((orientedFamily firstPaths secondPaths).circleMap q)
    (H.twoArcData q).data.isEmbedding

@[simp] theorem embeddedTorusCircle_apply
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (q : A.CycleIndex) (z : Circle) :
    (H.embeddedTorusCircle q).circle z =
      (orientedFamily firstPaths secondPaths).circleMap q z :=
  rfl

/-- The ambient carrier of all quotient cycles. -/
noncomputable def ambientCycleCarrier
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) : Set R3 :=
  ⋃ q : A.CycleIndex, Set.range (H.embeddedTorusCircle q).circle

/-- Distinct quotient cycles give disjoint ambient torus circles. -/
theorem embeddedTorusCircle_ranges_disjoint
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    {q r : A.CycleIndex} (hqr : q ≠ r) :
    Disjoint (Set.range (H.embeddedTorusCircle q).circle)
      (Set.range (H.embeddedTorusCircle r).circle) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz⟩ ⟨w, hw⟩
  have htorus :
      (orientedFamily firstPaths secondPaths).circleMap q z =
        (orientedFamily firstPaths secondPaths).circleMap r w := by
    apply Subtype.ext
    exact hz.trans hw.symm
  exact Set.disjoint_left.mp (H.circleMap_ranges_disjoint hqr)
    ⟨z, rfl⟩ ⟨w, htorus.symm⟩

/-- Exact finite torus-circle section supplied by the alternating arc incidence data. -/
noncomputable def finiteEmbeddedTorusCircleSection
    (H : ClosedArcIncidenceData A point firstPaths secondPaths) :
    FiniteEmbeddedTorusCircleSection Phi H.ambientCycleCarrier A.CycleIndex where
  circle := H.embeddedTorusCircle
  circle_mem_section := by
    intro q x hx
    exact Set.mem_iUnion.mpr ⟨q, hx⟩
  pairwise_disjoint := by
    intro q r hqr
    exact H.embeddedTorusCircle_ranges_disjoint hqr
  section_exact := rfl

/-- Transport the canonical section across an independently proved exact ambient-carrier name. -/
noncomputable def finiteEmbeddedTorusCircleSectionOfEq
    (H : ClosedArcIncidenceData A point firstPaths secondPaths)
    (ambientSection : Set R3) (hexact : ambientSection = H.ambientCycleCarrier) :
    FiniteEmbeddedTorusCircleSection Phi ambientSection A.CycleIndex where
  circle := H.embeddedTorusCircle
  circle_mem_section := by
    intro q x hx
    rw [hexact]
    exact Set.mem_iUnion.mpr ⟨q, hx⟩
  pairwise_disjoint := by
    intro q r hqr
    exact H.embeddedTorusCircle_ranges_disjoint hqr
  section_exact := hexact

end FiniteAlternatingEndpointSystem.ClosedArcIncidenceData
end Submission.Topology
