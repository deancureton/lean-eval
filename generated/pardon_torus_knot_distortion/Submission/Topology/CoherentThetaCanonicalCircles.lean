import Submission.Topology.CoherentThetaTopologicalPresentation

/-!
# Canonical Jordan circles of a coherent lifted theta graph

Each pair of coherent plane edges canonically glues to a Jordan circle.  This removes the three
carrier equalities from the remaining local-straightening interface.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

/-- Bundle the canonical two-arc circle as a Schoenflies Jordan circle. -/
def twoArcJordanCircle {a b : TorusCoveringPlane}
    (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : Set.range p ∩ Set.range q = {a, b}) : Schoenflies.JordanCircle where
  parametrization := fun z ↦
    TwoArcCircle.circleMap p q (JordanCurve.Arcs.spherePlaneHomeoCircle z)
  continuous := (TwoArcCircle.continuous_circleMap p q).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.continuous
  injective := (TwoArcCircle.circleMap_injective p q hp hq hinter).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

theorem carrier_twoArcJordanCircle {a b : TorusCoveringPlane}
    (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : Set.range p ∩ Set.range q = {a, b}) :
    (twoArcJordanCircle p q hp hq hinter).carrier =
      Set.range p ∪ Set.range q := by
  change Set.range
      (TwoArcCircle.circleMap p q ∘ JordanCurve.Arcs.spherePlaneHomeoCircle) = _
  rw [Set.range_comp]
  rw [JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq, Set.image_univ]
  exact TwoArcCircle.range_circleMap p q

variable {Phi : AmbientIsotopy}
  {T : TorusThetaPathSystem Phi}

namespace TorusThetaPathSystem.CoherentPlaneLiftData

variable (L : T.CoherentPlaneLiftData)

private theorem edgeLift_symm_injective (i : Fin 3) :
    Function.Injective (L.edgeLift i).symm := by
  intro u v huv
  apply unitInterval.symm_bijective.injective
  apply L.edgeLift_injective i
  simpa only [Path.symm_apply, Function.comp_apply] using huv

/-- Projection carries a canonical lifted two-edge circle to the corresponding torus circle. -/
theorem projection_circleMap_edges (i j : Fin 3) (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (TwoArcCircle.circleMap (L.edgeLift i) (L.edgeLift j).symm z) =
      TwoArcCircle.circleMap (T.edge i) (T.edge j).symm z := by
  apply TwoArcCircle.map_circleMap_of_pointwise
  · exact L.projection i
  · intro t
    simpa only [Path.symm_apply, Function.comp_apply] using
      L.projection j (unitInterval.symm t)

/-- The coherent circle formed by edges zero and one. -/
def circle01 : Schoenflies.JordanCircle :=
  twoArcJordanCircle (L.edgeLift 0) (L.edgeLift 1).symm
    (L.edgeLift_injective 0) (L.edgeLift_symm_injective 1)
    (by rw [Path.symm_range, L.edgeLift_range_inter (by decide)])

/-- The coherent circle formed by edges zero and two. -/
def circle02 : Schoenflies.JordanCircle :=
  twoArcJordanCircle (L.edgeLift 0) (L.edgeLift 2).symm
    (L.edgeLift_injective 0) (L.edgeLift_symm_injective 2)
    (by rw [Path.symm_range, L.edgeLift_range_inter (by decide)])

/-- The coherent circle formed by edges one and two. -/
def circle12 : Schoenflies.JordanCircle :=
  twoArcJordanCircle (L.edgeLift 1) (L.edgeLift 2).symm
    (L.edgeLift_injective 1) (L.edgeLift_symm_injective 2)
    (by rw [Path.symm_range, L.edgeLift_range_inter (by decide)])

@[simp] theorem carrier_circle01 : L.circle01.carrier =
    Set.range (L.edgeLift 0) ∪ Set.range (L.edgeLift 1) := by
  rw [circle01, carrier_twoArcJordanCircle, Path.symm_range]

@[simp] theorem carrier_circle02 : L.circle02.carrier =
    Set.range (L.edgeLift 0) ∪ Set.range (L.edgeLift 2) := by
  rw [circle02, carrier_twoArcJordanCircle, Path.symm_range]

@[simp] theorem carrier_circle12 : L.circle12.carrier =
    Set.range (L.edgeLift 1) ∪ Set.range (L.edgeLift 2) := by
  rw [circle12, carrier_twoArcJordanCircle, Path.symm_range]

/-- The sole local input remaining after the canonical coherent circles are constructed. -/
structure CanonicalLocalStraighteningData where
  exceptional : Set TorusCoveringPlane
  exceptional_finite : exceptional.Finite
  local0 : ∀ p ∈ Set.range (L.edgeLift 0) \ exceptional,
    CommonLocalStraighteningData L.circle01 L.circle02 p
  local1 : ∀ p ∈ Set.range (L.edgeLift 1) \ exceptional,
    CommonLocalStraighteningData L.circle01 L.circle12 p
  local2 : ∀ p ∈ Set.range (L.edgeLift 2) \ exceptional,
    CommonLocalStraighteningData L.circle02 L.circle12 p

namespace CanonicalLocalStraighteningData

/-- Canonical coherent circles and their local straightenings give the complete theta data. -/
noncomputable def toJordanLocalStraighteningData
    (D : L.CanonicalLocalStraighteningData) : L.JordanLocalStraighteningData where
  circle01 := L.circle01
  circle02 := L.circle02
  circle12 := L.circle12
  carrier01 := L.carrier_circle01
  carrier02 := L.carrier_circle02
  carrier12 := L.carrier_circle12
  exceptional := D.exceptional
  exceptional_finite := D.exceptional_finite
  local0 := D.local0
  local1 := D.local1
  local2 := D.local2

end CanonicalLocalStraighteningData
end TorusThetaPathSystem.CoherentPlaneLiftData
end Submission.Topology
