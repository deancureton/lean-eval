import Submission.Topology.ReducedTorusParityAxis

/-!
# Reduced stages from exact torus-circle sections

The reduced Pardon axis argument does not use ambient sphere parametrizations.  This module
packages the exact finite circle data it does use and converts a finite collection of classified
torus sections and open parity regions into its stage sequence.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

/-- A finite pairwise-disjoint family of embedded circles on the transported torus. -/
structure FiniteDisjointTorusCircleFamily (Phi : AmbientIsotopy) (ι : Type*)
    [Fintype ι] where
  circle : ι → EmbeddedTorusIntersectionCircle Phi
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)

namespace FiniteDisjointTorusCircleFamily

variable {ι : Type*} [Fintype ι]

/-- Forget the ambient name of an exact finite torus section. -/
def ofSection {ambientSection : Set R3}
    (S : FiniteEmbeddedTorusCircleSection Phi ambientSection ι) :
    FiniteDisjointTorusCircleFamily Phi ι where
  circle := S.circle
  pairwise_disjoint := S.pairwise_disjoint

def AllInessential (F : FiniteDisjointTorusCircleFamily Phi ι) : Prop :=
  ∀ i, (F.circle i).windingLoop.windingPair = (0, 0)

/-- The ambient carrier of the family, viewed as a subset of the transported torus. -/
def carrier (F : FiniteDisjointTorusCircleFamily Phi ι) :
    Set (transportedTorus Phi) :=
  ⋃ i, Set.range (F.circle i).windingLoop.curve

theorem carrier_eq_transportedTorusPart {ambientSection : Set R3}
    (S : FiniteEmbeddedTorusCircleSection Phi ambientSection ι) :
    (ofSection S).carrier = transportedTorusPart Phi ambientSection := by
  ext x
  change (x ∈ ⋃ i, Set.range (S.circle i).windingLoop.curve) ↔
    (x : R3) ∈ ambientSection
  have hxSection := Set.ext_iff.mp S.section_exact (x : R3)
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, t, ht⟩ := hx
    apply hxSection.mpr
    refine Set.mem_iUnion.mpr ⟨i, Circle.exp t, ?_⟩
    calc
      (S.circle i).circle (Circle.exp t) =
          ((S.circle i).windingLoop.curve t : R3) := (S.circle i).parametrization t
      _ = x := congrArg Subtype.val ht
  · intro hx
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (hxSection.mp hx)
    obtain ⟨t, ht⟩ := Circle.exp_surjective z
    refine Set.mem_iUnion.mpr ⟨i, t, ?_⟩
    apply Subtype.ext
    calc
      ((S.circle i).windingLoop.curve t : R3) = (S.circle i).circle (Circle.exp t) :=
        ((S.circle i).parametrization t).symm
      _ = (S.circle i).circle z := congrArg (S.circle i).circle ht
      _ = x := hz

end FiniteDisjointTorusCircleFamily

/-- Exact circle sections and exact open parity regions for finitely many reduced stages. -/
structure ReducedTorusCircleStageGeometry (Phi : AmbientIsotopy) where
  length : ℕ
  circleCount : ℕ → ℕ
  ambientSection : ℕ → Set R3
  circleSection : ∀ k, FiniteEmbeddedTorusCircleSection Phi
    (ambientSection k) (Fin (circleCount k))
  region : ℕ → Set (transportedTorus Phi)
  isOpen_region : ∀ k, IsOpen (region k)
  frontier_region : ∀ k,
    frontier (region k) = transportedTorusPart Phi (ambientSection k)

namespace ReducedTorusCircleStageGeometry

/-- The exact reduced parity stage at one natural-number index. -/
def parityStage (D : ReducedTorusCircleStageGeometry Phi) (k : ℕ) :
    ReducedTorusParityStage Phi :=
  (D.circleSection k).toReducedTorusParityStage
    (D.region k) (D.isOpen_region k) (D.frontier_region k)

/-- Forget the ambient section names and retain the reduced axis-stage family. -/
def toReducedTorusCircleStageSequence
    (D : ReducedTorusCircleStageGeometry Phi) :
    ReducedTorusCircleStageSequence Phi where
  length := D.length
  circleCount := D.circleCount
  circle k := (D.circleSection k).circle
  parityStage := D.parityStage

@[simp] theorem toReducedTorusCircleStageSequence_circle
    (D : ReducedTorusCircleStageGeometry Phi) (k : ℕ)
    (i : Fin (D.circleCount k)) :
    (D.toReducedTorusCircleStageSequence.circle k i) =
      (D.circleSection k).circle i :=
  rfl

@[simp] theorem toReducedTorusCircleStageSequence_inside
    (D : ReducedTorusCircleStageGeometry Phi) (k : ℕ) :
    (D.toReducedTorusCircleStageSequence.parityStage k).inside = D.region k :=
  rfl

@[simp] theorem toReducedTorusCircleStageSequence_boundary
    (D : ReducedTorusCircleStageGeometry Phi) (k : ℕ) :
    (D.toReducedTorusCircleStageSequence.parityStage k).boundary =
      transportedTorusPart Phi (D.ambientSection k) :=
  rfl

end ReducedTorusCircleStageGeometry
end Submission.Topology
