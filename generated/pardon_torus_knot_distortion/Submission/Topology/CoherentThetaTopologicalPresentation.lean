import Submission.Topology.CoherentThetaCoveringNeighborhood
import Submission.Topology.TopologicalThetaOuterCycle

/-!
# Topological theta data from coherent plane lifts

A coherent lift of three torus theta edges already supplies all global planar incidence and
connectedness facts needed by `TopologicalPlanarJordanThetaData`.  This module derives those
facts.  The remaining input consists only of exact Jordan-circle carriers and the local
two-face filling property along each lifted edge.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {T : TorusThetaPathSystem Phi}

namespace TorusThetaPathSystem.CoherentPlaneLiftData

variable (L : T.CoherentPlaneLiftData)

/-- Each coherent plane edge is injective because its projection is an injective torus edge. -/
theorem edgeLift_injective (i : Fin 3) : Function.Injective (L.edgeLift i) := by
  intro u v huv
  apply T.edge_injective i
  rw [← L.projection i u, ← L.projection i v, huv]

/-- Distinct coherent plane edges meet exactly at their common lifted endpoints. -/
theorem edgeLift_range_inter {i j : Fin 3} (hij : i ≠ j) :
    Set.range (L.edgeLift i) ∩ Set.range (L.edgeLift j) =
      {L.sourceLift, L.targetLift} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨u, rfl⟩, ⟨v, huv⟩⟩
    have hdown : T.edge i u = T.edge j v := by
      rw [← L.projection i u, ← L.projection j v, huv]
    have hmem : T.edge i u ∈ Set.range (T.edge i) ∩ Set.range (T.edge j) :=
      ⟨⟨u, rfl⟩, ⟨v, hdown.symm⟩⟩
    rw [T.edge_range_inter hij] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
    rcases hmem with hsource | htarget
    · left
      have hu : u = 0 := T.edge_injective i <|
        hsource.trans (T.edge i).source.symm
      subst u
      exact (L.edgeLift i).source
    · right
      have hu : u = 1 := T.edge_injective i <|
        htarget.trans (T.edge i).target.symm
      subst u
      exact (L.edgeLift i).target
  · rintro x (rfl | rfl)
    · exact ⟨⟨0, (L.edgeLift i).source⟩, ⟨0, (L.edgeLift j).source⟩⟩
    · exact ⟨⟨1, (L.edgeLift i).target⟩, ⟨1, (L.edgeLift j).target⟩⟩

private theorem range_diff_endpoints_eq_image_Ioo
    {a b : TorusCoveringPlane} (p : Path a b) (hp : Function.Injective p) :
    Set.range p \ ({a, b} : Set TorusCoveringPlane) =
      p '' Set.Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have ht0 : t ≠ 0 := by
      intro h
      apply ht
      left
      subst t
      exact p.source
    have ht1 : t ≠ 1 := by
      intro h
      apply ht
      right
      subst t
      exact p.target
    exact ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0),
      lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro (ha | hb)
    · have ht0 : t = 0 := hp <| ha.trans p.source.symm
      exact (ne_of_gt ht.1) ht0
    · have ht1 : t = 1 := hp <| hb.trans p.target.symm
      exact (ne_of_lt ht.2) ht1

/-- Removing the common endpoints from one coherent edge leaves a preconnected set. -/
theorem edgeLift_private_preconnected (i : Fin 3) :
    IsPreconnected
      (Set.range (L.edgeLift i) \ {L.sourceLift, L.targetLift}) := by
  rw [range_diff_endpoints_eq_image_Ioo (L.edgeLift i) (L.edgeLift_injective i)]
  exact isPreconnected_Ioo.image (L.edgeLift i)
    (L.edgeLift i).continuous.continuousOn

private def middleParameter : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

private theorem middleParameter_ne_zero : middleParameter ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [middleParameter] at this

private theorem middleParameter_ne_one : middleParameter ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [middleParameter] at this

private theorem middle_edgeLift_not_mem_other {i j : Fin 3} (hij : i ≠ j) :
    L.edgeLift i middleParameter ∉ Set.range (L.edgeLift j) := by
  intro hj
  have hmem : L.edgeLift i middleParameter ∈
      Set.range (L.edgeLift i) ∩ Set.range (L.edgeLift j) :=
    ⟨⟨middleParameter, rfl⟩, hj⟩
  rw [L.edgeLift_range_inter hij] at hmem
  rcases hmem with hsource | htarget
  · exact middleParameter_ne_zero <| L.edgeLift_injective i <|
      hsource.trans (L.edgeLift i).source.symm
  · exact middleParameter_ne_one <| L.edgeLift_injective i <|
      htarget.trans (L.edgeLift i).target.symm

/-- Each coherent edge has a point which lies on neither of the other two edges. -/
theorem edgeLift_private_nonempty {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) :
    (Set.range (L.edgeLift i) \
      (Set.range (L.edgeLift j) ∪ Set.range (L.edgeLift k))).Nonempty := by
  refine ⟨L.edgeLift i middleParameter, ⟨middleParameter, rfl⟩, ?_⟩
  rintro (hj | hk)
  · exact L.middle_edgeLift_not_mem_other hij hj
  · exact L.middle_edgeLift_not_mem_other hik hk

/-- The remaining geometric data needed to turn a coherent lift into a topological theta. -/
structure JordanLocalStraighteningData where
  circle01 : Schoenflies.JordanCircle
  circle02 : Schoenflies.JordanCircle
  circle12 : Schoenflies.JordanCircle
  carrier01 : circle01.carrier =
    Set.range (L.edgeLift 0) ∪ Set.range (L.edgeLift 1)
  carrier02 : circle02.carrier =
    Set.range (L.edgeLift 0) ∪ Set.range (L.edgeLift 2)
  carrier12 : circle12.carrier =
    Set.range (L.edgeLift 1) ∪ Set.range (L.edgeLift 2)
  exceptional : Set TorusCoveringPlane
  exceptional_finite : exceptional.Finite
  local0 : ∀ p ∈ Set.range (L.edgeLift 0) \ exceptional,
    CommonLocalStraighteningData circle01 circle02 p
  local1 : ∀ p ∈ Set.range (L.edgeLift 1) \ exceptional,
    CommonLocalStraighteningData circle01 circle12 p
  local2 : ∀ p ∈ Set.range (L.edgeLift 2) \ exceptional,
    CommonLocalStraighteningData circle02 circle12 p

namespace JordanLocalStraighteningData

/-- Coherent incidence plus local filling produces the full invariant planar theta package. -/
noncomputable def toTopologicalPlanarJordanThetaData
    (D : L.JordanLocalStraighteningData) : TopologicalPlanarJordanThetaData where
  source := L.sourceLift
  target := L.targetLift
  edge0 := Set.range (L.edgeLift 0)
  edge1 := Set.range (L.edgeLift 1)
  edge2 := Set.range (L.edgeLift 2)
  circle01 := D.circle01
  circle02 := D.circle02
  circle12 := D.circle12
  endpoints_subset_edge0 := by
    rintro x (rfl | rfl)
    · exact ⟨0, (L.edgeLift 0).source⟩
    · exact ⟨1, (L.edgeLift 0).target⟩
  endpoints_subset_edge1 := by
    rintro x (rfl | rfl)
    · exact ⟨0, (L.edgeLift 1).source⟩
    · exact ⟨1, (L.edgeLift 1).target⟩
  endpoints_subset_edge2 := by
    rintro x (rfl | rfl)
    · exact ⟨0, (L.edgeLift 2).source⟩
    · exact ⟨1, (L.edgeLift 2).target⟩
  edge0_inter_edge1 := L.edgeLift_range_inter (by decide)
  edge0_inter_edge2 := L.edgeLift_range_inter (by decide)
  edge1_inter_edge2 := L.edgeLift_range_inter (by decide)
  carrier01 := D.carrier01
  carrier02 := D.carrier02
  carrier12 := D.carrier12
  private0_preconnected := L.edgeLift_private_preconnected 0
  private1_preconnected := L.edgeLift_private_preconnected 1
  private2_preconnected := L.edgeLift_private_preconnected 2
  private0_nonempty := L.edgeLift_private_nonempty (by decide) (by decide)
  private1_nonempty := L.edgeLift_private_nonempty (by decide) (by decide)
  private2_nonempty := L.edgeLift_private_nonempty (by decide) (by decide)
  exceptional := D.exceptional
  exceptional_finite := D.exceptional_finite
  local0 := D.local0
  local1 := D.local1
  local2 := D.local2

end JordanLocalStraighteningData
end TorusThetaPathSystem.CoherentPlaneLiftData
end Submission.Topology
