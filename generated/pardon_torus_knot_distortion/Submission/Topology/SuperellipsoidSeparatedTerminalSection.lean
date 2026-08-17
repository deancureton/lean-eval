import Submission.Topology.SuperellipsoidCanonicalTruncatedSphereSection
import Submission.Topology.SuperellipsoidGlobalNeckPinchRounding

/-!
# Canonical circle section of the separated terminal spheres

The honest terminal family uses the lower truncation at `d - ε` and the upper truncation at
`d + ε`.  Applying the canonical truncated-sphere classification at those two distinct levels
and taking their disjoint union gives the exact finite torus section of that two-sphere family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

namespace FiniteSuperellipsoidBarrierGraph
namespace TruncatedSphereAlternatingCycles

universe u

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d ε : ℝ}
  {lowerOuterIndex lowerCutIndex upperOuterIndex upperCutIndex : Type u}
  [Fintype lowerOuterIndex] [Fintype lowerCutIndex]
  [Fintype upperOuterIndex] [Fintype upperCutIndex]
  {lowerGraph : FiniteSuperellipsoidBarrierGraph Phi frame c R (d - ε)
    lowerOuterIndex lowerCutIndex}
  {upperGraph : FiniteSuperellipsoidBarrierGraph Phi frame c R (d + ε)
    upperOuterIndex upperCutIndex}
  (lowerOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily lowerGraph)
  (lowerCutOrder : CutCircleTransverseCyclicOrderFamily lowerGraph)
  (upperOuterOrder : OuterCircleTransverseHeightCyclicOrderFamily upperGraph)
  (upperCutOrder : CutCircleTransverseCyclicOrderFamily upperGraph)
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d - ε))]
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d + ε))]

/-- The index type of the canonical separated terminal section. -/
abbrev SeparatedTerminalComponentIndex :=
  LowerComponentIndex lowerOuterOrder lowerCutOrder ⊕
    UpperComponentIndex upperOuterOrder upperCutOrder

/-- The ambient torus section of the two separated truncated spheres. -/
def separatedTerminalTorusSection : Set R3 :=
  lowerTruncatedSuperellipsoidTorusSection Phi frame c R (d - ε) ∪
    upperTruncatedSuperellipsoidTorusSection Phi frame c R (d + ε)

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R (d - ε))]
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d + ε))] in
private theorem lowerSection_disjoint_upperSection (hε : 0 < ε) :
    Disjoint
      (lowerTruncatedSuperellipsoidTorusSection Phi frame c R (d - ε))
      (upperTruncatedSuperellipsoidTorusSection Phi frame c R (d + ε)) := by
  apply (separatedTruncations_disjoint (frame := frame) (c := c) (R := R)
    (d := d) hε).mono
  · intro x hx
    exact isClosed_separatedLowerSuperellipsoidTruncation.frontier_subset hx.2
  · intro x hx
    exact isClosed_separatedUpperSuperellipsoidTruncation.frontier_subset hx.2

/-- The two canonical endpoint classifications combine into one exact finite section. -/
noncomputable def canonicalSeparatedTerminalFiniteSection (hR : 0 < R) (hε : 0 < ε) :
    FiniteEmbeddedTorusCircleSection Phi
      (separatedTerminalTorusSection (Phi := Phi) (frame := frame)
        (c := c) (R := R) (d := d) (ε := ε))
      (SeparatedTerminalComponentIndex lowerOuterOrder lowerCutOrder
        upperOuterOrder upperCutOrder) := by
  let lower := canonicalLowerFiniteSection lowerOuterOrder lowerCutOrder hR
  let upper := canonicalUpperFiniteSection upperOuterOrder upperCutOrder hR
  exact {
    circle := Sum.elim lower.circle upper.circle
    circle_mem_section := by
      rintro (i | j) x hx
      · exact Or.inl (lower.circle_mem_section i hx)
      · exact Or.inr (upper.circle_mem_section j hx)
    pairwise_disjoint := by
      rintro (i | i) (j | j) hij
      · exact lower.pairwise_disjoint fun h ↦ hij (congrArg Sum.inl h)
      · apply (lowerSection_disjoint_upperSection (Phi := Phi) (frame := frame)
          (c := c) (R := R) (d := d) (ε := ε) hε).mono
        · exact lower.circle_mem_section i
        · exact upper.circle_mem_section j
      · apply (lowerSection_disjoint_upperSection (Phi := Phi) (frame := frame)
          (c := c) (R := R) (d := d) (ε := ε) hε).symm.mono
        · exact upper.circle_mem_section i
        · exact lower.circle_mem_section j
      · exact upper.pairwise_disjoint fun h ↦ hij (congrArg Sum.inr h)
    section_exact := by
      rw [separatedTerminalTorusSection]
      apply Set.Subset.antisymm
      · rintro x (hx | hx)
        · rw [lower.section_exact] at hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
        · rw [upper.section_exact] at hx
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨Sum.inr j, hj⟩
      · intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        rcases i with i | j
        · left
          rw [lower.section_exact]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        · right
          rw [upper.section_exact]
          exact Set.mem_iUnion.mpr ⟨j, hi⟩ }

omit [Fintype (SuperellipsoidSeamVertex Phi frame c R (d - ε))]
  [Fintype (SuperellipsoidSeamVertex Phi frame c R (d + ε))] in
/-- The analytic separated section is exactly the intersection of the terminal sphere carrier
with the transported torus. -/
theorem separatedTerminalTorusSection_eq_sphereCarrier_inter
    (hR : 0 < R)
    (hlower : ∃ x, x ∈ superellipsoidBody frame c R ∧
      x.ofLp (frame 2) < d - ε)
    (hupper : ∃ x, x ∈ superellipsoidBody frame c R ∧
      d + ε < x.ofLp (frame 2)) (hε : 0 < ε) :
    separatedTerminalTorusSection (Phi := Phi) (frame := frame)
        (c := c) (R := R) (d := d) (ε := ε) =
      (separatedTruncationSphereFamily hR hlower hupper hε).carrier ∩
        transportedTorus Phi := by
  rw [separatedTerminalTorusSection,
    separatedTruncationSphereFamily_carrier hR hlower hupper hε]
  ext x
  simp only [lowerTruncatedSuperellipsoidTorusSection,
    upperTruncatedSuperellipsoidTorusSection, mem_union, mem_inter_iff]
  tauto

end TruncatedSphereAlternatingCycles
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
