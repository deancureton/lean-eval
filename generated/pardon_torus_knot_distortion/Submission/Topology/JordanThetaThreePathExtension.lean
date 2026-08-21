import Submission.PlaneSchoenflies.Schoenflies.JordanThetaAmbientExtension
import Submission.Topology.TwoArcCommonLocalStraightening

/-!
# Ambient extension for a three-path theta system

A three-path system whose `12` cycle is the outer cycle canonically supplies the filled theta
presentation required by `JordanThetaAmbientExtension`.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

open Schoenflies

namespace ThreePathSystem

variable {a b : Plane} {path : Fin 3 → Path a b} (G : ThreePathSystem path)

include G in
private theorem symm_injective (i : Fin 3) : Function.Injective (path i).symm := by
  intro s t hst
  apply unitInterval.symm_bijective.injective
  apply ThreePathSystem.injective G i
  simpa only [Path.symm_apply, Function.comp_apply] using hst

include G in
private theorem pairData (i j : Fin 3) (hij : i ≠ j) :
    TwoArcCircle.Data (path i) (path j).symm where
  first_injective := ThreePathSystem.injective G i
  second_injective := symm_injective G j
  range_inter := by
    rw [Path.symm_range]
    exact ThreePathSystem.range_inter G hij

private theorem carrier_circle01_inter_circle02 :
    G.circle01.carrier ∩ G.circle02.carrier = Set.range (path 0) := by
  rw [G.carrier_circle01, G.carrier_circle02]
  apply Set.Subset.antisymm
  · rintro x ⟨hx0 | hx1, hx0' | hx2⟩
    · exact hx0
    · exact hx0
    · exact hx0'
    · have hxEnds : x ∈ ({a, b} : Set Plane) := by
        rw [← G.range_inter (show (1 : Fin 3) ≠ 2 by decide)]
        exact ⟨hx1, hx2⟩
      rcases hxEnds with rfl | rfl
      · exact ⟨0, (path 0).source⟩
      · exact ⟨1, (path 0).target⟩
  · intro x hx
    exact ⟨Or.inl hx, Or.inl hx⟩

private theorem disjoint_inside_circle01_circle02
    (houter : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside) :
    Disjoint G.circle01.inside G.circle02.inside := by
  have h01 : G.circle01.carrier ⊆ G.circle12.inside ∪ G.circle12.carrier := by
    rw [← G.circle12.closure_inside, houter]
    intro x hx
    left
    rw [G.circle01.closure_inside]
    exact Or.inr hx
  have h02 : G.circle02.carrier ⊆ G.circle12.inside ∪ G.circle12.carrier := by
    rw [← G.circle12.closure_inside, houter]
    intro x hx
    right
    rw [G.circle02.closure_inside]
    exact Or.inr hx
  apply JordanThetaRegions.disjoint_inside h01 h02 G.carrier_circle12
      G.carrier_circle01 G.carrier_circle02
  · rw [G.carrier_circle02]
    exact G.toTopologicalPlanarJordanThetaData.private1_nonempty
  · rw [G.carrier_circle01]
    exact G.toTopologicalPlanarJordanThetaData.private2_nonempty

/-- A theta system with outer `12` cycle as a filled ambient-extension presentation. -/
noncomputable def outer12Presentation
    (houter : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside) :
    JordanThetaAmbientExtension.Presentation where
  source := a
  target := b
  shared := path 0
  lowerReturn := (path 1).symm
  upperReturn := (path 2).symm
  lowerData := G.pairData 0 1 (by decide)
  upperData := G.pairData 0 2 (by decide)
  outerData := by
    simpa only [Path.symm_symm] using G.pairData 1 2 (by decide)
  closed_inter := by
    change closure G.circle01.inside ∩ closure G.circle02.inside = Set.range (path 0)
    apply JordanThetaAmbientExtension.closure_inside_inter_eq_of_disjoint_inside_of_carrier_inter
    · exact G.disjoint_inside_circle01_circle02 houter
    · exact G.carrier_circle01_inter_circle02
  closed_union := by
    simp only [Path.symm_symm]
    let D01 := pairData G 0 1 (by decide)
    let D02 := pairData G 0 2 (by decide)
    let D12 := pairData G 1 2 (by decide)
    let J01 := TwoArcJordan.toJordanCircle (path 0) (path 1).symm
      D01.first_injective D01.second_injective D01.range_inter
    let J02 := TwoArcJordan.toJordanCircle (path 0) (path 2).symm
      D02.first_injective D02.second_injective D02.range_inter
    let J12 := TwoArcJordan.toJordanCircle (path 1) (path 2).symm
      D12.first_injective D12.second_injective D12.range_inter
    change closure J01.inside ∪ closure J02.inside = closure J12.inside
    have h01 : J01.inside = G.circle01.inside := by
      apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
      dsimp only [J01]
      rw [TwoArcJordan.carrier_toJordanCircle, G.carrier_circle01, Path.symm_range]
    have h02 : J02.inside = G.circle02.inside := by
      apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
      dsimp only [J02]
      rw [TwoArcJordan.carrier_toJordanCircle, G.carrier_circle02, Path.symm_range]
    have h12 : J12.inside = G.circle12.inside := by
      apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
      dsimp only [J12]
      rw [TwoArcJordan.carrier_toJordanCircle, G.carrier_circle12, Path.symm_range]
    rw [h01, h02, h12]
    exact houter.symm

variable {c d : Plane} {targetPath : Fin 3 → Path c d}
  (H : ThreePathSystem targetPath)

/-- The canonical ambient homeomorphism between two filled three-path theta systems. -/
noncomputable def outer12AmbientHomeomorph
    (hG : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside)
    (hH : closure H.circle12.inside =
      closure H.circle01.inside ∪ closure H.circle02.inside) :
    Plane ≃ₜ Plane :=
  JordanThetaAmbientExtension.ambientHomeomorph
    (G.outer12Presentation hG) (H.outer12Presentation hH)

theorem outer12AmbientHomeomorph_apply_path0
    (hG : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside)
    (hH : closure H.circle12.inside =
      closure H.circle01.inside ∪ closure H.circle02.inside)
    (t : unitInterval) :
    outer12AmbientHomeomorph G H hG hH (path 0 t) = targetPath 0 t := by
  exact JordanThetaAmbientExtension.ambientHomeomorph_apply_shared
    (G.outer12Presentation hG) (H.outer12Presentation hH) t

theorem outer12AmbientHomeomorph_apply_path1
    (hG : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside)
    (hH : closure H.circle12.inside =
      closure H.circle01.inside ∪ closure H.circle02.inside)
    (t : unitInterval) :
    outer12AmbientHomeomorph G H hG hH (path 1 t) = targetPath 1 t := by
  have h := JordanThetaAmbientExtension.ambientHomeomorph_apply_lowerReturn
    (G.outer12Presentation hG) (H.outer12Presentation hH) (unitInterval.symm t)
  have hsource : (path 1).symm (unitInterval.symm t) = path 1 t := by
    change (path 1).symm.symm t = path 1 t
    rw [Path.symm_symm]
  have htarget : (targetPath 1).symm (unitInterval.symm t) = targetPath 1 t := by
    change (targetPath 1).symm.symm t = targetPath 1 t
    rw [Path.symm_symm]
  simpa only [outer12AmbientHomeomorph, outer12Presentation, hsource, htarget] using h

theorem outer12AmbientHomeomorph_apply_path2
    (hG : closure G.circle12.inside =
      closure G.circle01.inside ∪ closure G.circle02.inside)
    (hH : closure H.circle12.inside =
      closure H.circle01.inside ∪ closure H.circle02.inside)
    (t : unitInterval) :
    outer12AmbientHomeomorph G H hG hH (path 2 t) = targetPath 2 t := by
  have h := JordanThetaAmbientExtension.ambientHomeomorph_apply_upperReturn
    (G.outer12Presentation hG) (H.outer12Presentation hH) (unitInterval.symm t)
  have hsource : (path 2).symm (unitInterval.symm t) = path 2 t := by
    change (path 2).symm.symm t = path 2 t
    rw [Path.symm_symm]
  have htarget : (targetPath 2).symm (unitInterval.symm t) = targetPath 2 t := by
    change (targetPath 2).symm.symm t = targetPath 2 t
    rw [Path.symm_symm]
  simpa only [outer12AmbientHomeomorph, outer12Presentation, hsource, htarget] using h

end ThreePathSystem
end Submission.Topology
