import Submission.Topology.FourPortSixEdgeRectangle
import Submission.Topology.JordanTranslate
import Submission.Topology.TwoArcCommonLocalStraightening

/-!
# Theta decompositions inside the six-edge four-port graph

The lower outside arc, lower rectangle edge, and upper rectangle route form a genuine theta
subgraph.  The invariant outer-cycle theorem therefore gives an exact decomposition of one of
its three closed Jordan regions, with no separate local-flatness hypothesis.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

namespace FourPortSixEdgePathSystem

variable (G : FourPortSixEdgePathSystem Schoenflies.Plane)

/-- The three lower-theta paths, all oriented from the lower-left to the lower-right port. -/
def lowerThetaPath : Fin 3 → Path G.leftBottom G.rightBottom
  | 0 => G.bottom
  | 1 => G.bottomOutside.symm
  | 2 => G.localRectangleUpperPath

@[simp] theorem lowerThetaPath_zero : G.lowerThetaPath 0 = G.bottom := rfl

@[simp] theorem lowerThetaPath_one : G.lowerThetaPath 1 = G.bottomOutside.symm := rfl

@[simp] theorem lowerThetaPath_two : G.lowerThetaPath 2 = G.localRectangleUpperPath := rfl

private theorem range_bottom_inter_lowerUpper :
    Set.range G.bottom ∩ Set.range G.localRectangleUpperPath =
      {G.leftBottom, G.rightBottom} := by
  rw [Set.inter_comm]
  exact G.localRectangleData.upper_inter_bottom

private theorem range_bottomOutside_symm_inter_lowerUpper :
    Set.range G.bottomOutside.symm ∩ Set.range G.localRectangleUpperPath =
      {G.leftBottom, G.rightBottom} := by
  rw [Path.symm_range]
  apply Set.Subset.antisymm
  · intro x hx
    have hxFull : x ∈ Set.range G.bottomOutside ∩ G.localRectangleCarrier := by
      refine ⟨hx.1, ?_⟩
      change x ∈ Set.range G.localRectangleUpperPath ∪ Set.range G.bottom
      exact Or.inl hx.2
    rw [G.bottomOutside_inter_localRectangleCarrier] at hxFull
    simpa only [Set.pair_comm] using hxFull
  · rintro x (rfl | rfl)
    · exact ⟨⟨1, G.bottomOutside.target⟩,
        ⟨0, G.localRectangleUpperPath.source⟩⟩
    · exact ⟨⟨0, G.bottomOutside.source⟩,
        ⟨1, G.localRectangleUpperPath.target⟩⟩

/-- The canonical lower theta system. -/
theorem lowerThetaSystem : ThreePathSystem G.lowerThetaPath where
  injective := by
    intro i
    fin_cases i
    · exact G.bottom_injective
    · intro s t hst
      apply unitInterval.symm_bijective.injective
      apply G.bottomOutside_injective
      simpa only [lowerThetaPath, Path.symm_apply, Function.comp_apply] using hst
    · exact G.localRectangleData.upper_injective
  range_inter := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [lowerThetaPath, Path.symm_range] using G.bottomData.range_inter
    · exact G.range_bottom_inter_lowerUpper
    · rw [Set.inter_comm]
      simpa only [lowerThetaPath, Path.symm_range] using G.bottomData.range_inter
    · exact (hij rfl).elim
    · exact G.range_bottomOutside_symm_inter_lowerUpper
    · rw [Set.inter_comm]
      exact G.range_bottom_inter_lowerUpper
    · rw [Set.inter_comm]
      exact G.range_bottomOutside_symm_inter_lowerUpper
    · exact (hij rfl).elim

/-- The auxiliary cycle using the lower outside arc and the upper rectangle route. -/
def lowerAuxiliaryJordanCircle : Schoenflies.JordanCircle :=
  G.lowerThetaSystem.circle12

@[simp] theorem carrier_lowerAuxiliaryJordanCircle :
    G.lowerAuxiliaryJordanCircle.carrier =
      Set.range G.bottomOutside ∪ Set.range G.localRectangleUpperPath := by
  rw [lowerAuxiliaryJordanCircle, ThreePathSystem.carrier_circle12]
  simp only [lowerThetaPath, Path.symm_range]

private theorem lowerTheta_circle01_inside :
    G.lowerThetaSystem.circle01.inside = G.bottomJordanCircle.inside := by
  apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
  rw [G.lowerThetaSystem.carrier_circle01, G.carrier_bottomJordanCircle]
  simp only [lowerThetaPath, Path.symm_range]

private theorem lowerTheta_circle02_inside :
    G.lowerThetaSystem.circle02.inside =
      (G.localRectangleJordanCircle G.localRectangleData).inside := by
  apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
  rw [G.lowerThetaSystem.carrier_circle02,
    G.carrier_localRectangleJordanCircle]
  simp only [lowerThetaPath, localRectangleCarrier, Set.union_comm]

/-- Exact lower-theta closed-region trichotomy. -/
theorem lowerTheta_exists_outer_cycle_decomposition :
    closure G.bottomJordanCircle.inside =
        closure (G.localRectangleJordanCircle G.localRectangleData).inside ∪
          closure G.lowerAuxiliaryJordanCircle.inside ∨
      closure (G.localRectangleJordanCircle G.localRectangleData).inside =
        closure G.bottomJordanCircle.inside ∪
          closure G.lowerAuxiliaryJordanCircle.inside ∨
      closure G.lowerAuxiliaryJordanCircle.inside =
        closure G.bottomJordanCircle.inside ∪
          closure (G.localRectangleJordanCircle G.localRectangleData).inside := by
  simpa only [G.lowerTheta_circle01_inside, G.lowerTheta_circle02_inside,
    lowerAuxiliaryJordanCircle] using
      G.lowerThetaSystem.exists_outer_cycle_decomposition

/-! ## The upper theta after adjoining the upper outside arc -/

/-- The lower route from the upper-left to the upper-right port. -/
def upperThetaLowerRoute : Path G.leftTop G.rightTop :=
  (G.left.symm.trans G.bottomOutside.symm).trans G.right

private theorem range_left_inter_bottomOutside :
    Set.range G.left ∩ Set.range G.bottomOutside = {G.leftBottom} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxLeft, hxOutside⟩
    have hxFull : x ∈ Set.range G.bottomOutside ∩ G.localRectangleCarrier := by
      refine ⟨hxOutside, ?_⟩
      rw [G.localRectangleCarrier_eq]
      exact Or.inl (Or.inl (Or.inl hxLeft))
    rw [G.bottomOutside_inter_localRectangleCarrier] at hxFull
    rcases hxFull with hx | hx
    · exact Set.mem_singleton_iff.mpr hx
    · have hxRight : x ∈ Set.range G.right := by
        rw [Set.mem_singleton_iff] at hx
        exact ⟨0, G.right.source.trans hx.symm⟩
      exact False.elim <| by
        have : x ∈ Set.range G.left ∩ Set.range G.right := ⟨hxLeft, hxRight⟩
        rwa [G.range_left_inter_right] at this
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, G.left.source⟩, ⟨1, G.bottomOutside.target⟩⟩

private theorem range_bottomOutside_inter_right :
    Set.range G.bottomOutside ∩ Set.range G.right = {G.rightBottom} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxOutside, hxRight⟩
    have hxFull : x ∈ Set.range G.bottomOutside ∩ G.localRectangleCarrier := by
      refine ⟨hxOutside, ?_⟩
      rw [G.localRectangleCarrier_eq]
      exact Or.inl (Or.inr hxRight)
    rw [G.bottomOutside_inter_localRectangleCarrier] at hxFull
    rcases hxFull with hx | hx
    · have hxLeft : x ∈ Set.range G.left := by
        subst x
        exact ⟨0, G.left.source⟩
      exact False.elim <| by
        have : x ∈ Set.range G.left ∩ Set.range G.right := ⟨hxLeft, hxRight⟩
        rwa [G.range_left_inter_right] at this
    · exact hx
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, G.bottomOutside.source⟩, ⟨0, G.right.source⟩⟩

private theorem range_top_inter_bottomOutside :
    Set.range G.top ∩ Set.range G.bottomOutside = ∅ := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  exact G.bottomCircle_disjoint_topCircle.symm.mono
    (by rw [G.range_topCircle]; exact Set.subset_union_left)
    (by rw [G.range_bottomCircle]; exact Set.subset_union_right)

private theorem range_topOutside_inter_bottomOutside :
    Set.range G.topOutside ∩ Set.range G.bottomOutside = ∅ := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  exact G.bottomCircle_disjoint_topCircle.symm.mono
    (by rw [G.range_topCircle]; exact Set.subset_union_right)
    (by rw [G.range_bottomCircle]; exact Set.subset_union_right)

private theorem upperThetaLowerRoute_injective :
    Function.Injective G.upperThetaLowerRoute := by
  have hleftOutside : Function.Injective (G.left.symm.trans G.bottomOutside.symm) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter _ _
      (by
        intro s t hst
        apply unitInterval.symm_bijective.injective
        apply G.left_injective
        simpa only [Path.symm_apply, Function.comp_apply] using hst)
      (by
        intro s t hst
        apply unitInterval.symm_bijective.injective
        apply G.bottomOutside_injective
        simpa only [Path.symm_apply, Function.comp_apply] using hst)
      (by simpa only [Path.symm_range] using G.range_left_inter_bottomOutside)
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter _ _
    hleftOutside G.right_injective
  rw [Path.trans_range, Path.symm_range, Path.symm_range,
    Set.union_inter_distrib_right, G.range_left_inter_right,
    G.range_bottomOutside_inter_right, Set.empty_union]

private theorem range_top_inter_upperThetaLowerRoute :
    Set.range G.top ∩ Set.range G.upperThetaLowerRoute =
      {G.leftTop, G.rightTop} := by
  rw [upperThetaLowerRoute, Path.trans_range, Path.trans_range,
    Path.symm_range, Path.symm_range, Set.inter_union_distrib_left,
    Set.inter_union_distrib_left]
  have hleft : Set.range G.top ∩ Set.range G.left = {G.leftTop} := by
    rw [Set.inter_comm]
    exact G.range_left_inter_top
  rw [hleft, G.range_top_inter_bottomOutside, G.range_top_inter_right,
    Set.union_empty]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

private theorem range_topOutside_symm_inter_upperThetaLowerRoute :
    Set.range G.topOutside.symm ∩ Set.range G.upperThetaLowerRoute =
      {G.leftTop, G.rightTop} := by
  rw [upperThetaLowerRoute, Path.trans_range, Path.trans_range,
    Path.symm_range, Path.symm_range, Set.inter_union_distrib_left,
    Set.inter_union_distrib_left]
  simp only [Path.symm_range]
  have hleft : Set.range G.topOutside ∩ Set.range G.left = {G.leftTop} := by
    rw [Set.inter_comm]
    exact G.range_left_inter_topOutside
  rw [hleft, G.range_topOutside_inter_bottomOutside,
    G.range_topOutside_inter_right, Set.union_empty]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- The upper theta paths, all oriented from the upper-left to the upper-right port. -/
def upperThetaPath : Fin 3 → Path G.leftTop G.rightTop
  | 0 => G.top
  | 1 => G.topOutside.symm
  | 2 => G.upperThetaLowerRoute

/-- The canonical upper theta system. -/
theorem upperThetaSystem : ThreePathSystem G.upperThetaPath where
  injective := by
    intro i
    fin_cases i
    · exact G.top_injective
    · intro s t hst
      apply unitInterval.symm_bijective.injective
      apply G.topOutside_injective
      simpa only [upperThetaPath, Path.symm_apply, Function.comp_apply] using hst
    · exact G.upperThetaLowerRoute_injective
  range_inter := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [upperThetaPath, Path.symm_range] using G.topData.range_inter
    · exact G.range_top_inter_upperThetaLowerRoute
    · rw [Set.inter_comm]
      simpa only [upperThetaPath, Path.symm_range] using G.topData.range_inter
    · exact (hij rfl).elim
    · exact G.range_topOutside_symm_inter_upperThetaLowerRoute
    · rw [Set.inter_comm]
      exact G.range_top_inter_upperThetaLowerRoute
    · rw [Set.inter_comm]
      exact G.range_topOutside_symm_inter_upperThetaLowerRoute
    · exact (hij rfl).elim

private theorem upperTheta_circle01_inside :
    G.upperThetaSystem.circle01.inside = G.topJordanCircle.inside := by
  apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
  rw [G.upperThetaSystem.carrier_circle01, G.carrier_topJordanCircle]
  simp only [upperThetaPath, Path.symm_range]

private theorem upperTheta_circle02_inside :
    G.upperThetaSystem.circle02.inside = G.lowerAuxiliaryJordanCircle.inside := by
  apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
  rw [G.upperThetaSystem.carrier_circle02, G.carrier_lowerAuxiliaryJordanCircle]
  simp only [upperThetaPath, upperThetaLowerRoute, localRectangleUpperPath,
    Path.trans_range, Path.symm_range]
  ext x
  simp only [Set.mem_union]
  tauto

private theorem upperTheta_circle12_inside :
    G.upperThetaSystem.circle12.inside = G.centralJordanCircle.inside := by
  apply Schoenflies.JordanCircle.inside_eq_of_carrier_eq
  rw [G.upperThetaSystem.carrier_circle12, G.carrier_centralJordanCircle]
  simp only [upperThetaPath, upperThetaLowerRoute, fourPortCentralUpperPath,
    Path.trans_range, Path.symm_range]
  ext x
  simp only [Set.mem_union]
  tauto

/-- Exact upper-theta closed-region trichotomy. -/
theorem upperTheta_exists_outer_cycle_decomposition :
    closure G.topJordanCircle.inside =
        closure G.lowerAuxiliaryJordanCircle.inside ∪
          closure G.centralJordanCircle.inside ∨
      closure G.lowerAuxiliaryJordanCircle.inside =
        closure G.topJordanCircle.inside ∪
          closure G.centralJordanCircle.inside ∨
      closure G.centralJordanCircle.inside =
        closure G.topJordanCircle.inside ∪
          closure G.lowerAuxiliaryJordanCircle.inside := by
  simpa only [G.upperTheta_circle01_inside, G.upperTheta_circle02_inside,
    G.upperTheta_circle12_inside] using
      G.upperThetaSystem.exists_outer_cycle_decomposition

private theorem closedInside_disjoint_outside (J : Schoenflies.JordanCircle) :
    Disjoint (closure J.inside) J.outside := by
  rw [Set.disjoint_left]
  intro x hxClosed hxOutside
  rw [J.closure_inside] at hxClosed
  rcases hxClosed with hxInside | hxCarrier
  · exact Set.disjoint_left.mp J.inside_disjoint_outside hxInside hxOutside
  · exact J.outside_subset_compl hxOutside hxCarrier

private theorem lowerTheta_rectangle_not_outer
    (D : G.RectangleRotationData)
    (houter : closure (G.localRectangleJordanCircle D.rectangle).inside =
      closure G.bottomJordanCircle.inside ∪
        closure G.lowerAuxiliaryJordanCircle.inside) : False := by
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  let x := G.bottomOutside t
  have hxPrivate : x ∈ Set.range G.bottomOutside \ {G.leftBottom, G.rightBottom} := by
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro (hxLeft | hxRight)
    · have ht : t = 1 := G.bottomOutside_injective <| by
        simpa only [x, G.bottomOutside.target] using hxLeft
      have := congrArg Subtype.val ht
      norm_num [t] at this
    · rw [Set.mem_singleton_iff] at hxRight
      have ht : t = 0 := G.bottomOutside_injective <| by
        simpa only [x, G.bottomOutside.source] using hxRight
      have := congrArg Subtype.val ht
      norm_num [t] at this
  have hxOutside := D.bottomOutside_private_subset_outside hxPrivate
  have hxBottomCarrier : x ∈ G.bottomJordanCircle.carrier := by
    rw [G.carrier_bottomJordanCircle]
    exact Or.inr ⟨t, rfl⟩
  have hxBottomClosed : x ∈ closure G.bottomJordanCircle.inside := by
    rw [G.bottomJordanCircle.closure_inside]
    exact Or.inr hxBottomCarrier
  have hxRectangleClosed :
      x ∈ closure (G.localRectangleJordanCircle D.rectangle).inside := by
    rw [houter]
    exact Or.inl hxBottomClosed
  exact Set.disjoint_left.mp
    (closedInside_disjoint_outside (G.localRectangleJordanCircle D.rectangle))
    hxRectangleClosed hxOutside

private theorem leftTop_mem_lowerAuxiliaryCarrier :
    G.leftTop ∈ G.lowerAuxiliaryJordanCircle.carrier := by
  rw [G.carrier_lowerAuxiliaryJordanCircle, localRectangleUpperPath,
    Path.trans_range, Path.trans_range, Path.symm_range]
  exact Or.inr (Or.inl (Or.inl ⟨1, G.left.target⟩))

private theorem leftTop_mem_topCarrier :
    G.leftTop ∈ G.topJordanCircle.carrier := by
  rw [G.carrier_topJordanCircle]
  exact Or.inl ⟨0, G.top.source⟩

private theorem lowerAuxiliary_not_outer_twice
    (D : G.RectangleRotationData)
    (hlower : closure G.lowerAuxiliaryJordanCircle.inside =
      closure G.bottomJordanCircle.inside ∪
        closure (G.localRectangleJordanCircle D.rectangle).inside)
    (hupper : closure G.lowerAuxiliaryJordanCircle.inside =
      closure G.topJordanCircle.inside ∪
        closure G.centralJordanCircle.inside) : False := by
  have hprivateSubset : G.topOutside '' Set.Ioo (0 : unitInterval) 1 ⊆
      closure G.bottomJordanCircle.inside := by
    rintro x ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : t ≠ 1 := ne_of_lt ht.2
    have hxPrivate : G.topOutside t ∈
        Set.range G.topOutside \ {G.leftTop, G.rightTop} := by
      refine ⟨⟨t, rfl⟩, ?_⟩
      rintro (hxLeft | hxRight)
      · have : t = 1 := G.topOutside_injective <| by
          simpa only [G.topOutside.target] using hxLeft
        exact ht1 this
      · rw [Set.mem_singleton_iff] at hxRight
        have : t = 0 := G.topOutside_injective <| by
          simpa only [G.topOutside.source] using hxRight
        exact ht0 this
    have hxOutside := D.topOutside_private_subset_outside hxPrivate
    have hxTopCarrier : G.topOutside t ∈ G.topJordanCircle.carrier := by
      rw [G.carrier_topJordanCircle]
      exact Or.inr ⟨t, rfl⟩
    have hxTopClosed : G.topOutside t ∈ closure G.topJordanCircle.inside := by
      rw [G.topJordanCircle.closure_inside]
      exact Or.inr hxTopCarrier
    have hxAuxiliaryClosed :
        G.topOutside t ∈ closure G.lowerAuxiliaryJordanCircle.inside := by
      rw [hupper]
      exact Or.inl hxTopClosed
    rw [hlower] at hxAuxiliaryClosed
    rcases hxAuxiliaryClosed with hxBottom | hxRectangle
    · exact hxBottom
    · exact False.elim <| Set.disjoint_left.mp
        (closedInside_disjoint_outside
          (G.localRectangleJordanCircle D.rectangle)) hxRectangle hxOutside
  have hdense : Dense (Set.Ioo (0 : unitInterval) 1) := by
    rw [dense_iff_closure_eq, closure_Ioo (by norm_num :
      (0 : unitInterval) ≠ 1)]
    exact Set.Icc_bot_top
  have hleftTopClosure :
      G.leftTop ∈ closure (G.topOutside '' Set.Ioo (0 : unitInterval) 1) := by
    apply G.topOutside.continuous.range_subset_closure_image_dense hdense
    exact ⟨1, G.topOutside.target⟩
  have hleftTopBottomClosed : G.leftTop ∈ closure G.bottomJordanCircle.inside :=
    closure_minimal hprivateSubset isClosed_closure hleftTopClosure
  have hbottomTopDisjoint :
      Disjoint G.bottomJordanCircle.carrier G.topJordanCircle.carrier := by
    rw [G.carrier_bottomJordanCircle, G.carrier_topJordanCircle]
    exact G.bottom_disjoint_top
  have hleftTopNotBottomCarrier : G.leftTop ∉ G.bottomJordanCircle.carrier := by
    exact fun hx ↦ Set.disjoint_left.mp hbottomTopDisjoint hx G.leftTop_mem_topCarrier
  have hbottomSubsetAuxiliary :
      G.bottomJordanCircle.carrier ⊆
        G.lowerAuxiliaryJordanCircle.inside ∪
          G.lowerAuxiliaryJordanCircle.carrier := by
    rw [← G.lowerAuxiliaryJordanCircle.closure_inside, hlower]
    intro x hx
    exact Or.inl <| by
      rw [G.bottomJordanCircle.closure_inside]
      exact Or.inr hx
  have hleftTopBottomOutside : G.leftTop ∈ G.bottomJordanCircle.outside :=
    G.lowerAuxiliaryJordanCircle.carrier_sdiff_subset_outside_of_carrier_subset
      G.bottomJordanCircle hbottomSubsetAuxiliary
      ⟨G.leftTop_mem_lowerAuxiliaryCarrier, hleftTopNotBottomCarrier⟩
  rw [G.bottomJordanCircle.closure_inside] at hleftTopBottomClosed
  rcases hleftTopBottomClosed with hleftTopInside | hleftTopCarrier
  · exact Set.disjoint_left.mp G.bottomJordanCircle.inside_disjoint_outside
      hleftTopInside hleftTopBottomOutside
  · exact hleftTopNotBottomCarrier hleftTopCarrier

private theorem leftTop_mem_rectangleClosed
    (D : G.RectangleRotationData) :
    G.leftTop ∈ closure (G.localRectangleJordanCircle D.rectangle).inside := by
  rw [(G.localRectangleJordanCircle D.rectangle).closure_inside,
    G.carrier_localRectangleJordanCircle, G.localRectangleCarrier_eq]
  exact Or.inr (Or.inl (Or.inl (Or.inl ⟨1, G.left.target⟩)))

private theorem bottomTop_closedDisks_not_disjoint_of_bottom_outer
    (D : G.RectangleRotationData)
    (hbottom : closure G.bottomJordanCircle.inside =
      closure (G.localRectangleJordanCircle D.rectangle).inside ∪
        closure G.lowerAuxiliaryJordanCircle.inside) :
    ¬ Disjoint (closure G.bottomJordanCircle.inside)
      (closure G.topJordanCircle.inside) := by
  intro hdisjoint
  have hleftBottom : G.leftTop ∈ closure G.bottomJordanCircle.inside := by
    rw [hbottom]
    exact Or.inl (G.leftTop_mem_rectangleClosed D)
  have hleftTop : G.leftTop ∈ closure G.topJordanCircle.inside := by
    rw [G.topJordanCircle.closure_inside]
    exact Or.inr G.leftTop_mem_topCarrier
  exact Set.disjoint_left.mp hdisjoint hleftBottom hleftTop

/-- One raw face of the six-edge graph is the outer cycle.  Its closed disk is exactly the union
of the rectangle and the other two raw closed disks. -/
theorem rawFace_exists_outer_cycle_decomposition
    (D : G.RectangleRotationData) :
    closure G.bottomJordanCircle.inside =
        closure (G.localRectangleJordanCircle D.rectangle).inside ∪
          closure G.topJordanCircle.inside ∪ closure G.centralJordanCircle.inside ∨
      closure G.topJordanCircle.inside =
        closure (G.localRectangleJordanCircle D.rectangle).inside ∪
          closure G.bottomJordanCircle.inside ∪ closure G.centralJordanCircle.inside ∨
      closure G.centralJordanCircle.inside =
        closure (G.localRectangleJordanCircle D.rectangle).inside ∪
          closure G.bottomJordanCircle.inside ∪ closure G.topJordanCircle.inside := by
  let Bc := closure G.bottomJordanCircle.inside
  let Rc := closure (G.localRectangleJordanCircle D.rectangle).inside
  let Ac := closure G.lowerAuxiliaryJordanCircle.inside
  let Tc := closure G.topJordanCircle.inside
  let Cc := closure G.centralJordanCircle.inside
  change Bc = Rc ∪ Tc ∪ Cc ∨ Tc = Rc ∪ Bc ∪ Cc ∨ Cc = Rc ∪ Bc ∪ Tc
  have hlower := G.lowerTheta_exists_outer_cycle_decomposition
  change Bc = Rc ∪ Ac ∨ Rc = Bc ∪ Ac ∨ Ac = Bc ∪ Rc at hlower
  have hupper := G.upperTheta_exists_outer_cycle_decomposition
  change Tc = Ac ∪ Cc ∨ Ac = Tc ∪ Cc ∨ Cc = Tc ∪ Ac at hupper
  rcases hlower with hbottom | hrectangle | hauxiliary
  · have hcases := G.bottomJordanCircle.disjoint_or_nested_closure_inside
        G.topJordanCircle (by
          rw [G.carrier_bottomJordanCircle, G.carrier_topJordanCircle]
          exact G.bottom_disjoint_top)
    rcases hcases with hdisjoint | hbottomInTop | htopInBottom
    · exact False.elim <| G.bottomTop_closedDisks_not_disjoint_of_bottom_outer
        D hbottom hdisjoint
    · have hbottomClosedInTop : Bc ⊆ Tc :=
        hbottomInTop.trans subset_closure
      rcases hupper with htop | hauxiliaryUpper | hcentral
      · right; left
        apply Set.Subset.antisymm
        · intro x hx
          rw [htop] at hx
          rcases hx with hxAuxiliary | hxCentral
          · exact Or.inl <| Or.inr <| by
              rw [hbottom]
              exact Or.inr hxAuxiliary
          · exact Or.inr hxCentral
        · rintro x ((hxRectangle | hxBottom) | hxCentral)
          · exact hbottomClosedInTop <| by rw [hbottom]; exact Or.inl hxRectangle
          · exact hbottomClosedInTop hxBottom
          · rw [htop]; exact Or.inr hxCentral
      · left
        rw [hbottom, hauxiliaryUpper]
        ac_rfl
      · right; right
        apply Set.Subset.antisymm
        · intro x hx
          rw [hcentral] at hx
          rcases hx with hxTop | hxAuxiliary
          · exact Or.inr hxTop
          · exact Or.inl <| Or.inr <| by rw [hbottom]; exact Or.inr hxAuxiliary
        · rintro x ((hxRectangle | hxBottom) | hxTop)
          · rw [hcentral]
            exact Or.inl <| hbottomClosedInTop <| by
              rw [hbottom]
              exact Or.inl hxRectangle
          · rw [hcentral]
            exact Or.inl (hbottomClosedInTop hxBottom)
          · rw [hcentral]
            exact Or.inl hxTop
    · have htopClosedInBottom : Tc ⊆ Bc :=
        htopInBottom.trans subset_closure
      rcases hupper with htop | hauxiliaryUpper | hcentral
      · left
        apply Set.Subset.antisymm
        · intro x hx
          rw [hbottom] at hx
          rcases hx with hxRectangle | hxAuxiliary
          · exact Or.inl (Or.inl hxRectangle)
          · exact Or.inl (Or.inr <| by rw [htop]; exact Or.inl hxAuxiliary)
        · rintro x ((hxRectangle | hxTop) | hxCentral)
          · rw [hbottom]; exact Or.inl hxRectangle
          · exact htopClosedInBottom hxTop
          · exact htopClosedInBottom <| by rw [htop]; exact Or.inr hxCentral
      · left
        rw [hbottom, hauxiliaryUpper]
        ac_rfl
      · left
        apply Set.Subset.antisymm
        · intro x hx
          rw [hbottom] at hx
          rcases hx with hxRectangle | hxAuxiliary
          · exact Or.inl (Or.inl hxRectangle)
          · exact Or.inr <| by rw [hcentral]; exact Or.inr hxAuxiliary
        · rintro x ((hxRectangle | hxTop) | hxCentral)
          · rw [hbottom]; exact Or.inl hxRectangle
          · exact htopClosedInBottom hxTop
          · rw [hcentral] at hxCentral
            rcases hxCentral with hxTop | hxAuxiliary
            · exact htopClosedInBottom hxTop
            · rw [hbottom]; exact Or.inr hxAuxiliary
  · exact False.elim <| G.lowerTheta_rectangle_not_outer D hrectangle
  · rcases hupper with htop | hauxiliaryUpper | hcentral
    · right; left
      rw [htop, hauxiliary]
      ac_rfl
    · exact False.elim <| G.lowerAuxiliary_not_outer_twice
        D hauxiliary hauxiliaryUpper
    · right; right
      rw [hcentral, hauxiliary]
      ac_rfl

end FourPortSixEdgePathSystem

end Submission.Topology
