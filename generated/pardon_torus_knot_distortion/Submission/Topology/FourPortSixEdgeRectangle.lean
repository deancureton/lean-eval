import Submission.Topology.FourPortSixEdgeFaces

/-!
# The fourth cycle of an honest six-edge four-port graph

The three raw-circle embedding and incidence conditions already force the four local edges to form
an embedded rectangle.  Thus the planar coherent lift needs no additional local-chart premise
to obtain its fourth Jordan circle.
-/

open Set Topology

noncomputable section

namespace Submission.Topology

variable {X : Type*} [TopologicalSpace X]
  (G : FourPortSixEdgePathSystem X)

namespace FourPortSixEdgePathSystem

theorem range_left_inter_right :
    Set.range G.left ∩ Set.range G.right = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hroute :
        fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.firstCoordinate s) =
          fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t)) := by
      rw [fourPortCentralUpperPath,
        Schoenflies.ThreePiecePath.trans_trans_firstCoordinate,
        Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
      simpa only [Path.symm_apply, Function.comp_apply,
        unitInterval.symm_symm] using hs.trans ht.symm
    have hcoordinate := G.centralData.first_injective hroute
    have hvalue := congrArg Subtype.val hcoordinate
    dsimp only [Schoenflies.ThreePiecePath.firstCoordinate,
      Schoenflies.ThreePiecePath.thirdCoordinate, unitInterval.symm] at hvalue
    nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]
  · intro hx
    exact hx.elim

theorem range_left_inter_top :
    Set.range G.left ∩ Set.range G.top = {G.leftTop} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxLeft, hxTop⟩
    have hxCentral : x ∈ Set.range G.centralCircle := by
      rw [G.range_centralCircle]
      left
      obtain ⟨s, rfl⟩ := hxLeft
      exact ⟨Schoenflies.ThreePiecePath.firstCoordinate s,
        Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ s⟩
    have hxTopCircle : x ∈ Set.range G.topCircle := by
      rw [G.range_topCircle]
      exact Or.inl hxTop
    have hxOutside : x ∈ Set.range G.topOutside := by
      rw [← G.centralCircle_inter_topCircle]
      exact ⟨hxCentral, hxTopCircle⟩
    have hxEnds : x ∈ ({G.leftTop, G.rightTop} : Set X) := by
      rw [← G.topData.range_inter]
      exact ⟨hxTop, hxOutside⟩
    rcases hxEnds with hx | hx
    · exact Set.mem_singleton_iff.mpr hx
    · obtain ⟨s, hs⟩ := hxLeft
      have hx' : x = G.rightTop := Set.mem_singleton_iff.mp hx
      have hroute :
          fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.firstCoordinate s) =
            fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.middleCoordinate 1) := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_firstCoordinate,
          Schoenflies.ThreePiecePath.trans_trans_middleCoordinate]
        calc
          G.left s = x := hs
          _ = G.rightTop := hx'
          _ = G.topOutside.symm 1 := (G.topOutside.symm.target).symm
      have hcoordinate := G.centralData.first_injective hroute
      have hvalue := congrArg Subtype.val hcoordinate
      dsimp only [Schoenflies.ThreePiecePath.firstCoordinate,
        Schoenflies.ThreePiecePath.middleCoordinate] at hvalue
      norm_num at hvalue
      nlinarith [s.2.1, s.2.2]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, G.left.target⟩, ⟨0, G.top.source⟩⟩

theorem range_top_inter_right :
    Set.range G.top ∩ Set.range G.right = {G.rightTop} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxTop, hxRight⟩
    have hxCentral : x ∈ Set.range G.centralCircle := by
      rw [G.range_centralCircle]
      left
      obtain ⟨t, rfl⟩ := hxRight
      refine ⟨Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t), ?_⟩
      rw [fourPortCentralUpperPath,
        Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
      simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
    have hxTopCircle : x ∈ Set.range G.topCircle := by
      rw [G.range_topCircle]
      exact Or.inl hxTop
    have hxOutside : x ∈ Set.range G.topOutside := by
      rw [← G.centralCircle_inter_topCircle]
      exact ⟨hxCentral, hxTopCircle⟩
    have hxEnds : x ∈ ({G.leftTop, G.rightTop} : Set X) := by
      rw [← G.topData.range_inter]
      exact ⟨hxTop, hxOutside⟩
    rcases hxEnds with hx | hx
    · obtain ⟨t, ht⟩ := hxRight
      have hroute :
          fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.middleCoordinate 0) =
            fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t)) := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_middleCoordinate,
          Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
        calc
          G.topOutside.symm 0 = G.leftTop := G.topOutside.symm.source
          _ = x := hx.symm
          _ = G.right t := ht.symm
          _ = G.right.symm (unitInterval.symm t) := by
            simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
      have hcoordinate := G.centralData.first_injective hroute
      have hvalue := congrArg Subtype.val hcoordinate
      dsimp only [Schoenflies.ThreePiecePath.middleCoordinate,
        Schoenflies.ThreePiecePath.thirdCoordinate, unitInterval.symm] at hvalue
      norm_num at hvalue
      nlinarith [t.2.1, t.2.2]
    · exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp hx)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, G.top.target⟩, ⟨1, G.right.target⟩⟩

private theorem range_left_inter_bottom :
    Set.range G.left ∩ Set.range G.bottom = {G.leftBottom} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxLeft, hxBottom⟩
    have hxCentral : x ∈ Set.range G.centralCircle := by
      rw [G.range_centralCircle]
      left
      obtain ⟨s, rfl⟩ := hxLeft
      exact ⟨Schoenflies.ThreePiecePath.firstCoordinate s,
        Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ s⟩
    have hxBottomCircle : x ∈ Set.range G.bottomCircle := by
      rw [G.range_bottomCircle]
      exact Or.inl hxBottom
    have hxOutside : x ∈ Set.range G.bottomOutside := by
      rw [← G.centralCircle_inter_bottomCircle]
      exact ⟨hxCentral, hxBottomCircle⟩
    have hxEnds : x ∈ ({G.leftBottom, G.rightBottom} : Set X) := by
      rw [← G.bottomData.range_inter]
      exact ⟨hxBottom, hxOutside⟩
    rcases hxEnds with hx | hx
    · exact Set.mem_singleton_iff.mpr hx
    · obtain ⟨s, hs⟩ := hxLeft
      have hx' : x = G.rightBottom := Set.mem_singleton_iff.mp hx
      have hroute :
          fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.firstCoordinate s) =
            fourPortCentralUpperPath G.left G.topOutside G.right 1 := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_firstCoordinate]
        calc
          G.left s = x := hs
          _ = G.rightBottom := hx'
          _ = ((G.left.trans G.topOutside.symm).trans G.right.symm) 1 :=
            ((G.left.trans G.topOutside.symm).trans G.right.symm).target.symm
      have hcoordinate := G.centralData.first_injective hroute
      have hvalue := congrArg Subtype.val hcoordinate
      dsimp only [Schoenflies.ThreePiecePath.firstCoordinate] at hvalue
      norm_num at hvalue
      nlinarith [s.2.1, s.2.2]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, G.left.source⟩, ⟨0, G.bottom.source⟩⟩

private theorem range_right_inter_bottom :
    Set.range G.right ∩ Set.range G.bottom = {G.rightBottom} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxRight, hxBottom⟩
    have hxCentral : x ∈ Set.range G.centralCircle := by
      rw [G.range_centralCircle]
      left
      obtain ⟨t, rfl⟩ := hxRight
      refine ⟨Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t), ?_⟩
      rw [fourPortCentralUpperPath,
        Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
      simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
    have hxBottomCircle : x ∈ Set.range G.bottomCircle := by
      rw [G.range_bottomCircle]
      exact Or.inl hxBottom
    have hxOutside : x ∈ Set.range G.bottomOutside := by
      rw [← G.centralCircle_inter_bottomCircle]
      exact ⟨hxCentral, hxBottomCircle⟩
    have hxEnds : x ∈ ({G.leftBottom, G.rightBottom} : Set X) := by
      rw [← G.bottomData.range_inter]
      exact ⟨hxBottom, hxOutside⟩
    rcases hxEnds with hx | hx
    · obtain ⟨t, ht⟩ := hxRight
      have hroute :
          fourPortCentralUpperPath G.left G.topOutside G.right 0 =
            fourPortCentralUpperPath G.left G.topOutside G.right
              (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t)) := by
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
        calc
          ((G.left.trans G.topOutside.symm).trans G.right.symm) 0 =
              G.leftBottom :=
            ((G.left.trans G.topOutside.symm).trans G.right.symm).source
          _ = x := hx.symm
          _ = G.right t := ht.symm
          _ = G.right.symm (unitInterval.symm t) := by
            simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
      have hcoordinate := G.centralData.first_injective hroute
      have hvalue := congrArg Subtype.val hcoordinate
      dsimp only [Schoenflies.ThreePiecePath.thirdCoordinate,
        unitInterval.symm] at hvalue
      norm_num at hvalue
      nlinarith [t.2.1, t.2.2]
    · exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp hx)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, G.right.source⟩, ⟨1, G.bottom.target⟩⟩

theorem range_top_inter_bottom :
    Set.range G.top ∩ Set.range G.bottom = ∅ := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  exact G.bottom_disjoint_top.symm.mono Set.subset_union_left Set.subset_union_left

/-- Every honest six-edge four-port graph has an embedded fourth rectangle cycle. -/
theorem localRectangleData : G.LocalRectangleData where
  twoArcData := {
    first_injective := by
      have hleftTop : Function.Injective (G.left.trans G.top) :=
        LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
          G.left G.top G.left_injective G.top_injective G.range_left_inter_top
      apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
        (G.left.trans G.top) G.right.symm hleftTop
      · intro s t hst
        apply unitInterval.symm_bijective.injective
        apply G.right_injective
        simpa only [Path.symm_apply, Function.comp_apply] using hst
      · rw [Path.trans_range, Path.symm_range, Set.union_inter_distrib_right,
          G.range_left_inter_right, G.range_top_inter_right, Set.empty_union]
    second_injective := by
      intro s t hst
      apply unitInterval.symm_bijective.injective
      apply G.bottom_injective
      simpa only [Path.symm_apply, Function.comp_apply] using hst
    range_inter := by
      rw [localRectangleUpperPath, Path.trans_range, Path.trans_range]
      simp only [Path.symm_range]
      rw [
        Set.union_inter_distrib_right, Set.union_inter_distrib_right,
        G.range_left_inter_bottom, G.range_top_inter_bottom,
        G.range_right_inter_bottom, Set.union_empty]
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  }

theorem range_left_inter_topOutside :
    Set.range G.left ∩ Set.range G.topOutside = {G.leftTop} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hroute :
        fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.firstCoordinate s) =
          fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.middleCoordinate (unitInterval.symm t)) := by
      rw [fourPortCentralUpperPath,
        Schoenflies.ThreePiecePath.trans_trans_firstCoordinate,
        Schoenflies.ThreePiecePath.trans_trans_middleCoordinate]
      simpa only [Path.symm_apply, Function.comp_apply,
        unitInterval.symm_symm] using hs.trans ht.symm
    have hcoordinate := G.centralData.first_injective hroute
    have hvalue := congrArg Subtype.val hcoordinate
    dsimp only [Schoenflies.ThreePiecePath.firstCoordinate,
      Schoenflies.ThreePiecePath.middleCoordinate, unitInterval.symm] at hvalue
    have hsOne : s = 1 := by
      apply Subtype.ext
      dsimp
      nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans G.left.target)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, G.left.target⟩, ⟨1, G.topOutside.target⟩⟩

theorem range_topOutside_inter_right :
    Set.range G.topOutside ∩ Set.range G.right = {G.rightTop} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hroute :
        fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.middleCoordinate (unitInterval.symm s)) =
          fourPortCentralUpperPath G.left G.topOutside G.right
            (Schoenflies.ThreePiecePath.thirdCoordinate (unitInterval.symm t)) := by
      rw [fourPortCentralUpperPath,
        Schoenflies.ThreePiecePath.trans_trans_middleCoordinate,
        Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
      simpa only [Path.symm_apply, Function.comp_apply,
        unitInterval.symm_symm] using hs.trans ht.symm
    have hcoordinate := G.centralData.first_injective hroute
    have hvalue := congrArg Subtype.val hcoordinate
    dsimp only [Schoenflies.ThreePiecePath.middleCoordinate,
      Schoenflies.ThreePiecePath.thirdCoordinate, unitInterval.symm] at hvalue
    have hsZero : s = 0 := by
      apply Subtype.ext
      dsimp
      nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]
    subst s
    exact Set.mem_singleton_iff.mpr (hs.symm.trans G.topOutside.source)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, G.topOutside.source⟩, ⟨1, G.right.target⟩⟩

/-- The lower outside arc meets the local rectangle only at its two ports. -/
theorem bottomOutside_inter_localRectangleCarrier :
    Set.range G.bottomOutside ∩ G.localRectangleCarrier =
      {G.leftBottom, G.rightBottom} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxOutside, hxRectangle⟩
    rw [G.localRectangleCarrier_eq] at hxRectangle
    rcases hxRectangle with ((hxLeft | hxTop) | hxRight) | hxBottom
    · have hxUpper : x ∈ Set.range
          (fourPortCentralUpperPath G.left G.topOutside G.right) := by
        obtain ⟨s, rfl⟩ := hxLeft
        exact ⟨Schoenflies.ThreePiecePath.firstCoordinate s,
          Schoenflies.ThreePiecePath.trans_trans_firstCoordinate _ _ _ s⟩
      rw [← G.centralData.range_inter]
      exact ⟨hxUpper, hxOutside⟩
    · have hxBottomCircle : x ∈ Set.range G.bottomCircle := by
        rw [G.range_bottomCircle]
        exact Or.inr hxOutside
      have hxTopCircle : x ∈ Set.range G.topCircle := by
        rw [G.range_topCircle]
        exact Or.inl hxTop
      exact False.elim <|
        Set.disjoint_left.mp G.bottomCircle_disjoint_topCircle
          hxBottomCircle hxTopCircle
    · have hxUpper : x ∈ Set.range
          (fourPortCentralUpperPath G.left G.topOutside G.right) := by
        obtain ⟨t, rfl⟩ := hxRight
        refine ⟨Schoenflies.ThreePiecePath.thirdCoordinate
          (unitInterval.symm t), ?_⟩
        rw [fourPortCentralUpperPath,
          Schoenflies.ThreePiecePath.trans_trans_thirdCoordinate]
        simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
      rw [← G.centralData.range_inter]
      exact ⟨hxUpper, hxOutside⟩
    · rw [← G.bottomData.range_inter]
      exact ⟨hxBottom, hxOutside⟩
  · intro x hx
    rcases hx with hx | hx
    · subst x
      refine ⟨⟨1, G.bottomOutside.target⟩, ?_⟩
      rw [G.localRectangleCarrier_eq]
      exact Or.inr ⟨0, G.bottom.source⟩
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨⟨0, G.bottomOutside.source⟩, ?_⟩
      rw [G.localRectangleCarrier_eq]
      exact Or.inr ⟨1, G.bottom.target⟩

/-- The upper outside arc meets the local rectangle only at its two ports. -/
theorem topOutside_inter_localRectangleCarrier :
    Set.range G.topOutside ∩ G.localRectangleCarrier =
      {G.leftTop, G.rightTop} := by
  rw [G.localRectangleCarrier_eq, Set.inter_union_distrib_left,
    Set.inter_union_distrib_left, Set.inter_union_distrib_left]
  have hleft : Set.range G.topOutside ∩ Set.range G.left = {G.leftTop} := by
    rw [Set.inter_comm]
    exact G.range_left_inter_topOutside
  have htop : Set.range G.topOutside ∩ Set.range G.top =
      {G.leftTop, G.rightTop} := by
    rw [Set.inter_comm]
    exact G.topData.range_inter
  have hright : Set.range G.topOutside ∩ Set.range G.right = {G.rightTop} :=
    G.range_topOutside_inter_right
  have hbottom : Set.range G.topOutside ∩ Set.range G.bottom = ∅ := by
    apply Set.disjoint_iff_inter_eq_empty.mp
    exact G.bottomCircle_disjoint_topCircle.symm.mono
      (by rw [G.range_topCircle]; exact Set.subset_union_right)
      (by rw [G.range_bottomCircle]; exact Set.subset_union_left)
  rw [hleft, htop, hright, hbottom, Set.union_empty]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

private theorem path_private_preconnected
    {a b : X} (p : Path a b) (hp : Function.Injective p) :
    IsPreconnected (Set.range p \ ({a, b} : Set X)) := by
  have hrange : Set.range p \ ({a, b} : Set X) =
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
      · exact (ne_of_gt ht.1) (hp <| ha.trans p.source.symm)
      · exact (ne_of_lt ht.2) (hp <| hb.trans p.target.symm)
  rw [hrange]
  exact isPreconnected_Ioo.image p p.continuous.continuousOn

end FourPortSixEdgePathSystem

namespace FourPortSixEdgePathSystem

variable (P : FourPortSixEdgePathSystem Schoenflies.Plane)

/-- The private lower outside arc lies wholly on one side of the rectangle Jordan circle. -/
theorem bottomOutside_private_side :
    Set.range P.bottomOutside \ {P.leftBottom, P.rightBottom} ⊆
        (P.localRectangleJordanCircle P.localRectangleData).inside ∨
      Set.range P.bottomOutside \ {P.leftBottom, P.rightBottom} ⊆
        (P.localRectangleJordanCircle P.localRectangleData).outside := by
  have hside :=
    (path_private_preconnected P.bottomOutside P.bottomOutside_injective).subset_or_subset
      (P.localRectangleJordanCircle P.localRectangleData).inside_isOpen
      (P.localRectangleJordanCircle P.localRectangleData).outside_isOpen
      (P.localRectangleJordanCircle P.localRectangleData).inside_disjoint_outside
      (by
        rw [(P.localRectangleJordanCircle P.localRectangleData).inside_union_outside]
        rintro x ⟨hxPath, hxEnds⟩ hxCarrier
        apply hxEnds
        have hxInter : x ∈ Set.range P.bottomOutside ∩
            P.localRectangleCarrier := by
          refine ⟨hxPath, ?_⟩
          rwa [P.carrier_localRectangleJordanCircle] at hxCarrier
        rw [P.bottomOutside_inter_localRectangleCarrier] at hxInter
        simpa only [Set.pair_comm] using hxInter)
  simpa only [Set.pair_comm] using hside

/-- The private upper outside arc lies wholly on one side of the rectangle Jordan circle. -/
theorem topOutside_private_side :
    Set.range P.topOutside \ {P.leftTop, P.rightTop} ⊆
        (P.localRectangleJordanCircle P.localRectangleData).inside ∨
      Set.range P.topOutside \ {P.leftTop, P.rightTop} ⊆
        (P.localRectangleJordanCircle P.localRectangleData).outside := by
  have hside :=
    (path_private_preconnected P.topOutside P.topOutside_injective).subset_or_subset
      (P.localRectangleJordanCircle P.localRectangleData).inside_isOpen
      (P.localRectangleJordanCircle P.localRectangleData).outside_isOpen
      (P.localRectangleJordanCircle P.localRectangleData).inside_disjoint_outside
      (by
        rw [(P.localRectangleJordanCircle P.localRectangleData).inside_union_outside]
        rintro x ⟨hxPath, hxEnds⟩ hxCarrier
        apply hxEnds
        have hxInter : x ∈ Set.range P.topOutside ∩
            P.localRectangleCarrier := by
          refine ⟨hxPath, ?_⟩
          rwa [P.carrier_localRectangleJordanCircle] at hxCarrier
        rw [P.topOutside_inter_localRectangleCarrier] at hxInter
        simpa only [Set.pair_comm] using hxInter)
  simpa only [Set.pair_comm] using hside

/-- One exterior witness on each private outside arc determines the full rectangle rotation.

All endpoint incidence is already forced by the honest six-edge graph, so callers need only
locate one private point of each outside arc on the unbounded side of the local rectangle. -/
theorem rectangleRotationData_of_private_outside
    (hbottom :
      ((Set.range P.bottomOutside \ {P.leftBottom, P.rightBottom}) ∩
        (P.localRectangleJordanCircle P.localRectangleData).outside).Nonempty)
    (htop :
      ((Set.range P.topOutside \ {P.leftTop, P.rightTop}) ∩
        (P.localRectangleJordanCircle P.localRectangleData).outside).Nonempty) :
    P.RectangleRotationData := by
  let W : P.RectangleRotationWitnessData := {
    rectangle := P.localRectangleData
    bottomOutside_inter_rectangle := by
      rw [P.carrier_localRectangleJordanCircle]
      exact P.bottomOutside_inter_localRectangleCarrier
    topOutside_inter_rectangle := by
      rw [P.carrier_localRectangleJordanCircle]
      exact P.topOutside_inter_localRectangleCarrier
    bottomOutside_private_point := hbottom
    topOutside_private_point := htop
  }
  exact W.toRectangleRotationData

end FourPortSixEdgePathSystem

open LeanEval.KnotTheory.PardonDistortion
open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}
  {T : FourPortSixEdgePathSystem (transportedTorus Phi)}

namespace FourPortSixEdgeZeroWindingData

/-- The coherent universal-cover lift has its fourth planar Jordan cycle unconditionally. -/
theorem planeLocalRectangleData (Z : FourPortSixEdgeZeroWindingData T) :
    Z.planePathSystem.LocalRectangleData :=
  Z.planePathSystem.localRectangleData

end FourPortSixEdgeZeroWindingData
end Submission.Topology
