import Submission.PlaneSchoenflies.Schoenflies.JordanTwoCellAmbientExtension
import Submission.PlaneSchoenflies.Schoenflies.TwoArcCarrierHomeomorph
import Submission.Topology.TwoArcCircle

/-!
# Ambient extension between filled Jordan theta presentations

Three injective arcs with common endpoints determine two cells sharing the first arc and one
outer cycle made from the other two arcs.  When the two closed cells fill that outer disk, the
canonical carrier correspondences glue and extend to an ambient homeomorphism which preserves
the unit-interval parameter on all three arcs.
-/

namespace Schoenflies

open Function Set

noncomputable section

namespace JordanThetaAmbientExtension

/-- Disjoint Jordan interiors can meet after closure only where their carriers meet. -/
theorem closure_inside_inter_eq_of_disjoint_inside_of_carrier_inter
    (J K : JordanCircle) {sharedCarrier : Set Plane}
    (hinside : Disjoint J.inside K.inside)
    (hcarrier : J.carrier ∩ K.carrier = sharedCarrier) :
    closure J.inside ∩ closure K.inside = sharedCarrier := by
  have hinsideCarrier : Disjoint J.inside K.carrier := by
    rw [Set.disjoint_left]
    intro x hxInside hxCarrier
    have hxClosure : x ∈ closure K.inside := by
      rw [K.closure_inside]
      exact Or.inr hxCarrier
    have hxInterClosure : x ∈ closure (J.inside ∩ K.inside) :=
      J.inside_isOpen.inter_closure ⟨hxInside, hxClosure⟩
    obtain ⟨y, hyJ, hyK⟩ := Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact Set.disjoint_left.mp hinside hyJ hyK
  have hcarrierInside : Disjoint J.carrier K.inside := by
    rw [Set.disjoint_left]
    intro x hxCarrier hxInside
    have hxClosure : x ∈ closure J.inside := by
      rw [J.closure_inside]
      exact Or.inr hxCarrier
    have hxInterClosure : x ∈ closure (K.inside ∩ J.inside) :=
      K.inside_isOpen.inter_closure ⟨hxInside, hxClosure⟩
    obtain ⟨y, hyK, hyJ⟩ := Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact Set.disjoint_left.mp hinside hyJ hyK
  apply Set.Subset.antisymm
  · rintro x ⟨hxJ, hxK⟩
    rw [J.closure_inside] at hxJ
    rw [K.closure_inside] at hxK
    rcases hxJ with hxInsideJ | hxCarrierJ <;>
      rcases hxK with hxInsideK | hxCarrierK
    · exact (Set.disjoint_left.mp hinside hxInsideJ hxInsideK).elim
    · exact (Set.disjoint_left.mp hinsideCarrier hxInsideJ hxCarrierK).elim
    · exact (Set.disjoint_left.mp hcarrierInside hxCarrierJ hxInsideK).elim
    · rw [← hcarrier]
      exact ⟨hxCarrierJ, hxCarrierK⟩
  · intro x hx
    have hxCarriers : x ∈ J.carrier ∩ K.carrier := by
      rw [hcarrier]
      exact hx
    constructor
    · rw [J.closure_inside]
      exact Or.inr hxCarriers.1
    · rw [K.closure_inside]
      exact Or.inr hxCarriers.2

/-- A parametrized Jordan theta graph together with its exact two-cell region decomposition. -/
structure Presentation where
  source : Plane
  target : Plane
  shared : Path source target
  lowerReturn : Path target source
  upperReturn : Path target source
  lowerData : Submission.Topology.TwoArcCircle.Data shared lowerReturn
  upperData : Submission.Topology.TwoArcCircle.Data shared upperReturn
  outerData : Submission.Topology.TwoArcCircle.Data lowerReturn.symm upperReturn
  closed_inter :
    closure
          (TwoArcJordan.toJordanCircle shared lowerReturn lowerData.first_injective
            lowerData.second_injective lowerData.range_inter).inside ∩
        closure
          (TwoArcJordan.toJordanCircle shared upperReturn upperData.first_injective
            upperData.second_injective upperData.range_inter).inside =
      range shared
  closed_union :
    closure
          (TwoArcJordan.toJordanCircle shared lowerReturn lowerData.first_injective
            lowerData.second_injective lowerData.range_inter).inside ∪
        closure
          (TwoArcJordan.toJordanCircle shared upperReturn upperData.first_injective
            upperData.second_injective upperData.range_inter).inside =
      closure
        (TwoArcJordan.toJordanCircle lowerReturn.symm upperReturn outerData.first_injective
          outerData.second_injective outerData.range_inter).inside

namespace Presentation

variable (P : Presentation)

/-- The lower cycle, consisting of the shared edge and the lower return edge. -/
def lowerCircle : JordanCircle :=
  TwoArcJordan.toJordanCircle P.shared P.lowerReturn P.lowerData.first_injective
    P.lowerData.second_injective P.lowerData.range_inter

/-- The upper cycle, consisting of the shared edge and the upper return edge. -/
def upperCircle : JordanCircle :=
  TwoArcJordan.toJordanCircle P.shared P.upperReturn P.upperData.first_injective
    P.upperData.second_injective P.upperData.range_inter

/-- The outer cycle, consisting of the two return edges. -/
def outerCircle : JordanCircle :=
  TwoArcJordan.toJordanCircle P.lowerReturn.symm P.upperReturn P.outerData.first_injective
    P.outerData.second_injective P.outerData.range_inter

@[simp] theorem lowerCircle_carrier :
    P.lowerCircle.carrier = range P.shared ∪ range P.lowerReturn := by
  exact TwoArcJordan.carrier_toJordanCircle _ _ _ _ _

@[simp] theorem upperCircle_carrier :
    P.upperCircle.carrier = range P.shared ∪ range P.upperReturn := by
  exact TwoArcJordan.carrier_toJordanCircle _ _ _ _ _

@[simp] theorem outerCircle_carrier :
    P.outerCircle.carrier = range P.lowerReturn ∪ range P.upperReturn := by
  rw [outerCircle, TwoArcJordan.carrier_toJordanCircle, Path.symm_range]

/-- The theta graph as the two closed Jordan cells used by the gluing theorem. -/
def toTwoCellPresentation : JordanTwoCellBoundaryExtension.Presentation where
  lower := P.lowerCircle
  upper := P.upperCircle
  startPoint := P.source
  endPoint := P.target
  shared := P.shared
  shared_lower := by
    rw [P.lowerCircle_carrier]
    exact Set.subset_union_left
  shared_upper := by
    rw [P.upperCircle_carrier]
    exact Set.subset_union_left
  closed_inter := P.closed_inter

/-- The filled theta graph as one outer Jordan disk. -/
def toAmbientPresentation : JordanTwoCellAmbientExtension.Presentation where
  toPresentation := P.toTwoCellPresentation
  outer := P.outerCircle
  closed_union := P.closed_union

end Presentation

variable (P Q : Presentation)

private theorem return_union_symm :
    range P.lowerReturn ∪ range P.upperReturn =
      range P.lowerReturn.symm ∪ range P.upperReturn := by
  rw [Path.symm_range]

private theorem coe_setCongr_apply {s t : Set Plane} (h : s = t) (z : s) :
    ((Homeomorph.setCongr h z : t) : Plane) = z := by
  subst t
  rfl

private def rawLowerBoundary :
    (range P.shared ∪ range P.lowerReturn : Set Plane) ≃ₜ
      (range Q.shared ∪ range Q.lowerReturn : Set Plane) :=
  TwoArcJordan.carrierCorrespondence P.shared P.lowerReturn
    P.lowerData.first_injective P.lowerData.second_injective P.lowerData.range_inter
    Q.shared Q.lowerReturn Q.lowerData.first_injective Q.lowerData.second_injective
    Q.lowerData.range_inter

private def rawUpperBoundary :
    (range P.shared ∪ range P.upperReturn : Set Plane) ≃ₜ
      (range Q.shared ∪ range Q.upperReturn : Set Plane) :=
  TwoArcJordan.carrierCorrespondence P.shared P.upperReturn
    P.upperData.first_injective P.upperData.second_injective P.upperData.range_inter
    Q.shared Q.upperReturn Q.upperData.first_injective Q.upperData.second_injective
    Q.upperData.range_inter

private def rawOuterBoundaryCore :
    (range P.lowerReturn.symm ∪ range P.upperReturn : Set Plane) ≃ₜ
      (range Q.lowerReturn.symm ∪ range Q.upperReturn : Set Plane) :=
  TwoArcJordan.carrierCorrespondence P.lowerReturn.symm P.upperReturn
    P.outerData.first_injective P.outerData.second_injective P.outerData.range_inter
    Q.lowerReturn.symm Q.upperReturn Q.outerData.first_injective
    Q.outerData.second_injective Q.outerData.range_inter

private def rawOuterBoundary :
    (range P.lowerReturn ∪ range P.upperReturn : Set Plane) ≃ₜ
      (range Q.lowerReturn ∪ range Q.upperReturn : Set Plane) :=
  (Homeomorph.setCongr (return_union_symm P)).trans <|
    (rawOuterBoundaryCore P Q).trans (Homeomorph.setCongr (return_union_symm Q).symm)

private theorem coe_rawOuterBoundary_apply
    (z : (range P.lowerReturn ∪ range P.upperReturn : Set Plane)) :
    ((rawOuterBoundary P Q z : _) : Plane) =
      (rawOuterBoundaryCore P Q (Homeomorph.setCongr (return_union_symm P) z) : Plane) := by
  rw [rawOuterBoundary, Homeomorph.trans_apply, Homeomorph.trans_apply]
  exact coe_setCongr_apply _ _

/-- Canonical lower-boundary correspondence, preserving both edge parameters. -/
def lowerBoundary : P.lowerCircle.carrier ≃ₜ Q.lowerCircle.carrier :=
  (Homeomorph.setCongr P.lowerCircle_carrier).trans <|
    (rawLowerBoundary P Q).trans (Homeomorph.setCongr Q.lowerCircle_carrier.symm)

/-- Canonical upper-boundary correspondence, preserving both edge parameters. -/
def upperBoundary : P.upperCircle.carrier ≃ₜ Q.upperCircle.carrier :=
  (Homeomorph.setCongr P.upperCircle_carrier).trans <|
    (rawUpperBoundary P Q).trans (Homeomorph.setCongr Q.upperCircle_carrier.symm)

/-- Canonical outer-boundary correspondence, preserving both return-edge parameters. -/
def outerBoundary : P.outerCircle.carrier ≃ₜ Q.outerCircle.carrier :=
  (Homeomorph.setCongr P.outerCircle_carrier).trans <|
    (rawOuterBoundary P Q).trans (Homeomorph.setCongr Q.outerCircle_carrier.symm)

theorem lowerBoundary_shared (t : unitInterval) :
    lowerBoundary P Q
        ⟨P.shared t, by rw [P.lowerCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ =
      ⟨Q.shared t, by rw [Q.lowerCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change ((rawLowerBoundary P Q) ⟨P.shared t, Or.inl ⟨t, rfl⟩⟩ : Plane) = _
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_first _ _ _ _ _ _ _ _ _ _ t

theorem upperBoundary_shared (t : unitInterval) :
    upperBoundary P Q
        ⟨P.shared t, by rw [P.upperCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ =
      ⟨Q.shared t, by rw [Q.upperCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change ((rawUpperBoundary P Q) ⟨P.shared t, Or.inl ⟨t, rfl⟩⟩ : Plane) = _
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_first _ _ _ _ _ _ _ _ _ _ t

theorem lowerBoundary_lowerReturn (t : unitInterval) :
    lowerBoundary P Q
        ⟨P.lowerReturn t, by rw [P.lowerCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ =
      ⟨Q.lowerReturn t, by rw [Q.lowerCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change ((rawLowerBoundary P Q) ⟨P.lowerReturn t, Or.inr ⟨t, rfl⟩⟩ : Plane) = _
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_second _ _ _ _ _ _ _ _ _ _ t

theorem upperBoundary_upperReturn (t : unitInterval) :
    upperBoundary P Q
        ⟨P.upperReturn t, by rw [P.upperCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ =
      ⟨Q.upperReturn t, by rw [Q.upperCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change ((rawUpperBoundary P Q) ⟨P.upperReturn t, Or.inr ⟨t, rfl⟩⟩ : Plane) = _
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_second _ _ _ _ _ _ _ _ _ _ t

theorem outerBoundary_lowerReturn (t : unitInterval) :
    outerBoundary P Q
        ⟨P.lowerReturn t, by rw [P.outerCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ =
      ⟨Q.lowerReturn t, by rw [Q.outerCircle_carrier]; exact Or.inl ⟨t, rfl⟩⟩ := by
  have hsource :
      Homeomorph.setCongr (return_union_symm P)
          ⟨P.lowerReturn t, Or.inl ⟨t, rfl⟩⟩ =
        ⟨P.lowerReturn.symm (unitInterval.symm t),
          Or.inl ⟨unitInterval.symm t, rfl⟩⟩ := by
    apply Subtype.ext
    rw [coe_setCongr_apply]
    simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
  apply Subtype.ext
  change ((rawOuterBoundary P Q) ⟨P.lowerReturn t, Or.inl ⟨t, rfl⟩⟩ : Plane) = _
  rw [coe_rawOuterBoundary_apply, hsource]
  change
    ((TwoArcJordan.carrierCorrespondence P.lowerReturn.symm P.upperReturn
        P.outerData.first_injective P.outerData.second_injective P.outerData.range_inter
        Q.lowerReturn.symm Q.upperReturn Q.outerData.first_injective
        Q.outerData.second_injective Q.outerData.range_inter)
      ⟨P.lowerReturn.symm (unitInterval.symm t),
        Or.inl ⟨unitInterval.symm t, rfl⟩⟩ : Plane) = _
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using
    congrArg Subtype.val
      (TwoArcJordan.carrierCorrespondence_apply_first P.lowerReturn.symm P.upperReturn
        P.outerData.first_injective P.outerData.second_injective P.outerData.range_inter
        Q.lowerReturn.symm Q.upperReturn Q.outerData.first_injective
        Q.outerData.second_injective Q.outerData.range_inter (unitInterval.symm t))

theorem outerBoundary_upperReturn (t : unitInterval) :
    outerBoundary P Q
        ⟨P.upperReturn t, by rw [P.outerCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ =
      ⟨Q.upperReturn t, by rw [Q.outerCircle_carrier]; exact Or.inr ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change ((rawOuterBoundary P Q) ⟨P.upperReturn t, Or.inr ⟨t, rfl⟩⟩ : Plane) = _
  rw [coe_rawOuterBoundary_apply]
  exact congrArg Subtype.val <| TwoArcJordan.carrierCorrespondence_apply_second
    P.lowerReturn.symm P.upperReturn P.outerData.first_injective
    P.outerData.second_injective P.outerData.range_inter Q.lowerReturn.symm Q.upperReturn
    Q.outerData.first_injective Q.outerData.second_injective Q.outerData.range_inter t

/-- The two cellwise disk extensions glued along the shared edge. -/
def cellHomeomorph :
    (closure P.lowerCircle.inside ∪ closure P.upperCircle.inside : Set Plane) ≃ₜ
      (closure Q.lowerCircle.inside ∪ closure Q.upperCircle.inside : Set Plane) :=
  JordanTwoCellBoundaryExtension.homeomorph P.toTwoCellPresentation
    Q.toTwoCellPresentation (lowerBoundary P Q) (upperBoundary P Q)
    (lowerBoundary_shared P Q) (upperBoundary_shared P Q)

theorem cellHomeomorph_apply_lower (x : Plane) (hx : x ∈ closure P.lowerCircle.inside) :
    (cellHomeomorph P Q ⟨x, Or.inl hx⟩ : Plane) =
      P.lowerCircle.extendBoundaryHomeomorph Q.lowerCircle (lowerBoundary P Q) ⟨x, hx⟩ := by
  exact JordanTwoCellBoundaryExtension.homeomorph_apply_lower
    P.toTwoCellPresentation Q.toTwoCellPresentation (lowerBoundary P Q)
      (upperBoundary P Q) (lowerBoundary_shared P Q) (upperBoundary_shared P Q) x hx

theorem cellHomeomorph_apply_upper (x : Plane) (hx : x ∈ closure P.upperCircle.inside) :
    (cellHomeomorph P Q ⟨x, Or.inr hx⟩ : Plane) =
      P.upperCircle.extendBoundaryHomeomorph Q.upperCircle (upperBoundary P Q) ⟨x, hx⟩ := by
  exact JordanTwoCellBoundaryExtension.homeomorph_apply_upper
    P.toTwoCellPresentation Q.toTwoCellPresentation (lowerBoundary P Q)
      (upperBoundary P Q) (lowerBoundary_shared P Q) (upperBoundary_shared P Q) x hx

theorem cellHomeomorph_apply_shared (t : unitInterval) :
    (cellHomeomorph P Q
        ⟨P.shared t, Or.inl (P.toTwoCellPresentation.shared_mem_lowerClosed t)⟩ : Plane) =
      Q.shared t := by
  calc
    (cellHomeomorph P Q
        ⟨P.shared t, Or.inl (P.toTwoCellPresentation.shared_mem_lowerClosed t)⟩ : Plane) =
        P.lowerCircle.extendBoundaryHomeomorph Q.lowerCircle (lowerBoundary P Q)
          ⟨P.shared t, P.toTwoCellPresentation.shared_mem_lowerClosed t⟩ :=
      cellHomeomorph_apply_lower P Q _ _
    _ = (lowerBoundary P Q
        ⟨P.shared t, P.toTwoCellPresentation.shared_mem_lowerCarrier t⟩ : Plane) := by
      simpa only using P.lowerCircle.extendBoundaryHomeomorph_apply Q.lowerCircle
        (lowerBoundary P Q)
        ⟨P.shared t, P.toTwoCellPresentation.shared_mem_lowerCarrier t⟩
    _ = Q.shared t := congrArg Subtype.val (lowerBoundary_shared P Q t)

theorem cellHomeomorph_apply_lowerReturn (t : unitInterval) :
    let hxCarrier : P.lowerReturn t ∈ P.lowerCircle.carrier := by
      rw [P.lowerCircle_carrier]
      exact Or.inr ⟨t, rfl⟩
    let hxClosed : P.lowerReturn t ∈ closure P.lowerCircle.inside := by
      rw [P.lowerCircle.closure_inside]
      exact Or.inr hxCarrier
    (cellHomeomorph P Q ⟨P.lowerReturn t, Or.inl hxClosed⟩ : Plane) =
      Q.lowerReturn t := by
  dsimp only
  have hxCarrier : P.lowerReturn t ∈ P.lowerCircle.carrier := by
    rw [P.lowerCircle_carrier]
    exact Or.inr ⟨t, rfl⟩
  have hxClosed : P.lowerReturn t ∈ closure P.lowerCircle.inside := by
    rw [P.lowerCircle.closure_inside]
    exact Or.inr hxCarrier
  calc
    (cellHomeomorph P Q ⟨P.lowerReturn t, Or.inl hxClosed⟩ : Plane) =
        P.lowerCircle.extendBoundaryHomeomorph Q.lowerCircle (lowerBoundary P Q)
          ⟨P.lowerReturn t, hxClosed⟩ := cellHomeomorph_apply_lower P Q _ _
    _ = (lowerBoundary P Q ⟨P.lowerReturn t, hxCarrier⟩ : Plane) := by
      simpa only using P.lowerCircle.extendBoundaryHomeomorph_apply Q.lowerCircle
        (lowerBoundary P Q) ⟨P.lowerReturn t, hxCarrier⟩
    _ = Q.lowerReturn t := congrArg Subtype.val (lowerBoundary_lowerReturn P Q t)

theorem cellHomeomorph_apply_upperReturn (t : unitInterval) :
    let hxCarrier : P.upperReturn t ∈ P.upperCircle.carrier := by
      rw [P.upperCircle_carrier]
      exact Or.inr ⟨t, rfl⟩
    let hxClosed : P.upperReturn t ∈ closure P.upperCircle.inside := by
      rw [P.upperCircle.closure_inside]
      exact Or.inr hxCarrier
    (cellHomeomorph P Q ⟨P.upperReturn t, Or.inr hxClosed⟩ : Plane) =
      Q.upperReturn t := by
  dsimp only
  have hxCarrier : P.upperReturn t ∈ P.upperCircle.carrier := by
    rw [P.upperCircle_carrier]
    exact Or.inr ⟨t, rfl⟩
  have hxClosed : P.upperReturn t ∈ closure P.upperCircle.inside := by
    rw [P.upperCircle.closure_inside]
    exact Or.inr hxCarrier
  calc
    (cellHomeomorph P Q ⟨P.upperReturn t, Or.inr hxClosed⟩ : Plane) =
        P.upperCircle.extendBoundaryHomeomorph Q.upperCircle (upperBoundary P Q)
          ⟨P.upperReturn t, hxClosed⟩ := cellHomeomorph_apply_upper P Q _ _
    _ = (upperBoundary P Q ⟨P.upperReturn t, hxCarrier⟩ : Plane) := by
      simpa only using P.upperCircle.extendBoundaryHomeomorph_apply Q.upperCircle
        (upperBoundary P Q) ⟨P.upperReturn t, hxCarrier⟩
    _ = Q.upperReturn t := congrArg Subtype.val (upperBoundary_upperReturn P Q t)

theorem cell_boundary (x : P.outerCircle.carrier) :
    (cellHomeomorph P Q ⟨x, P.toAmbientPresentation.outerCarrier_mem_cells x⟩ : Plane) =
      (outerBoundary P Q x : Plane) := by
  rcases x with ⟨x, hxOuter⟩
  have hxReturns : x ∈ range P.lowerReturn ∪ range P.upperReturn := by
    rw [← P.outerCircle_carrier]
    exact hxOuter
  rcases hxReturns with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact (cellHomeomorph_apply_lowerReturn P Q t).trans <|
      (congrArg Subtype.val (outerBoundary_lowerReturn P Q t)).symm
  · exact (cellHomeomorph_apply_upperReturn P Q t).trans <|
      (congrArg Subtype.val (outerBoundary_upperReturn P Q t)).symm

/-- The canonical theta correspondence promoted to an ambient plane homeomorphism. -/
def ambientHomeomorph : Plane ≃ₜ Plane :=
  JordanTwoCellAmbientExtension.ambientHomeomorph P.toAmbientPresentation
    Q.toAmbientPresentation (lowerBoundary P Q) (upperBoundary P Q)
    (lowerBoundary_shared P Q) (upperBoundary_shared P Q) (outerBoundary P Q)
    (cell_boundary P Q)

theorem ambientHomeomorph_apply_cells (x : Plane)
    (hx : x ∈ closure P.lowerCircle.inside ∪ closure P.upperCircle.inside) :
    ambientHomeomorph P Q x = (cellHomeomorph P Q ⟨x, hx⟩ : Plane) := by
  exact JordanTwoCellAmbientExtension.ambientHomeomorph_apply_cells
    P.toAmbientPresentation Q.toAmbientPresentation (lowerBoundary P Q)
    (upperBoundary P Q) (lowerBoundary_shared P Q) (upperBoundary_shared P Q)
    (outerBoundary P Q) (cell_boundary P Q) x hx

theorem ambientHomeomorph_apply_shared (t : unitInterval) :
    ambientHomeomorph P Q (P.shared t) = Q.shared t := by
  calc
    ambientHomeomorph P Q (P.shared t) =
        (cellHomeomorph P Q ⟨P.shared t,
          Or.inl (P.toTwoCellPresentation.shared_mem_lowerClosed t)⟩ : Plane) :=
      ambientHomeomorph_apply_cells P Q _ _
    _ = Q.shared t := cellHomeomorph_apply_shared P Q t

theorem ambientHomeomorph_apply_lowerReturn (t : unitInterval) :
    ambientHomeomorph P Q (P.lowerReturn t) = Q.lowerReturn t := by
  let hxCarrier : P.lowerReturn t ∈ P.lowerCircle.carrier := by
    rw [P.lowerCircle_carrier]
    exact Or.inr ⟨t, rfl⟩
  let hxClosed : P.lowerReturn t ∈ closure P.lowerCircle.inside := by
    rw [P.lowerCircle.closure_inside]
    exact Or.inr hxCarrier
  calc
    ambientHomeomorph P Q (P.lowerReturn t) =
        (cellHomeomorph P Q ⟨P.lowerReturn t, Or.inl hxClosed⟩ : Plane) :=
      ambientHomeomorph_apply_cells P Q _ _
    _ = Q.lowerReturn t := cellHomeomorph_apply_lowerReturn P Q t

theorem ambientHomeomorph_apply_upperReturn (t : unitInterval) :
    ambientHomeomorph P Q (P.upperReturn t) = Q.upperReturn t := by
  let hxCarrier : P.upperReturn t ∈ P.upperCircle.carrier := by
    rw [P.upperCircle_carrier]
    exact Or.inr ⟨t, rfl⟩
  let hxClosed : P.upperReturn t ∈ closure P.upperCircle.inside := by
    rw [P.upperCircle.closure_inside]
    exact Or.inr hxCarrier
  calc
    ambientHomeomorph P Q (P.upperReturn t) =
        (cellHomeomorph P Q ⟨P.upperReturn t, Or.inr hxClosed⟩ : Plane) :=
      ambientHomeomorph_apply_cells P Q _ _
    _ = Q.upperReturn t := cellHomeomorph_apply_upperReturn P Q t

end JordanThetaAmbientExtension

end

end Schoenflies
