import Submission.Topology.SuperellipsoidGlobalBandTubularChart
import Submission.Topology.TorusPlaneCircleLiftAlignment

/-!
# Retaining the covering-plane sheet of a global band chart

The construction of a global band chart first builds an open planar sheet on which the torus
covering projection is injective, then forgets that sheet when it descends to the transported
torus.  This module retains it.  The complement of the particular sheet constructed here is
preconnected and unbounded.  Consequently every closed Jordan disk whose boundary lies in the
sheet lies in the sheet as well.
-/

open LeanEval.KnotTheory.PardonDistortion
open Metric Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open EmbeddedTorusIntersectionCircle

/-- A planar open set with preconnected unbounded complement contains the closed inside of every
Jordan circle whose carrier it contains. -/
theorem closure_inside_subset_of_compl_preconnected_unbounded
    (J : Schoenflies.JordanCircle) {U : Set Schoenflies.Plane}
    (hcarrier : J.carrier ⊆ U) (hpre : IsPreconnected Uᶜ)
    (hunbounded : ¬ Bornology.IsBounded Uᶜ) :
    closure J.inside ⊆ U := by
  have hcompl : Uᶜ ⊆ J.inside ∪ J.outside := by
    rw [J.inside_union_outside]
    intro x hxU hxCarrier
    exact hxU (hcarrier hxCarrier)
  have houtside : Uᶜ ⊆ J.outside := by
    rcases hpre.subset_or_subset J.inside_isOpen J.outside_isOpen
        J.inside_disjoint_outside hcompl with hinside | houtside
    · exact False.elim (hunbounded (J.inside_bounded.subset hinside))
    · exact houtside
  rw [J.closure_inside]
  intro x hx
  by_cases hxU : x ∈ U
  · exact hxU
  · have hxOutside := houtside hxU
    rcases hx with hxInside | hxCarrier
    · exact False.elim <| Set.disjoint_left.mp J.inside_disjoint_outside
        hxInside hxOutside
    · exact False.elim <| J.outside_subset_compl hxOutside hxCarrier

private theorem openRectangle_compl_isPreconnected
    (a b c d : ℝ) :
    IsPreconnected ((Ioo a b ×ˢ Ioo c d)ᶜ : Set (ℝ × ℝ)) := by
  let A : Set (ℝ × ℝ) := Iic a ×ˢ Set.univ
  let B : Set (ℝ × ℝ) := Ici b ×ˢ Set.univ
  let C : Set (ℝ × ℝ) := Set.univ ×ˢ Iic c
  let D : Set (ℝ × ℝ) := Set.univ ×ˢ Ici d
  have hA : IsPreconnected A := ((convex_Iic a).prod convex_univ).isPreconnected
  have hB : IsPreconnected B := ((convex_Ici b).prod convex_univ).isPreconnected
  have hC : IsPreconnected C := (convex_univ.prod (convex_Iic c)).isPreconnected
  have hD : IsPreconnected D := (convex_univ.prod (convex_Ici d)).isPreconnected
  have hAC : IsPreconnected (A ∪ C) :=
    hA.union (a, c) (by simp [A]) (by simp [C]) hC
  have hACB : IsPreconnected ((A ∪ C) ∪ B) :=
    hAC.union (b, c) (by simp [C]) (by simp [B]) hB
  have hACBD : IsPreconnected (((A ∪ C) ∪ B) ∪ D) :=
    hACB.union (b, d) (by simp [B]) (by simp [D]) hD
  have heq : ((Ioo a b ×ˢ Ioo c d)ᶜ : Set (ℝ × ℝ)) =
      ((A ∪ C) ∪ B) ∪ D := by
    ext x
    simp only [mem_compl_iff, mem_prod, mem_Ioo, mem_union, mem_Iic, mem_Ici,
      mem_univ, and_true, true_and, not_and_or, not_lt, A, B, C, D]
    tauto
  rwa [heq]

private theorem openRectangle_compl_unbounded
    (a b c d : ℝ) :
    ¬ Bornology.IsBounded ((Ioo a b ×ˢ Ioo c d)ᶜ : Set (ℝ × ℝ)) := by
  intro hbounded
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  let x : ℝ × ℝ := (|M| + |b| + 1, 0)
  have hx : x ∈ ((Ioo a b ×ˢ Ioo c d)ᶜ : Set (ℝ × ℝ)) := by
    intro hxOpen
    have hxb := hxOpen.1.2
    dsimp only [x] at hxb
    nlinarith [le_abs_self b, abs_nonneg M]
  have hxNorm := hM x hx
  have hcoord : |M| + |b| + 1 ≤ ‖x‖ := by
    have hfirst : ‖x.1‖ = |M| + |b| + 1 := by
      dsimp only [x]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [← hfirst]
    exact norm_fst_le x
  linarith [le_abs_self M, abs_nonneg b]

private theorem homeomorph_image_unbounded_of_closed
    {X Y : Type*} [MetricSpace X] [ProperSpace X]
    [MetricSpace Y] [ProperSpace Y] (e : X ≃ₜ Y) {s : Set X}
    (hs : IsClosed s) (hunbounded : ¬ Bornology.IsBounded s) :
    ¬ Bornology.IsBounded (e '' s) := by
  intro hbounded
  have hcompact : IsCompact (e '' s) :=
    isCompact_iff_isClosed_bounded.mpr ⟨e.isClosed_image.mpr hs, hbounded⟩
  exact hunbounded ((e.isCompact_image.mp hcompact).isBounded)

private theorem standardRectangle_compl_isPreconnected (delta rho : ℝ) :
    IsPreconnected
      (Schoenflies.ExtendibleInjectivePath.standardRectangle delta rho)ᶜ := by
  let S : Set (ℝ × ℝ) := Ioo (-1 - delta) (1 + delta) ×ˢ Ioo (-rho) rho
  have hS : IsPreconnected Sᶜ :=
    openRectangle_compl_isPreconnected (-1 - delta) (1 + delta) (-rho) rho
  have himage :=
    (Schoenflies.planeCoordinates.symm.isPreconnected_image).mpr hS
  simpa only [S, Schoenflies.ExtendibleInjectivePath.standardRectangle,
    Schoenflies.planeCoordinates.symm.image_compl] using himage

private theorem standardRectangle_compl_unbounded (delta rho : ℝ) :
    ¬ Bornology.IsBounded
      (Schoenflies.ExtendibleInjectivePath.standardRectangle delta rho)ᶜ := by
  let S : Set (ℝ × ℝ) := Ioo (-1 - delta) (1 + delta) ×ˢ Ioo (-rho) rho
  have hclosed : IsClosed Sᶜ := (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl
  have hunbounded : ¬ Bornology.IsBounded Sᶜ :=
    openRectangle_compl_unbounded (-1 - delta) (1 + delta) (-rho) rho
  have himage := homeomorph_image_unbounded_of_closed
    Schoenflies.planeCoordinates.symm hclosed hunbounded
  simpa only [S, Schoenflies.ExtendibleInjectivePath.standardRectangle,
    Schoenflies.planeCoordinates.symm.image_compl] using himage

namespace FiniteSuperellipsoidBarrierGraph

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
  {outerIndex cutIndex : Type*} [Fintype outerIndex] [Fintype cutIndex]
  {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}

namespace CutCircleTransverseCyclicOrderFamily

variable (F : CutCircleTransverseCyclicOrderFamily G)
  (b : Fin F.toPairedSeamEnumeration.bandCount)

/-- A global band chart together with the planar covering sheet from which it descends. -/
structure LiftedGlobalBandTubularChartData extends GlobalBandTubularChartData F b where
  liftedPatch : Set TorusCoveringPlane
  liftedPatch_open : IsOpen liftedPatch
  liftedStrip : Submission.SurfaceRegularValue.Plane ≃ₜ liftedPatch
  projection_liftedStrip : ∀ z,
    torusCoveringProjectionToTorus Phi (liftedStrip z) =
      (toGlobalBandTubularChartData.strip z : transportedTorus Phi)
  liftedPatch_compl_preconnected : IsPreconnected liftedPatchᶜ
  liftedPatch_compl_unbounded : ¬ Bornology.IsBounded liftedPatchᶜ

/-- The canonical global band chart can be chosen together with its covering-plane sheet, whose
complement is preconnected and unbounded. -/
theorem exists_liftedGlobalBandTubularChartData :
    Nonempty (LiftedGlobalBandTubularChartData F b) := by
  let E := F.globalBandExtendibleInjectivePath b
  obtain ⟨Uinj, hUinjOpen, hpathUinj, hinj⟩ :=
    F.exists_open_injOn_globalBandExtendedPlanePath b
  let ambientBand : Set (transportedTorus Phi) :=
    {x | (x : R3) ∈ F.globalBandOpenNeighborhood b}
  have hambientBandOpen : IsOpen ambientBand :=
    (F.globalBandOpenNeighborhood_spec.1 b).1.preimage continuous_subtype_val
  let U : Set TorusCoveringPlane := Uinj ∩
    torusCoveringProjectionToTorus Phi ⁻¹' ambientBand
  have hUopen : IsOpen U := hUinjOpen.inter <|
    hambientBandOpen.preimage
      (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).continuous
  have hcoreU : E.coreRange ⊆ U := by
    intro x hx
    rw [← E.range_corePath] at hx
    obtain ⟨u, rfl⟩ := hx
    constructor
    · apply hpathUinj
      exact ⟨Icc.convexComb E.coreLeft E.coreRight u, rfl⟩
    · change ((torusCoveringProjectionToTorus Phi (E.corePath u) :
          transportedTorus Phi) : R3) ∈ F.globalBandOpenNeighborhood b
      rw [show E.corePath u =
          (F.globalBandCircle b).zeroWindingPlaneLift
            (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) from
        F.globalBandExtendible_corePath_apply b u,
        F.torusCoveringProjection_globalBandCircle_planeLift]
      exact F.globalBandOpenNeighborhood_spec.1 b |>.2 ⟨u, rfl⟩
  let H : Schoenflies.Plane ≃ₜ Schoenflies.Plane := E.ambientCoreStraightener
  let W : Set Schoenflies.Plane := H ⁻¹' U
  have hWopen : IsOpen W := H.isOpen_preimage.mpr hUopen
  have hseamW : Set.range Schoenflies.ExtendibleInjectivePath.bandSeamPath ⊆ W := by
    rintro _ ⟨t, rfl⟩
    change H (Schoenflies.ExtendibleInjectivePath.bandSeamPath t) ∈ U
    rw [show H (Schoenflies.ExtendibleInjectivePath.bandSeamPath t) = E.corePath t from
      E.ambientCoreStraightener_apply_bandSeamPath t]
    exact hcoreU (E.range_corePath ▸ ⟨t, rfl⟩)
  have hseamCompact :
      IsCompact (Set.range Schoenflies.ExtendibleInjectivePath.bandSeamPath) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image
        Schoenflies.ExtendibleInjectivePath.bandSeamPath.continuous)
  obtain ⟨epsilon, hepsilon, hthickW⟩ :=
    hseamCompact.exists_thickening_subset_open hWopen hseamW
  let r : ℝ := epsilon / 3
  have hr : 0 < r := by dsimp [r]; linarith
  let rectangle : Set Schoenflies.Plane :=
    Schoenflies.ExtendibleInjectivePath.standardRectangle r r
  have hrectangleOpen : IsOpen rectangle :=
    Schoenflies.ExtendibleInjectivePath.isOpen_standardRectangle r r
  have hrectangleW : rectangle ⊆ W := by
    exact (Schoenflies.ExtendibleInjectivePath.standardRectangle_subset_thickening
      hepsilon).trans hthickW
  let V : Set Schoenflies.Plane := H '' rectangle
  have hVopen : IsOpen V := by
    dsimp [V]
    exact H.isOpen_image.mpr hrectangleOpen
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hrectangleW hx
  let e0 : Schoenflies.Plane ≃ₜ rectangle :=
    Schoenflies.ExtendibleInjectivePath.standardRectangleHomeomorph r r hr hr
  let e : Schoenflies.Plane ≃ₜ V := e0.trans (Homeomorph.image H rectangle)
  have heCore (t : unitInterval) :
      (e (Schoenflies.ExtendibleInjectivePath.bandSeamPath t) :
        Schoenflies.Plane) = E.corePath t := by
    change H ((e0 (Schoenflies.ExtendibleInjectivePath.bandSeamPath t) : rectangle) :
      Schoenflies.Plane) = E.corePath t
    rw [show ((e0 (Schoenflies.ExtendibleInjectivePath.bandSeamPath t) : rectangle) :
        Schoenflies.Plane) = Schoenflies.ExtendibleInjectivePath.bandSeamPath t from
      Schoenflies.ExtendibleInjectivePath.standardRectangleHomeomorph_apply_bandSeamPath
        r r hr hr t,
      E.ambientCoreStraightener_apply_bandSeamPath]
  have hVcomplPreconnected : IsPreconnected Vᶜ := by
    have himage := (H.isPreconnected_image).mpr
      (standardRectangle_compl_isPreconnected r r)
    simpa only [V, rectangle, H.image_compl] using himage
  have hVcomplUnbounded : ¬ Bornology.IsBounded Vᶜ := by
    have himage := homeomorph_image_unbounded_of_closed H
      (hrectangleOpen.isClosed_compl) (standardRectangle_compl_unbounded r r)
    simpa only [V, H.image_compl] using himage
  let pV : V → transportedTorus Phi :=
    fun x ↦ torusCoveringProjectionToTorus Phi x
  have hpVlocal : IsLocalHomeomorph pV := by
    change IsLocalHomeomorph
      (torusCoveringProjectionToTorus Phi ∘ (fun x : V ↦ (x : TorusCoveringPlane)))
    exact (isLocalHomeomorph_torusCoveringProjectionToTorus Phi).comp
      hVopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hpVinj : Function.Injective pV := by
    intro x y hxy
    apply Subtype.ext
    apply hinj (hVU x.2).1 (hVU y.2).1 hxy
  let ep : V ≃ₜ Set.range pV :=
    (hpVlocal.isOpenEmbedding_of_injective hpVinj).isEmbedding.toHomeomorph
  let strip : Submission.SurfaceRegularValue.Plane ≃ₜ Set.range pV :=
    coveringPlaneCoordinates.symm.trans (e.trans ep)
  let base : GlobalBandTubularChartData F b :=
    GlobalBandTubularChartData.ofStrip (Set.range pV) strip (by
      rintro _ ⟨z, rfl⟩
      change ((pV (e (coveringPlaneCoordinates.symm z)) : transportedTorus Phi) : R3) ∈
        F.globalBandOpenNeighborhood b
      exact (hVU (e (coveringPlaneCoordinates.symm z)).2).2) (by
      intro u
      change ((pV (e (coveringPlaneCoordinates.symm (bandSeamPath u))) :
        transportedTorus Phi) : R3) =
        ((F.globalBandPath b u : transportedTorus Phi) : R3)
      rw [coveringPlaneCoordinates_symm_bandSeamPath]
      calc
        ((pV (e (Schoenflies.ExtendibleInjectivePath.bandSeamPath u)) :
            transportedTorus Phi) : R3) =
            ((torusCoveringProjectionToTorus Phi (E.corePath u) :
              transportedTorus Phi) : R3) :=
          congrArg Subtype.val <|
            congrArg (torusCoveringProjectionToTorus Phi) (heCore u)
        _ = (((F.globalBandCircle b).windingLoop.curve
            (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) :
              transportedTorus Phi) : R3) := by
          rw [show E.corePath u =
              (F.globalBandCircle b).zeroWindingPlaneLift
                (F.globalInwardExcursionParameter (F.globalGapOfBand b) u) from
            F.globalBandExtendible_corePath_apply b u,
            F.torusCoveringProjection_globalBandCircle_planeLift]
        _ = ((F.globalBandPath b u : transportedTorus Phi) : R3) := by
          rfl)
  let liftedStrip : Submission.SurfaceRegularValue.Plane ≃ₜ V :=
    coveringPlaneCoordinates.symm.trans e
  refine ⟨{
    toGlobalBandTubularChartData := base
    liftedPatch := V
    liftedPatch_open := hVopen
    liftedStrip := liftedStrip
    projection_liftedStrip := ?_
    liftedPatch_compl_preconnected := hVcomplPreconnected
    liftedPatch_compl_unbounded := hVcomplUnbounded
  }⟩
  intro z
  rfl

namespace LiftedGlobalBandTubularChartData

variable {F : CutCircleTransverseCyclicOrderFamily G}
  {b : Fin F.toPairedSeamEnumeration.bandCount}

/-- Every closed Jordan disk bounded by a curve in the retained sheet remains in that sheet. -/
theorem closure_inside_subset_liftedPatch
    (T : LiftedGlobalBandTubularChartData F b) (J : Schoenflies.JordanCircle)
    (hcarrier : J.carrier ⊆ T.liftedPatch) :
    closure J.inside ⊆ T.liftedPatch :=
  closure_inside_subset_of_compl_preconnected_unbounded J hcarrier
    T.liftedPatch_compl_preconnected T.liftedPatch_compl_unbounded

end LiftedGlobalBandTubularChartData

end CutCircleTransverseCyclicOrderFamily
end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
