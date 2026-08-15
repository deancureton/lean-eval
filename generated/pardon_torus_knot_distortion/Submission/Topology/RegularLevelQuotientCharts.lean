import Submission.Topology.CoordinatePlaneIntersectionCircles
import Submission.Topology.LocalFlatness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Descending planar regular-level charts to the quotient torus

This module first turns the kernel-valued implicit-function chart of a regular planar level into
an actual local chart with target an open subset of `ℝ`.  It then transfers local line models
through a surjective local homeomorphism.  Applied to the product exponential covering, this is
the seam-safe mechanism needed for coordinate levels on `Circle × Circle`.
-/

open Set Topology
open scoped Topology
open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.SurfaceRegularValue

/-! ## A regular planar fiber is locally modelled on a line -/

/-- The kernel of a nonzero functional on the plane is continuously linearly equivalent to
`ℝ`. -/
def regularLevelKernelEquiv {f : Plane → ℝ} {x : Plane}
    (hx : fderiv ℝ f x ≠ 0) :
    (fderiv ℝ f x).toLinearMap.ker ≃L[ℝ] ℝ := by
  apply ContinuousLinearEquiv.ofFinrankEq
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (f := (fderiv ℝ f x).toLinearMap)
    (fun hzero ↦ hx (ContinuousLinearMap.coe_injective hzero))
  norm_num at h ⊢
  omega

/-- The open real target cut out by an implicit-function chart on the level `y`. -/
def regularLevelLineTarget {f : Plane → ℝ} {x : Plane}
    (C : RegularLevelChart f x) (y : ℝ)
    (E : (fderiv ℝ f x).toLinearMap.ker ≃L[ℝ] ℝ) : Set ℝ :=
  {r | (y, E.symm r) ∈ C.chart.target}

theorem isOpen_regularLevelLineTarget {f : Plane → ℝ} {x : Plane}
    (C : RegularLevelChart f x) (y : ℝ)
    (E : (fderiv ℝ f x).toLinearMap.ker ≃L[ℝ] ℝ) :
    IsOpen (regularLevelLineTarget C y E) := by
  exact C.chart.open_target.preimage
    (continuous_const.prodMk E.symm.continuous)

/-- Restrict an implicit-function chart to its fiber and identify its one-dimensional kernel
with `ℝ`. -/
def regularLevelFiberHomeomorph {f : Plane → ℝ} {x : Plane}
    (C : RegularLevelChart f x) (y : ℝ)
    (E : (fderiv ℝ f x).toLinearMap.ker ≃L[ℝ] ℝ) :
    {z : f ⁻¹' {y} | z.1 ∈ C.chart.source} ≃ₜ
      regularLevelLineTarget C y E where
  toFun z := ⟨E (C.chart z.1.1).2, by
    change (y, E.symm (E (C.chart z.1.1).2)) ∈ C.chart.target
    have hzlevel : f z.1.1 = y := z.1.property
    have heq : (y, E.symm (E (C.chart z.1.1).2)) = C.chart z.1.1 := by
      apply Prod.ext
      · exact hzlevel.symm.trans (C.fst_eq z.1.1).symm
      · exact E.symm_apply_apply _
    rw [heq]
    exact C.chart.map_source z.property⟩
  invFun r := ⟨⟨C.chart.symm (y, E.symm r.1), by
    have happly := C.chart.right_inv r.property
    have hfst := congrArg Prod.fst happly
    exact (C.fst_eq (C.chart.symm (y, E.symm r.1))).symm.trans hfst⟩,
    C.chart.symm.map_source r.property⟩
  left_inv := fun z ↦ by
    apply Subtype.ext
    apply Subtype.ext
    change C.chart.symm (y, E.symm (E (C.chart z.1.1).2)) = z.1.1
    have hzlevel : f z.1.1 = y := z.1.property
    have heq : (y, E.symm (E (C.chart z.1.1).2)) = C.chart z.1.1 := by
      apply Prod.ext
      · exact hzlevel.symm.trans (C.fst_eq z.1.1).symm
      · exact E.symm_apply_apply _
    rw [heq]
    exact C.chart.left_inv z.property
  right_inv := fun r ↦ by
    apply Subtype.ext
    change E (C.chart (C.chart.symm (y, E.symm r.1))).2 = r.1
    rw [C.chart.right_inv r.property]
    exact E.apply_symm_apply r.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact E.continuous.comp <| continuous_snd.comp <|
      C.chart.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun z ↦ z.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact C.chart.symm.continuousOn.comp_continuous
      (continuous_const.prodMk (E.symm.continuous.comp continuous_subtype_val))
      (fun r ↦ r.property)

/-- Every smooth regular planar fiber has boundaryless local line charts. -/
theorem isLocallyLineModeled_regularFiber {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {y : ℝ}
    (hy : IsRegularValue f y) : IsLocallyLineModeled (f ⁻¹' {y}) := by
  intro z
  let C := Classical.choice (exists_regularLevelChart hf (hy z z.property))
  let E := regularLevelKernelEquiv (hy z z.property)
  exact ⟨{
    source := {w | w.1 ∈ C.chart.source}
    target := regularLevelLineTarget C y E
    source_open := C.chart.open_source.preimage continuous_subtype_val
    target_open := isOpen_regularLevelLineTarget C y E
    mem_source := C.mem_source
    equiv := regularLevelFiberHomeomorph C y E
  }⟩

/-! ## Local-line models descend through a covering -/

/-- Local line models transfer across a surjective local homeomorphism. -/
theorem isLocallyLineModeled_of_surjective_localHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsLocalHomeomorph p) (hsurj : Function.Surjective p)
    (hX : IsLocallyLineModeled X) : IsLocallyLineModeled Y := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨e, hxe, he⟩ := hp x
  obtain ⟨C⟩ := hX x
  let U : Set X := C.source ∩ e.source
  have hUopen : IsOpen U := C.source_open.inter e.open_source
  have hxU : x ∈ U := ⟨C.mem_source, hxe⟩
  let incC : U → C.source := Set.inclusion inter_subset_left
  let incE : U → e.source := Set.inclusion inter_subset_right
  have hincC : IsOpenEmbedding incC :=
    Topology.IsOpenEmbedding.inclusion inter_subset_left <| by
      convert e.open_source.preimage continuous_subtype_val using 1
      ext z
      simp
  have hincE : IsOpenEmbedding incE :=
    Topology.IsOpenEmbedding.inclusion inter_subset_right <| by
      convert C.source_open.preimage continuous_subtype_val using 1
      ext z
      simp
  let lineMap : U → ℝ := fun u ↦ C.equiv (incC u)
  have hline : IsOpenEmbedding lineMap := by
    exact C.target_open.isOpenEmbedding_subtypeVal.comp
      ((C.equiv.isOpenEmbedding).comp hincC)
  let baseMap : U → Y := fun u ↦ e (incE u)
  have hbase : IsOpenEmbedding baseMap := by
    exact e.isOpenEmbedding_restrict.comp hincE
  refine ⟨{
    source := Set.range baseMap
    target := Set.range lineMap
    source_open := hbase.isOpen_range
    target_open := hline.isOpen_range
    mem_source := ⟨⟨x, hxU⟩, by simp only [baseMap, incE]; rw [← he]⟩
    equiv := hbase.toIsEmbedding.toHomeomorph.symm.trans
      hline.toIsEmbedding.toHomeomorph
  }⟩

/-- Restrict a map to the preimage of a subset of its codomain. -/
def preimageRestriction {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (t : Set Y) : (p ⁻¹' t) → t :=
  fun x ↦ ⟨p x, x.property⟩

/-- Base change to an arbitrary codomain subset preserves a local homeomorphism. -/
theorem isLocalHomeomorph_preimageRestriction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsLocalHomeomorph p) (t : Set Y) :
    IsLocalHomeomorph (preimageRestriction p t) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨e, hxe, he⟩ := hp x.1
  let U : Set (p ⁻¹' t) := Subtype.val ⁻¹' e.source
  let V : Set t := Subtype.val ⁻¹' e.target
  have hUopen : IsOpen U := e.open_source.preimage continuous_subtype_val
  have hVopen : IsOpen V := e.open_target.preimage continuous_subtype_val
  have hxU : x ∈ U := hxe
  let E : U ≃ₜ V := {
    toFun := fun u ↦ ⟨⟨e u.1.1, by
      rw [← he]
      exact u.1.property⟩, e.map_source u.property⟩
    invFun := fun v ↦ ⟨⟨e.symm v.1.1, by
      change p (e.symm v.1.1) ∈ t
      rw [he, e.right_inv v.property]
      exact v.1.property⟩, e.symm.map_source v.property⟩
    left_inv := fun u ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact e.left_inv u.property
    right_inv := fun v ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact e.right_inv v.property
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact e.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun u ↦ u.property)
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact e.symm.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun v ↦ v.property)
  }
  refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
  have hopen : IsOpenEmbedding (fun u : U ↦ ((E u : V) : t)) :=
    hVopen.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  have hfun : U.domRestrict (preimageRestriction p t) =
      (fun u : U ↦ ((E u : V) : t)) := by
    funext u
    apply Subtype.ext
    exact congrFun he u.1.1
  rw [hfun]
  exact hopen

end Submission.SurfaceRegularValue

namespace Submission.Topology

open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## The product exponential covering and its level restriction -/

/-- The universal product-circle covering map. -/
def planeExpPair (uv : Plane) : Circle × Circle :=
  (Circle.exp uv.1, Circle.exp uv.2)

theorem planeExpPair_surjective : Function.Surjective planeExpPair := by
  rintro ⟨z, w⟩
  obtain ⟨u, rfl⟩ := Circle.exp_surjective z
  obtain ⟨v, rfl⟩ := Circle.exp_surjective w
  exact ⟨(u, v), rfl⟩

theorem planeExpPair_isLocalHomeomorph : IsLocalHomeomorph planeExpPair := by
  intro uv
  obtain ⟨eu, hu, heu⟩ := isLocalHomeomorph_circleExp uv.1
  obtain ⟨ev, hv, hev⟩ := isLocalHomeomorph_circleExp uv.2
  refine ⟨eu.prod ev, ⟨hu, hv⟩, ?_⟩
  funext x
  change (Circle.exp x.1, Circle.exp x.2) = (eu x.1, ev x.2)
  exact Prod.ext (congrFun heu x.1) (congrFun hev x.2)

theorem transportedTorusPlaneMap_eq_expPair (Phi : AmbientIsotopy) (uv : Plane) :
    transportedTorusPlaneMap Phi uv = transportedTorusMap Phi (planeExpPair uv) := by
  rw [transportedTorusPlaneMap, transportedTorusMap, planeExpPair,
    Function.uncurry_apply_pair, circleTorusMap_exp_exp,
    ambientHomeomorph_symm_apply]

theorem orientedCoordinateLift_eq_torusLongCoordinate_expPair
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (uv : Plane) :
    orientedCoordinateLift Phi frame 2 uv =
      torusLongCoordinate Phi frame (planeExpPair uv) := by
  rw [orientedCoordinateLift, torusLongCoordinate,
    transportedTorusPlaneMap_eq_expPair]

/-- Restrict the product exponential to a coordinate fiber. -/
def regularPlaneFiberToCoordinateTorusLevel (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    (orientedCoordinateLift Phi frame 2 ⁻¹' {d}) →
      coordinateTorusLevelSet Phi frame d :=
  fun uv ↦ ⟨planeExpPair uv, by
    change torusLongCoordinate Phi frame (planeExpPair uv) = d
    rw [← orientedCoordinateLift_eq_torusLongCoordinate_expPair]
    exact uv.property⟩

theorem regularPlaneFiberToCoordinateTorusLevel_surjective
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    Function.Surjective (regularPlaneFiberToCoordinateTorusLevel Phi frame d) := by
  intro z
  obtain ⟨uv, huv⟩ := planeExpPair_surjective z.1
  have huvlevel : orientedCoordinateLift Phi frame 2 uv = d := by
    rw [orientedCoordinateLift_eq_torusLongCoordinate_expPair, huv]
    exact z.property
  exact ⟨⟨uv, huvlevel⟩, Subtype.ext huv⟩

theorem preimage_coordinateTorusLevelSet_expPair
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    planeExpPair ⁻¹' coordinateTorusLevelSet Phi frame d =
      orientedCoordinateLift Phi frame 2 ⁻¹' {d} := by
  ext uv
  change torusLongCoordinate Phi frame (planeExpPair uv) = d ↔
    orientedCoordinateLift Phi frame 2 uv = d
  rw [orientedCoordinateLift_eq_torusLongCoordinate_expPair]

/-- The identity on angular coordinates, with its domain regarded as the preimage of the quotient
level under the product exponential. -/
def regularPlaneFiberPreimageHomeomorph (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    (orientedCoordinateLift Phi frame 2 ⁻¹' {d}) ≃ₜ
      (planeExpPair ⁻¹' coordinateTorusLevelSet Phi frame d) :=
  Homeomorph.setCongr (preimage_coordinateTorusLevelSet_expPair Phi frame d).symm

theorem regularPlaneFiberToCoordinateTorusLevel_isLocalHomeomorph
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsLocalHomeomorph (regularPlaneFiberToCoordinateTorusLevel Phi frame d) := by
  have hrestrict : IsLocalHomeomorph
      (preimageRestriction planeExpPair
        (coordinateTorusLevelSet Phi frame d)) :=
    isLocalHomeomorph_preimageRestriction
      planeExpPair_isLocalHomeomorph _
  have hcomp := hrestrict.comp
    (regularPlaneFiberPreimageHomeomorph Phi frame d).isLocalHomeomorph
  convert hcomp using 1
  funext uv
  apply Subtype.ext
  rfl

/-- A regular value of the periodic planar lift has a boundaryless local-line quotient level.
This is the explicit seam descent: the full planar regular fiber covers the quotient fiber by a
surjective local homeomorphism. -/
theorem isLocallyLineModeled_coordinateTorusLevel_of_regularValue
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) {d : ℝ}
    (hd : IsRegularValue (orientedCoordinateLift Phi frame 2) d) :
    IsLocallyLineModeled (coordinateTorusLevelSet Phi frame d) := by
  apply isLocallyLineModeled_of_surjective_localHomeomorph
    (regularPlaneFiberToCoordinateTorusLevel_isLocalHomeomorph Phi frame d)
    (regularPlaneFiberToCoordinateTorusLevel_surjective Phi frame d)
  exact isLocallyLineModeled_regularFiber
    (orientedCoordinateLift_contDiff Phi frame 2) hd

/-- Planar Sard supplies an unconditional selected regular coordinate level with the quotient
local-line field required by `RegularCoordinateTorusLevel`. -/
theorem nonempty_regularCoordinateTorusLevel
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    {a b : ℝ} (hab : a < b) :
    Nonempty (RegularCoordinateTorusLevel Phi frame a b) := by
  let f := orientedCoordinateLift Phi frame 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    orientedCoordinateLift_contDiff Phi frame 2
  have hnull : CriticalValuesNull f :=
    criticalValuesNull_of_sardMoreiraConclusion
      (planarSardTheorem f hf)
  obtain ⟨d, hdmem, hdregular⟩ := exists_regularValue_between hnull hab
  let selection : CompactRegularLevelSelection f a b := {
    level := d
    level_mem := hdmem
    isCompact := isCompact_fundamentalLevelSet hf.continuous d
    localCharts := regularValue_has_local_charts hf hdregular
  }
  exact ⟨{
    selection := selection
    quotientLocallyLineModeled :=
      isLocallyLineModeled_coordinateTorusLevel_of_regularValue
        Phi frame hdregular
  }⟩

end Submission.Topology
