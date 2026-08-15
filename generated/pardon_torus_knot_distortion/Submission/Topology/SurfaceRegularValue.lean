import Submission.Coarea.OrientedShell
import Submission.Torus.AmbientTransfer
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.MeasureTheory.Measure.Hausdorff

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Submission
namespace SurfaceRegularValue

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Regular values for real-valued functions on a transported torus

We work with the periodic lift to `ℝ × ℝ`.  This avoids asserting a smooth
manifold structure on the subtype used elsewhere for the transported torus,
while retaining explicit compact fundamental domains and the full local
implicit-function conclusion.

The pinned Mathlib contains only equal-dimension Sard and the easy
dimension-increasing case.  The missing dimension-two-to-one Sard theorem is
isolated below as the proposition `CriticalValuesNull`; every consequence of
that proposition is proved.  Lean Pool's `SardMoreira` development proves the
missing proposition, but it is not a dependency of this project.
-/

abbrev Plane := ℝ × ℝ

/-- Critical points of a differentiable real-valued function on the plane. -/
def criticalPoints (f : Plane → ℝ) : Set Plane :=
  {x | fderiv ℝ f x = 0}

/-- Values attained at critical points. -/
def criticalValues (f : Plane → ℝ) : Set ℝ :=
  f '' criticalPoints f

/-- A value is regular when the derivative is nonzero at every point of its
fiber. -/
def IsRegularValue (f : Plane → ℝ) (y : ℝ) : Prop :=
  ∀ x, f x = y → fderiv ℝ f x ≠ 0

lemma isRegularValue_iff_not_mem_criticalValues (f : Plane → ℝ) (y : ℝ) :
    IsRegularValue f y ↔ y ∉ criticalValues f := by
  constructor
  · intro hreg ⟨x, hxcritical, hxy⟩
    exact hreg x hxy hxcritical
  · intro hy x hxy hxcritical
    exact hy ⟨x, hxcritical, hxy⟩

/-- The exact missing Sard conclusion for a planar lift. -/
def CriticalValuesNull (f : Plane → ℝ) : Prop :=
  volume (criticalValues f) = 0

/-- The exact Hausdorff-measure conclusion produced by the planar
specialization of Lean Pool's Sard--Moreira theorem. -/
def SardMoreiraConclusion (f : Plane → ℝ) : Prop :=
  μH[1] (criticalValues f) = 0

lemma criticalValuesNull_of_sardMoreiraConclusion {f : Plane → ℝ}
    (h : SardMoreiraConclusion f) : CriticalValuesNull f := by
  change volume (criticalValues f) = 0
  rw [← hausdorffMeasure_real]
  exact h

/-- A reusable name for the single external theorem still needed to obtain
unconditional Sard for all smooth planar lifts. -/
def PlanarSardTheorem : Prop :=
  ∀ f : Plane → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) f → SardMoreiraConclusion f

/-- A concrete local normal-form chart for a regular level.  Its first
coordinate is literally `f`, so the fiber is locally a slice with the first
coordinate fixed. -/
structure RegularLevelChart (f : Plane → ℝ) (x : Plane) where
  chart : OpenPartialHomeomorph Plane
    (ℝ × (fderiv ℝ f x).toLinearMap.ker)
  mem_source : x ∈ chart.source
  fst_eq : ∀ z, (chart z).1 = f z

/-- A nonzero real-valued continuous linear map is surjective. -/
lemma range_fderiv_eq_top_of_ne_zero {f : Plane → ℝ} {x : Plane}
    (h : fderiv ℝ f x ≠ 0) :
    LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ := by
  apply Module.Dual.range_eq_top_of_ne_zero
  intro hz
  apply h
  exact ContinuousLinearMap.coe_injective hz

/-- The implicit function theorem gives an honest local product chart at
every regular point. -/
theorem exists_regularLevelChart {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane}
    (hx : fderiv ℝ f x ≠ 0) :
    Nonempty (RegularLevelChart f x) := by
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f x) x :=
    hf.hasStrictFDerivAt (by simp)
  have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ :=
    range_fderiv_eq_top_of_ne_zero hx
  let e := hstrict.implicitToOpenPartialHomeomorph f (fderiv ℝ f x) hrange
  refine ⟨⟨e, ?_, ?_⟩⟩
  · exact hstrict.mem_implicitToOpenPartialHomeomorph_source hrange
  · intro z
    exact hstrict.implicitToOpenPartialHomeomorph_fst hrange z

/-- Every point of a regular fiber has the local product chart above. -/
theorem regularValue_has_local_charts {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {y : ℝ}
    (hy : IsRegularValue f y) :
    ∀ x ∈ f ⁻¹' {y}, Nonempty (RegularLevelChart f x) := by
  intro x hx
  apply exists_regularLevelChart hf
  exact hy x hx

/-- A closed fundamental square for the periodic lift. -/
def fundamentalSquare : Set Plane :=
  Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi)

lemma isCompact_fundamentalSquare : IsCompact fundamentalSquare :=
  isCompact_Icc.prod isCompact_Icc

/-- The part of a level in one closed fundamental square. -/
def fundamentalLevelSet (f : Plane → ℝ) (y : ℝ) : Set Plane :=
  fundamentalSquare ∩ f ⁻¹' {y}

lemma isCompact_fundamentalLevelSet {f : Plane → ℝ}
    (hf : Continuous f) (y : ℝ) :
    IsCompact (fundamentalLevelSet f y) := by
  exact isCompact_fundamentalSquare.inter_right
    (isClosed_singleton.preimage hf)

/-- A null set of critical values misses every nonempty interval. -/
theorem exists_regularValue_between {f : Plane → ℝ}
    (hnull : CriticalValuesNull f) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, IsRegularValue f y := by
  have hnot : ¬Ioo a b ⊆ criticalValues f := by
    intro hsub
    have hz : volume (Ioo a b) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo] at hz
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hz
  obtain ⟨y, hy, hycritical⟩ := Set.not_subset.mp hnot
  exact ⟨y, hy, (isRegularValue_iff_not_mem_criticalValues f y).2 hycritical⟩

/-- Consequently regular values are dense. -/
theorem dense_regularValues {f : Plane → ℝ}
    (hnull : CriticalValuesNull f) :
    Dense {y | IsRegularValue f y} := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨y, hy, hyreg⟩ :=
    exists_regularValue_between hnull (show x - r < x + r by linarith)
  refine ⟨y, ?_, hyreg⟩
  rw [Metric.mem_ball, Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- A regular value selected in an arbitrary interval has a compact
fundamental-domain fiber and a local normal-form chart at every point. -/
theorem exists_compact_locallyRegular_level {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hnull : CriticalValuesNull f)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      IsCompact (fundamentalLevelSet f y) ∧
      ∀ x ∈ f ⁻¹' {y}, Nonempty (RegularLevelChart f x) := by
  obtain ⟨y, hy, hyreg⟩ := exists_regularValue_between hnull hab
  exact ⟨y, hy, isCompact_fundamentalLevelSet hf.continuous y,
    regularValue_has_local_charts hf hyreg⟩

/-! ## The explicit transported-torus lift -/

open Submission.PardonDistortion Submission.Torus

/-- The transported torus parametrized by its two real angles. -/
def transportedTorusPlaneMap (Phi : AmbientIsotopy) (uv : Plane) : R3 :=
  Phi.Hinv 1 (standardTorusMap uv.1 uv.2)

lemma transportedTorusPlaneMap_contDiff (Phi : AmbientIsotopy) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedTorusPlaneMap Phi) := by
  exact Phi.smooth_inv.comp
    (contDiff_const.prodMk standardTorusMap_contDiff)

lemma transportedTorusPlaneMap_add_int_periods
    (Phi : AmbientIsotopy) (m n : ℤ) (uv : Plane) :
    transportedTorusPlaneMap Phi
        (uv.1 + (m : ℝ) * (2 * Real.pi),
          uv.2 + (n : ℝ) * (2 * Real.pi)) =
      transportedTorusPlaneMap Phi uv := by
  rw [transportedTorusPlaneMap, transportedTorusPlaneMap,
    standardTorusMap_add_int_mul_two_pi]

lemma range_transportedTorusPlaneMap (Phi : AmbientIsotopy) :
    range (transportedTorusPlaneMap Phi) = transportedTorus Phi := by
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(Circle.exp u, Circle.exp v), ?_⟩
    rw [transportedTorusMap, transportedTorusPlaneMap,
      Function.uncurry_apply_pair, circleTorusMap_exp_exp,
      ambientHomeomorph_symm_apply]
  · rintro ⟨⟨z, w⟩, rfl⟩
    refine ⟨((z : ℂ).arg, (w : ℂ).arg), ?_⟩
    have hstd : standardTorusMap (z : ℂ).arg (w : ℂ).arg =
        circleTorusMap z w := by
      calc
        standardTorusMap (z : ℂ).arg (w : ℂ).arg =
            circleTorusMap (Circle.exp (z : ℂ).arg)
              (Circle.exp (w : ℂ).arg) :=
          (circleTorusMap_exp_exp _ _).symm
        _ = circleTorusMap z w := by rw [Circle.exp_arg, Circle.exp_arg]
    rw [transportedTorusPlaneMap, transportedTorusMap,
      Function.uncurry_apply_pair, ambientHomeomorph_symm_apply, hstd]

/-- Ambient coordinate projection as a continuous linear functional. -/
def ambientCoordinate (i : Fin 3) : R3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 ↦ ℝ)).toContinuousLinearMap

@[simp]
lemma ambientCoordinate_apply (i : Fin 3) (x : R3) :
    ambientCoordinate i x = x.ofLp i :=
  rfl

/-- A coordinate-plane function pulled back to the periodic planar model of
the transported torus. -/
def orientedCoordinateLift (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (i : Fin 3) (uv : Plane) : ℝ :=
  ambientCoordinate (frame i) (transportedTorusPlaneMap Phi uv)

lemma orientedCoordinateLift_contDiff (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (orientedCoordinateLift Phi frame i) := by
  exact (ambientCoordinate (frame i)).contDiff.comp
    (transportedTorusPlaneMap_contDiff Phi)

/-- The signed normalized coordinate defining one face of an oriented box.
The Boolean chooses the positive or negative face. -/
def signedOrientedFaceLift (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3)
    (face : Fin 3 × Bool) (uv : Plane) : ℝ :=
  (if face.2 then 1 else -1) *
    ((orientedCoordinateLift Phi frame face.1 uv -
      ambientCoordinate (frame face.1) c) / axisWeight face.1)

lemma signedOrientedFaceLift_contDiff (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (face : Fin 3 × Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (signedOrientedFaceLift Phi frame c face) := by
  unfold signedOrientedFaceLift
  exact contDiff_const.mul
    (((orientedCoordinateLift_contDiff Phi frame face.1).sub contDiff_const).div_const _)

/-- Simultaneous regularity of all six smooth face functions at a box scale.
This is the rigorous conclusion available for the nonsmooth sup gauge; no
claim is made that ridge crossings form a manifold. -/
def FacewiseRegularValue (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (y : ℝ) : Prop :=
  ∀ face : Fin 3 × Bool,
    IsRegularValue (signedOrientedFaceLift Phi frame c face) y

/-- The finite union of the critical values of the six smooth face lifts. -/
def orientedFaceCriticalValues (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) : Set ℝ :=
  ⋃ face : Fin 3 × Bool,
    criticalValues (signedOrientedFaceLift Phi frame c face)

lemma orientedFaceCriticalValues_null
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (hSard : ∀ face : Fin 3 × Bool,
      CriticalValuesNull (signedOrientedFaceLift Phi frame c face)) :
    volume (orientedFaceCriticalValues Phi frame c) = 0 := by
  rw [orientedFaceCriticalValues, measure_iUnion_null_iff]
  exact hSard

lemma facewiseRegularValue_iff_not_mem
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (y : ℝ) :
    FacewiseRegularValue Phi frame c y ↔
      y ∉ orientedFaceCriticalValues Phi frame c := by
  simp only [FacewiseRegularValue, orientedFaceCriticalValues, mem_iUnion,
    not_exists, isRegularValue_iff_not_mem_criticalValues]

/-- A null subset of the real line misses every nonempty open interval. -/
theorem exists_not_mem_nullSet_between {s : Set ℝ}
    (hs : volume s = 0) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, y ∉ s := by
  have hnot : ¬Ioo a b ⊆ s := by
    intro hsub
    have hz : volume (Ioo a b) = 0 := measure_mono_null hsub hs
    rw [Real.volume_Ioo] at hz
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hz
  exact Set.not_subset.mp hnot

/-- A single perturbation of the box scale makes all six smooth face
restrictions locally regular. -/
theorem exists_facewiseRegularValue_between
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (hSard : ∀ face : Fin 3 × Bool,
      CriticalValuesNull (signedOrientedFaceLift Phi frame c face))
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, FacewiseRegularValue Phi frame c y := by
  obtain ⟨y, hy, hycrit⟩ := exists_not_mem_nullSet_between
    (orientedFaceCriticalValues_null Phi frame c hSard) hab
  exact ⟨y, hy, (facewiseRegularValue_iff_not_mem Phi frame c y).2 hycrit⟩

/-- At the selected box scale every face level is compact in the fundamental
square and has a local product chart at each lifted preimage point. -/
theorem exists_compact_facewiseLocallyRegular_levels
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (hSard : ∀ face : Fin 3 × Bool,
      CriticalValuesNull (signedOrientedFaceLift Phi frame c face))
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, ∀ face : Fin 3 × Bool,
      IsCompact (fundamentalLevelSet
        (signedOrientedFaceLift Phi frame c face) y) ∧
      ∀ x ∈ (signedOrientedFaceLift Phi frame c face) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (signedOrientedFaceLift Phi frame c face) x) := by
  obtain ⟨y, hy, hyreg⟩ :=
    exists_facewiseRegularValue_between Phi frame c hSard hab
  refine ⟨y, hy, fun face ↦ ?_⟩
  exact ⟨isCompact_fundamentalLevelSet
      (signedOrientedFaceLift_contDiff Phi frame c face).continuous y,
    regularValue_has_local_charts
      (signedOrientedFaceLift_contDiff Phi frame c face) (hyreg face)⟩

/-- The previous result with the sole missing Sard theorem supplied once,
rather than separately for the six faces. -/
theorem exists_compact_facewiseLocallyRegular_levels_of_planarSard
    (hSard : PlanarSardTheorem)
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, ∀ face : Fin 3 × Bool,
      IsCompact (fundamentalLevelSet
        (signedOrientedFaceLift Phi frame c face) y) ∧
      ∀ x ∈ (signedOrientedFaceLift Phi frame c face) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (signedOrientedFaceLift Phi frame c face) x) := by
  apply exists_compact_facewiseLocallyRegular_levels Phi frame c _ hab
  intro face
  exact criticalValuesNull_of_sardMoreiraConclusion
    (hSard _ (signedOrientedFaceLift_contDiff Phi frame c face))

/-- For an oriented coordinate plane, Sard nullity gives a perturbation with
a compact fundamental-domain level and an implicit-function chart at every
lifted preimage point. -/
theorem exists_regular_orientedCoordinateLevel
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hSard : CriticalValuesNull (orientedCoordinateLift Phi frame i))
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      IsCompact (fundamentalLevelSet
        (orientedCoordinateLift Phi frame i) y) ∧
      ∀ x ∈ (orientedCoordinateLift Phi frame i) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (orientedCoordinateLift Phi frame i) x) :=
  exists_compact_locallyRegular_level
    (orientedCoordinateLift_contDiff Phi frame i) hSard hab

/-- Coordinate-plane version assuming the planar Sard theorem once. -/
theorem exists_regular_orientedCoordinateLevel_of_planarSard
    (hSard : PlanarSardTheorem) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      IsCompact (fundamentalLevelSet
        (orientedCoordinateLift Phi frame i) y) ∧
      ∀ x ∈ (orientedCoordinateLift Phi frame i) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (orientedCoordinateLift Phi frame i) x) := by
  apply exists_regular_orientedCoordinateLevel Phi frame i _ hab
  exact criticalValuesNull_of_sardMoreiraConclusion
    (hSard _ (orientedCoordinateLift_contDiff Phi frame i))

end


end SurfaceRegularValue
end Submission
