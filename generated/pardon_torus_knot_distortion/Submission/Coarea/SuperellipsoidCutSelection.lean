import Submission.Coarea.SuperellipsoidOuterSelection
import Submission.Coarea.SurfaceRegularBasedDoubleBubbleSelection
import Submission.Topology.RegularLevelTangentODE

/-!
# Cutting a regular superellipsoid without hitting its seam events

For a regular outer scale, the intersection of the transported torus with the outer surface is a
regular one-dimensional level.  A cutting height fails to be regular on that seam exactly when
the two planar differentials are dependent.  We record this bad-height set directly in covering
coordinates.  Its nullity is the one-dimensional Sard consequence required from the regular
level; all remaining exceptional sets, including the finitely many knot/outer-seam heights, are
handled here without further geometric assumptions.
-/

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Submission.PardonDistortion

open LeanEval.KnotTheory.PardonDistortion
open Submission.Topology
open Submission.SurfaceRegularValue

/-- Determinant of two planar differentials in the standard covering-plane basis. -/
def planarDifferentialDet (f g : Plane → ℝ) (uv : Plane) : ℝ :=
  fderiv ℝ f uv planeBasisFirst * fderiv ℝ g uv planeBasisSecond -
    fderiv ℝ f uv planeBasisSecond * fderiv ℝ g uv planeBasisFirst

/-- Points of a fixed outer seam at which cutting height is critical along the seam. -/
def superellipsoidSeamHeightCriticalPoints
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set Plane :=
  {uv | superellipsoidPolynomialLift Phi frame c uv = R ^ 256 ∧
    planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
      (orientedCoordinateLift Phi frame 2) uv = 0}

/-- Critical cutting heights of the regular outer seam. -/
def superellipsoidSeamHeightCriticalValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R : ℝ) : Set ℝ :=
  orientedCoordinateLift Phi frame 2 ''
    superellipsoidSeamHeightCriticalPoints Phi frame c R

/-- Explicit transversality condition for the height cut on the outer seam. -/
def IsRegularSuperellipsoidSeamHeight
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (R d : ℝ) : Prop :=
  ∀ uv, superellipsoidPolynomialLift Phi frame c uv = R ^ 256 →
    orientedCoordinateLift Phi frame 2 uv = d →
      planarDifferentialDet (superellipsoidPolynomialLift Phi frame c)
        (orientedCoordinateLift Phi frame 2) uv ≠ 0

lemma regularSuperellipsoidSeamHeight_iff_not_mem_criticalValues
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3) (R d : ℝ) :
    IsRegularSuperellipsoidSeamHeight Phi frame c R d ↔
      d ∉ superellipsoidSeamHeightCriticalValues Phi frame c R := by
  constructor
  · rintro h ⟨uv, ⟨hlevel, hdet⟩, hheight⟩
    exact h uv hlevel hheight hdet
  · intro h uv hlevel hheight hdet
    exact h ⟨uv, ⟨hlevel, hdet⟩, hheight⟩

/-- Knot parameters on the selected outer boundary. -/
def outerKnotSeamParameters
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : SuperellipsoidOuterSelection K Phi frame c r) : Set ℝ :=
  Submission.Coarea.fiberSet (superellipsoidShellParameter K frame c)
    (Ico (0 : ℝ) (2 * Real.pi)) S.scale

/-- Heights of knot points lying on the outer seam.  The cut must avoid this finite set so knot
events are assigned to exactly one of the outer and cutting boundaries. -/
def outerKnotSeamHeights
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : SuperellipsoidOuterSelection K Phi frame c r) : Set ℝ :=
  longCoordinate K frame '' outerKnotSeamParameters S

lemma outerKnotSeamHeights_finite
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : SuperellipsoidOuterSelection K Phi frame c r) :
    (outerKnotSeamHeights S).Finite :=
  S.knotFiberFinite.image _

lemma volume_outerKnotSeamHeights
    {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (S : SuperellipsoidOuterSelection K Phi frame c r) :
    volume (outerKnotSeamHeights S) = 0 :=
  (outerKnotSeamHeights_finite S).measure_zero volume

/-- Output of the cut selector at a fixed smooth outer surface. -/
structure SuperellipsoidRegularCutSelection
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (c : R3) (r D : ℝ)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r))
    (outer : SuperellipsoidOuterSelection K Phi frame c r) where
  toSmoothCarrierPlaneSelection : SmoothCarrierPlaneSelection K frame c
    (closedSuperellipsoidParameters K frame c outer.scale) r D W
  surfaceRegular : IsRegularValue (orientedCoordinateLift Phi frame 2)
    toSmoothCarrierPlaneSelection.height
  seamRegular : IsRegularSuperellipsoidSeamHeight Phi frame c outer.scale
    toSmoothCarrierPlaneSelection.height
  avoidsKnotOuterSeam :
    toSmoothCarrierPlaneSelection.height ∉ outerKnotSeamHeights outer

namespace SuperellipsoidRegularCutSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r D : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {outer : SuperellipsoidOuterSelection K Phi frame c r}

abbrev height (S : SuperellipsoidRegularCutSelection K Phi frame c r D W outer) :=
  S.toSmoothCarrierPlaneSelection.height

theorem knotFiberBound
    (S : SuperellipsoidRegularCutSelection K Phi frame c r D W outer) :
    (Submission.Coarea.fiberCount (longCoordinate K frame)
      (closedSuperellipsoidParameters K frame c outer.scale) S.height : ℝ≥0∞) ≤
        ENNReal.ofReal (40 * D) :=
  S.toSmoothCarrierPlaneSelection.knotFiberBound

end SuperellipsoidRegularCutSelection

/-- The smooth-body arclength estimate fits the existing `40D` cutting selector input. -/
lemma superellipsoidOuter_local_speed_bound
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (outer : SuperellipsoidOuterSelection K Phi frame c r) :
    (∫⁻ t in closedSuperellipsoidParameters K frame c outer.scale,
        ENNReal.ofReal (speed K t)) ≤
      ENNReal.ofReal
        (10 * (1 + shellEpsilon) * r * (distortion K).toReal) := by
  have hscalePos : 0 < outer.scale :=
    (mul_pos superellipsoidInnerFactor_pos hr).trans outer.scale_mem.1
  calc
    (∫⁻ t in closedSuperellipsoidParameters K frame c outer.scale,
        ENNReal.ofReal (speed K t)) =
        ∫⁻ t in Ico (0 : ℝ) (2 * Real.pi) ∩
          K.curve ⁻¹' closedSuperellipsoidBody frame c outer.scale,
          ENNReal.ofReal (speed K t) :=
      lintegral_closedSuperellipsoidParameters_speed_eq_halfOpen
        K frame c outer.scale
    _ ≤ ENNReal.ofReal (9 * outer.scale * (distortion K).toReal) :=
      lintegral_speed_preimage_closedSuperellipsoidBody_le K hscalePos hfinite
    _ ≤ ENNReal.ofReal
        (10 * (1 + shellEpsilon) * r * (distortion K).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      have hcoefficient : 9 * superellipsoidOuterFactor ≤
          10 * (1 + shellEpsilon) := by
        norm_num [superellipsoidOuterFactor, shellEpsilon]
      calc
        9 * outer.scale * (distortion K).toReal ≤
            9 * (superellipsoidOuterFactor * r) * (distortion K).toReal := by
          gcongr
          exact outer.scale_mem.2
        _ = (9 * superellipsoidOuterFactor) * r * (distortion K).toReal := by ring
        _ ≤ (10 * (1 + shellEpsilon)) * r * (distortion K).toReal := by
          gcongr
        _ = 10 * (1 + shellEpsilon) * r * (distortion K).toReal := by ring

/-- Choose a cut avoiding all surface, seam, and double-counting events.  The only new analytic
input is nullity of the explicitly defined seam critical-height set; global planar Sard and
finiteness of the knot/outer intersection supply the other two null sets. -/
theorem exists_superellipsoidRegularCutSelection_of_seamCriticalValues_null
    (K : Knot) (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {r : ℝ} (hr : 0 < r) (hfinite : distortion K ≠ ⊤)
    (W : SmoothLoopCarrierWitness Phi (orientedBox frame c r))
    (outer : SuperellipsoidOuterSelection K Phi frame c r)
    (hseamNull : volume
      (superellipsoidSeamHeightCriticalValues Phi frame c outer.scale) = 0) :
    Nonempty (SuperellipsoidRegularCutSelection K Phi frame c r
      (distortion K).toReal W outer) := by
  let surfaceBad := criticalValues (orientedCoordinateLift Phi frame 2)
  let seamBad := superellipsoidSeamHeightCriticalValues Phi frame c outer.scale
  let knotSeamBad := outerKnotSeamHeights outer
  let bad := surfaceBad ∪ seamBad ∪ knotSeamBad
  have hsurfaceNull : volume surfaceBad = 0 :=
    criticalValuesNull_of_sardMoreiraConclusion
      (planarSardTheorem _ (orientedCoordinateLift_contDiff Phi frame 2))
  have hbadNull : volume bad = 0 :=
    measure_union_null (measure_union_null hsurfaceNull hseamNull)
      (volume_outerKnotSeamHeights outer)
  obtain ⟨cut, hcutBad⟩ := exists_smoothCarrierPlaneSelection_avoiding_nullSet
    K W frame c (isCompact_closedSuperellipsoidParameters K frame c outer.scale)
      hr ENNReal.toReal_nonneg
      (superellipsoidOuter_local_speed_bound K Phi frame c hr hfinite outer) hbadNull
  refine ⟨{
    toSmoothCarrierPlaneSelection := cut
    surfaceRegular := (isRegularValue_iff_not_mem_criticalValues _ _).2 ?_
    seamRegular :=
      (regularSuperellipsoidSeamHeight_iff_not_mem_criticalValues _ _ _ _ _).2 ?_
    avoidsKnotOuterSeam := ?_
  }⟩
  · exact fun hmem ↦ hcutBad (Or.inl (Or.inl hmem))
  · exact fun hmem ↦ hcutBad (Or.inl (Or.inr hmem))
  · exact fun hmem ↦ hcutBad (Or.inr hmem)

end Submission.PardonDistortion
