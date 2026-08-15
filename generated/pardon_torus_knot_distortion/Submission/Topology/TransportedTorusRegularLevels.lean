import Submission.SardMoreira.Planar

open Set
open scoped Topology

namespace Submission
namespace SurfaceRegularValue

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# Unconditional regular slices of a transported torus

The planar Sard theorem proved in `Submission.SardMoreira.Planar` removes the
last hypothesis from the coordinate-plane and simultaneous six-face selectors.
The two small structures below retain precisely the compact fundamental-domain
fiber and the local implicit-function charts used by later component arguments.
-/

/-- A level chosen in an interval, together with compactness in the closed
fundamental square and a regular-level chart at every point of the full lifted
fiber. -/
structure CompactRegularLevelSelection (f : Plane → ℝ) (a b : ℝ) where
  level : ℝ
  level_mem : level ∈ Ioo a b
  isCompact : IsCompact (fundamentalLevelSet f level)
  localCharts : ∀ x ∈ f ⁻¹' {level}, Nonempty (RegularLevelChart f x)

/-- A common scale chosen for all six oriented faces, retaining compactness and
local regular-level charts face by face. -/
structure CompactFacewiseRegularLevelSelection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    (a b : ℝ) where
  level : ℝ
  level_mem : level ∈ Ioo a b
  isCompact : ∀ face : Fin 3 × Bool,
    IsCompact (fundamentalLevelSet
      (signedOrientedFaceLift Phi frame c face) level)
  localCharts : ∀ face : Fin 3 × Bool,
    ∀ x ∈ (signedOrientedFaceLift Phi frame c face) ⁻¹' {level},
      Nonempty (RegularLevelChart
        (signedOrientedFaceLift Phi frame c face) x)

/-- Unconditional coordinate-plane selector for the transported torus. -/
theorem exists_regular_orientedCoordinateLevel_unconditional
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      IsCompact (fundamentalLevelSet
        (orientedCoordinateLift Phi frame i) y) ∧
      ∀ x ∈ (orientedCoordinateLift Phi frame i) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (orientedCoordinateLift Phi frame i) x) :=
  exists_regular_orientedCoordinateLevel_of_planarSard
    planarSardTheorem Phi frame i hab

/-- The coordinate-plane selector packaged for subsequent component
arguments. -/
theorem nonempty_compactRegular_orientedCoordinateLevelSelection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (i : Fin 3)
    {a b : ℝ} (hab : a < b) :
    Nonempty (CompactRegularLevelSelection
      (orientedCoordinateLift Phi frame i) a b) := by
  obtain ⟨y, hy, hcompact, hcharts⟩ :=
    exists_regular_orientedCoordinateLevel_unconditional Phi frame i hab
  exact ⟨⟨y, hy, hcompact, hcharts⟩⟩

/-- Unconditional simultaneous selector for all six oriented box faces. -/
theorem exists_compact_facewiseLocallyRegular_levels_unconditional
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, ∀ face : Fin 3 × Bool,
      IsCompact (fundamentalLevelSet
        (signedOrientedFaceLift Phi frame c face) y) ∧
      ∀ x ∈ (signedOrientedFaceLift Phi frame c face) ⁻¹' {y},
        Nonempty (RegularLevelChart
          (signedOrientedFaceLift Phi frame c face) x) :=
  exists_compact_facewiseLocallyRegular_levels_of_planarSard
    planarSardTheorem Phi frame c hab

/-- The simultaneous six-face selector packaged for subsequent component
arguments. -/
theorem nonempty_compactFacewiseRegularLevelSelection
    (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3)) (c : R3)
    {a b : ℝ} (hab : a < b) :
    Nonempty (CompactFacewiseRegularLevelSelection Phi frame c a b) := by
  obtain ⟨y, hy, hfaces⟩ :=
    exists_compact_facewiseLocallyRegular_levels_unconditional
      Phi frame c hab
  exact ⟨⟨y, hy, fun face ↦ (hfaces face).1,
    fun face ↦ (hfaces face).2⟩⟩

end
end SurfaceRegularValue
end Submission
