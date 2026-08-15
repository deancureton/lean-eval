import Submission.Topology.CoordinatePlaneIntersectionCircles
import Submission.Topology.ShiftedCompressingDisk

/-!
# Smooth essential circles in a regular torus section

`ComponentCircleClassification` supplies only a topological circle parametrization.  In
particular, its chosen homeomorphism and the covering lift chosen from it do not carry the `C¹`
data required by the direct intersection certificate.

This module records the extra geometric input without strengthening the topological
classification falsely.  A `SmoothEssentialSectionCircle` is an already embedded section circle
whose real-periodic transported loop has explicit smooth angle lifts, an embedded fundamental
parametrization, and regular transformed-slope roots.  Its range is required to be exactly one
connected component, so it can replace the arbitrary topological parametrization of that
component in the disk-surgery construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {a b : ℝ}

/-- Honest smooth data for one essential circle component of a regular coordinate-plane section.

The underlying `EmbeddedTorusIntersectionCircle` retains both the explicit real-periodic ambient
parametrization and its chosen pair of real angle lifts.  The next four fields are precisely the
analytic and embeddedness hypotheses consumed by the seam-free `SL(2,ℤ)` certificate. -/
structure SmoothEssentialSectionCircle
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (p q : ℕ) where
  embeddedCircle : EmbeddedTorusIntersectionCircle Phi
  range_eq_component : Set.range embeddedCircle.circle =
    (fun z : coordinateTorusLevelSet Phi frame S.selection.level ↦
      transportedTorusMap Phi z) '' componentPiece c
  contDiff_first : ContDiff ℝ 1 embeddedCircle.windingLoop.lift.first.angle
  contDiff_second : ContDiff ℝ 1 embeddedCircle.windingLoop.lift.second.angle
  coordinates_injOn : Set.InjOn
    (transportedLoopCoordinates Phi embeddedCircle.windingLoop.curve)
    (Ico (0 : ℝ) (2 * Real.pi))
  regular_transformed_roots : ∀ t,
    Circle.exp (transformedSlopeAngle p q embeddedCircle.windingLoop.lift t) = 1 →
      deriv (transformedSlopeAngle p q embeddedCircle.windingLoop.lift) t ≠ 0
  essential : embeddedCircle.Essential

namespace SmoothEssentialSectionCircle

variable {S : RegularCoordinateTorusLevel Phi frame a b}
  {c : ConnectedComponents
    (coordinateTorusLevelSet Phi frame S.selection.level)}
  {p q : ℕ}

/-- Forgetting the extra smooth structure gives exactly the embedded circle used by the existing
plane-section and surgery APIs. -/
def toEmbeddedTorusIntersectionCircle
    (E : SmoothEssentialSectionCircle S c p q) :
    EmbeddedTorusIntersectionCircle Phi :=
  E.embeddedCircle

/-- The smooth parametrization and the arbitrary topological parametrization supplied by a
`ComponentCircleClassification` have the same ambient range.  No differentiability of the latter
is asserted. -/
theorem range_eq_embeddedCircleOfComponent
    (E : SmoothEssentialSectionCircle S c p q)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level)) :
    Set.range E.embeddedCircle.circle =
      Set.range
        (FiniteCoordinatePlaneTorusCircleFamily.embeddedCircleOfComponent S C c).circle := by
  rw [E.range_eq_component,
    FiniteCoordinatePlaneTorusCircleFamily.component_circle_range]

end SmoothEssentialSectionCircle

/-- An embedded disk bounded by a smooth essential section circle, including the exact interior
disjointness needed for compression.  This separates the disk construction from the smooth
section parametrization contract. -/
structure SmoothEssentialSectionCompression
    {S : RegularCoordinateTorusLevel Phi frame a b}
    {c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)}
    {p q : ℕ} (E : SmoothEssentialSectionCircle S c p q) where
  disk : ClosedUnitDisk → R3
  isEmbedding : IsEmbedding disk
  boundary : ∀ t, disk (unitDiskBoundary t) = E.embeddedCircle.windingLoop.curve t
  interior_disjoint : ∀ z : ClosedUnitDisk, ‖(z : ℂ)‖ < 1 →
    disk z ∉ transportedTorus Phi

namespace SmoothEssentialSectionCompression

variable {S : RegularCoordinateTorusLevel Phi frame a b}
  {c : ConnectedComponents
    (coordinateTorusLevelSet Phi frame S.selection.level)}
  {p q : ℕ} {E : SmoothEssentialSectionCircle S c p q}

/-- Upgrade an existing essential-boundary disk when its boundary loop is exactly the smooth
section loop.  This is the minimal boundary-preservation input needed after an innermost-circle
surgery: range equality alone would not preserve the chosen real lift or its derivatives. -/
def ofEssentialBoundaryEmbeddedDisk
    (D : EssentialBoundaryEmbeddedDisk Phi)
    (hboundaryLoop : D.boundaryLoop = E.embeddedCircle.windingLoop)
    (hinterior : D.InteriorDisjoint) :
    SmoothEssentialSectionCompression E where
  disk := D.disk
  isEmbedding := D.isEmbedding
  boundary t := by
    rw [← hboundaryLoop]
    exact D.boundary t
  interior_disjoint := hinterior

/-- Upgrade an already constructed general compression when its retained boundary is the smooth
section loop. -/
def ofGeneralCompressingDiskWitness
    (D : GeneralCompressingDiskWitness Phi)
    (hboundaryLoop : D.boundaryLoop = E.embeddedCircle.windingLoop) :
    SmoothEssentialSectionCompression E where
  disk := D.disk
  isEmbedding := D.isEmbedding
  boundary t := by
    rw [← hboundaryLoop]
    exact D.boundary t
  interior_disjoint := D.interior_disjoint

/-- Forget the smooth certificate fields while retaining the exact essential boundary loop. -/
def toEssentialBoundaryEmbeddedDisk
    (W : SmoothEssentialSectionCompression E) :
    EssentialBoundaryEmbeddedDisk Phi where
  boundaryLoop := E.embeddedCircle.windingLoop
  disk := W.disk
  isEmbedding := W.isEmbedding
  boundary := W.boundary
  essential := E.essential

/-- A smooth essential section disk with disjoint interior is an ordinary general compression
witness, with its smooth boundary lift definitionally retained. -/
def toGeneralCompressingDiskWitness
    (W : SmoothEssentialSectionCompression E) :
    GeneralCompressingDiskWitness Phi :=
  W.toEssentialBoundaryEmbeddedDisk.toGeneralCompressingDiskWitness W.interior_disjoint

@[simp] theorem toGeneralCompressingDiskWitness_boundaryLoop
    (W : SmoothEssentialSectionCompression E) :
    W.toGeneralCompressingDiskWitness.boundaryLoop = E.embeddedCircle.windingLoop :=
  rfl

end SmoothEssentialSectionCompression

namespace FiniteInnermostCircleSurgeryContract

variable {S : RegularCoordinateTorusLevel Phi frame a b}
  {component : ConnectedComponents
    (coordinateTorusLevelSet Phi frame S.selection.level)}
  {p q : ℕ} {E : SmoothEssentialSectionCircle S component p q}
  {ι : Type*} [DecidableEq ι]
  {system : FinitePlaneDiskTorusCircleSystem Phi ι}

/-- Boundary preservation in the surgery contract transports the smooth lift and transversality
data of the specified initial circle all the way to the final interior-disjoint compression.
The only matching hypothesis is equality of the two retained boundary loops; equality of their
ranges would not suffice. -/
theorem exists_smoothEssentialSectionCompression
    (C : FiniteInnermostCircleSurgeryContract Phi ι system)
    (i : ι) (hi : system.InnermostEssential i)
    (hboundary : (system.circle i).windingLoop = E.embeddedCircle.windingLoop) :
    Nonempty (SmoothEssentialSectionCompression E) := by
  obtain ⟨D, hD⟩ := C.exists_generalCompressingDiskWitness_with_boundary i hi
  exact ⟨SmoothEssentialSectionCompression.ofGeneralCompressingDiskWitness D
    (hD.trans hboundary)⟩

end FiniteInnermostCircleSurgeryContract

end Submission.Topology

namespace Submission.PardonDistortion.DoubleBubbleSelection

open Submission.Topology
open Submission.Torus

variable {K : Knot} {frame : Equiv.Perm (Fin 3)} {c0 : R3} {r a b : ℝ}
  {Phi : AmbientIsotopy}
  {R : RegularCoordinateTorusLevel Phi frame a b}
  {component : ConnectedComponents
    (coordinateTorusLevelSet Phi frame R.selection.level)}
  {p q : ℕ} {E : SmoothEssentialSectionCircle R component p q}

/-- End-to-end seam-free charging for a compression whose boundary is supplied by an honest
smooth essential section circle.  The disk is rotated through the canonical non-root phase; its
image and geometric event cover are unchanged. -/
noncomputable def CompressionBoundaryEventCover.ofSmoothEssentialSectionCompression
    (S : DoubleBubbleSelection K frame c0 r)
    (W : SmoothEssentialSectionCompression E) (hc : p.Coprime q)
    (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) = standardTorusCurve p q (sigma.f t))
    (G : CompressionBoundaryEventCover S W.toGeneralCompressingDiskWitness p q) :
    ChargedCompression (Phi := Phi) p q S :=
  G.toCanonicallyShiftedChargedCompressionOfRawRegular S
    W.toGeneralCompressingDiskWitness p q hc sigma hclass
    E.contDiff_first E.contDiff_second E.regular_transformed_roots
    E.coordinates_injOn

end Submission.PardonDistortion.DoubleBubbleSelection
