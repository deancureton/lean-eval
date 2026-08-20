import Submission.Topology.FiniteSphereCircleSystem
import Submission.Topology.GeneralCompression
import Submission.Topology.SuperellipsoidFiniteStageAxisCharging

/-!
# Coordinate fillings for essential sphere circles

The innermost-circle argument only needs a homological conclusion.  For an essential
intersection circle, a continuous filling of either product-torus coordinate makes the
corresponding winding number zero.  The other winding is then nonzero, so the circle has the
axis slope consumed by the charged-loop counting argument.

Unlike an innermost disk surgery, the filling below is circle-valued and need not be embedded.
It is the natural target for a planar sphere-disk decomposition: cap every inessential inner
boundary by a real covering lift and glue the resulting coordinate maps.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota]
  {S : FiniteSphereSurgeryIntersectionSystem Phi iota} {i : iota}

/-- A continuous filling of one coordinate of a stage circle. -/
inductive SphereCircleCoordinateFilling
    (C : EmbeddedTorusIntersectionCircle Phi) where
  | first
      (filling : ClosedUnitDisk → Circle)
      (continuous_filling : Continuous filling)
      (boundary : ∀ t, filling (unitDiskBoundary t) =
        (transportedLoopCoordinates Phi C.windingLoop.curve t).1)
  | second
      (filling : ClosedUnitDisk → Circle)
      (continuous_filling : Continuous filling)
      (boundary : ∀ t, filling (unitDiskBoundary t) =
        (transportedLoopCoordinates Phi C.windingLoop.curve t).2)

namespace SphereCircleCoordinateFilling

/-- Filling one coordinate forces its winding to vanish. -/
theorem winding_eq_zero
    {C : EmbeddedTorusIntersectionCircle Phi}
    (D : SphereCircleCoordinateFilling C) :
    C.windingLoop.lift.first.winding = 0 ∨
      C.windingLoop.lift.second.winding = 0 := by
  cases D with
  | first filling continuous_filling boundary =>
      exact Or.inl <|
        C.windingLoop.lift.first.winding_eq_zero_of_unitDisk_filling
          filling continuous_filling boundary
  | second filling continuous_filling boundary =>
      exact Or.inr <|
        C.windingLoop.lift.second.winding_eq_zero_of_unitDisk_filling
          filling continuous_filling boundary

/-- An essential circle with one filled coordinate has nonzero coordinate-axis slope. -/
theorem isNonzeroAxisSlope
    {C : EmbeddedTorusIntersectionCircle Phi}
    (D : SphereCircleCoordinateFilling C) (hessential : C.Essential) :
    IsNonzeroAxisSlope C.windingLoop.lift.first.winding
      C.windingLoop.lift.second.winding := by
  exact ⟨D.winding_eq_zero, hessential⟩

end SphereCircleCoordinateFilling

/-- A continuous filling of an inverse-square torus coordinate.  These are exactly the
circle-valued coordinates supplied by the two ambient solid-torus sides. -/
inductive SphereCircleDoubledCoordinateFilling
    (C : EmbeddedTorusIntersectionCircle Phi) where
  | first
      (filling : ClosedUnitDisk → Circle)
      (continuous_filling : Continuous filling)
      (boundary : ∀ t, filling (unitDiskBoundary t) =
        ((transportedLoopCoordinates Phi C.windingLoop.curve t).1)⁻¹ ^ 2)
  | second
      (filling : ClosedUnitDisk → Circle)
      (continuous_filling : Continuous filling)
      (boundary : ∀ t, filling (unitDiskBoundary t) =
        ((transportedLoopCoordinates Phi C.windingLoop.curve t).2)⁻¹ ^ 2)

namespace SphereCircleDoubledCoordinateFilling

/-- Filling an inverse-square coordinate still forces the original winding to vanish. -/
theorem winding_eq_zero
    {C : EmbeddedTorusIntersectionCircle Phi}
    (D : SphereCircleDoubledCoordinateFilling C) :
    C.windingLoop.lift.first.winding = 0 ∨
      C.windingLoop.lift.second.winding = 0 := by
  cases D with
  | first filling continuous_filling boundary =>
      have hzero := C.windingLoop.lift.first.invSq.winding_eq_zero_of_unitDisk_filling
        filling continuous_filling boundary
      change -2 * C.windingLoop.lift.first.winding = 0 at hzero
      exact Or.inl (by omega)
  | second filling continuous_filling boundary =>
      have hzero := C.windingLoop.lift.second.invSq.winding_eq_zero_of_unitDisk_filling
        filling continuous_filling boundary
      change -2 * C.windingLoop.lift.second.winding = 0 at hzero
      exact Or.inr (by omega)

/-- An essential circle with a doubled-coordinate filling has nonzero coordinate-axis slope. -/
theorem isNonzeroAxisSlope
    {C : EmbeddedTorusIntersectionCircle Phi}
    (D : SphereCircleDoubledCoordinateFilling C) (hessential : C.Essential) :
    IsNonzeroAxisSlope C.windingLoop.lift.first.winding
      C.windingLoop.lift.second.winding :=
  ⟨D.winding_eq_zero, hessential⟩

end SphereCircleDoubledCoordinateFilling

/-! ## Canonical doubled-coordinate caps of one zero-winding circle -/

namespace EmbeddedTorusIntersectionCircle

variable (C : EmbeddedTorusIntersectionCircle Phi)

/-- The canonical torus-side disk map of one zero-winding circle. -/
def zeroWindingTorusDiskMap
    (hzero : C.windingLoop.windingPair = (0, 0))
    (z : ClosedUnitDisk) : transportedTorus Phi :=
  let D := C.inessentialTorusCircleDisk hzero
  ⟨D.disk z, D.range_subset ⟨z, rfl⟩⟩

theorem continuous_zeroWindingTorusDiskMap
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.zeroWindingTorusDiskMap hzero) :=
  let D := C.inessentialTorusCircleDisk hzero
  D.isEmbedding.continuous.subtype_mk _

theorem zeroWindingTorusDiskMap_boundary
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.zeroWindingTorusDiskMap hzero (unitDiskBoundary t) = C.windingLoop.curve t := by
  apply Subtype.ext
  exact (C.inessentialTorusCircleDisk hzero).boundary t

/-- Product-torus coordinates on the canonical disk of one zero-winding circle. -/
def zeroWindingTorusDiskCoordinates
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    ClosedUnitDisk → Circle × Circle :=
  fun z ↦ (transportedTorusHomeomorph Phi).symm (C.zeroWindingTorusDiskMap hzero z)

theorem continuous_zeroWindingTorusDiskCoordinates
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.zeroWindingTorusDiskCoordinates hzero) :=
  (transportedTorusHomeomorph Phi).symm.continuous.comp
    (C.continuous_zeroWindingTorusDiskMap hzero)

theorem zeroWindingTorusDiskCoordinates_boundary
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.zeroWindingTorusDiskCoordinates hzero (unitDiskBoundary t) =
      transportedLoopCoordinates Phi C.windingLoop.curve t := by
  simp only [zeroWindingTorusDiskCoordinates, transportedLoopCoordinates]
  rw [C.zeroWindingTorusDiskMap_boundary hzero t]

/-- The doubled first-coordinate map on the canonical zero-winding cap. -/
def firstZeroWindingDoubledCapMap
    (hzero : C.windingLoop.windingPair = (0, 0)) : ClosedUnitDisk → Circle :=
  fun z ↦ (C.zeroWindingTorusDiskCoordinates hzero z).1⁻¹ ^ 2

theorem continuous_firstZeroWindingDoubledCapMap
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.firstZeroWindingDoubledCapMap hzero) := by
  have hcoordinates := C.continuous_zeroWindingTorusDiskCoordinates hzero
  unfold firstZeroWindingDoubledCapMap
  fun_prop

theorem firstZeroWindingDoubledCapMap_boundary
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.firstZeroWindingDoubledCapMap hzero (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi C.windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstZeroWindingDoubledCapMap,
    C.zeroWindingTorusDiskCoordinates_boundary hzero t]

/-- The doubled second-coordinate map on the canonical zero-winding cap. -/
def secondZeroWindingDoubledCapMap
    (hzero : C.windingLoop.windingPair = (0, 0)) : ClosedUnitDisk → Circle :=
  fun z ↦ (C.zeroWindingTorusDiskCoordinates hzero z).2⁻¹ ^ 2

theorem continuous_secondZeroWindingDoubledCapMap
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    Continuous (C.secondZeroWindingDoubledCapMap hzero) := by
  have hcoordinates := C.continuous_zeroWindingTorusDiskCoordinates hzero
  unfold secondZeroWindingDoubledCapMap
  fun_prop

theorem secondZeroWindingDoubledCapMap_boundary
    (hzero : C.windingLoop.windingPair = (0, 0)) (t : ℝ) :
    C.secondZeroWindingDoubledCapMap hzero (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi C.windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondZeroWindingDoubledCapMap,
    C.zeroWindingTorusDiskCoordinates_boundary hzero t]

/-- The first zero-winding cap reparameterized onto a planar Jordan disk. -/
def firstPlanarizedZeroWindingDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (C.firstZeroWindingDoubledCapMap hzero)

theorem continuous_firstPlanarizedZeroWindingDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) :
    Continuous (C.firstPlanarizedZeroWindingDoubledCapMap hzero P) :=
  P.continuous_planarizedDiskMap (C.continuous_firstZeroWindingDoubledCapMap hzero)

@[simp]
theorem firstPlanarizedZeroWindingDoubledCapMap_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) (t : ℝ) :
    C.firstPlanarizedZeroWindingDoubledCapMap hzero P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi C.windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstPlanarizedZeroWindingDoubledCapMap,
    P.planarizedDiskMap_planeCirclePoint_exp,
    C.firstZeroWindingDoubledCapMap_boundary hzero]

/-- The second zero-winding cap reparameterized onto a planar Jordan disk. -/
def secondPlanarizedZeroWindingDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (C.secondZeroWindingDoubledCapMap hzero)

theorem continuous_secondPlanarizedZeroWindingDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) :
    Continuous (C.secondPlanarizedZeroWindingDoubledCapMap hzero P) :=
  P.continuous_planarizedDiskMap (C.continuous_secondZeroWindingDoubledCapMap hzero)

@[simp]
theorem secondPlanarizedZeroWindingDoubledCapMap_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (hzero : C.windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T C) (t : ℝ) :
    C.secondPlanarizedZeroWindingDoubledCapMap hzero P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi C.windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondPlanarizedZeroWindingDoubledCapMap,
    P.planarizedDiskMap_planeCirclePoint_exp,
    C.secondZeroWindingDoubledCapMap_boundary hzero]

end EmbeddedTorusIntersectionCircle

/-- The reduced innermost-circle property required of one finite sphere stage. -/
def FiniteSphereSurgeryIntersectionSystem.HasEssentialCoordinateFilling
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) : Prop :=
  (∃ i, (S.circle i).Essential) →
    ∃ i, (S.circle i).Essential ∧
      Nonempty (SphereCircleCoordinateFilling (S.circle i))

/-- The weaker reduced property using the inverse-square coordinates which extend over the two
ambient solid-torus sides. -/
def FiniteSphereSurgeryIntersectionSystem.HasEssentialDoubledCoordinateFilling
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) : Prop :=
  (∃ i, (S.circle i).Essential) →
    ∃ i, (S.circle i).Essential ∧
      Nonempty (SphereCircleDoubledCoordinateFilling (S.circle i))

namespace FiniteSphereSurgeryIntersectionSystem

/-! ## Canonical doubled-coordinate caps for inessential circles -/

/-! ### Caps from one zero-winding circle

The innermost-essential-circle argument does not make every circle in the ambient finite
system inessential.  It only makes the circles strictly inside the selected essential circle
inessential.  The following pointwise API exposes the same canonical torus cap from the zero
winding of one specified circle, so the later planar pasting theorem need not assume
`AllInessential` for the whole stage. -/

/-- The canonical torus-side disk of one specified zero-winding circle. -/
def torusDiskMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (z : ClosedUnitDisk) : transportedTorus Phi :=
  let D := EmbeddedTorusIntersectionCircle.inessentialTorusCircleDisk (S.circle i) hzero
  ⟨D.disk z, D.range_subset ⟨z, rfl⟩⟩

theorem continuous_torusDiskMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    Continuous (S.torusDiskMapOfZero i hzero) :=
  let D := EmbeddedTorusIntersectionCircle.inessentialTorusCircleDisk (S.circle i) hzero
  D.isEmbedding.continuous.subtype_mk _

theorem torusDiskMapOfZero_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) (t : ℝ) :
    S.torusDiskMapOfZero i hzero (unitDiskBoundary t) =
      (S.circle i).windingLoop.curve t := by
  apply Subtype.ext
  exact (EmbeddedTorusIntersectionCircle.inessentialTorusCircleDisk
    (S.circle i) hzero).boundary t

/-- Product-torus coordinates on the canonical cap of one zero-winding circle. -/
def inessentialTorusDiskCoordinatesOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    ClosedUnitDisk → Circle × Circle :=
  fun z ↦ (transportedTorusHomeomorph Phi).symm (S.torusDiskMapOfZero i hzero z)

theorem continuous_inessentialTorusDiskCoordinatesOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    Continuous (S.inessentialTorusDiskCoordinatesOfZero i hzero) :=
  (transportedTorusHomeomorph Phi).symm.continuous.comp
    (S.continuous_torusDiskMapOfZero i hzero)

theorem inessentialTorusDiskCoordinatesOfZero_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) (t : ℝ) :
    S.inessentialTorusDiskCoordinatesOfZero i hzero (unitDiskBoundary t) =
      transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t := by
  simp only [inessentialTorusDiskCoordinatesOfZero, transportedLoopCoordinates]
  rw [S.torusDiskMapOfZero_boundary i hzero t]

/-- The doubled first-coordinate map on one zero-winding torus cap. -/
def firstInessentialDoubledCapMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    ClosedUnitDisk → Circle :=
  fun z ↦ (S.inessentialTorusDiskCoordinatesOfZero i hzero z).1⁻¹ ^ 2

theorem continuous_firstInessentialDoubledCapMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    Continuous (S.firstInessentialDoubledCapMapOfZero i hzero) := by
  have hcoordinates := S.continuous_inessentialTorusDiskCoordinatesOfZero i hzero
  unfold firstInessentialDoubledCapMapOfZero
  fun_prop

theorem firstInessentialDoubledCapMapOfZero_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) (t : ℝ) :
    S.firstInessentialDoubledCapMapOfZero i hzero (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstInessentialDoubledCapMapOfZero,
    S.inessentialTorusDiskCoordinatesOfZero_boundary i hzero t]

/-- The doubled second-coordinate map on one zero-winding torus cap. -/
def secondInessentialDoubledCapMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    ClosedUnitDisk → Circle :=
  fun z ↦ (S.inessentialTorusDiskCoordinatesOfZero i hzero z).2⁻¹ ^ 2

theorem continuous_secondInessentialDoubledCapMapOfZero
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) :
    Continuous (S.secondInessentialDoubledCapMapOfZero i hzero) := by
  have hcoordinates := S.continuous_inessentialTorusDiskCoordinatesOfZero i hzero
  unfold secondInessentialDoubledCapMapOfZero
  fun_prop

theorem secondInessentialDoubledCapMapOfZero_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0)) (t : ℝ) :
    S.secondInessentialDoubledCapMapOfZero i hzero (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondInessentialDoubledCapMapOfZero,
    S.inessentialTorusDiskCoordinatesOfZero_boundary i hzero t]

/-! ### Stage-wide convenience wrappers -/

/-- Product-torus coordinates of the canonical torus disk capping an inessential circle. -/
def inessentialTorusDiskCoordinates
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) : ClosedUnitDisk → Circle × Circle :=
  fun z ↦ (transportedTorusHomeomorph Phi).symm (S.torusDiskMap hzero i z)

theorem continuous_inessentialTorusDiskCoordinates
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) :
    Continuous (S.inessentialTorusDiskCoordinates hzero i) :=
  (transportedTorusHomeomorph Phi).symm.continuous.comp
    (S.continuous_torusDiskMap hzero i)

theorem inessentialTorusDiskCoordinates_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) (t : ℝ) :
    S.inessentialTorusDiskCoordinates hzero i (unitDiskBoundary t) =
      transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t := by
  have hboundary :
      S.torusDiskMap hzero i (unitDiskBoundary t) =
        (S.circle i).windingLoop.curve t := by
    apply Subtype.ext
    exact (S.torusDisk hzero i).boundary t
  simp only [inessentialTorusDiskCoordinates, transportedLoopCoordinates]
  rw [hboundary]

/-- The doubled first-coordinate map on the canonical inessential torus cap. -/
def firstInessentialDoubledCapMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) : ClosedUnitDisk → Circle :=
  fun z ↦ (S.inessentialTorusDiskCoordinates hzero i z).1⁻¹ ^ 2

theorem continuous_firstInessentialDoubledCapMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) :
    Continuous (S.firstInessentialDoubledCapMap hzero i) := by
  have hcoordinates := S.continuous_inessentialTorusDiskCoordinates hzero i
  unfold firstInessentialDoubledCapMap
  fun_prop

theorem firstInessentialDoubledCapMap_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) (t : ℝ) :
    S.firstInessentialDoubledCapMap hzero i (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstInessentialDoubledCapMap, S.inessentialTorusDiskCoordinates_boundary hzero i t]

/-- The doubled second-coordinate map on the canonical inessential torus cap. -/
def secondInessentialDoubledCapMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) : ClosedUnitDisk → Circle :=
  fun z ↦ (S.inessentialTorusDiskCoordinates hzero i z).2⁻¹ ^ 2

theorem continuous_secondInessentialDoubledCapMap
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) :
    Continuous (S.secondInessentialDoubledCapMap hzero i) := by
  have hcoordinates := S.continuous_inessentialTorusDiskCoordinates hzero i
  unfold secondInessentialDoubledCapMap
  fun_prop

theorem secondInessentialDoubledCapMap_boundary
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) (t : ℝ) :
    S.secondInessentialDoubledCapMap hzero i (unitDiskBoundary t) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondInessentialDoubledCapMap, S.inessentialTorusDiskCoordinates_boundary hzero i t]

/-! ## Canonical caps in a common planar sphere chart -/

/-- The first pointwise zero-winding cap, reparameterized onto a planar Jordan disk. -/
def firstPlanarizedInessentialDoubledCapMapOfZero
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (S.firstInessentialDoubledCapMapOfZero i hzero)

theorem continuous_firstPlanarizedInessentialDoubledCapMapOfZero
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    Continuous (S.firstPlanarizedInessentialDoubledCapMapOfZero i hzero P) :=
  P.continuous_planarizedDiskMap
    (S.continuous_firstInessentialDoubledCapMapOfZero i hzero)

@[simp]
theorem firstPlanarizedInessentialDoubledCapMapOfZero_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) (t : ℝ) :
    S.firstPlanarizedInessentialDoubledCapMapOfZero i hzero P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstPlanarizedInessentialDoubledCapMapOfZero,
    P.planarizedDiskMap_planeCirclePoint_exp,
    S.firstInessentialDoubledCapMapOfZero_boundary i hzero]

/-- The second pointwise zero-winding cap, reparameterized onto a planar Jordan disk. -/
def secondPlanarizedInessentialDoubledCapMapOfZero
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (S.secondInessentialDoubledCapMapOfZero i hzero)

theorem continuous_secondPlanarizedInessentialDoubledCapMapOfZero
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    Continuous (S.secondPlanarizedInessentialDoubledCapMapOfZero i hzero P) :=
  P.continuous_planarizedDiskMap
    (S.continuous_secondInessentialDoubledCapMapOfZero i hzero)

@[simp]
theorem secondPlanarizedInessentialDoubledCapMapOfZero_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hzero : (S.circle i).windingLoop.windingPair = (0, 0))
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) (t : ℝ) :
    S.secondPlanarizedInessentialDoubledCapMapOfZero i hzero P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondPlanarizedInessentialDoubledCapMapOfZero,
    P.planarizedDiskMap_planeCirclePoint_exp,
    S.secondInessentialDoubledCapMapOfZero_boundary i hzero]

/-- The first doubled-coordinate cap, reparameterized onto a closed planar Jordan disk. -/
def firstPlanarizedInessentialDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (S.firstInessentialDoubledCapMap hzero i)

theorem continuous_firstPlanarizedInessentialDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    Continuous (S.firstPlanarizedInessentialDoubledCapMap hzero i P) :=
  P.continuous_planarizedDiskMap
    (S.continuous_firstInessentialDoubledCapMap hzero i)

@[simp]
theorem firstPlanarizedInessentialDoubledCapMap_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) (t : ℝ) :
    S.firstPlanarizedInessentialDoubledCapMap hzero i P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
  rw [firstPlanarizedInessentialDoubledCapMap,
    P.planarizedDiskMap_planeCirclePoint_exp,
    S.firstInessentialDoubledCapMap_boundary hzero i]

/-- The second doubled-coordinate cap, reparameterized onto a closed planar Jordan disk. -/
def secondPlanarizedInessentialDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    closure P.planeJordanCircle.inside → Circle :=
  P.planarizedDiskMap (S.secondInessentialDoubledCapMap hzero i)

theorem continuous_secondPlanarizedInessentialDoubledCapMap
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) :
    Continuous (S.secondPlanarizedInessentialDoubledCapMap hzero i P) :=
  P.continuous_planarizedDiskMap
    (S.continuous_secondInessentialDoubledCapMap hzero i)

@[simp]
theorem secondPlanarizedInessentialDoubledCapMap_planeCirclePoint_exp
    {T : EmbeddedTopologicalSphereInR3}
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota)
    (P : EmbeddedSphereCirclePoleData T (S.circle i)) (t : ℝ) :
    S.secondPlanarizedInessentialDoubledCapMap hzero i P
        (P.planeCirclePoint (Circle.exp t)) =
      ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
  rw [secondPlanarizedInessentialDoubledCapMap,
    P.planarizedDiskMap_planeCirclePoint_exp,
    S.secondInessentialDoubledCapMap_boundary hzero i]

/-- The canonical torus-side disk of an inessential circle fills its doubled first
coordinate.  This is the cap used on an inner boundary of an innermost sphere disk. -/
def firstDoubledCoordinateFillingOfInessential
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) :
    SphereCircleDoubledCoordinateFilling (S.circle i) :=
  .first (S.firstInessentialDoubledCapMap hzero i)
    (S.continuous_firstInessentialDoubledCapMap hzero i)
    (S.firstInessentialDoubledCapMap_boundary hzero i)

/-- The canonical torus-side disk of an inessential circle also fills its doubled second
coordinate. -/
def secondDoubledCoordinateFillingOfInessential
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (hzero : S.AllInessential) (i : iota) :
    SphereCircleDoubledCoordinateFilling (S.circle i) :=
  .second (S.secondInessentialDoubledCapMap hzero i)
    (S.continuous_secondInessentialDoubledCapMap hzero i)
    (S.secondInessentialDoubledCapMap_boundary hzero i)

/-- A coordinate filling supplies the axis circle required by the quantitative route. -/
theorem exists_nonzeroAxisSlope_of_hasEssentialCoordinateFilling
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (D : S.HasEssentialCoordinateFilling)
    (hessential : ∃ i, (S.circle i).Essential) :
    ∃ i, IsNonzeroAxisSlope
      (S.circle i).windingLoop.lift.first.winding
      (S.circle i).windingLoop.lift.second.winding := by
  obtain ⟨i, hi, ⟨F⟩⟩ := D hessential
  exact ⟨i, F.isNonzeroAxisSlope hi⟩

/-- A doubled-coordinate filling supplies the axis circle required by the quantitative route. -/
theorem exists_nonzeroAxisSlope_of_hasEssentialDoubledCoordinateFilling
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (D : S.HasEssentialDoubledCoordinateFilling)
    (hessential : ∃ i, (S.circle i).Essential) :
    ∃ i, IsNonzeroAxisSlope
      (S.circle i).windingLoop.lift.first.winding
      (S.circle i).windingLoop.lift.second.winding := by
  obtain ⟨i, hi, ⟨F⟩⟩ := D hessential
  exact ⟨i, F.isNonzeroAxisSlope hi⟩

end FiniteSphereSurgeryIntersectionSystem

/-! ## Axis slopes from sphere disks lying on one torus side -/

namespace FiniteSphereSurgeryIntersectionSystem

/-- The chosen sphere-side disk for a circle lies entirely on one closed side of the transported
torus.  Unlike a compressing disk, its interior is not required to miss the torus. -/
def SphereDiskLiesOnOneTorusSide
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota) : Prop :=
  (∀ z, (S.sphereDisk i).disk z ∈ transportedTubeSide Phi) ∨
    (∀ z, (S.sphereDisk i).disk z ∈ transportedExteriorSide Phi)

private theorem curve_eq_transportedTorusMap_coordinates
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota) (t : ℝ) :
    ((S.circle i).windingLoop.curve t : R3) = transportedTorusMap Phi
      (transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t) := by
  change ((S.circle i).windingLoop.curve t : R3) =
    (((transportedTorusHomeomorph Phi)
      ((transportedTorusHomeomorph Phi).symm ((S.circle i).windingLoop.curve t))) :
        transportedTorus Phi)
  exact congrArg Subtype.val <|
    ((transportedTorusHomeomorph Phi).apply_symm_apply
      ((S.circle i).windingLoop.curve t)).symm

private def firstDoubledCoordinateFillingOfSphereDiskLiesInTubeSide
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hside : ∀ z, (S.sphereDisk i).disk z ∈ transportedTubeSide Phi) :
    SphereCircleDoubledCoordinateFilling (S.circle i) := by
  let g : ClosedUnitDisk → transportedTubeSide Phi :=
    fun z ↦ ⟨(S.sphereDisk i).disk z, hside z⟩
  have hg : Continuous g := (S.sphereDisk i).isEmbedding.continuous.subtype_mk _
  have hboundary : ∀ t,
      transportedTubeLongitudeCoordinate Phi (g (unitDiskBoundary t)) =
        ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).1)⁻¹ ^ 2 := by
    intro t
    let zw := transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t
    have hcurve := S.curve_eq_transportedTorusMap_coordinates i t
    change transportedTubeLongitudeCoordinate Phi
      ⟨(S.sphereDisk i).disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨(S.sphereDisk i).disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedTubeSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedTubeSide Phi zw.1 zw.2⟩ by
      apply Subtype.ext
      exact (S.sphereDisk_boundary i t).trans hcurve]
    exact transportedTubeLongitudeCoordinate_torusMap Phi zw.1 zw.2
  exact .first (transportedTubeLongitudeCoordinate Phi ∘ g)
    ((continuous_transportedTubeLongitudeCoordinate Phi).comp hg) hboundary

private def secondDoubledCoordinateFillingOfSphereDiskLiesInExteriorSide
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hside : ∀ z, (S.sphereDisk i).disk z ∈ transportedExteriorSide Phi) :
    SphereCircleDoubledCoordinateFilling (S.circle i) := by
  let g : ClosedUnitDisk → transportedExteriorSide Phi :=
    fun z ↦ ⟨(S.sphereDisk i).disk z, hside z⟩
  have hg : Continuous g := (S.sphereDisk i).isEmbedding.continuous.subtype_mk _
  have hboundary : ∀ t,
      transportedExteriorMeridianCoordinate Phi (g (unitDiskBoundary t)) =
        ((transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t).2)⁻¹ ^ 2 := by
    intro t
    let zw := transportedLoopCoordinates Phi (S.circle i).windingLoop.curve t
    have hcurve := S.curve_eq_transportedTorusMap_coordinates i t
    change transportedExteriorMeridianCoordinate Phi
      ⟨(S.sphereDisk i).disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ = _
    rw [show
      (⟨(S.sphereDisk i).disk (unitDiskBoundary t), hside (unitDiskBoundary t)⟩ :
        transportedExteriorSide Phi) =
      ⟨transportedTorusMap Phi zw,
        transportedTorusMap_mem_transportedExteriorSide Phi zw.1 zw.2⟩ by
      apply Subtype.ext
      exact (S.sphereDisk_boundary i t).trans hcurve]
    exact transportedExteriorMeridianCoordinate_torusMap Phi zw.1 zw.2
  exact .second (transportedExteriorMeridianCoordinate Phi ∘ g)
    ((continuous_transportedExteriorMeridianCoordinate Phi).comp hg) hboundary

/-- A one-sided chosen sphere disk directly supplies the weaker doubled-coordinate filling. -/
theorem nonempty_doubledCoordinateFilling_of_sphereDiskLiesOnOneTorusSide
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hside : S.SphereDiskLiesOnOneTorusSide i) :
    Nonempty (SphereCircleDoubledCoordinateFilling (S.circle i)) := by
  rcases hside with hin | hout
  · exact ⟨S.firstDoubledCoordinateFillingOfSphereDiskLiesInTubeSide i hin⟩
  · exact ⟨S.secondDoubledCoordinateFillingOfSphereDiskLiesInExteriorSide i hout⟩

/-- An essential circle whose chosen sphere disk lies on one torus side has a nonzero coordinate
axis slope. -/
theorem isNonzeroAxisSlope_of_sphereDisk_liesOnOneTorusSide
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) (i : iota)
    (hessential : (S.circle i).Essential) (hside : S.SphereDiskLiesOnOneTorusSide i) :
    IsNonzeroAxisSlope (S.circle i).windingLoop.lift.first.winding
      (S.circle i).windingLoop.lift.second.winding := by
  obtain ⟨D⟩ := S.nonempty_doubledCoordinateFilling_of_sphereDiskLiesOnOneTorusSide i hside
  exact D.isNonzeroAxisSlope hessential

/-- The concrete reduced innermost-circle property: whenever a stage has an essential circle,
one essential circle has a canonical sphere disk lying on a single torus side. -/
def HasEssentialOneSidedSphereDisk
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) : Prop :=
  (∃ i, (S.circle i).Essential) →
    ∃ i, (S.circle i).Essential ∧ S.SphereDiskLiesOnOneTorusSide i

/-- A one-sided sphere disk supplies the axis-circle alternative. -/
theorem exists_nonzeroAxisSlope_of_hasEssentialOneSidedSphereDisk
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    (D : S.HasEssentialOneSidedSphereDisk)
    (hessential : ∃ i, (S.circle i).Essential) :
    ∃ i, IsNonzeroAxisSlope
      (S.circle i).windingLoop.lift.first.winding
      (S.circle i).windingLoop.lift.second.winding := by
  obtain ⟨i, hi, hside⟩ := D hessential
  exact ⟨i, S.isNonzeroAxisSlope_of_sphereDisk_liesOnOneTorusSide i hi hside⟩

end FiniteSphereSurgeryIntersectionSystem

namespace PairedBandMovingSphereCollarData
namespace FiniteRegularSphereSurgeryStageSequence

variable {F : FiniteRegularSphereSurgeryStageSequence Phi}

/-- Coordinate fillings at every audited stage establish the axis-circle alternative. -/
theorem hasAxisCircleIfEssential_of_coordinateFillings
    (fillings : ∀ k, k ≤ F.length →
      (F.system k).HasEssentialCoordinateFilling) :
    F.HasAxisCircleIfEssential := by
  intro k hk hessential
  exact (F.system k).exists_nonzeroAxisSlope_of_hasEssentialCoordinateFilling
    (fillings k hk) hessential

/-- Doubled-coordinate fillings at every audited stage establish the axis-circle alternative. -/
theorem hasAxisCircleIfEssential_of_doubledCoordinateFillings
    (fillings : ∀ k, k ≤ F.length →
      (F.system k).HasEssentialDoubledCoordinateFilling) :
    F.HasAxisCircleIfEssential := by
  intro k hk hessential
  exact (F.system k).exists_nonzeroAxisSlope_of_hasEssentialDoubledCoordinateFilling
    (fillings k hk) hessential

/-- One-sided canonical sphere disks at every audited stage establish the axis-circle
alternative. -/
theorem hasAxisCircleIfEssential_of_oneSidedSphereDisks
    (fillings : ∀ k, k ≤ F.length →
      (F.system k).HasEssentialOneSidedSphereDisk) :
    F.HasAxisCircleIfEssential := by
  intro k hk hessential
  exact (F.system k).exists_nonzeroAxisSlope_of_hasEssentialOneSidedSphereDisk
    (fillings k hk) hessential

end FiniteRegularSphereSurgeryStageSequence
end PairedBandMovingSphereCollarData
end Submission.Topology
