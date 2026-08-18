import Submission.Topology.FiniteSphereCircleSystem
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

/-- The reduced innermost-circle property required of one finite sphere stage. -/
def FiniteSphereSurgeryIntersectionSystem.HasEssentialCoordinateFilling
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota) : Prop :=
  (∃ i, (S.circle i).Essential) →
    ∃ i, (S.circle i).Essential ∧
      Nonempty (SphereCircleCoordinateFilling (S.circle i))

namespace FiniteSphereSurgeryIntersectionSystem

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

end FiniteRegularSphereSurgeryStageSequence
end PairedBandMovingSphereCollarData
end Submission.Topology
