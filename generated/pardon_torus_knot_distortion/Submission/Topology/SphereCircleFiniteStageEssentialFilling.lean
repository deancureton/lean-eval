import Submission.Topology.SphereCircleSectionPlanarPasting

/-!
# Essential doubled-coordinate fillings for finite sphere stages

Every essential circle belongs to one sphere component.  Restricting the exact stage section to
that component and applying the planar innermost-circle theorem produces an essential circle
with a doubled-coordinate filling.  Applying this independently at every audited stage proves
the essential-axis alternative for a finite regular sphere-surgery sequence.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota]

namespace FiniteSphereSurgeryIntersectionSystem

variable (F : FiniteSphereSurgeryIntersectionSystem Phi iota)

/-- The component containing any chosen essential stage circle contains an essential fiber
circle. -/
theorem exists_essential_sphereComponentFiber
    (hessential : ∃ i, (F.circle i).Essential) :
    ∃ j : Fin F.sphereFamily.count,
      ∃ i : F.sphereComponentFiber j,
        ((F.sphereComponentSection j).circle i).Essential := by
  obtain ⟨i, hi⟩ := hessential
  let j := F.sphereComponent i
  let k : F.sphereComponentFiber j := ⟨i, rfl⟩
  exact ⟨j, k, hi⟩

/-- Every finite sphere stage with an essential circle has an essential circle carrying a
doubled-coordinate filling. -/
theorem hasEssentialDoubledCoordinateFilling_of_sphereComponents :
    F.HasEssentialDoubledCoordinateFilling := by
  intro hessential
  obtain ⟨j, i, hi⟩ := F.exists_essential_sphereComponentFiber hessential
  obtain ⟨D⟩ := F.nonempty_sphereComponentCommonPoleData j
  obtain ⟨k, hk, hfill⟩ :=
    D.exists_essential_doubledCoordinateFilling_of_section ⟨i, hi⟩
  exact ⟨k.1, hk, hfill⟩

end FiniteSphereSurgeryIntersectionSystem

namespace PairedBandMovingSphereCollarData
namespace FiniteRegularSphereSurgeryStageSequence

variable (F : FiniteRegularSphereSurgeryStageSequence Phi)

/-- The componentwise planar filling theorem establishes the essential-axis alternative at
every audited stage. -/
theorem hasAxisCircleIfEssential_of_sphereComponents : F.HasAxisCircleIfEssential :=
  F.hasAxisCircleIfEssential_of_doubledCoordinateFillings fun k _ ↦
    (F.system k).hasEssentialDoubledCoordinateFilling_of_sphereComponents

end FiniteRegularSphereSurgeryStageSequence
end PairedBandMovingSphereCollarData

end Submission.Topology
