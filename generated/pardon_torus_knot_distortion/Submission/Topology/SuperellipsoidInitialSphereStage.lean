import Submission.Topology.FiniteSphereCircleSystem
import Submission.Topology.SuperellipsoidAnalyticSphere
import Submission.Topology.SuperellipsoidOuterSmoothCircleSection
import Submission.Topology.SuperellipsoidThreePageAttachment

/-!
# Canonical initial outer-superellipsoid sphere stage

The regular outer polynomial level supplies its exact smooth finite circle section.  The convex
outer superellipsoid supplies the one embedded sphere and its parity side.  Connected-component
selection and all sphere-side filling disks are then automatic.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}

namespace FiniteSuperellipsoidOuterTorusSmoothCircleFamily

variable (F : FiniteSuperellipsoidOuterTorusSmoothCircleFamily Phi frame c R d)
  [Fintype F.index] (hR : 0 < R)

/-- Minimal exact geometry of the initial convex outer sphere. -/
def initialOuterBasicStageGeometry :
    FiniteCircleSectionBasicStageGeometry F.toFiniteEmbeddedTorusCircleSection where
  sphereFamily := outerSuperellipsoidSphereFamily frame c hR
  insideCell := interior (closedSuperellipsoidBody frame c R)
  sphereFamily_is_boundary := outerSuperellipsoidSphereFamily_is_boundary frame c hR
  intersection_eq := by
    rw [outerSuperellipsoidSphereFamily_carrier frame c hR,
      frontier_closedSuperellipsoidBody_eq_boundary frame c hR]
    exact Set.inter_comm _ _
  eventRegion := superellipsoidOuterTorusSection Phi frame c R
  circle_mem_event i t := F.circle_mem_outer i ⟨Circle.exp t, (F.circle i).parametrization t⟩

/-- The initial convex sphere and its smooth outer circles form a complete surgery system. -/
def initialOuterSphereSurgerySystem :
    FiniteSphereSurgeryIntersectionSystem Phi F.index :=
  (F.initialOuterBasicStageGeometry hR).toFiniteSphereSurgeryIntersectionSystem

@[simp] theorem initialOuterSphereSurgerySystem_sphereFamily :
    (F.initialOuterSphereSurgerySystem hR).sphereFamily =
      outerSuperellipsoidSphereFamily frame c hR :=
  rfl

@[simp] theorem initialOuterSphereSurgerySystem_insideCell :
    (F.initialOuterSphereSurgerySystem hR).insideCell =
      interior (closedSuperellipsoidBody frame c R) :=
  rfl

/-- Reindex the canonical initial stage by `Fin`, as required by finite stage sequences. -/
def initialOuterFinSphereSurgerySystem :
    FiniteSphereSurgeryIntersectionSystem Phi (Fin (Fintype.card F.index)) :=
  (F.initialOuterSphereSurgerySystem hR).reindex (Fintype.equivFin F.index).symm

end FiniteSuperellipsoidOuterTorusSmoothCircleFamily
end Submission.Topology
