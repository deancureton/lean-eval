import Submission.SuperellipsoidPardonGeometricStep
import Submission.Topology.PairedBandMovingSphere

/-!
# Superellipsoid adapter for a finite regular sphere-surgery sequence

This module consumes the finite regular-stage alternative proved by the paired-band topology.
The geometric premises identify the initial parity side, place the terminal children in the two
selected closed half-bodies, and convert a compression covered by the common event region into
the quantitative charged-compression record.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Topology.PairedBandMovingSphereCollarData
open Submission.Torus

/-- A finite sequence of honest regular sphere-family stages gives the exact resolved
superellipsoid step once its initial side, terminal children, and common event region have been
identified with the selected geometry. -/
theorem SuperellipsoidResolvedDoubleBubbleStep.ofFiniteRegularSphereSurgery
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) {r : ℝ} (hr : 0 < r)
    (WB : SmoothBasedLoopCarrierWitness Phi (orientedBox frame c r))
    (selection : SuperellipsoidDoubleBubbleSelection K Phi frame c r
      WB.toSmoothLoopCarrierWitness)
    (F : FiniteRegularSphereSurgeryStageSequence Phi)
    (lower upper : Set (transportedTorus Phi))
    (initialInside_eq : (F.parityStage 0).inside = transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale))
    (lower_subset : lower ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | x.ofLp (frame 2) ≤ selection.cut.height}))
    (upper_subset : upper ⊆ transportedTorusPart Phi
      (superellipsoidBody frame c selection.outer.scale ∩
        {x | selection.cut.height ≤ x.ofLp (frame 2)}))
    (essentialSurgery : ∀ k, k ≤ F.length → ∀ i,
      ((F.system k).circle i).Essential →
        Nonempty (EssentialSphereCircleSurgeryData (F.system k) i))
    (inessentialResolution : F.AllInessential →
      Nonempty (AllInessentialFiniteBandResolution F lower upper))
    (charge : EventCoveredCompressingDisk (Phi := Phi) F.commonEventRegion →
      SuperellipsoidChargedCompression (Phi := Phi) p q selection) :
    SuperellipsoidResolvedDoubleBubbleStep p q K Phi frame c r WB selection where
  cutAlternative := by
    have hInitial : CarriesBasedLoopTorusGenus Phi (F.parityStage 0).inside := by
      rw [initialInside_eq]
      exact CarriesTransportedBasedLoopGenus.mono
        (selection.originalBox_subset_outerBody hr)
        (⟨WB.toBasedLoopCarrierWitness⟩ : CarriesTransportedBasedLoopGenus Phi
          (orientedBox frame c r))
    rcases F.eventCoveredCompression_or_carries_terminalChild lower upper
        essentialSurgery inessentialResolution hInitial with hcompression | hlower | hupper
    · obtain ⟨D⟩ := hcompression
      exact Or.inr (Or.inr ⟨charge D⟩)
    · exact Or.inl (hlower.mono lower_subset)
    · exact Or.inr (Or.inl (hupper.mono upper_subset))

end Submission.PardonDistortion
