import Submission.Topology.SuperellipsoidEventCharging
import Submission.Topology.TransverseContinuation

/-!
# Charging smoothed circle intersections by transverse continuation

The quantitative superellipsoid argument only needs an injective assignment of knot/intersection
parameters to the selected finite event set.  A smoothed stage circle need not itself lie in the
original outer/cutting-disk barrier: it is enough to continue its intersections transversely from
an original barrier loop which already has such an assignment.

This file isolates that finite transport.  The endpoint equivalence in
`RegularIntersectionContinuation` pulls a charging across the homotopy.  The stronger
`TransverseBranchFamily` API supplies this equivalence automatically.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

namespace SuperellipsoidDoubleBubbleSelection

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}

/-- An injective charge for the intersections of an arbitrary torus-coordinate loop.  Unlike
`CompressionCharging`, this source loop need not already be the boundary of a compressing disk. -/
structure LoopCharging
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (gamma : ℝ → Circle × Circle) where
  encode : ℝ → Sum ℝ (Bool × ℝ)
  mem_counted : ∀ t ∈ torusLoopIntersectionParameters p q gamma,
    encode t ∈ S.countedEvents
  injOn : Set.InjOn encode (torusLoopIntersectionParameters p q gamma)

namespace LoopCharging

/-- Pull an injective source charge to the target of a regular intersection continuation. -/
def transport
    {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (Q : LoopCharging S p q gamma₀)
    (R : RegularIntersectionContinuation p q gamma₀ gamma₁ m n C) :
    LoopCharging S p q gamma₁ where
  encode := fun t ↦
    if ht : t ∈ R.targetParameters then
      Q.encode (R.matching.symm ⟨t, ht⟩).1
    else Q.encode t
  mem_counted := by
    intro t ht
    have htTarget : t ∈ R.targetParameters := by
      change t ∈ (R.targetParameters : Set ℝ)
      rw [R.targetParameters_eq]
      exact ht
    simp only [dif_pos htTarget]
    apply Q.mem_counted
    rw [← C.parameters_eq]
    exact (R.matching.symm ⟨t, htTarget⟩).2
  injOn := by
    intro s hs t ht hst
    have hsTarget : s ∈ R.targetParameters := by
      change s ∈ (R.targetParameters : Set ℝ)
      rw [R.targetParameters_eq]
      exact hs
    have htTarget : t ∈ R.targetParameters := by
      change t ∈ (R.targetParameters : Set ℝ)
      rw [R.targetParameters_eq]
      exact ht
    simp only [dif_pos hsTarget, dif_pos htTarget] at hst
    have hsSource : (R.matching.symm ⟨s, hsTarget⟩).1 ∈
        torusLoopIntersectionParameters p q gamma₀ := by
      rw [← C.parameters_eq]
      exact (R.matching.symm ⟨s, hsTarget⟩).2
    have htSource : (R.matching.symm ⟨t, htTarget⟩).1 ∈
        torusLoopIntersectionParameters p q gamma₀ := by
      rw [← C.parameters_eq]
      exact (R.matching.symm ⟨t, htTarget⟩).2
    have hsourceVal :
        (R.matching.symm ⟨s, hsTarget⟩).1 =
          (R.matching.symm ⟨t, htTarget⟩).1 :=
      Q.injOn hsSource htSource hst
    have hsource :
        R.matching.symm ⟨s, hsTarget⟩ =
          R.matching.symm ⟨t, htTarget⟩ :=
      Subtype.ext hsourceVal
    have htarget :
        (⟨s, hsTarget⟩ : {u // u ∈ R.targetParameters}) = ⟨t, htTarget⟩ :=
      R.matching.symm.injective hsource
    exact congrArg Subtype.val htarget

/-- A loop charge for the actual coordinate loop of a compressing disk is the existing
`CompressionCharging` interface. -/
def toCompressionCharging
    {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
    {D : GeneralCompressingDiskWitness Phi} {p q : ℕ}
    (Q : LoopCharging S p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)) :
    S.CompressionCharging D p q where
  encode := Q.encode
  mem_counted := Q.mem_counted
  injOn := Q.injOn

end LoopCharging

/-- The minimal per-circle replacement for ambient containment of a smoothed stage event region.
The source loop carries an original barrier charge, while the continuation supplies both the
target certificate and the bijection used to transport that charge. -/
structure SmoothedLoopChargingTransport
    (S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W)
    (p q : ℕ) (targetLoop : ℝ → Circle × Circle) (m n : ℤ) where
  sourceLoop : ℝ → Circle × Circle
  sourceCertificate : TransverseIntersectionCertificate p q sourceLoop m n
  sourceCharging : LoopCharging S p q sourceLoop
  continuation : RegularIntersectionContinuation p q sourceLoop targetLoop m n
    sourceCertificate

namespace SmoothedLoopChargingTransport

variable {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}
  {p q : ℕ} {targetLoop : ℝ → Circle × Circle} {m n : ℤ}

/-- The continued target loop has a transverse intersection certificate. -/
def targetCertificate (T : SmoothedLoopChargingTransport S p q targetLoop m n) :
    TransverseIntersectionCertificate p q targetLoop m n :=
  T.continuation.targetCertificate

/-- Endpoint matching pulls the original barrier charge injectively to the smoothed loop. -/
def targetCharging (T : SmoothedLoopChargingTransport S p q targetLoop m n) :
    LoopCharging S p q targetLoop :=
  T.sourceCharging.transport T.continuation

/-- Global noncolliding transverse branches are sufficient to build the charging transport. -/
def ofTransverseBranches
    {sourceLoop : ℝ → Circle × Circle}
    (C : TransverseIntersectionCertificate p q sourceLoop m n)
    (Q : LoopCharging S p q sourceLoop)
    (B : TransverseBranchFamily p q sourceLoop targetLoop m n C) :
    SmoothedLoopChargingTransport S p q targetLoop m n where
  sourceLoop := sourceLoop
  sourceCertificate := C
  sourceCharging := Q
  continuation := B.toRegularIntersectionContinuation

/-- Once the smoothed target is the boundary loop of a compressing disk, transported charging
and the transported certificate give the complete quantitative compression package. -/
def toChargedCompression
    (D : GeneralCompressingDiskWitness Phi)
    (T : SmoothedLoopChargingTransport S p q
      (transportedLoopCoordinates Phi D.boundaryLoop.curve)
      D.boundaryLoop.lift.first.winding D.boundaryLoop.lift.second.winding) :
    SuperellipsoidChargedCompression (Phi := Phi) p q S where
  disk := D
  certificate := T.targetCertificate
  charging := ⟨T.targetCharging.toCompressionCharging⟩

end SmoothedLoopChargingTransport

end SuperellipsoidDoubleBubbleSelection

end Submission.PardonDistortion
