import Submission.Topology.FinitePunctureAxisCarrier
import Submission.Topology.LoopHalfspaceCut

/-!
# Transporting the finite-puncture carrier through a disk pushout

This module is the abstract adapter for a radial disk-puncture construction.  Its geometric
input is a continuous map from a finite-point complement into a target subset of the transported
torus, together with a deformation from the inclusion to that map.  The two explicit based axes
from `FinitePunctureAxisCarrier` can then be pushed into the target.  Periodic-homotopy
invariance proves that their winding pairs remain `(1, 0)` and `(0, 1)`.

The contract neither assumes that the pushout exists nor hides a homotopy assertion.  A finite
composition of the local radial puncture-to-disk homeomorphisms supplies exactly these fields.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

variable {Phi : AmbientIsotopy} {ι : Type*}
  {centers : ι → Circle × Circle} {target : Set (transportedTorus Phi)}

/-- The exact continuous data supplied by a finite radial pushout from point punctures to disk
punctures.  The deformation parameter is real because the winding-invariance API uses a real
parameter; a compact-interval isotopy extends to this form by clamping to `[0, 1]`. -/
structure FinitePuncturePushoutData (Phi : AmbientIsotopy)
    (centers : ι → Circle × Circle) (target : Set (transportedTorus Phi)) where
  push : transportedFinitePointComplement Phi centers → transportedTorus Phi
  continuous_push : Continuous push
  push_mem : ∀ x, push x ∈ target
  deformation : ℝ → transportedFinitePointComplement Phi centers → transportedTorus Phi
  continuous_deformation : Continuous (Function.uncurry deformation)
  deformation_zero : ∀ x, deformation 0 x = x.1
  deformation_one : ∀ x, deformation 1 x = push x

/-- Build the real-parameter contract from the compact-unit-interval isotopy naturally produced
by a radial construction.  Outside `[0, 1]` the deformation is held fixed at an endpoint. -/
def FinitePuncturePushoutData.ofUnitInterval
    (push : transportedFinitePointComplement Phi centers → transportedTorus Phi)
    (continuous_push : Continuous push) (push_mem : ∀ x, push x ∈ target)
    (deformation : Set.Icc (0 : ℝ) 1 →
      transportedFinitePointComplement Phi centers → transportedTorus Phi)
    (continuous_deformation : Continuous (Function.uncurry deformation))
    (deformation_zero : ∀ x, deformation ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ x = x.1)
    (deformation_one : ∀ x, deformation ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ x = push x) :
    FinitePuncturePushoutData Phi centers target where
  push := push
  continuous_push := continuous_push
  push_mem := push_mem
  deformation := fun s x ↦ deformation (Set.projIcc 0 1 zero_le_one s) x
  continuous_deformation := by
    change Continuous (fun z : ℝ × transportedFinitePointComplement Phi centers ↦
      deformation (Set.projIcc 0 1 zero_le_one z.1) z.2)
    have hclamp : Continuous
        (Set.projIcc (0 : ℝ) 1 (show (0 : ℝ) ≤ 1 by norm_num)) :=
      continuous_projIcc
    exact continuous_deformation.comp <|
      (hclamp.comp continuous_fst).prodMk continuous_snd
  deformation_zero := by
    intro x
    rw [Set.projIcc_left]
    exact deformation_zero x
  deformation_one := by
    intro x
    rw [Set.projIcc_right]
    exact deformation_one x

namespace FinitePuncturePushoutData

variable (D : FinitePuncturePushoutData Phi centers target)

/-- A loop in the finite-point complement, bundled as a loop in the pushout source subtype. -/
def sourceCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers))
    (t : ℝ) : transportedFinitePointComplement Phi centers :=
  ⟨L.curve t, L.curve_mem t⟩

theorem continuous_sourceCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    Continuous (sourceCurve L) :=
  L.continuous_curve.subtype_mk _

theorem periodic_sourceCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    Function.Periodic (sourceCurve L) (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  exact L.periodic_curve t

/-- The pushout image of a winding loop. -/
def pushedCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers))
    (t : ℝ) : transportedTorus Phi :=
  D.push (sourceCurve L t)

theorem continuous_pushedCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    Continuous (D.pushedCurve L) :=
  D.continuous_push.comp (continuous_sourceCurve L)

theorem periodic_pushedCurve
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    Function.Periodic (D.pushedCurve L) (2 * Real.pi) := by
  intro t
  exact congrArg D.push (periodic_sourceCurve L t)

/-- A chosen coordinate lift for the pushed loop. -/
def pushedLift
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    TorusLoopLift (transportedLoopCoordinates Phi (D.pushedCurve L)) :=
  Classical.choice <| exists_torusLoopLift_of_transportedLoop Phi (D.pushedCurve L)
    (D.continuous_pushedCurve L) (D.periodic_pushedCurve L)

/-- The pushed loop, bundled in the target subset. -/
def pushedLoop
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    TransportedWindingLoop Phi target where
  curve := D.pushedCurve L
  continuous_curve := D.continuous_pushedCurve L
  periodic_curve := D.periodic_pushedCurve L
  curve_mem := fun t ↦ D.push_mem (sourceCurve L t)
  lift := D.pushedLift L

/-- The supplied deformation induces a continuous periodic homotopy from a source loop to its
pushout image, written in product-torus coordinates. -/
def pushedPeriodicHomotopy
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    PeriodicTorusLoopHomotopy
      (transportedLoopCoordinates Phi L.curve)
      (transportedLoopCoordinates Phi (D.pushedCurve L)) where
  homotopy := fun s t ↦
    (transportedTorusHomeomorph Phi).symm
      (D.deformation s (sourceCurve L t))
  continuous_homotopy := by
    apply (transportedTorusHomeomorph Phi).symm.continuous.comp
    exact D.continuous_deformation.comp <|
      continuous_fst.prodMk ((continuous_sourceCurve L).comp continuous_snd)
  periodic_homotopy := by
    intro s t
    exact congrArg (fun x ↦
      (transportedTorusHomeomorph Phi).symm (D.deformation s x))
      (periodic_sourceCurve L t)
  homotopy_zero := by
    funext t
    rw [D.deformation_zero]
    rfl
  homotopy_one := by
    funext t
    rw [D.deformation_one]
    rfl

/-- Radial pushout preserves both winding coordinates of every loop in its source. -/
theorem windingPair_pushedLoop
    (L : TransportedWindingLoop Phi (transportedFinitePointComplement Phi centers)) :
    (D.pushedLoop L).windingPair = L.windingPair := by
  symm
  exact TorusLoopLift.windingPair_eq_of_periodicHomotopy
    (D.pushedPeriodicHomotopy L) L.lift (D.pushedLift L)

/-- A based carrier in the finite-point complement remains a based carrier after pushout. -/
def pushBasedLoopCarrierWitness
    (W : BasedLoopCarrierWitness Phi
      (transportedFinitePointComplement Phi centers)) :
    BasedLoopCarrierWitness Phi target where
  basepoint := D.push ⟨W.basepoint, W.basepoint_mem⟩
  first := D.pushedLoop W.first
  second := D.pushedLoop W.second
  first_zero := by
    exact congrArg D.push <| Subtype.ext W.first_zero
  second_zero := by
    exact congrArg D.push <| Subtype.ext W.second_zero
  independent := by
    rw [D.windingPair_pushedLoop, D.windingPair_pushedLoop]
    exact W.independent

end FinitePuncturePushoutData

/-- A finite radial pushout turns the explicit finite-point axes into a based carrier of its
target. -/
theorem carriesBasedLoopTorusGenus_of_finitePuncturePushout
    [Fintype ι] (D : FinitePuncturePushoutData Phi centers target) :
    CarriesBasedLoopTorusGenus Phi target := by
  obtain ⟨B⟩ := exists_avoidingAxisBase centers
  exact ⟨D.pushBasedLoopCarrierWitness (B.toBasedLoopCarrierWitness Phi)⟩

end Submission.Topology
