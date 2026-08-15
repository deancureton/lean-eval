import Submission.LoopNested

/-!
# Based loop carriers

The arbitrary-loop carrier records two independent winding loops, but does not say that their
images meet.  This module introduces the stronger datum needed by connected cutting arguments:
both loops pass through one explicitly recorded point at parameter zero.

The new predicate is deliberately not inferred from the old one.  It is upward monotone, the
whole transported torus carries it via the canonical longitude and meridian, and the local-chart
obstruction from `LoopCarrier` applies after forgetting the common basepoint.  These facts suffice
to run the complete nested shrinking contradiction for based carriers.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.Torus

/-- Two independent transported winding loops through one common point at parameter zero. -/
structure BasedLoopCarrierWitness (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) where
  basepoint : transportedTorus Phi
  first : TransportedWindingLoop Phi s
  second : TransportedWindingLoop Phi s
  first_zero : first.curve 0 = basepoint
  second_zero : second.curve 0 = basepoint
  independent : windingDet first.windingPair.1 first.windingPair.2
    second.windingPair.1 second.windingPair.2 ≠ 0

/-- A surface subset carries based loop genus when it contains a based independent pair. -/
def CarriesBasedLoopTorusGenus (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) : Prop :=
  Nonempty (BasedLoopCarrierWitness Phi s)

namespace BasedLoopCarrierWitness

variable {Phi : AmbientIsotopy} {s t : Set (transportedTorus Phi)}

/-- Forgetting the common basepoint produces an ordinary arbitrary-loop carrier. -/
def toLoopCarrierWitness (W : BasedLoopCarrierWitness Phi s) :
    LoopCarrierWitness Phi s where
  first := W.first
  second := W.second
  independent := W.independent

/-- Enlarging the containing set preserves all based carrier data. -/
def mono (W : BasedLoopCarrierWitness Phi s) (hst : s ⊆ t) :
    BasedLoopCarrierWitness Phi t where
  basepoint := W.basepoint
  first := W.first.mono hst
  second := W.second.mono hst
  first_zero := W.first_zero
  second_zero := W.second_zero
  independent := W.independent

/-- The two loop parametrizations agree exactly at parameter zero. -/
theorem curves_zero_eq (W : BasedLoopCarrierWitness Phi s) :
    W.first.curve 0 = W.second.curve 0 := by
  rw [W.first_zero, W.second_zero]

/-- The recorded common basepoint belongs to the carrier subset. -/
theorem basepoint_mem (W : BasedLoopCarrierWitness Phi s) : W.basepoint ∈ s := by
  rw [← W.first_zero]
  exact W.first.curve_mem 0

end BasedLoopCarrierWitness

/-- A based carrier is, after forgetting its basepoint, an ordinary loop carrier. -/
theorem CarriesBasedLoopTorusGenus.toCarriesLoopTorusGenus
    {Phi : AmbientIsotopy} {s : Set (transportedTorus Phi)}
    (hs : CarriesBasedLoopTorusGenus Phi s) : CarriesLoopTorusGenus Phi s := by
  obtain ⟨W⟩ := hs
  exact ⟨W.toLoopCarrierWitness⟩

/-- Exact upward monotonicity for based carriers. -/
theorem CarriesBasedLoopTorusGenus.mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (hs : CarriesBasedLoopTorusGenus Phi s) : CarriesBasedLoopTorusGenus Phi t := by
  obtain ⟨W⟩ := hs
  exact ⟨W.mono hst⟩

/-- Contrapositive monotonicity for based carriers. -/
theorem not_carriesBasedLoopTorusGenus_mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (ht : ¬ CarriesBasedLoopTorusGenus Phi t) : ¬ CarriesBasedLoopTorusGenus Phi s :=
  fun hs ↦ ht (hs.mono hst)

/-- The canonical longitude and meridian have common basepoint `(1, 1)` and determinant one. -/
theorem univ_carriesBasedLoopTorusGenus (Phi : AmbientIsotopy) :
    CarriesBasedLoopTorusGenus Phi Set.univ := by
  refine ⟨{
    basepoint := transportedTorusHomeomorph Phi (1, 1)
    first := {
      curve := transportedLongitudePeriodicLoop Phi
      continuous_curve := continuous_transportedLongitudePeriodicLoop Phi
      periodic_curve := periodic_transportedLongitudePeriodicLoop Phi
      curve_mem := fun _ ↦ mem_univ _
      lift := transportedLongitudeLoopLift Phi
    }
    second := {
      curve := transportedMeridianPeriodicLoop Phi
      continuous_curve := continuous_transportedMeridianPeriodicLoop Phi
      periodic_curve := periodic_transportedMeridianPeriodicLoop Phi
      curve_mem := fun _ ↦ mem_univ _
      lift := transportedMeridianLoopLift Phi
    }
    first_zero := by simp [transportedLongitudePeriodicLoop]
    second_zero := by simp [transportedMeridianPeriodicLoop]
    independent := by
      norm_num [TransportedWindingLoop.windingPair, TorusLoopLift.windingPair,
        windingDet, transportedLongitudeLoopLift, transportedMeridianLoopLift]
  }⟩

/-- A subset contained in one transported product chart cannot be a based carrier. -/
theorem not_carriesBasedLoopTorusGenus_of_subset_transportedTorusChart_source
    (Phi : AmbientIsotopy) (s : Set (transportedTorus Phi))
    (x : transportedTorus Phi)
    (hs : s ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesBasedLoopTorusGenus Phi s := by
  intro hcarrier
  exact not_carriesLoopTorusGenus_of_subset_transportedTorusChart_source Phi s x hs
    hcarrier.toCarriesLoopTorusGenus

/-- Uniform surface-ball noncarrying for the stronger based predicate. -/
theorem exists_uniform_pos_ball_basedLoop_noncarrier (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ (y : transportedTorus Phi) (s : Set (transportedTorus Phi)),
      s ⊆ Metric.ball y δ → ¬ CarriesBasedLoopTorusGenus Phi s := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_pos_ball_loop_noncarrier Phi
  refine ⟨δ, hδ, ?_⟩
  intro y s hs hcarrier
  exact hsmall y s hs hcarrier.toCarriesLoopTorusGenus

/-! ## Ambient regions -/

/-- An ambient region carries based loop genus through its transported-torus part. -/
def CarriesTransportedBasedLoopGenus (Phi : AmbientIsotopy) (a : Set R3) : Prop :=
  CarriesBasedLoopTorusGenus Phi (transportedTorusPart Phi a)

/-- Forgetting basepoint data produces an ambient ordinary-loop carrier. -/
theorem CarriesTransportedBasedLoopGenus.toCarriesTransportedLoopGenus
    {Phi : AmbientIsotopy} {a : Set R3}
    (ha : CarriesTransportedBasedLoopGenus Phi a) : CarriesTransportedLoopGenus Phi a :=
  CarriesBasedLoopTorusGenus.toCarriesLoopTorusGenus ha

/-- Ambient-set monotonicity for based carriers. -/
theorem CarriesTransportedBasedLoopGenus.mono {Phi : AmbientIsotopy}
    {a b : Set R3} (hab : a ⊆ b) (ha : CarriesTransportedBasedLoopGenus Phi a) :
    CarriesTransportedBasedLoopGenus Phi b :=
  CarriesBasedLoopTorusGenus.mono (preimage_mono hab) ha

/-- The ambient transported torus carries the based longitude-meridian pair. -/
theorem transportedTorus_carriesTransportedBasedLoopGenus (Phi : AmbientIsotopy) :
    CarriesTransportedBasedLoopGenus Phi (transportedTorus Phi) := by
  apply (univ_carriesBasedLoopTorusGenus Phi).mono
  intro x _
  exact x.property

/-- An ambient region whose surface part lies in one chart is not a based carrier. -/
theorem not_carriesTransportedBasedLoopGenus_of_part_subset_chart
    (Phi : AmbientIsotopy) (a : Set R3) (x : transportedTorus Phi)
    (ha : transportedTorusPart Phi a ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesTransportedBasedLoopGenus Phi a :=
  not_carriesBasedLoopTorusGenus_of_subset_transportedTorusChart_source Phi _ x ha

/-- Uniform ambient-ball noncarrying for based carriers. -/
theorem exists_uniform_pos_ambient_ball_basedLoop_noncarrier (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ y : transportedTorus Phi,
      ¬ CarriesTransportedBasedLoopGenus Phi (Metric.ball (y : R3) δ) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_pos_ball_basedLoop_noncarrier Phi
  refine ⟨δ, hδ, ?_⟩
  intro y
  rw [CarriesTransportedBasedLoopGenus, transportedTorusPart_ambient_ball_eq_surface_ball]
  exact hsmall y (Metric.ball y δ) Subset.rfl

end Submission.Topology

namespace Submission.PardonDistortion

open Submission.Topology
open Submission.Torus

/-- An oriented box carries based loop genus through its transported-torus part. -/
def OrientedBasedLoopCarrier (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ) : Prop :=
  CarriesTransportedBasedLoopGenus Phi (orientedBox frame c r)

/-- Forgetting the common basepoint turns an oriented based carrier into the old oriented
arbitrary-loop carrier. -/
theorem OrientedBasedLoopCarrier.toOrientedLoopCarrier
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {r : ℝ}
    (hcarrier : OrientedBasedLoopCarrier Phi frame c r) :
    OrientedLoopCarrier Phi frame c r :=
  hcarrier.toCarriesTransportedLoopGenus

private theorem transportedTorus_isCompact_based (Phi : AmbientIsotopy) :
    IsCompact (transportedTorus Phi) := by
  exact isCompact_range (transportedTorusMap_isEmbedding Phi).continuous

private theorem ball_zero_subset_orientedBox_based
    (frame : Equiv.Perm (Fin 3)) {r : ℝ} (hr : 0 < r) :
    Metric.ball (0 : R3) r ⊆ orientedBox frame 0 r := by
  intro x hx
  rw [mem_orientedBox_iff]
  intro i
  have hcoord : |x.ofLp (frame i)| ≤ ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x (frame i)
  have hnorm : ‖x‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  have hweight : r ≤ axisWeight i * r := by
    nlinarith [one_le_axisWeight i]
  simpa using hcoord.trans_lt (hnorm.trans_le hweight)

/-- Some positive oriented box carries the canonical based longitude-meridian pair. -/
theorem exists_positive_orientedBasedLoopCarrier (Phi : AmbientIsotopy) :
    ∃ (frame : Equiv.Perm (Fin 3)) (c : R3) (r : ℝ),
      0 < r ∧ OrientedBasedLoopCarrier Phi frame c r := by
  obtain ⟨r, hr, htorus⟩ :=
    (transportedTorus_isCompact_based Phi).isBounded.subset_ball_lt 0 (0 : R3)
  let frame : Equiv.Perm (Fin 3) := Equiv.refl _
  have hbox : transportedTorus Phi ⊆ orientedBox frame 0 r :=
    htorus.trans (ball_zero_subset_orientedBox_based frame hr)
  refine ⟨frame, 0, r, hr, ?_⟩
  exact (transportedTorus_carriesTransportedBasedLoopGenus Phi).mono hbox

private theorem mem_closedOrientedBox_of_mem_orientedBox_based
    {frame : Equiv.Perm (Fin 3)} {c x : R3} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ orientedBox frame c r) :
    x ∈ closedOrientedBox frame c r := by
  rw [closedOrientedBox, mem_ofPred_eq]
  exact (mem_orientedBox_iff_gauge_lt hr).mp hx |>.le

/-- Every based-loop-carrying box has a uniform positive lower bound on its scale. -/
theorem exists_uniform_basedLoop_scale_lower_bound (Phi : AmbientIsotopy) :
    ∃ rho > 0, ∀ frame c r, 0 < r →
      OrientedBasedLoopCarrier Phi frame c r → rho ≤ r := by
  obtain ⟨delta, hdelta, hsmall⟩ :=
    exists_uniform_pos_ambient_ball_basedLoop_noncarrier Phi
  refine ⟨delta / 5, div_pos hdelta (by norm_num), ?_⟩
  intro frame c r hr hcarrier
  by_contra hnot
  have hrho : r < delta / 5 := lt_of_not_ge hnot
  obtain ⟨W⟩ := hcarrier
  let y : transportedTorus Phi := W.basepoint
  have hybox : (y : R3) ∈ orientedBox frame c r := by
    change (W.basepoint : R3) ∈ orientedBox frame c r
    rw [← W.first_zero]
    exact W.first.curve_mem 0
  have hsubset : orientedBox frame c r ⊆ Metric.ball (y : R3) delta := by
    intro x hx
    have hdist := dist_lt_five_mul_scale_of_mem_closedOrientedBox hr
      (mem_closedOrientedBox_of_mem_orientedBox_based hr hx)
      (mem_closedOrientedBox_of_mem_orientedBox_based hr hybox)
    rw [Metric.mem_ball]
    calc
      dist x (y : R3) < 5 * r := hdist
      _ < delta := by nlinarith
  apply hsmall y
  exact ⟨W.mono (preimage_mono hsubset)⟩

/-- A uniformly shrinking successor for every positive based carrier box is impossible. -/
theorem not_exists_shrinking_orientedBasedLoopCarrier
    (Phi : AmbientIsotopy)
    (hshrink : ∀ frame c r, 0 < r → OrientedBasedLoopCarrier Phi frame c r →
      ∃ frame' c' r', 0 < r' ∧ OrientedBasedLoopCarrier Phi frame' c' r' ∧
        r' ≤ shrinkFactor * r) : False := by
  obtain ⟨rho, hrho, hlower⟩ := exists_uniform_basedLoop_scale_lower_bound Phi
  apply not_exists_uniformly_positive_shrinkable
    (fun r ↦ ∃ frame c, OrientedBasedLoopCarrier Phi frame c r)
    shrinkFactor rho shrinkFactor_pos.le shrinkFactor_lt_one hrho
  · obtain ⟨frame, c, r, hr, hcarrier⟩ :=
      exists_positive_orientedBasedLoopCarrier Phi
    exact ⟨r, hr, frame, c, hcarrier⟩
  · rintro r hr ⟨frame, c, hcarrier⟩
    exact hlower frame c r hr hcarrier
  · rintro r hr ⟨frame, c, hcarrier⟩
    obtain ⟨frame', c', r', hr', hcarrier', hscale⟩ :=
      hshrink frame c r hr hcarrier
    exact ⟨r', hr', ⟨frame', c', hcarrier'⟩, hscale⟩

end Submission.PardonDistortion
