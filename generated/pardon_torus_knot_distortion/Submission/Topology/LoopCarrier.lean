import Submission.Topology.SlopeNormalization
import Submission.Topology.Carrier

/-!
# Carriers built from arbitrary periodic torus loops

Unlike the straight-slope carrier, this module allows arbitrary continuous `2π`-periodic loops.
Each loop carries the coordinatewise covering lift from `SlopeNormalization`, so its two winding
integers are explicit and independent of all choices.  A subset carries loop genus when it
contains two such loops whose winding pairs have nonzero determinant.

This broader predicate has the desired local obstruction.  If a loop lies in one transported
product chart, each circle coordinate can be lifted through the real chart.  That chart lift is
itself periodic, hence has winding zero; uniqueness of winding for circle lifts then forces both
original winding integers to vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-! ## Arbitrary periodic loops with winding data -/

/-- A continuous periodic loop in the transported torus, contained in `s`, together with its
coordinatewise covering lift and winding pair. -/
structure TransportedWindingLoop (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) where
  curve : ℝ → transportedTorus Phi
  continuous_curve : Continuous curve
  periodic_curve : Function.Periodic curve (2 * Real.pi)
  curve_mem : ∀ t, curve t ∈ s
  lift : TorusLoopLift (transportedLoopCoordinates Phi curve)

namespace TransportedWindingLoop

variable {Phi : AmbientIsotopy}
  {s t : Set (transportedTorus Phi)}

/-- The winding pair certified by the chosen coordinate lift. -/
def windingPair (L : TransportedWindingLoop Phi s) : ℤ × ℤ :=
  L.lift.windingPair

/-- Enlarging the containing set preserves a winding loop and its exact lift data. -/
def mono (L : TransportedWindingLoop Phi s) (hst : s ⊆ t) :
    TransportedWindingLoop Phi t where
  curve := L.curve
  continuous_curve := L.continuous_curve
  periodic_curve := L.periodic_curve
  curve_mem u := hst (L.curve_mem u)
  lift := L.lift

end TransportedWindingLoop

/-- Two arbitrary periodic loops with independent winding pairs inside a surface subset. -/
structure LoopCarrierWitness (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) where
  first : TransportedWindingLoop Phi s
  second : TransportedWindingLoop Phi s
  independent : windingDet first.windingPair.1 first.windingPair.2
    second.windingPair.1 second.windingPair.2 ≠ 0

/-- The arbitrary-loop genus-carrier predicate. -/
def CarriesLoopTorusGenus (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) : Prop :=
  Nonempty (LoopCarrierWitness Phi s)

/-! ## Monotonicity -/

/-- A loop carrier remains a loop carrier after enlarging its subset. -/
def LoopCarrierWitness.mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (W : LoopCarrierWitness Phi s)
    (hst : s ⊆ t) : LoopCarrierWitness Phi t where
  first := W.first.mono hst
  second := W.second.mono hst
  independent := W.independent

/-- Exact upward monotonicity for the arbitrary-loop carrier. -/
theorem CarriesLoopTorusGenus.mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (hs : CarriesLoopTorusGenus Phi s) : CarriesLoopTorusGenus Phi t := by
  obtain ⟨W⟩ := hs
  exact ⟨W.mono hst⟩

/-- Contrapositive monotonicity. -/
theorem not_carriesLoopTorusGenus_mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (ht : ¬ CarriesLoopTorusGenus Phi t) : ¬ CarriesLoopTorusGenus Phi s :=
  fun hs ↦ ht (hs.mono hst)

/-! ## Canonical longitude and meridian loops -/

/-- The canonical periodic longitude on the transported torus. -/
def transportedLongitudePeriodicLoop (Phi : AmbientIsotopy) (u : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi (Circle.exp u, 1)

/-- The canonical periodic meridian on the transported torus. -/
def transportedMeridianPeriodicLoop (Phi : AmbientIsotopy) (u : ℝ) :
    transportedTorus Phi :=
  transportedTorusHomeomorph Phi (1, Circle.exp u)

theorem continuous_transportedLongitudePeriodicLoop (Phi : AmbientIsotopy) :
    Continuous (transportedLongitudePeriodicLoop Phi) := by
  exact (transportedTorusHomeomorph Phi).continuous.comp
    (Circle.exp.continuous.prodMk continuous_const)

theorem continuous_transportedMeridianPeriodicLoop (Phi : AmbientIsotopy) :
    Continuous (transportedMeridianPeriodicLoop Phi) := by
  exact (transportedTorusHomeomorph Phi).continuous.comp
    (continuous_const.prodMk Circle.exp.continuous)

theorem periodic_transportedLongitudePeriodicLoop (Phi : AmbientIsotopy) :
    Function.Periodic (transportedLongitudePeriodicLoop Phi) (2 * Real.pi) := by
  intro u
  unfold transportedLongitudePeriodicLoop
  congr 1
  apply Prod.ext
  · apply Circle.exp_eq_exp.mpr
    exact ⟨1, by ring⟩
  · rfl

theorem periodic_transportedMeridianPeriodicLoop (Phi : AmbientIsotopy) :
    Function.Periodic (transportedMeridianPeriodicLoop Phi) (2 * Real.pi) := by
  intro u
  unfold transportedMeridianPeriodicLoop
  congr 1
  apply Prod.ext
  · rfl
  · apply Circle.exp_eq_exp.mpr
    exact ⟨1, by ring⟩

/-- Explicit lift data with winding pair `(1, 0)` for the longitude. -/
def transportedLongitudeLoopLift (Phi : AmbientIsotopy) :
    TorusLoopLift
      (transportedLoopCoordinates Phi (transportedLongitudePeriodicLoop Phi)) where
  first := {
    angle := fun u ↦ u
    continuous_angle := continuous_id
    exp_angle := fun u ↦ by
      simp [transportedLoopCoordinates, transportedLongitudePeriodicLoop]
    winding := 1
    angle_add_period := fun u ↦ by norm_num
  }
  second := {
    angle := fun _ ↦ 0
    continuous_angle := continuous_const
    exp_angle := fun u ↦ by
      simp [transportedLoopCoordinates, transportedLongitudePeriodicLoop]
    winding := 0
    angle_add_period := fun u ↦ by norm_num
  }

/-- Explicit lift data with winding pair `(0, 1)` for the meridian. -/
def transportedMeridianLoopLift (Phi : AmbientIsotopy) :
    TorusLoopLift
      (transportedLoopCoordinates Phi (transportedMeridianPeriodicLoop Phi)) where
  first := {
    angle := fun _ ↦ 0
    continuous_angle := continuous_const
    exp_angle := fun u ↦ by
      simp [transportedLoopCoordinates, transportedMeridianPeriodicLoop]
    winding := 0
    angle_add_period := fun u ↦ by norm_num
  }
  second := {
    angle := fun u ↦ u
    continuous_angle := continuous_id
    exp_angle := fun u ↦ by
      simp [transportedLoopCoordinates, transportedMeridianPeriodicLoop]
    winding := 1
    angle_add_period := fun u ↦ by norm_num
  }

/-- The whole transported torus carries arbitrary-loop genus. -/
theorem univ_carriesLoopTorusGenus (Phi : AmbientIsotopy) :
    CarriesLoopTorusGenus Phi Set.univ := by
  refine ⟨{
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
    independent := by norm_num [TransportedWindingLoop.windingPair,
      TorusLoopLift.windingPair, windingDet, transportedLongitudeLoopLift,
      transportedMeridianLoopLift]
  }⟩

/-! ## Vanishing inside one local chart -/

/-- A circle loop contained in one real circle chart has zero winding.  The chart itself supplies
a periodic real lift, and winding uniqueness compares it to the given lift. -/
theorem CircleLoopLift.winding_eq_zero_of_forall_mem_circleChartAt_source
    (z : Circle) (gamma : ℝ → Circle)
    (hgamma : Continuous gamma)
    (hperiodic : Function.Periodic gamma (2 * Real.pi))
    (hsource : ∀ u, gamma u ∈ (circleChartAt z).source)
    (L : CircleLoopLift gamma) :
    L.winding = 0 := by
  let chartLift : CircleLoopLift gamma := {
    angle := fun u ↦ circleChartAt z (gamma u)
    continuous_angle := by
      exact (circleChartAt z).continuousOn.comp_continuous hgamma hsource
    exp_angle := fun u ↦ by
      simpa only [circleChartAt] using
        isLocalHomeomorph_circleExp.apply_localInverseAt_of_mem (hsource u)
    winding := 0
    angle_add_period := fun u ↦ by
      simp only [Int.cast_zero, zero_mul, add_zero]
      rw [hperiodic]
  }
  exact L.winding_eq chartLift

/-- Both winding coordinates of an arbitrary loop vanish when its range is contained in one
transported product chart. -/
theorem TransportedWindingLoop.windings_eq_zero_of_subset_chart
    {Phi : AmbientIsotopy} {s : Set (transportedTorus Phi)}
    (L : TransportedWindingLoop Phi s) (x : transportedTorus Phi)
    (hs : s ⊆ (transportedTorusChart Phi x).source) :
    L.windingPair = (0, 0) := by
  let center := (transportedTorusHomeomorph Phi).symm x
  let gamma := transportedLoopCoordinates Phi L.curve
  have hgamma : Continuous gamma :=
    continuous_transportedLoopCoordinates Phi L.curve L.continuous_curve
  have hperiodic : Function.Periodic gamma (2 * Real.pi) :=
    periodic_transportedLoopCoordinates Phi L.curve L.periodic_curve
  have hsources : ∀ u,
      (gamma u).1 ∈ (circleChartAt center.1).source ∧
      (gamma u).2 ∈ (circleChartAt center.2).source := by
    intro u
    have hu := hs (L.curve_mem u)
    rw [transportedTorusChart, OpenPartialHomeomorph.trans_source] at hu
    have hp := hu.2
    rw [circleProductChartAt, OpenPartialHomeomorph.prod_source] at hp
    change (transportedTorusHomeomorph Phi).symm (L.curve u) ∈
      (circleChartAt center.1).source ×ˢ (circleChartAt center.2).source at hp
    exact hp
  have hfirst : L.lift.first.winding = 0 :=
    Submission.Topology.CircleLoopLift.winding_eq_zero_of_forall_mem_circleChartAt_source
      center.1 _
      (continuous_fst.comp hgamma)
      (fun u ↦ congrArg Prod.fst (hperiodic u))
      (fun u ↦ (hsources u).1)
      L.lift.first
  have hsecond : L.lift.second.winding = 0 :=
    Submission.Topology.CircleLoopLift.winding_eq_zero_of_forall_mem_circleChartAt_source
      center.2 _
      (continuous_snd.comp hgamma)
      (fun u ↦ congrArg Prod.snd (hperiodic u))
      (fun u ↦ (hsources u).2)
      L.lift.second
  exact Prod.ext hfirst hsecond

/-- A chart-contained subset cannot contain two arbitrary loops with independent windings. -/
theorem not_carriesLoopTorusGenus_of_subset_transportedTorusChart_source
    (Phi : AmbientIsotopy) (s : Set (transportedTorus Phi))
    (x : transportedTorus Phi)
    (hs : s ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesLoopTorusGenus Phi s := by
  rintro ⟨W⟩
  have hfirst := W.first.windings_eq_zero_of_subset_chart x hs
  have hsecond := W.second.windings_eq_zero_of_subset_chart x hs
  apply W.independent
  simp [windingDet, hfirst, hsecond]

/-- A uniform positive radius makes every subset of every surface ball an arbitrary-loop
noncarrier. -/
theorem exists_uniform_pos_ball_loop_noncarrier (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ (y : transportedTorus Phi) (s : Set (transportedTorus Phi)),
      s ⊆ Metric.ball y δ → ¬ CarriesLoopTorusGenus Phi s := by
  obtain ⟨δ, hδ, hchart⟩ :=
    exists_uniform_pos_ball_subset_transportedTorusChart_source Phi
  refine ⟨δ, hδ, ?_⟩
  intro y s hs
  obtain ⟨x, hball⟩ := hchart y
  exact not_carriesLoopTorusGenus_of_subset_transportedTorusChart_source
    Phi s x (hs.trans hball)

/-! ## Ambient regions -/

/-- An ambient region carries arbitrary-loop genus through its transported-torus part. -/
def CarriesTransportedLoopGenus (Phi : AmbientIsotopy) (a : Set R3) : Prop :=
  CarriesLoopTorusGenus Phi (transportedTorusPart Phi a)

/-- Ambient-set monotonicity. -/
theorem CarriesTransportedLoopGenus.mono {Phi : AmbientIsotopy}
    {a b : Set R3} (hab : a ⊆ b) (ha : CarriesTransportedLoopGenus Phi a) :
    CarriesTransportedLoopGenus Phi b :=
  CarriesLoopTorusGenus.mono (preimage_mono hab) ha

/-- The ambient transported torus carries arbitrary-loop genus. -/
theorem transportedTorus_carriesTransportedLoopGenus (Phi : AmbientIsotopy) :
    CarriesTransportedLoopGenus Phi (transportedTorus Phi) := by
  apply (univ_carriesLoopTorusGenus Phi).mono
  intro x _
  exact x.property

/-- An ambient region whose surface part lies in one chart is an arbitrary-loop noncarrier. -/
theorem not_carriesTransportedLoopGenus_of_part_subset_chart
    (Phi : AmbientIsotopy) (a : Set R3) (x : transportedTorus Phi)
    (ha : transportedTorusPart Phi a ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesTransportedLoopGenus Phi a :=
  not_carriesLoopTorusGenus_of_subset_transportedTorusChart_source Phi _ x ha

/-- Pulling an ambient ball back to the transported-torus subtype gives the corresponding subtype
metric ball. -/
theorem transportedTorusPart_ambient_ball_eq_surface_ball
    (Phi : AmbientIsotopy) (y : transportedTorus Phi) (r : ℝ) :
    transportedTorusPart Phi (Metric.ball (y : R3) r) = Metric.ball y r := by
  ext z
  simp only [transportedTorusPart, mem_preimage, Metric.mem_ball, Subtype.dist_eq]

/-- Uniform ambient-ball form of local noncarrying: sufficiently small ambient balls have
noncarrying intersections with the transported torus. -/
theorem exists_uniform_pos_ambient_ball_loop_noncarrier (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ y : transportedTorus Phi,
      ¬ CarriesTransportedLoopGenus Phi (Metric.ball (y : R3) δ) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_pos_ball_loop_noncarrier Phi
  refine ⟨δ, hδ, ?_⟩
  intro y
  rw [CarriesTransportedLoopGenus,
    transportedTorusPart_ambient_ball_eq_surface_ball]
  exact hsmall y (Metric.ball y δ) Subset.rfl

end Submission.Topology
