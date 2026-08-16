import Submission.Topology.RegularBandCyclicWinding
import Submission.Topology.SuperellipsoidSeparatedTwoLevelPartition

/-!
# Absorbing an outer-collar middle cell into a regular coordinate band

The honest three-sphere partition has a middle cell containing both the central coordinate band
and the radial collar between the original and enclosing superellipsoids.  An ambient collar of
the enclosing sphere does not by itself move points of the transported torus.  The exact extra
geometric input needed by the winding argument is a continuous transported-torus homotopy which
starts at the identity on the middle cell and ends in the closed regular coordinate band.

This file proves the purely topological adapter from that input.  A based carrier in the middle
cell would be carried by the endpoint homotopy to a based carrier in one connected component of
the regular band, with both winding pairs unchanged.  The normalized-gradient cyclic retraction
of that component then gives a contradiction.

The absorption homotopy is deliberately not asserted to exist here.  Constructing it from gauge
geometry requires a collar statement for the restriction of the gauge to the transported torus,
not merely an ambient radial collar.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d : ℝ}

/-- An ambient-in-the-torus absorption of a surface subset into a closed regular coordinate
band.  No intermediate containment is required for winding invariance. -/
structure RegularBandAbsorptionData
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (source : Set (transportedTorus Phi)) where
  absorption : ℝ → source → transportedTorus Phi
  continuous_absorption : Continuous (Function.uncurry absorption)
  absorption_zero : ∀ x, absorption 0 x = x.1
  absorption_one_mem_band : ∀ x, absorption 1 x ∈ B.transportedClosedBand

namespace RegularBandAbsorptionData

variable {B : OrientedCoordinateRegularBandData Phi frame d}
  {source : Set (transportedTorus Phi)}

/-- A source loop bundled in the absorption domain subtype. -/
def sourceCurve
    (L : TransportedWindingLoop Phi source) (t : ℝ) : source :=
  ⟨L.curve t, L.curve_mem t⟩

theorem continuous_sourceCurve
    (L : TransportedWindingLoop Phi source) : Continuous (sourceCurve L) :=
  L.continuous_curve.subtype_mk _

theorem periodic_sourceCurve
    (L : TransportedWindingLoop Phi source) :
    Function.Periodic (sourceCurve L) (2 * Real.pi) := by
  intro t
  exact Subtype.ext (L.periodic_curve t)

/-- Endpoint of the absorption applied to a periodic source loop. -/
def endpointCurve
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) : ℝ → transportedTorus Phi :=
  fun t ↦ A.absorption 1 (sourceCurve L t)

theorem continuous_endpointCurve
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    Continuous (A.endpointCurve L) :=
  A.continuous_absorption.comp
    (continuous_const.prodMk (continuous_sourceCurve L))

theorem periodic_endpointCurve
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    Function.Periodic (A.endpointCurve L) (2 * Real.pi) := by
  intro t
  exact congrArg (A.absorption 1) (periodic_sourceCurve L t)

/-- A chosen covering lift of the endpoint loop. -/
def endpointLift
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    TorusLoopLift (transportedLoopCoordinates Phi (A.endpointCurve L)) :=
  Classical.choice <| exists_torusLoopLift_of_transportedLoop Phi _
    (A.continuous_endpointCurve L) (A.periodic_endpointCurve L)

/-- The endpoint loop, first regarded only as a loop in the full regular band. -/
def endpointBandLoop
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    TransportedWindingLoop Phi B.transportedClosedBand where
  curve := A.endpointCurve L
  continuous_curve := A.continuous_endpointCurve L
  periodic_curve := A.periodic_endpointCurve L
  curve_mem := fun t ↦ A.absorption_one_mem_band (sourceCurve L t)
  lift := A.endpointLift L

/-- The absorption gives a periodic torus homotopy from a source loop to its endpoint. -/
def periodicHomotopyToEndpoint
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    PeriodicTorusLoopHomotopy
      (transportedLoopCoordinates Phi L.curve)
      (transportedLoopCoordinates Phi (A.endpointCurve L)) where
  homotopy := fun u t ↦
    (transportedTorusHomeomorph Phi).symm (A.absorption u (sourceCurve L t))
  continuous_homotopy :=
    (transportedTorusHomeomorph Phi).symm.continuous.comp <|
      A.continuous_absorption.comp
        (continuous_fst.prodMk ((continuous_sourceCurve L).comp continuous_snd))
  periodic_homotopy := by
    intro u t
    exact congrArg (fun x ↦
      (transportedTorusHomeomorph Phi).symm (A.absorption u x))
      (periodic_sourceCurve L t)
  homotopy_zero := by
    funext t
    rw [A.absorption_zero]
    rfl
  homotopy_one := rfl

/-- Absorption preserves the winding pair of every periodic source loop. -/
theorem endpointBandLoop_windingPair
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source) :
    (A.endpointBandLoop L).windingPair = L.windingPair := by
  symm
  exact TorusLoopLift.windingPair_eq_of_periodicHomotopy
    (A.periodicHomotopyToEndpoint L) L.lift (A.endpointLift L)

/-- An endpoint loop through an absorbed basepoint lies in that basepoint's connected regular
band component. -/
theorem endpointCurve_mem_component
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source)
    (base : transportedTorus Phi) (hbase : base ∈ source)
    (hzero : L.curve 0 = base) (t : ℝ) :
    A.endpointCurve L t ∈
      B.closedBandComponent (A.absorption 1 ⟨base, hbase⟩) := by
  let loopRange : Set (transportedTorus Phi) := Set.range (A.endpointCurve L)
  have hpre : IsPreconnected loopRange :=
    (isConnected_range (A.continuous_endpointCurve L)).isPreconnected
  have hsubset : loopRange ⊆ B.transportedClosedBand := by
    rintro _ ⟨s, rfl⟩
    exact A.absorption_one_mem_band (sourceCurve L s)
  have hendpoint : A.absorption 1 ⟨base, hbase⟩ ∈ loopRange := by
    refine ⟨0, ?_⟩
    have hsource : sourceCurve L 0 = ⟨base, hbase⟩ := by
      apply Subtype.ext
      exact hzero
    exact congrArg (A.absorption 1) hsource
  exact hpre.subset_connectedComponentIn hendpoint hsubset ⟨t, rfl⟩

/-- The absorbed loop, now bundled in the component through the absorbed common basepoint. -/
def endpointComponentLoop
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source)
    (base : transportedTorus Phi) (hbase : base ∈ source)
    (hzero : L.curve 0 = base) :
    TransportedWindingLoop Phi
      (B.closedBandComponent (A.absorption 1 ⟨base, hbase⟩)) where
  curve := A.endpointCurve L
  continuous_curve := A.continuous_endpointCurve L
  periodic_curve := A.periodic_endpointCurve L
  curve_mem := A.endpointCurve_mem_component L base hbase hzero
  lift := A.endpointLift L

@[simp] theorem endpointComponentLoop_windingPair
    (A : RegularBandAbsorptionData B source)
    (L : TransportedWindingLoop Phi source)
    (base : transportedTorus Phi) (hbase : base ∈ source)
    (hzero : L.curve 0 = base) :
    (A.endpointComponentLoop L base hbase hzero).windingPair = L.windingPair :=
  A.endpointBandLoop_windingPair L

/-- Absorption sends a based carrier to a based carrier in one regular-band component. -/
def absorbBasedLoopCarrierWitness
    (A : RegularBandAbsorptionData B source)
    (W : BasedLoopCarrierWitness Phi source) :
    BasedLoopCarrierWitness Phi
      (B.closedBandComponent (A.absorption 1 ⟨W.basepoint, W.basepoint_mem⟩)) where
  basepoint := A.absorption 1 ⟨W.basepoint, W.basepoint_mem⟩
  first := A.endpointComponentLoop W.first W.basepoint W.basepoint_mem W.first_zero
  second := A.endpointComponentLoop W.second W.basepoint W.basepoint_mem W.second_zero
  first_zero := congrArg (A.absorption 1) (Subtype.ext W.first_zero)
  second_zero := congrArg (A.absorption 1) (Subtype.ext W.second_zero)
  independent := by
    rw [A.endpointComponentLoop_windingPair,
      A.endpointComponentLoop_windingPair]
    exact W.independent

/-- A regular-band absorption and cyclic retraction rule out based genus in the source. -/
theorem not_carriesBasedLoopTorusGenus
    (A : RegularBandAbsorptionData B source)
    (G : OrientedCoordinateRegularBandCyclicRetractionData B) :
    ¬ CarriesBasedLoopTorusGenus Phi source := by
  rintro ⟨W⟩
  let base : source := ⟨W.basepoint, W.basepoint_mem⟩
  have hbase : A.absorption 1 base ∈ B.transportedClosedBand :=
    A.absorption_one_mem_band base
  obtain ⟨D⟩ := G.componentRetraction (A.absorption 1 base) hbase
  exact D.not_carriesBasedLoopTorusGenus ⟨A.absorbBasedLoopCarrierWitness W⟩

end RegularBandAbsorptionData

/-! ## The separated three-sphere middle cell -/

/-- The exact collar-absorption contract specialized to the honest three-sphere middle cell. -/
abbrev SeparatedThreeSphereMiddleBandAbsorptionData
    (B : OrientedCoordinateRegularBandData Phi frame d)
    (c : R3) (R ε η : ℝ) :=
  RegularBandAbsorptionData B
    (separatedThreeSphereMiddlePart Phi frame c R d ε η)

/-- Once the radial collar is absorbed into the regular band, the full honest middle cell cannot
carry based torus genus. -/
theorem separatedThreeSphereMiddle_not_carriesBasedLoopTorusGenus
    {c : R3} {R ε η : ℝ}
    {B : OrientedCoordinateRegularBandData Phi frame d}
    (A : SeparatedThreeSphereMiddleBandAbsorptionData B c R ε η)
    (G : OrientedCoordinateRegularBandCyclicRetractionData B) :
    ¬ CarriesBasedLoopTorusGenus Phi
      (separatedThreeSphereMiddlePart Phi frame c R d ε η) :=
  A.not_carriesBasedLoopTorusGenus G

end Submission.Topology
