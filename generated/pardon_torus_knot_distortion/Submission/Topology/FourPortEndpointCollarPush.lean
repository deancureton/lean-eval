import Submission.Topology.FourPortFiberwiseTubeHomeomorph
import Submission.Topology.FourPortPairOfPantsTrace
import Submission.Topology.LoopHalfspaceCut

/-!
# Collar pushes for the endpoints of a four-port move

The normal-tube maps used to move the sphere sheet are fiberwise in the ambient normal
coordinate.  They do not, by themselves, move a curve tangentially in the transported torus.
This file records that limitation, and then isolates the honest surface-collar output needed to
separate the two resolutions of a four-port graph.

A surface self-isotopy has a canonical extension to the transported normal tube: conjugate the
surface homeomorphism to `Circle × Circle`, take its product with the identity normal map, and
conjugate back through `transportedTorusNormalTubeHomeomorph`.  Thus no further ambient extension
hypothesis is needed once the tangential collar isotopy is known.

For one four-port move, two such small self-isotopies push the pre- and post-resolution in
opposite directions.  Embedded sweeps record the annular strips between the raw and pushed
endpoints.  The resulting restriction maps construct `FourPortEndpointCircleData`.  Only the
global attachment of the two annular sweeps to the strict local change region, including its
exact three-circle frontier, remains a separate premise.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus
open PairedBandMovingSphereCollarData

variable {Phi : AmbientIsotopy}

/-! ## Extending a tangential torus homeomorphism through the normal tube -/

/-- The expression of a transported-torus self-homeomorphism in the standard product-torus
coordinates. -/
def transportedTorusCoordinateHomeomorph
    (h : transportedTorus Phi ≃ₜ transportedTorus Phi) :
    Circle × Circle ≃ₜ Circle × Circle :=
  (transportedTorusHomeomorph Phi).trans <|
    h.trans (transportedTorusHomeomorph Phi).symm

/-- Extend a transported-torus self-homeomorphism over the standard normal tube without changing
the signed normal coordinate. -/
def transportedTorusHomeomorphNormalLift
    (h : transportedTorus Phi ≃ₜ transportedTorus Phi) :
    StandardTorusNormalTube ≃ₜ StandardTorusNormalTube :=
  (transportedTorusCoordinateHomeomorph h).prodCongr
    (Homeomorph.refl (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))

@[simp] theorem transportedTorusHomeomorphNormalLift_normal
    (h : transportedTorus Phi ≃ₜ transportedTorus Phi)
    (p : StandardTorusNormalTube) :
    (transportedTorusHomeomorphNormalLift h p).2 = p.2 :=
  rfl

/-- Conjugate the product extension to the actual transported normal-tube range in `R3`. -/
def transportedTorusHomeomorphTubeRangeLift
    (h : transportedTorus Phi ≃ₜ transportedTorus Phi) :
    Set.range (transportedTorusNormalTubeMap Phi) ≃ₜ
      Set.range (transportedTorusNormalTubeMap Phi) :=
  (transportedTorusNormalTubeHomeomorph Phi).symm.trans <|
    (transportedTorusHomeomorphNormalLift h).trans
      (transportedTorusNormalTubeHomeomorph Phi)

/-- On the zero slice, the normal-tube extension is exactly the original torus homeomorphism. -/
theorem transportedTorusHomeomorphTubeRangeLift_zero
    (h : transportedTorus Phi ≃ₜ transportedTorus Phi)
    (z : Circle × Circle) :
    ((transportedTorusHomeomorphTubeRangeLift h
      ⟨transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero),
        ⟨(z, standardTorusNormalZero), rfl⟩⟩ :
          Set.range (transportedTorusNormalTubeMap Phi)) : R3) =
      (h (transportedTorusHomeomorph Phi z) : R3) := by
  simp only [transportedTorusHomeomorphTubeRangeLift, Homeomorph.trans_apply]
  have hinput :
      (⟨transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero),
        ⟨(z, standardTorusNormalZero), rfl⟩⟩ :
          Set.range (transportedTorusNormalTubeMap Phi)) =
        transportedTorusNormalTubeHomeomorph Phi (z, standardTorusNormalZero) := by
    apply Subtype.ext
    rfl
  rw [hinput, Homeomorph.symm_apply_apply]
  change transportedTorusNormalTubeMap Phi
      (transportedTorusCoordinateHomeomorph h z, standardTorusNormalZero) = _
  rw [transportedTorusNormalTubeMap_zero]
  change (((transportedTorusHomeomorph Phi)
    ((transportedTorusHomeomorph Phi).symm
      (h (transportedTorusHomeomorph Phi z))) : transportedTorus Phi) : R3) = _
  exact congrArg Subtype.val <|
    (transportedTorusHomeomorph Phi).apply_symm_apply
      (h (transportedTorusHomeomorph Phi z))

/-- A base-fixed normal-fiber map which takes the zero slice back into the transported torus is
pointwise the identity on that slice.  In particular, the fiberwise Möbius maps cannot create
parallel curves *in* the torus; the tangential collar homeomorphism is genuine extra geometry. -/
theorem transportedTorusNormalTubeMap_eq_self_of_baseFixed_mem_torus
    (f : StandardTorusNormalTube → StandardTorusNormalTube)
    (hbase : ∀ p, (f p).1 = p.1)
    (htorus : ∀ z, transportedTorusNormalTubeMap Phi
      (f (z, standardTorusNormalZero)) ∈ transportedTorus Phi)
    (z : Circle × Circle) :
    transportedTorusNormalTubeMap Phi (f (z, standardTorusNormalZero)) =
      transportedTorusNormalTubeMap Phi (z, standardTorusNormalZero) := by
  have hnormal : (f (z, standardTorusNormalZero)).2 = standardTorusNormalZero :=
    (transportedTorusNormalTubeMap_mem_transportedTorus_iff Phi _).mp (htorus z)
  congr 1
  exact Prod.ext (hbase _) hnormal

/-! ## Small self-isotopies and their annular sweeps -/

/-- A continuous family of self-homeomorphisms of the transported torus, starting at the
identity and fixed away from a prescribed collar support. -/
structure SupportedTorusSelfIsotopy (Phi : AmbientIsotopy) where
  support : Set (transportedTorus Phi)
  homeomorph : unitInterval → transportedTorus Phi ≃ₜ transportedTorus Phi
  continuous_eval : Continuous fun p : unitInterval × transportedTorus Phi ↦
    homeomorph p.1 p.2
  at_zero : homeomorph 0 = Homeomorph.refl (transportedTorus Phi)
  fixed_off_support : ∀ t x, x ∉ support → homeomorph t x = x

namespace SupportedTorusSelfIsotopy

variable (I : SupportedTorusSelfIsotopy Phi)

/-- The terminal torus homeomorphism. -/
def terminal : transportedTorus Phi ≃ₜ transportedTorus Phi :=
  I.homeomorph 1

/-- The trace of a surface subset under the isotopy. -/
def sweep (s : Set (transportedTorus Phi)) :
    s × unitInterval → transportedTorus Phi := fun p ↦ I.homeomorph p.2 p.1

/-- The open part of the trace, omitting its two endpoint fibers. -/
def openSweep (s : Set (transportedTorus Phi)) : Set (transportedTorus Phi) :=
  Set.range fun p : s × Set.Ioo (0 : ℝ) 1 ↦
    I.homeomorph ⟨p.2.1, ⟨p.2.2.1.le, p.2.2.2.le⟩⟩ p.1

theorem continuous_sweep (s : Set (transportedTorus Phi)) :
    Continuous (I.sweep s) := by
  change Continuous ((fun p : unitInterval × transportedTorus Phi ↦
    I.homeomorph p.1 p.2) ∘ fun p : s × unitInterval ↦ (p.2, p.1))
  exact I.continuous_eval.comp
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))

@[simp] theorem sweep_zero (s : Set (transportedTorus Phi)) (x : s) :
    I.sweep s (x, 0) = x := by
  rw [sweep, I.at_zero]
  rfl

@[simp] theorem sweep_one (s : Set (transportedTorus Phi)) (x : s) :
    I.sweep s (x, 1) = I.terminal x :=
  rfl

/-- Each time slice has exactly the homeomorphic image of the source subset as its range. -/
theorem range_sweep_slice (s : Set (transportedTorus Phi)) (t : unitInterval) :
    Set.range (fun x : s ↦ I.sweep s (x, t)) = I.homeomorph t '' s := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The isotopy also has a canonical ambient extension over the transported normal-tube range at
every time. -/
def tubeRangeLift (t : unitInterval) :
    Set.range (transportedTorusNormalTubeMap Phi) ≃ₜ
      Set.range (transportedTorusNormalTubeMap Phi) :=
  transportedTorusHomeomorphTubeRangeLift (I.homeomorph t)

/-! ### Winding preservation for a pushed circle -/

theorem isEmbedding_torusCircle
    (C : EmbeddedTorusIntersectionCircle Phi) :
    IsEmbedding C.torusCircle := by
  have h := C.isEmbedding.codRestrict (transportedTorus Phi) fun z ↦
    C.range_subset_transportedTorus ⟨z, rfl⟩
  convert h using 1
  funext z
  apply Subtype.ext
  rfl

/-- The terminal homeomorphic image of the bundled circle parametrization. -/
def pushedCircleMap (C : EmbeddedTorusIntersectionCircle Phi) (z : Circle) : R3 :=
  I.terminal (C.torusCircle z)

theorem isEmbedding_pushedCircleMap (C : EmbeddedTorusIntersectionCircle Phi) :
    IsEmbedding (I.pushedCircleMap C) :=
  IsEmbedding.subtypeVal.comp <|
    I.terminal.isEmbedding.comp (isEmbedding_torusCircle C)

/-- The real-periodic parametrization obtained by applying the terminal homeomorphism to an
embedded torus circle. -/
def pushedCircleCurve (C : EmbeddedTorusIntersectionCircle Phi) (t : ℝ) :
    transportedTorus Phi :=
  I.terminal (C.windingLoop.curve t)

theorem continuous_pushedCircleCurve (C : EmbeddedTorusIntersectionCircle Phi) :
    Continuous (I.pushedCircleCurve C) :=
  I.terminal.continuous.comp C.windingLoop.continuous_curve

theorem periodic_pushedCircleCurve (C : EmbeddedTorusIntersectionCircle Phi) :
    Function.Periodic (I.pushedCircleCurve C) (2 * Real.pi) := fun t ↦
  congrArg I.terminal (C.windingLoop.periodic_curve t)

/-- A chosen coordinate lift of the terminal pushed circle. -/
def pushedCircleLift (C : EmbeddedTorusIntersectionCircle Phi) :
    TorusLoopLift (transportedLoopCoordinates Phi (I.pushedCircleCurve C)) :=
  Classical.choice <| exists_torusLoopLift_of_transportedLoop Phi
    (I.pushedCircleCurve C) (I.continuous_pushedCircleCurve C)
      (I.periodic_pushedCircleCurve C)

/-- The terminal pushed circle as a winding loop. -/
def pushedCircleLoop (C : EmbeddedTorusIntersectionCircle Phi) :
    TransportedWindingLoop Phi Set.univ where
  curve := I.pushedCircleCurve C
  continuous_curve := I.continuous_pushedCircleCurve C
  periodic_curve := I.periodic_pushedCircleCurve C
  curve_mem := fun _ ↦ Set.mem_univ _
  lift := I.pushedCircleLift C

/-- The terminal image bundled again as an embedded transported-torus intersection circle. -/
def pushedEmbeddedCircle (C : EmbeddedTorusIntersectionCircle Phi) :
    EmbeddedTorusIntersectionCircle Phi where
  circle := I.pushedCircleMap C
  isEmbedding := I.isEmbedding_pushedCircleMap C
  windingLoop := I.pushedCircleLoop C
  parametrization := by
    intro t
    apply congrArg Subtype.val
    apply congrArg I.terminal
    apply Subtype.ext
    exact C.parametrization t

/-- The surface isotopy gives a periodic product-torus homotopy from a circle to its terminal
push.  Clamping merely extends the compact isotopy parameter to the real parameter used by
`PeriodicTorusLoopHomotopy`. -/
def pushedCirclePeriodicHomotopy (C : EmbeddedTorusIntersectionCircle Phi) :
    PeriodicTorusLoopHomotopy
      (transportedLoopCoordinates Phi C.windingLoop.curve)
      (transportedLoopCoordinates Phi (I.pushedCircleCurve C)) where
  homotopy := fun s t ↦
    (transportedTorusHomeomorph Phi).symm
      (I.homeomorph (Set.projIcc 0 1 zero_le_one s) (C.windingLoop.curve t))
  continuous_homotopy := by
    apply (transportedTorusHomeomorph Phi).symm.continuous.comp
    change Continuous ((fun p : unitInterval × transportedTorus Phi ↦
      I.homeomorph p.1 p.2) ∘ fun p : ℝ × ℝ ↦
        (Set.projIcc 0 1 zero_le_one p.1, C.windingLoop.curve p.2))
    apply I.continuous_eval.comp
    exact ((continuous_projIcc.comp continuous_fst).prodMk
      (C.windingLoop.continuous_curve.comp continuous_snd))
  periodic_homotopy := by
    intro s t
    exact congrArg (fun x ↦
      (transportedTorusHomeomorph Phi).symm
        (I.homeomorph (Set.projIcc 0 1 zero_le_one s) x))
      (C.windingLoop.periodic_curve t)
  homotopy_zero := by
    funext t
    have hzero : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := by
      exact Set.projIcc_left (a := (0 : ℝ)) (b := 1) zero_le_one
    rw [hzero, I.at_zero]
    rfl
  homotopy_one := by
    funext t
    have hone : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := by
      exact Set.projIcc_right (a := (0 : ℝ)) (b := 1) zero_le_one
    rw [hone]
    rfl

/-- Both winding coordinates are preserved by a supported surface collar push. -/
theorem windingPair_pushedCircleLoop (C : EmbeddedTorusIntersectionCircle Phi) :
    (I.pushedCircleLoop C).windingPair = C.windingLoop.windingPair := by
  symm
  exact TorusLoopLift.windingPair_eq_of_periodicHomotopy
    (I.pushedCirclePeriodicHomotopy C) C.windingLoop.lift (I.pushedCircleLift C)

theorem windingPair_pushedEmbeddedCircle (C : EmbeddedTorusIntersectionCircle Phi) :
    (I.pushedEmbeddedCircle C).windingLoop.windingPair =
      C.windingLoop.windingPair :=
  I.windingPair_pushedCircleLoop C

theorem zeroWinding_pushedEmbeddedCircle
    (C : EmbeddedTorusIntersectionCircle Phi)
    (hzero : C.windingLoop.windingPair = (0, 0)) :
    (I.pushedEmbeddedCircle C).windingLoop.windingPair = (0, 0) := by
  rw [I.windingPair_pushedEmbeddedCircle, hzero]

end SupportedTorusSelfIsotopy

/-! ## The two endpoint collar pushes -/

/-- Parametrized raw circles before the two opposite collar pushes.  Unlike the pushed family,
these three circles are not required to be pairwise disjoint: the pre- and post-resolutions share
their outside arcs. -/
structure FourPortRawCircleData
    {B : PairedSeamBandChart}
    {pre post : RegularSphereFamilyParityStage Phi}
    (raw : FourPortRawEndpointData B pre post) where
  direction : FourPortBoundaryDirection
  circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi
  zeroWinding : ∀ i, (circle i).windingLoop.windingPair = (0, 0)
  pre_range : fourPortPreAffectedBoundary direction circle = raw.preAffectedBoundary
  post_range : fourPortPostAffectedBoundary direction circle = raw.postAffectedBoundary

namespace FourPortRawCircleData

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}

/-- Push the central raw circle with the isotopy belonging to its endpoint and the other two raw
circles with the opposite endpoint isotopy. -/
def pushedCircleFamily (R : FourPortRawCircleData raw)
    (preIsotopy postIsotopy : SupportedTorusSelfIsotopy Phi) :
    Fin 3 → EmbeddedTorusIntersectionCircle Phi :=
  match R.direction with
  | .split => ![preIsotopy.pushedEmbeddedCircle (R.circle 0),
      postIsotopy.pushedEmbeddedCircle (R.circle 1),
      postIsotopy.pushedEmbeddedCircle (R.circle 2)]
  | .merge => ![postIsotopy.pushedEmbeddedCircle (R.circle 0),
      preIsotopy.pushedEmbeddedCircle (R.circle 1),
      preIsotopy.pushedEmbeddedCircle (R.circle 2)]

theorem pushedCircleFamily_zeroWinding
    (R : FourPortRawCircleData raw)
    (preIsotopy postIsotopy : SupportedTorusSelfIsotopy Phi) :
    ∀ i, ((R.pushedCircleFamily preIsotopy postIsotopy) i).windingLoop.windingPair =
      (0, 0) := by
  intro i
  cases hdirection : R.direction <;> fin_cases i
  · simpa [pushedCircleFamily, hdirection] using
      preIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 0)
  · simpa [pushedCircleFamily, hdirection] using
      postIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 1)
  · simpa [pushedCircleFamily, hdirection] using
      postIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 2)
  · simpa [pushedCircleFamily, hdirection] using
      postIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 0)
  · simpa [pushedCircleFamily, hdirection] using
      preIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 1)
  · simpa [pushedCircleFamily, hdirection] using
      preIsotopy.zeroWinding_pushedEmbeddedCircle _ (R.zeroWinding 2)

end FourPortRawCircleData

/-- Local collar output for the two resolutions of one four-port move.

The two endpoint sets may overlap before pushing.  The terminal images are the three disjoint
circles.  Requiring each complete sweep to be embedded says precisely that the region between a
raw endpoint and its pushed copy is a disjoint union of annular strips.  This is the output of a
regular-neighborhood construction for the global theta graph; it is not implied by the ambient
normal-fiber homeomorphism alone. -/
structure FourPortEndpointCollarPushData
    {B : PairedSeamBandChart}
    {pre post : RegularSphereFamilyParityStage Phi}
    (raw : FourPortRawEndpointData B pre post) where
  direction : FourPortBoundaryDirection
  circle : Fin 3 → EmbeddedTorusIntersectionCircle Phi
  zeroWinding : ∀ i, (circle i).windingLoop.windingPair = (0, 0)
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (circle i).circle) (Set.range (circle j).circle)
  preIsotopy : SupportedTorusSelfIsotopy Phi
  postIsotopy : SupportedTorusSelfIsotopy Phi
  preSweep_isEmbedding : IsEmbedding (preIsotopy.sweep raw.preAffectedBoundary)
  postSweep_isEmbedding : IsEmbedding (postIsotopy.sweep raw.postAffectedBoundary)
  pre_terminal_range : Set.range
      (fun x : raw.preAffectedBoundary ↦ preIsotopy.terminal x) =
    fourPortPreAffectedBoundary direction circle
  post_terminal_range : Set.range
      (fun x : raw.postAffectedBoundary ↦ postIsotopy.terminal x) =
    fourPortPostAffectedBoundary direction circle

namespace FourPortEndpointCollarPushData

variable {B : PairedSeamBandChart}
  {pre post : RegularSphereFamilyParityStage Phi}
  {raw : FourPortRawEndpointData B pre post}

/-- Construct the local collar package from parametrized raw circles and the two actual surface
self-isotopies.  The pushed circles and their zero winding are derived.  The two range equalities
are exactly the remaining endpoint attachment calculation for the global outside arcs. -/
def ofRawCircles
    (R : FourPortRawCircleData raw)
    (preIsotopy postIsotopy : SupportedTorusSelfIsotopy Phi)
    (preSweep_isEmbedding : IsEmbedding (preIsotopy.sweep raw.preAffectedBoundary))
    (postSweep_isEmbedding : IsEmbedding (postIsotopy.sweep raw.postAffectedBoundary))
    (pairwise_disjoint : Pairwise fun i j ↦
      Disjoint
        (Set.range ((R.pushedCircleFamily preIsotopy postIsotopy) i).circle)
        (Set.range ((R.pushedCircleFamily preIsotopy postIsotopy) j).circle))
    (pre_terminal_range : Set.range
        (fun x : raw.preAffectedBoundary ↦ preIsotopy.terminal x) =
      fourPortPreAffectedBoundary R.direction
        (R.pushedCircleFamily preIsotopy postIsotopy))
    (post_terminal_range : Set.range
        (fun x : raw.postAffectedBoundary ↦ postIsotopy.terminal x) =
      fourPortPostAffectedBoundary R.direction
        (R.pushedCircleFamily preIsotopy postIsotopy)) :
    FourPortEndpointCollarPushData raw where
  direction := R.direction
  circle := R.pushedCircleFamily preIsotopy postIsotopy
  zeroWinding := R.pushedCircleFamily_zeroWinding preIsotopy postIsotopy
  pairwise_disjoint := pairwise_disjoint
  preIsotopy := preIsotopy
  postIsotopy := postIsotopy
  preSweep_isEmbedding := preSweep_isEmbedding
  postSweep_isEmbedding := postSweep_isEmbedding
  pre_terminal_range := pre_terminal_range
  post_terminal_range := post_terminal_range

/-- Restriction of the pre-side terminal homeomorphism to its raw affected boundary. -/
def prePush (D : FourPortEndpointCollarPushData raw) :
    raw.preAffectedBoundary → transportedTorus Phi := fun x ↦ D.preIsotopy.terminal x

/-- Restriction of the post-side terminal homeomorphism to its raw affected boundary. -/
def postPush (D : FourPortEndpointCollarPushData raw) :
    raw.postAffectedBoundary → transportedTorus Phi := fun x ↦ D.postIsotopy.terminal x

theorem prePush_isEmbedding (D : FourPortEndpointCollarPushData raw) :
    IsEmbedding D.prePush :=
  D.preIsotopy.terminal.isEmbedding.comp IsEmbedding.subtypeVal

theorem postPush_isEmbedding (D : FourPortEndpointCollarPushData raw) :
    IsEmbedding D.postPush :=
  D.postIsotopy.terminal.isEmbedding.comp IsEmbedding.subtypeVal

/-- The local collar output supplies exactly the endpoint package used by the pair-of-pants
trace. -/
def toFourPortEndpointCircleData
    (D : FourPortEndpointCollarPushData raw) :
    FourPortEndpointCircleData raw where
  direction := D.direction
  circle := D.circle
  zeroWinding := D.zeroWinding
  pairwise_disjoint := D.pairwise_disjoint
  prePush := D.prePush
  postPush := D.postPush
  prePush_isEmbedding := D.prePush_isEmbedding
  postPush_isEmbedding := D.postPush_isEmbedding
  prePush_range := D.pre_terminal_range
  postPush_range := D.post_terminal_range

/-- The open collar strips swept from both endpoint resolutions. -/
def openAnnularStrips (D : FourPortEndpointCollarPushData raw) :
    Set (transportedTorus Phi) :=
  D.preIsotopy.openSweep raw.preAffectedBoundary ∪
    D.postIsotopy.openSweep raw.postAffectedBoundary

/-- The natural candidate interior is the strict parity-change region enlarged by the two open
annular sweeps. -/
def collarAugmentedInterior (D : FourPortEndpointCollarPushData raw) :
    Set (transportedTorus Phi) :=
  regularStageStrictLabelChangeLocus pre post ∪ D.openAnnularStrips

/-- The only global attachment input left after constructing the two local collar pushes.

It says that the strict change region and the two swept annular strips glue to one open connected
pair-of-pants interior, that all label-change points lie in its closure, and that its frontier is
exactly the three pushed circles.  No collar homeomorphism or annular embedding is repeated in
this structure. -/
structure GlobalTraceAttachment (D : FourPortEndpointCollarPushData raw) : Prop where
  nonempty : D.collarAugmentedInterior.Nonempty
  isConnected : IsConnected D.collarAugmentedInterior
  isOpen : IsOpen D.collarAugmentedInterior
  labelChange_subset_closure : regularStageLabelChangeLocus pre post ⊆
    closure D.collarAugmentedInterior
  frontier_exact : closure D.collarAugmentedInterior \ D.collarAugmentedInterior =
    ⋃ i, torusCircleCarrier (D.circle i)

/-- Once the global theta-graph attachment is identified, the local collar construction gives
the exact embedded pair-of-pants trace expected by the disk-side argument. -/
def toEmbeddedPairOfPantsTrace
    (D : FourPortEndpointCollarPushData raw)
    (A : D.GlobalTraceAttachment) :
    EmbeddedPairOfPantsTrace D.toFourPortEndpointCircleData :=
  EmbeddedPairOfPantsTrace.ofCollarAugmentedInterior
    D.toFourPortEndpointCircleData D.collarAugmentedInterior A.nonempty
      A.isConnected A.isOpen A.labelChange_subset_closure A.frontier_exact

end FourPortEndpointCollarPushData

end Submission.Topology
