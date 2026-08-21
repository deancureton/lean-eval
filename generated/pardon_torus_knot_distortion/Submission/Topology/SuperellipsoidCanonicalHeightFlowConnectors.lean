import Submission.Topology.ThreePathFilledRegion

/-!
# Canonical height-flow slices for the four-port connectors

The normalized gradient flow of the regular height band moves the complete extended inward
excursion through a family of injective constant-height arcs.  At nonzero time, its intersection
with the analytic barrier is exactly the zero set of the outer defect.  The lower and upper
connectors will be obtained by trimming these slices between their two outer-level crossings.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus
open EmbeddedTorusIntersectionCircle
open FiniteSuperellipsoidBarrierGraph
open FiniteSuperellipsoidBarrierGraph.CutCircleTransverseCyclicOrderFamily

namespace SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

variable (D : CanonicalEndpointRegularityData S)

private abbrev ConnectorBand := D.openChartNarrowedData.heightData.band

private abbrev ConnectorBandIndex :=
  Fin D.centralCutOrder.toPairedSeamEnumeration.bandCount

private abbrev ConnectorFlowTimes := globalBandFlowCollarTimes D.ConnectorBand

/-- The complete normalized-gradient flow of the narrowed regular height band. -/
noncomputable def centralHeightFlowData :
    RegularBandNormalizedGradientFlowData D.ConnectorBand :=
  Classical.choice (exists_regularBandNormalizedGradientFlowData D.ConnectorBand)

/-- One point of the extended inward excursion flowed to a fixed nearby height. -/
def centralHeightFlowSliceLift (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (u : unitInterval) : Plane :=
  globalBandPlaneFlowCollarMap D.centralCutOrder b D.ConnectorBand
    D.centralHeightFlowData (u, t)

theorem continuous_centralHeightFlowSliceLift (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Continuous (D.centralHeightFlowSliceLift b t) := by
  exact (D.centralCutOrder.continuous_globalBandPlaneFlowCollarMap b D.ConnectorBand
    D.centralHeightFlowData).comp (continuous_id.prodMk continuous_const)

theorem centralHeightFlowSliceLift_injective (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Function.Injective (D.centralHeightFlowSliceLift b t) := by
  intro u v huv
  have hp := D.centralCutOrder.globalBandPlaneFlowCollarMap_injective b D.ConnectorBand
    D.centralHeightFlowData huv
  exact congrArg Prod.fst hp

/-- Every fixed-time slice has the expected exact oriented height. -/
theorem orientedCoordinateLift_centralHeightFlowSliceLift (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (u : unitInterval) :
    orientedCoordinateLift Phi frame 2 (D.centralHeightFlowSliceLift b t u) =
      S.cut.height + t := by
  exact D.centralCutOrder.orientedCoordinateLift_globalBandPlaneFlowCollarMap
    b D.ConnectorBand D.centralHeightFlowData (u, t)

/-- Restrict a fixed-time collar slice to the original closed inward excursion. -/
def centralHeightFlowCoreSliceLift (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (u : unitInterval) : Plane :=
  D.centralHeightFlowSliceLift b t
    (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
      (D.centralCutOrder.globalBandCoreRight b) u)

theorem continuous_centralHeightFlowCoreSliceLift (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Continuous (D.centralHeightFlowCoreSliceLift b t) := by
  exact (D.continuous_centralHeightFlowSliceLift b t).comp
    (Icc.continuous_convexComb _ _)

theorem centralHeightFlowCoreSliceLift_injective (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Function.Injective (D.centralHeightFlowCoreSliceLift b t) := by
  intro u v huv
  have hparameter := D.centralHeightFlowSliceLift_injective b t huv
  have hvalue := congrArg Subtype.val hparameter
  simp only [Icc.coe_convexComb] at hvalue
  apply Subtype.ext
  have hfactor :
      ((u : ℝ) - v) *
        ((D.centralCutOrder.globalBandCoreRight b : ℝ) -
          D.centralCutOrder.globalBandCoreLeft b) = 0 := by
    nlinarith
  have hgap :
      (D.centralCutOrder.globalBandCoreRight b : ℝ) -
          D.centralCutOrder.globalBandCoreLeft b ≠ 0 :=
    ne_of_gt (sub_pos.mpr (D.centralCutOrder.globalBandCoreLeft_lt_coreRight b))
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hgap)

theorem orientedCoordinateLift_centralHeightFlowCoreSliceLift
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) (u : unitInterval) :
    orientedCoordinateLift Phi frame 2 (D.centralHeightFlowCoreSliceLift b t u) =
      S.cut.height + t := by
  exact D.orientedCoordinateLift_centralHeightFlowSliceLift b t _

/-- At time zero, the core slice projects pointwise to the selected inward excursion. -/
theorem transportedTorusPlaneMap_centralHeightFlowCoreSliceLift_zero
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    transportedTorusPlaneMap Phi
        (D.centralHeightFlowCoreSliceLift b
          (globalBandFlowCollarZeroTime D.ConnectorBand) u) =
      ((D.centralCutOrder.globalBandPath b u : transportedTorus Phi) : R3) := by
  exact D.centralCutOrder.transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_core
    b D.ConnectorBand D.centralHeightFlowData u

/-- Outer polynomial minus the selected outer level along one height-flow slice. -/
def centralHeightFlowOuterDefect (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (u : unitInterval) : ℝ :=
  globalBandFlowOuterDefect D.centralCutOrder b D.ConnectorBand
    D.centralHeightFlowData (u, t)

theorem continuous_centralHeightFlowOuterDefect (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Continuous (D.centralHeightFlowOuterDefect b t) := by
  exact (D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
    D.centralHeightFlowData).comp (continuous_id.prodMk continuous_const)

theorem centralHeightFlowOuterDefect_coreLeft_zero (b : D.ConnectorBandIndex) :
    D.centralHeightFlowOuterDefect b (globalBandFlowCollarZeroTime D.ConnectorBand)
        (D.centralCutOrder.globalBandCoreLeft b) = 0 := by
  unfold centralHeightFlowOuterDefect globalBandFlowOuterDefect
  rw [D.centralCutOrder.globalBandPlaneFlowCollarMap_zeroTime]
  rw [sub_eq_zero]
  exact congrArg Prod.fst
    (D.centralCutOrder.globalBandLeftFlowSeamLift_mem_seamFiber b D.scale_pos)

theorem centralHeightFlowOuterDefect_coreRight_zero (b : D.ConnectorBandIndex) :
    D.centralHeightFlowOuterDefect b (globalBandFlowCollarZeroTime D.ConnectorBand)
        (D.centralCutOrder.globalBandCoreRight b) = 0 := by
  unfold centralHeightFlowOuterDefect globalBandFlowOuterDefect
  rw [D.centralCutOrder.globalBandPlaneFlowCollarMap_zeroTime]
  rw [sub_eq_zero]
  exact congrArg Prod.fst
    (D.centralCutOrder.globalBandRightFlowSeamLift_mem_seamFiber b D.scale_pos)

/-- The open interior of the zero-time core has strictly negative outer defect. -/
theorem centralHeightFlowOuterDefect_core_zero_neg (b : D.ConnectorBandIndex)
    (u : unitInterval) (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    D.centralHeightFlowOuterDefect b (globalBandFlowCollarZeroTime D.ConnectorBand)
        (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
          (D.centralCutOrder.globalBandCoreRight b) u) < 0 := by
  have hbody := D.centralCutOrder.globalInwardExcursionPath_mem_body
    (D.centralCutOrder.globalGapOfBand b) u hu0 hu1
  have hmap := D.transportedTorusPlaneMap_centralHeightFlowCoreSliceLift_zero b u
  unfold centralHeightFlowOuterDefect globalBandFlowOuterDefect
  unfold centralHeightFlowCoreSliceLift centralHeightFlowSliceLift at hmap
  unfold superellipsoidPolynomialLift
  rw [hmap]
  exact sub_neg.mpr
    ((mem_superellipsoidBody_iff_polynomial_lt_pow frame c _ D.scale_pos).mp hbody)

/-- Fixed interior parameters used to retain a compact negative core. -/
def connectorInnerLeft : unitInterval := ⟨1 / 4, by norm_num⟩

def connectorInnerRight : unitInterval := ⟨3 / 4, by norm_num⟩

theorem connectorInnerLeft_pos : (0 : unitInterval) < connectorInnerLeft := by
  change (0 : ℝ) < 1 / 4
  norm_num

theorem connectorInnerRight_lt_one : connectorInnerRight < (1 : unitInterval) := by
  change (3 / 4 : ℝ) < 1
  norm_num

theorem connectorInnerLeft_le_right : connectorInnerLeft ≤ connectorInnerRight := by
  norm_num [connectorInnerLeft, connectorInnerRight]

/-- The outer defect on the original inward core, jointly in core parameter and flow time. -/
def centralHeightFlowCoreOuterDefect (b : D.ConnectorBandIndex)
    (p : unitInterval × D.ConnectorFlowTimes) : ℝ :=
  D.centralHeightFlowOuterDefect b p.2
    (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
      (D.centralCutOrder.globalBandCoreRight b) p.1)

theorem continuous_centralHeightFlowCoreOuterDefect (b : D.ConnectorBandIndex) :
    Continuous (D.centralHeightFlowCoreOuterDefect b) := by
  exact (D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
    D.centralHeightFlowData).comp
      (((Icc.continuous_convexComb _ _).comp continuous_fst).prodMk continuous_snd)

def centralConnectorInteriorParameters : Set unitInterval :=
  Icc connectorInnerLeft connectorInnerRight

def centralHeightFlowCoreNegativeParameters (b : D.ConnectorBandIndex) :
    Set (unitInterval × D.ConnectorFlowTimes) :=
  {p | D.centralHeightFlowCoreOuterDefect b p < 0}

theorem isOpen_centralHeightFlowCoreNegativeParameters (b : D.ConnectorBandIndex) :
    IsOpen (D.centralHeightFlowCoreNegativeParameters b) :=
  isOpen_lt (D.continuous_centralHeightFlowCoreOuterDefect b) continuous_const

theorem centralConnectorInterior_zero_subset_negative (b : D.ConnectorBandIndex) :
    centralConnectorInteriorParameters ×ˢ
        {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆
      D.centralHeightFlowCoreNegativeParameters b := by
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have ht0 : t = globalBandFlowCollarZeroTime D.ConnectorBand :=
    Set.mem_singleton_iff.mp ht
  subst t
  apply D.centralHeightFlowOuterDefect_core_zero_neg b u
  · intro hu0
    have huval := hu0
    have hul := hu.1
    change (connectorInnerLeft : ℝ) ≤ (u : ℝ) at hul
    have hleft : (0 : ℝ) < connectorInnerLeft := connectorInnerLeft_pos
    linarith
  · intro hu1
    have huval := hu1
    have hur := hu.2
    change (u : ℝ) ≤ (connectorInnerRight : ℝ) at hur
    have hright : (connectorInnerRight : ℝ) < 1 := connectorInnerRight_lt_one
    linarith

/-- For one band, a single time radius keeps the fixed compact core strictly inside the outer
surface. -/
theorem exists_centralConnectorNegativeTimeRadius (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ centralConnectorInteriorParameters,
        D.centralHeightFlowCoreOuterDefect b (u, t) < 0 := by
  obtain ⟨U, V, hUopen, hVopen, htrimU, hzeroV, hUV⟩ :=
    generalized_tube_lemma
      (isCompact_Icc : IsCompact centralConnectorInteriorParameters)
      (isCompact_singleton : IsCompact
        ({globalBandFlowCollarZeroTime D.ConnectorBand} : Set D.ConnectorFlowTimes))
      (D.isOpen_centralHeightFlowCoreNegativeParameters b)
      (D.centralConnectorInterior_zero_subset_negative b)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hVopen
    (globalBandFlowCollarZeroTime D.ConnectorBand)
    (hzeroV (Set.mem_singleton _))
  refine ⟨η, hη, fun t ht u hu ↦ ?_⟩
  apply hUV
  constructor
  · exact htrimU hu
  · apply hball
    change dist (t : ℝ) 0 < η
    simpa only [Real.dist_eq, sub_zero] using ht

/-- A selected negative-core radius for one band. -/
noncomputable def centralConnectorNegativeTimeRadius (b : D.ConnectorBandIndex) : ℝ :=
  Classical.choose (D.exists_centralConnectorNegativeTimeRadius b)

theorem centralConnectorNegativeTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorNegativeTimeRadius b :=
  (Classical.choose_spec (D.exists_centralConnectorNegativeTimeRadius b)).1

theorem centralConnectorNegativeTimeRadius_spec (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (ht : |(t : ℝ)| < D.centralConnectorNegativeTimeRadius b)
    (u : unitInterval) (hu : u ∈ centralConnectorInteriorParameters) :
    D.centralHeightFlowCoreOuterDefect b (u, t) < 0 :=
  (Classical.choose_spec (D.exists_centralConnectorNegativeTimeRadius b)).2 t ht u hu

private def centralConnectorRadiusCandidates : Finset ℝ :=
  insert D.ConnectorBand.ε
    (Finset.univ.image D.centralConnectorNegativeTimeRadius)

private theorem centralConnectorRadiusCandidates_nonempty :
    D.centralConnectorRadiusCandidates.Nonempty :=
  ⟨D.ConnectorBand.ε, Finset.mem_insert_self _ _⟩

/-- One positive radius works for the negative core of every canonical band. -/
noncomputable def uniformCentralConnectorNegativeTimeRadius : ℝ :=
  D.centralConnectorRadiusCandidates.inf'
    D.centralConnectorRadiusCandidates_nonempty id

theorem uniformCentralConnectorNegativeTimeRadius_pos :
    0 < D.uniformCentralConnectorNegativeTimeRadius := by
  apply (Finset.lt_inf'_iff D.centralConnectorRadiusCandidates_nonempty).2
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact D.ConnectorBand.ε_pos
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    exact D.centralConnectorNegativeTimeRadius_pos b

theorem uniformCentralConnectorNegativeTimeRadius_le_band
    (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorNegativeTimeRadius ≤
      D.centralConnectorNegativeTimeRadius b := by
  apply Finset.inf'_le id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

theorem uniformCentralConnectorNegativeTimeRadius_le_epsilon :
    D.uniformCentralConnectorNegativeTimeRadius ≤ D.ConnectorBand.ε := by
  apply Finset.inf'_le id
  exact Finset.mem_insert_self _ _

theorem uniformCentralConnectorNegativeTimeRadius_spec
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.uniformCentralConnectorNegativeTimeRadius)
    (u : unitInterval) (hu : u ∈ centralConnectorInteriorParameters) :
    D.centralHeightFlowCoreOuterDefect b (u, t) < 0 := by
  apply D.centralConnectorNegativeTimeRadius_spec b t
    (ht.trans_le (D.uniformCentralConnectorNegativeTimeRadius_le_band b)) u hu

private theorem exists_positive_left_probe_of_negative_right
    {f : ℝ → ℝ} {a c r : ℝ} (hac : a < c) (hcr : c < r)
    (hnegative : ∀ y ∈ Ioo c r, f y < 0)
    (hflip : ∃ ε > 0, ∀ x ∈ Ioo (c - ε) c,
      ∀ y ∈ Ioo c (c + ε), f x * f y < 0) :
    ∃ x ∈ Ioo a c, 0 < f x := by
  obtain ⟨ε, hε, hflip⟩ := hflip
  let δ := min (ε / 2) (min ((c - a) / 2) ((r - c) / 2))
  have hδ : 0 < δ := by
    exact lt_min (half_pos hε) <| lt_min
      (half_pos (sub_pos.mpr hac)) (half_pos (sub_pos.mpr hcr))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδa : δ < c - a :=
    (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hac))
  have hδr : δ < r - c :=
    (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hcr))
  let x := c - δ
  let y := c + δ
  have hxLocal : x ∈ Ioo (c - ε) c := by
    dsimp [x]
    constructor <;> linarith
  have hyLocal : y ∈ Ioo c (c + ε) := by
    dsimp [y]
    constructor <;> linarith
  have hxInterval : x ∈ Ioo a c := by
    dsimp [x]
    constructor <;> linarith
  have hyInterval : y ∈ Ioo c r := by
    dsimp [y]
    constructor <;> linarith
  have hproduct := hflip x hxLocal y hyLocal
  have hynegative := hnegative y hyInterval
  refine ⟨x, hxInterval, ?_⟩
  rcases mul_neg_iff.mp hproduct with hxy | hxy
  · exact hxy.1
  · exact False.elim ((not_lt_of_ge hynegative.le) hxy.2)

private theorem exists_positive_right_probe_of_negative_left
    {f : ℝ → ℝ} {l c a : ℝ} (hlc : l < c) (hca : c < a)
    (hnegative : ∀ x ∈ Ioo l c, f x < 0)
    (hflip : ∃ ε > 0, ∀ x ∈ Ioo (c - ε) c,
      ∀ y ∈ Ioo c (c + ε), f x * f y < 0) :
    ∃ y ∈ Ioo c a, 0 < f y := by
  obtain ⟨ε, hε, hflip⟩ := hflip
  let δ := min (ε / 2) (min ((c - l) / 2) ((a - c) / 2))
  have hδ : 0 < δ := by
    exact lt_min (half_pos hε) <| lt_min
      (half_pos (sub_pos.mpr hlc)) (half_pos (sub_pos.mpr hca))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδl : δ < c - l :=
    (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hlc))
  have hδa : δ < a - c :=
    (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hca))
  let x := c - δ
  let y := c + δ
  have hxLocal : x ∈ Ioo (c - ε) c := by
    dsimp [x]
    constructor <;> linarith
  have hyLocal : y ∈ Ioo c (c + ε) := by
    dsimp [y]
    constructor <;> linarith
  have hxInterval : x ∈ Ioo l c := by
    dsimp [x]
    constructor <;> linarith
  have hyInterval : y ∈ Ioo c a := by
    dsimp [y]
    constructor <;> linarith
  have hproduct := hflip x hxLocal y hyLocal
  have hxnegative := hnegative x hxInterval
  refine ⟨y, hyInterval, ?_⟩
  rcases mul_neg_iff.mp hproduct with hxy | hxy
  · exact False.elim ((not_lt_of_ge hxnegative.le) hxy.1)
  · exact hxy.2

private theorem localSignFlip_add_period
    {f : ℝ → ℝ} {c p : ℝ} (hperiodic : Function.Periodic f p)
    (hflip : ∃ ε > 0, ∀ x ∈ Ioo (c - ε) c, ∀ y ∈ Ioo c (c + ε),
      f x * f y < 0) :
    ∃ ε > 0, ∀ x ∈ Ioo (c + p - ε) (c + p),
      ∀ y ∈ Ioo (c + p) (c + p + ε), f x * f y < 0 := by
  obtain ⟨ε, hε, hflip⟩ := hflip
  refine ⟨ε, hε, fun x hx y hy ↦ ?_⟩
  have hx' : x - p ∈ Ioo (c - ε) c := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : y - p ∈ Ioo c (c + ε) := by
    constructor <;> linarith [hy.1, hy.2]
  have hxperiod : f x = f (x - p) := by
    calc
      f x = f ((x - p) + p) := by ring_nf
      _ = f (x - p) := hperiodic (x - p)
  have hyperiod : f y = f (y - p) := by
    calc
      f y = f ((y - p) + p) := by ring_nf
      _ = f (y - p) := hperiodic (y - p)
  rw [hxperiod, hyperiod]
  exact hflip (x - p) hx' (y - p) hy'

private theorem centralBandOuterDefect_neg
    (b : D.ConnectorBandIndex) {t : ℝ}
    (ht : t ∈ Ioo (D.centralCutOrder.globalBandLeftParameter b)
      (D.centralCutOrder.globalBandRightParameter b)) :
    D.centralGraph.cutCircleOuterPolynomialDifference
        (D.centralCutOrder.globalGapOfBand b).1.1 t < 0 := by
  let F := D.centralCutOrder
  let G := D.centralGraph
  let g := F.globalGapOfBand b
  let O := F.order g.1
  let q := F.globalGapFinIndex g
  have hside := G.cutCircleCyclicGapSide_strict g.1.1 D.scale_pos.le
    O.crossings_nonempty q t (by
      simpa [F, G, g, q, globalBandLeftParameter, globalBandRightParameter] using ht)
  have hgap : G.cutCircleCyclicGapSide g.1.1 O.crossings_nonempty q = false := by
    simpa [CutCircleTransverseCyclicOrder.sideData, cutCircleZModGapSide,
      F, G, g, O, q, globalGapFinIndex] using g.2.2
  rw [hgap] at hside
  simpa [F, G, g] using hside

private theorem centralBandLeftLocalSignFlip (b : D.ConnectorBandIndex) :
    ∃ ε > 0,
      ∀ x ∈ Ioo (D.centralCutOrder.globalBandLeftParameter b - ε)
          (D.centralCutOrder.globalBandLeftParameter b),
      ∀ y ∈ Ioo (D.centralCutOrder.globalBandLeftParameter b)
          (D.centralCutOrder.globalBandLeftParameter b + ε),
        D.centralGraph.cutCircleOuterPolynomialDifference
            (D.centralCutOrder.globalGapOfBand b).1.1 x *
          D.centralGraph.cutCircleOuterPolynomialDifference
            (D.centralCutOrder.globalGapOfBand b).1.1 y < 0 := by
  let g := D.centralCutOrder.globalGapOfBand b
  let M : SmoothCutCircleLiftData D.centralGraph g.1.1 :=
    (D.centralCutFamily.smoothLift g.1.1).toSmoothCutCircleLiftData
      (G := D.centralGraph) (j := g.1.1) rfl
  exact M.hasLocalPolynomialSignFlipAtCrossings D.scale_pos.le S.cut.seamRegular
    _ (D.centralGraph.cutCircleSortedCrossing_mem g.1.1
      (D.centralCutOrder.globalGapFinIndex g))

private theorem centralBandRightLocalSignFlip (b : D.ConnectorBandIndex) :
    ∃ ε > 0,
      ∀ x ∈ Ioo (D.centralCutOrder.globalBandRightParameter b - ε)
          (D.centralCutOrder.globalBandRightParameter b),
      ∀ y ∈ Ioo (D.centralCutOrder.globalBandRightParameter b)
          (D.centralCutOrder.globalBandRightParameter b + ε),
        D.centralGraph.cutCircleOuterPolynomialDifference
            (D.centralCutOrder.globalGapOfBand b).1.1 x *
          D.centralGraph.cutCircleOuterPolynomialDifference
            (D.centralCutOrder.globalGapOfBand b).1.1 y < 0 := by
  let F := D.centralCutOrder
  let G := D.centralGraph
  let g := F.globalGapOfBand b
  let O := F.order g.1
  let q := F.globalGapFinIndex g
  let M : SmoothCutCircleLiftData G g.1.1 :=
    (D.centralCutFamily.smoothLift g.1.1).toSmoothCutCircleLiftData
      (G := G) (j := g.1.1) rfl
  by_cases hnext : q.1 + 1 < (G.cutCircleSeamCrossings g.1.1).card
  · have hflip := M.hasLocalPolynomialSignFlipAtCrossings D.scale_pos.le
      S.cut.seamRegular _
        (G.cutCircleSortedCrossing_mem g.1.1 ⟨q.1 + 1, hnext⟩)
    simpa [F, G, g, O, q, globalBandRightParameter, cutCircleCyclicRight, hnext]
      using hflip
  · let first : Fin (G.cutCircleSeamCrossings g.1.1).card :=
      ⟨0, Finset.card_pos.mpr O.crossings_nonempty⟩
    have hflip := M.hasLocalPolynomialSignFlipAtCrossings D.scale_pos.le
      S.cut.seamRegular (G.cutCircleSortedCrossing g.1.1 first)
        (G.cutCircleSortedCrossing_mem g.1.1 first)
    have hshift := localSignFlip_add_period
      (G.periodic_cutCircleOuterPolynomialDifference g.1.1) hflip
    simpa [F, G, g, O, q, first, globalBandRightParameter,
      cutCircleCyclicRight, hnext, add_assoc] using hshift

/-- Real parameters whose zero-time cutting-circle points lie in the chosen open band chart. -/
def centralConnectorSurfacePatchParameters (b : D.ConnectorBandIndex) : Set ℝ :=
  {s | (D.centralCutOrder.globalBandCircle b).windingLoop.curve s ∈
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch}

theorem isOpen_centralConnectorSurfacePatchParameters (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorSurfacePatchParameters b) := by
  exact (D.centralCutOrder.globalBandOpenTubularChartFamily_surfacePatch_open b).preimage
    (D.centralCutOrder.globalBandCircle b).windingLoop.continuous_curve

private theorem globalBandLeftParameter_mem_surfacePatchParameters
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandLeftParameter b ∈
      D.centralConnectorSurfacePatchParameters b := by
  let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  have hEq :
      (D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandLeftParameter b) =
        ((T.strip (bandSeamPath (0 : unitInterval)) : T.surfacePatch) :
          transportedTorus Phi) := by
    apply Subtype.ext
    calc
      ((D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandLeftParameter b) : R3) =
          ((D.centralCutOrder.globalBandPath b (0 : unitInterval) :
            transportedTorus Phi) : R3) := by
        simp [globalBandPath, globalBandCircle, globalBandLeftParameter]
      _ = (((T.strip (bandSeamPath (0 : unitInterval)) : T.surfacePatch) :
          transportedTorus Phi) : R3) := (T.core_alignment 0).symm
  change (D.centralCutOrder.globalBandCircle b).windingLoop.curve
      (D.centralCutOrder.globalBandLeftParameter b) ∈ T.surfacePatch
  rw [hEq]
  exact (T.strip (bandSeamPath (0 : unitInterval))).property

private theorem globalBandRightParameter_mem_surfacePatchParameters
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandRightParameter b ∈
      D.centralConnectorSurfacePatchParameters b := by
  let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  have hEq :
      (D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandRightParameter b) =
        ((T.strip (bandSeamPath (1 : unitInterval)) : T.surfacePatch) :
          transportedTorus Phi) := by
    apply Subtype.ext
    calc
      ((D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandRightParameter b) : R3) =
          ((D.centralCutOrder.globalBandPath b (1 : unitInterval) :
            transportedTorus Phi) : R3) := by
        simp [globalBandPath, globalBandCircle, globalBandRightParameter]
      _ = (((T.strip (bandSeamPath (1 : unitInterval)) : T.surfacePatch) :
          transportedTorus Phi) : R3) := (T.core_alignment 1).symm
  change (D.centralCutOrder.globalBandCircle b).windingLoop.curve
      (D.centralCutOrder.globalBandRightParameter b) ∈ T.surfacePatch
  rw [hEq]
  exact (T.strip (bandSeamPath (1 : unitInterval))).property

/-- The canonical covering-plane lift at one real cutting-circle parameter. -/
def centralConnectorPlanePoint (b : D.ConnectorBandIndex) (s : ℝ) : Plane :=
  EmbeddedTorusIntersectionCircle.coveringPlaneCoordinates
    ((D.centralCutOrder.globalBandCircle b).zeroWindingPlaneLift s)

theorem continuous_centralConnectorPlanePoint (b : D.ConnectorBandIndex) :
    Continuous (D.centralConnectorPlanePoint b) :=
  EmbeddedTorusIntersectionCircle.coveringPlaneCoordinates.continuous.comp
    (D.centralCutOrder.globalBandCircle b).continuous_zeroWindingPlaneLift

private theorem centralConnectorPlanePoint_leftBoundary (b : D.ConnectorBandIndex) :
    D.centralConnectorPlanePoint b (D.centralCutOrder.globalBandLeftParameter b) =
      D.centralCutOrder.globalBandLeftFlowSeamLift b := by
  unfold centralConnectorPlanePoint globalBandLeftFlowSeamLift globalBandFlowBasePoint
  congr 1
  change (D.centralCutOrder.globalBandCircle b).zeroWindingPlaneLift
      (D.centralCutOrder.globalBandLeftParameter b) =
    (D.centralCutOrder.globalBandCircle b).zeroWindingPlaneLift
      (D.centralCutOrder.globalBandExtensionParameter b
        (D.centralCutOrder.globalBandCoreLeft b))
  rw [D.centralCutOrder.globalBandExtensionParameter_coreLeft b]

private theorem centralConnectorPlanePoint_rightBoundary (b : D.ConnectorBandIndex) :
    D.centralConnectorPlanePoint b (D.centralCutOrder.globalBandRightParameter b) =
      D.centralCutOrder.globalBandRightFlowSeamLift b := by
  unfold centralConnectorPlanePoint globalBandRightFlowSeamLift globalBandFlowBasePoint
  congr 1
  change (D.centralCutOrder.globalBandCircle b).zeroWindingPlaneLift
      (D.centralCutOrder.globalBandRightParameter b) =
    (D.centralCutOrder.globalBandCircle b).zeroWindingPlaneLift
      (D.centralCutOrder.globalBandExtensionParameter b
        (D.centralCutOrder.globalBandCoreRight b))
  rw [D.centralCutOrder.globalBandExtensionParameter_coreRight b]

/-- Left-side real parameters lying simultaneously in the tubular strip and the seam inverse
function chart. -/
def centralConnectorLeftAdmissibleParameters (b : D.ConnectorBandIndex) : Set ℝ :=
  D.centralConnectorSurfacePatchParameters b ∩
    D.centralConnectorPlanePoint b ⁻¹'
      (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source

/-- Right-side real parameters lying simultaneously in the tubular strip and the seam inverse
function chart. -/
def centralConnectorRightAdmissibleParameters (b : D.ConnectorBandIndex) : Set ℝ :=
  D.centralConnectorSurfacePatchParameters b ∩
    D.centralConnectorPlanePoint b ⁻¹'
      (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source

private theorem isOpen_centralConnectorLeftAdmissibleParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorLeftAdmissibleParameters b) :=
  (D.isOpen_centralConnectorSurfacePatchParameters b).inter
    ((D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
      S.cut.seamRegular).open_source.preimage
        (D.continuous_centralConnectorPlanePoint b))

private theorem isOpen_centralConnectorRightAdmissibleParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorRightAdmissibleParameters b) :=
  (D.isOpen_centralConnectorSurfacePatchParameters b).inter
    ((D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
      S.cut.seamRegular).open_source.preimage
        (D.continuous_centralConnectorPlanePoint b))

private theorem globalBandLeftParameter_mem_admissibleParameters
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandLeftParameter b ∈
      D.centralConnectorLeftAdmissibleParameters b := by
  constructor
  · exact D.globalBandLeftParameter_mem_surfacePatchParameters b
  · show D.centralConnectorPlanePoint b
        (D.centralCutOrder.globalBandLeftParameter b) ∈
      (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source
    rw [D.centralConnectorPlanePoint_leftBoundary b]
    exact D.centralCutOrder.globalBandLeftFlowSeamLift_mem_standardChartSource b
      D.scale_pos S.cut.seamRegular

private theorem globalBandRightParameter_mem_admissibleParameters
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandRightParameter b ∈
      D.centralConnectorRightAdmissibleParameters b := by
  constructor
  · exact D.globalBandRightParameter_mem_surfacePatchParameters b
  · show D.centralConnectorPlanePoint b
        (D.centralCutOrder.globalBandRightParameter b) ∈
      (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source
    rw [D.centralConnectorPlanePoint_rightBoundary b]
    exact D.centralCutOrder.globalBandRightFlowSeamLift_mem_standardChartSource b
      D.scale_pos S.cut.seamRegular

/-- Two real parameters just outside an inward seam interval, where the outer defect is strictly
positive, together with the complete side intervals on which the selected open band chart is
available. -/
structure CentralConnectorRealProbeData
    (f : ℝ → ℝ) (leftAdmissible rightAdmissible : ℝ → Prop)
    (source leftBoundary rightBoundary target : ℝ) where
  left : ℝ
  right : ℝ
  leftInner : ℝ
  rightInner : ℝ
  left_mem : left ∈ Ioo source leftBoundary
  right_mem : right ∈ Ioo rightBoundary target
  leftInner_mem : leftInner ∈ Ioo leftBoundary rightBoundary
  rightInner_mem : rightInner ∈ Ioo leftBoundary rightBoundary
  leftInner_lt_rightInner : leftInner < rightInner
  left_positive : 0 < f left
  right_positive : 0 < f right
  leftInner_negative : f leftInner < 0
  rightInner_negative : f rightInner < 0
  left_admissible : ∀ s ∈ Icc left leftBoundary, leftAdmissible s
  right_admissible : ∀ s ∈ Icc rightBoundary right, rightAdmissible s
  leftInner_admissible : ∀ s ∈ Icc leftBoundary leftInner, leftAdmissible s
  rightInner_admissible : ∀ s ∈ Icc rightInner rightBoundary, rightAdmissible s

/-- The simple seam zeros and the inward sign determine positive probes on both outward arms. -/
theorem exists_centralConnectorRealProbeData (b : D.ConnectorBandIndex) :
    Nonempty (CentralConnectorRealProbeData
      (D.centralGraph.cutCircleOuterPolynomialDifference
        (D.centralCutOrder.globalGapOfBand b).1.1)
      (fun s ↦ s ∈ D.centralConnectorLeftAdmissibleParameters b)
      (fun s ↦ s ∈ D.centralConnectorRightAdmissibleParameters b)
      (D.centralCutOrder.globalBandExtensionSourceParameter b)
      (D.centralCutOrder.globalBandLeftParameter b)
      (D.centralCutOrder.globalBandRightParameter b)
      (D.centralCutOrder.globalBandExtensionTargetParameter b)) := by
  have hsource : D.centralCutOrder.globalBandExtensionSourceParameter b <
      D.centralCutOrder.globalBandLeftParameter b := by
    unfold globalBandExtensionSourceParameter
    linarith [D.centralCutOrder.globalBandExtensionMargin_pos b]
  have htarget : D.centralCutOrder.globalBandRightParameter b <
      D.centralCutOrder.globalBandExtensionTargetParameter b := by
    unfold globalBandExtensionTargetParameter
    linarith [D.centralCutOrder.globalBandExtensionMargin_pos b]
  obtain ⟨ηLeft, hηLeft, hleftBall⟩ := Metric.isOpen_iff.mp
    (D.isOpen_centralConnectorLeftAdmissibleParameters b)
    (D.centralCutOrder.globalBandLeftParameter b)
    (D.globalBandLeftParameter_mem_admissibleParameters b)
  obtain ⟨ηRight, hηRight, hrightBall⟩ := Metric.isOpen_iff.mp
    (D.isOpen_centralConnectorRightAdmissibleParameters b)
    (D.centralCutOrder.globalBandRightParameter b)
    (D.globalBandRightParameter_mem_admissibleParameters b)
  let leftSource := max (D.centralCutOrder.globalBandExtensionSourceParameter b)
    (D.centralCutOrder.globalBandLeftParameter b - ηLeft / 2)
  let rightTarget := min (D.centralCutOrder.globalBandExtensionTargetParameter b)
    (D.centralCutOrder.globalBandRightParameter b + ηRight / 2)
  let leftInnerOffset := min (ηLeft / 2)
    ((D.centralCutOrder.globalBandRightParameter b -
      D.centralCutOrder.globalBandLeftParameter b) / 4)
  let rightInnerOffset := min (ηRight / 2)
    ((D.centralCutOrder.globalBandRightParameter b -
      D.centralCutOrder.globalBandLeftParameter b) / 4)
  let leftInner := D.centralCutOrder.globalBandLeftParameter b + leftInnerOffset
  let rightInner := D.centralCutOrder.globalBandRightParameter b - rightInnerOffset
  have hleftSource : leftSource < D.centralCutOrder.globalBandLeftParameter b := by
    apply max_lt
    · exact hsource
    · linarith
  have hrightTarget : D.centralCutOrder.globalBandRightParameter b < rightTarget := by
    apply lt_min
    · exact htarget
    · linarith
  have hleftInnerOffset : 0 < leftInnerOffset := by
    apply lt_min
    · exact half_pos hηLeft
    · exact div_pos (sub_pos.mpr
        (D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b)) (by norm_num)
  have hrightInnerOffset : 0 < rightInnerOffset := by
    apply lt_min
    · exact half_pos hηRight
    · exact div_pos (sub_pos.mpr
        (D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b)) (by norm_num)
  have hleftInner : leftInner ∈ Ioo
      (D.centralCutOrder.globalBandLeftParameter b)
      (D.centralCutOrder.globalBandRightParameter b) := by
    dsimp [leftInner]
    constructor
    · linarith
    · have hoffset := min_le_right (ηLeft / 2)
        ((D.centralCutOrder.globalBandRightParameter b -
          D.centralCutOrder.globalBandLeftParameter b) / 4)
      nlinarith [D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b]
  have hrightInner : rightInner ∈ Ioo
      (D.centralCutOrder.globalBandLeftParameter b)
      (D.centralCutOrder.globalBandRightParameter b) := by
    dsimp [rightInner]
    constructor
    · have hoffset := min_le_right (ηRight / 2)
        ((D.centralCutOrder.globalBandRightParameter b -
          D.centralCutOrder.globalBandLeftParameter b) / 4)
      nlinarith [D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b]
    · linarith
  have hinnerOrder : leftInner < rightInner := by
    have hleftOffset := min_le_right (ηLeft / 2)
      ((D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b) / 4)
    have hrightOffset := min_le_right (ηRight / 2)
      ((D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b) / 4)
    dsimp [leftInner, rightInner, leftInnerOffset, rightInnerOffset]
    nlinarith [D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b]
  obtain ⟨left, hleft, hleftPositive⟩ :=
    exists_positive_left_probe_of_negative_right hleftSource
      (D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b)
      (fun _ ht ↦ D.centralBandOuterDefect_neg b ht)
      (D.centralBandLeftLocalSignFlip b)
  obtain ⟨right, hright, hrightPositive⟩ :=
    exists_positive_right_probe_of_negative_left
      (D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b) hrightTarget
      (fun _ ht ↦ D.centralBandOuterDefect_neg b ht)
      (D.centralBandRightLocalSignFlip b)
  have hleftOriginal : left ∈ Ioo
      (D.centralCutOrder.globalBandExtensionSourceParameter b)
      (D.centralCutOrder.globalBandLeftParameter b) :=
    ⟨(le_max_left _ _).trans_lt hleft.1, hleft.2⟩
  have hrightOriginal : right ∈ Ioo
      (D.centralCutOrder.globalBandRightParameter b)
      (D.centralCutOrder.globalBandExtensionTargetParameter b) :=
    ⟨hright.1, hright.2.trans_le (min_le_left _ _)⟩
  refine ⟨⟨left, right, leftInner, rightInner, hleftOriginal, hrightOriginal,
    hleftInner, hrightInner, hinnerOrder, hleftPositive, hrightPositive,
    D.centralBandOuterDefect_neg b hleftInner,
    D.centralBandOuterDefect_neg b hrightInner, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    apply hleftBall
    change dist s (D.centralCutOrder.globalBandLeftParameter b) < ηLeft
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    have hnear : D.centralCutOrder.globalBandLeftParameter b - ηLeft / 2 < left :=
      (le_max_right _ _).trans_lt hleft.1
    nlinarith [hs.1, hnear, hηLeft]
  · intro s hs
    apply hrightBall
    change dist s (D.centralCutOrder.globalBandRightParameter b) < ηRight
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have hnear : right <
        D.centralCutOrder.globalBandRightParameter b + ηRight / 2 :=
      hright.2.trans_le (min_le_right _ _)
    nlinarith [hs.2, hnear, hηRight]
  · intro s hs
    apply hleftBall
    change dist s (D.centralCutOrder.globalBandLeftParameter b) < ηLeft
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have hoffset := min_le_left (ηLeft / 2)
      ((D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b) / 4)
    dsimp [leftInner, leftInnerOffset] at hs hoffset
    change leftInnerOffset ≤ ηLeft / 2 at hoffset
    have hdist : s - D.centralCutOrder.globalBandLeftParameter b ≤ ηLeft / 2 := by
      rw [sub_le_iff_le_add]
      calc
        s ≤ D.centralCutOrder.globalBandLeftParameter b + leftInnerOffset := hs.2
        _ = leftInnerOffset + D.centralCutOrder.globalBandLeftParameter b := add_comm _ _
        _ ≤ ηLeft / 2 + D.centralCutOrder.globalBandLeftParameter b :=
          add_le_add_left hoffset _
    have hhalf : ηLeft / 2 < ηLeft := by linarith
    exact hdist.trans_lt hhalf
  · intro s hs
    apply hrightBall
    change dist s (D.centralCutOrder.globalBandRightParameter b) < ηRight
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    have hoffset := min_le_left (ηRight / 2)
      ((D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b) / 4)
    dsimp [rightInner, rightInnerOffset] at hs hoffset
    have hdist : D.centralCutOrder.globalBandRightParameter b - s ≤ ηRight / 2 := by
      rw [sub_le_iff_le_add]
      calc
        D.centralCutOrder.globalBandRightParameter b =
            rightInnerOffset +
              (D.centralCutOrder.globalBandRightParameter b - rightInnerOffset) := by ring
        _ ≤ ηRight / 2 + s := add_le_add hoffset hs.1
    have hhalf : ηRight / 2 < ηRight := by linarith
    simpa only [neg_sub] using hdist.trans_lt hhalf

/-- Canonically selected real probes for one connector band. -/
noncomputable def centralConnectorRealProbeData (b : D.ConnectorBandIndex) :
    CentralConnectorRealProbeData
      (D.centralGraph.cutCircleOuterPolynomialDifference
        (D.centralCutOrder.globalGapOfBand b).1.1)
      (fun s ↦ s ∈ D.centralConnectorLeftAdmissibleParameters b)
      (fun s ↦ s ∈ D.centralConnectorRightAdmissibleParameters b)
      (D.centralCutOrder.globalBandExtensionSourceParameter b)
      (D.centralCutOrder.globalBandLeftParameter b)
      (D.centralCutOrder.globalBandRightParameter b)
      (D.centralCutOrder.globalBandExtensionTargetParameter b) :=
  Classical.choice (D.exists_centralConnectorRealProbeData b)

/-- Normalized collar parameter of the selected left probe. -/
noncomputable def centralConnectorLeftProbe (b : D.ConnectorBandIndex) : unitInterval :=
  let P := D.centralConnectorRealProbeData b
  ⟨(P.left - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b, by
    have hspan := D.centralCutOrder.globalBandExtensionSpan_pos b
    constructor
    · exact div_nonneg (sub_nonneg.mpr P.left_mem.1.le) hspan.le
    · rw [div_le_one hspan]
      unfold globalBandExtensionSpan
      have hleftTarget : P.left <
          D.centralCutOrder.globalBandExtensionTargetParameter b :=
        P.left_mem.2.trans (D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b)
          |>.trans (by
            unfold globalBandExtensionTargetParameter
            linarith [D.centralCutOrder.globalBandExtensionMargin_pos b])
      linarith⟩

/-- Normalized collar parameter of the selected right probe. -/
noncomputable def centralConnectorRightProbe (b : D.ConnectorBandIndex) : unitInterval :=
  let P := D.centralConnectorRealProbeData b
  ⟨(P.right - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b, by
    have hspan := D.centralCutOrder.globalBandExtensionSpan_pos b
    constructor
    · have hsourceRight : D.centralCutOrder.globalBandExtensionSourceParameter b <
          P.right := by
        unfold globalBandExtensionSourceParameter
        linarith [D.centralCutOrder.globalBandExtensionMargin_pos b,
          D.centralCutOrder.globalBandLeftParameter_lt_rightParameter b, P.right_mem.1]
      exact div_nonneg (sub_nonneg.mpr hsourceRight.le) hspan.le
    · rw [div_le_one hspan]
      unfold globalBandExtensionSpan
      exact sub_le_sub_right P.right_mem.2.le _⟩

/-- Normalized collar parameter of the selected inner point just right of the left seam. -/
noncomputable def centralConnectorLeftInnerProbe
    (b : D.ConnectorBandIndex) : unitInterval :=
  let P := D.centralConnectorRealProbeData b
  ⟨(P.leftInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b, by
    have hspan := D.centralCutOrder.globalBandExtensionSpan_pos b
    have hsource : D.centralCutOrder.globalBandExtensionSourceParameter b < P.leftInner :=
      (by
        unfold globalBandExtensionSourceParameter
        linarith [D.centralCutOrder.globalBandExtensionMargin_pos b,
          P.leftInner_mem.1])
    have htarget : P.leftInner <
        D.centralCutOrder.globalBandExtensionTargetParameter b :=
      P.leftInner_mem.2.trans (by
        unfold globalBandExtensionTargetParameter
        linarith [D.centralCutOrder.globalBandExtensionMargin_pos b])
    constructor
    · exact div_nonneg (sub_nonneg.mpr hsource.le) hspan.le
    · rw [div_le_one hspan]
      unfold globalBandExtensionSpan
      linarith⟩

/-- Normalized collar parameter of the selected inner point just left of the right seam. -/
noncomputable def centralConnectorRightInnerProbe
    (b : D.ConnectorBandIndex) : unitInterval :=
  let P := D.centralConnectorRealProbeData b
  ⟨(P.rightInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b, by
    have hspan := D.centralCutOrder.globalBandExtensionSpan_pos b
    have hsource : D.centralCutOrder.globalBandExtensionSourceParameter b < P.rightInner :=
      (by
        unfold globalBandExtensionSourceParameter
        linarith [D.centralCutOrder.globalBandExtensionMargin_pos b,
          P.rightInner_mem.1])
    have htarget : P.rightInner <
        D.centralCutOrder.globalBandExtensionTargetParameter b :=
      P.rightInner_mem.2.trans (by
        unfold globalBandExtensionTargetParameter
        linarith [D.centralCutOrder.globalBandExtensionMargin_pos b])
    constructor
    · exact div_nonneg (sub_nonneg.mpr hsource.le) hspan.le
    · rw [div_le_one hspan]
      unfold globalBandExtensionSpan
      linarith⟩

theorem globalBandExtensionParameter_centralConnectorLeftProbe
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandExtensionParameter b (D.centralConnectorLeftProbe b) =
      (D.centralConnectorRealProbeData b).left := by
  unfold globalBandExtensionParameter centralConnectorLeftProbe
  dsimp only
  field_simp [ne_of_gt (D.centralCutOrder.globalBandExtensionSpan_pos b)]
  ring

theorem globalBandExtensionParameter_centralConnectorRightProbe
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandExtensionParameter b (D.centralConnectorRightProbe b) =
      (D.centralConnectorRealProbeData b).right := by
  unfold globalBandExtensionParameter centralConnectorRightProbe
  dsimp only
  field_simp [ne_of_gt (D.centralCutOrder.globalBandExtensionSpan_pos b)]
  ring

theorem globalBandExtensionParameter_centralConnectorLeftInnerProbe
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandExtensionParameter b
        (D.centralConnectorLeftInnerProbe b) =
      (D.centralConnectorRealProbeData b).leftInner := by
  unfold globalBandExtensionParameter centralConnectorLeftInnerProbe
  dsimp only
  field_simp [ne_of_gt (D.centralCutOrder.globalBandExtensionSpan_pos b)]
  ring

theorem globalBandExtensionParameter_centralConnectorRightInnerProbe
    (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandExtensionParameter b
        (D.centralConnectorRightInnerProbe b) =
      (D.centralConnectorRealProbeData b).rightInner := by
  unfold globalBandExtensionParameter centralConnectorRightInnerProbe
  dsimp only
  field_simp [ne_of_gt (D.centralCutOrder.globalBandExtensionSpan_pos b)]
  ring

theorem centralConnectorLeftProbe_lt_coreLeft (b : D.ConnectorBandIndex) :
    D.centralConnectorLeftProbe b < D.centralCutOrder.globalBandCoreLeft b := by
  let P := D.centralConnectorRealProbeData b
  change (P.left - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b <
    D.centralCutOrder.globalBandExtensionMargin b /
      D.centralCutOrder.globalBandExtensionSpan b
  apply div_lt_div_of_pos_right _ (D.centralCutOrder.globalBandExtensionSpan_pos b)
  unfold globalBandExtensionSourceParameter
  exact sub_lt_iff_lt_add.mpr (by simpa using P.left_mem.2)

theorem centralConnectorCoreRight_lt_rightProbe (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandCoreRight b < D.centralConnectorRightProbe b := by
  let P := D.centralConnectorRealProbeData b
  change (D.centralCutOrder.globalBandExtensionMargin b +
      (D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b)) /
        D.centralCutOrder.globalBandExtensionSpan b <
    (P.right - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b
  apply div_lt_div_of_pos_right _ (D.centralCutOrder.globalBandExtensionSpan_pos b)
  unfold globalBandExtensionSourceParameter
  linarith [P.right_mem.1]

theorem centralConnectorCoreLeft_lt_leftInnerProbe (b : D.ConnectorBandIndex) :
    D.centralCutOrder.globalBandCoreLeft b < D.centralConnectorLeftInnerProbe b := by
  let P := D.centralConnectorRealProbeData b
  change D.centralCutOrder.globalBandExtensionMargin b /
      D.centralCutOrder.globalBandExtensionSpan b <
    (P.leftInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b
  apply div_lt_div_of_pos_right _ (D.centralCutOrder.globalBandExtensionSpan_pos b)
  unfold globalBandExtensionSourceParameter
  linarith [P.leftInner_mem.1]

theorem centralConnectorRightInnerProbe_lt_coreRight (b : D.ConnectorBandIndex) :
    D.centralConnectorRightInnerProbe b < D.centralCutOrder.globalBandCoreRight b := by
  let P := D.centralConnectorRealProbeData b
  change (P.rightInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b <
    (D.centralCutOrder.globalBandExtensionMargin b +
      (D.centralCutOrder.globalBandRightParameter b -
        D.centralCutOrder.globalBandLeftParameter b)) /
      D.centralCutOrder.globalBandExtensionSpan b
  apply div_lt_div_of_pos_right _ (D.centralCutOrder.globalBandExtensionSpan_pos b)
  unfold globalBandExtensionSourceParameter
  linarith [P.rightInner_mem.2]

theorem centralConnectorLeftInnerProbe_lt_rightInnerProbe (b : D.ConnectorBandIndex) :
    D.centralConnectorLeftInnerProbe b < D.centralConnectorRightInnerProbe b := by
  let P := D.centralConnectorRealProbeData b
  change (P.leftInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b <
    (P.rightInner - D.centralCutOrder.globalBandExtensionSourceParameter b) /
      D.centralCutOrder.globalBandExtensionSpan b
  apply div_lt_div_of_pos_right _ (D.centralCutOrder.globalBandExtensionSpan_pos b)
  exact sub_lt_sub_right P.leftInner_lt_rightInner _

private theorem centralHeightFlowSliceLift_mem_transportedTorus
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) (u : unitInterval) :
    transportedTorusPlaneMap Phi (D.centralHeightFlowSliceLift b t u) ∈
      transportedTorus Phi := by
  rw [← range_transportedTorusPlaneMap Phi]
  exact Set.mem_range_self _

/-- A height-flow slice regarded as a curve in the transported torus. -/
def centralHeightFlowSlicePoint (b : D.ConnectorBandIndex)
    (p : unitInterval × D.ConnectorFlowTimes) : transportedTorus Phi :=
  ⟨transportedTorusPlaneMap Phi (D.centralHeightFlowSliceLift b p.2 p.1),
    D.centralHeightFlowSliceLift_mem_transportedTorus b p.2 p.1⟩

theorem continuous_centralHeightFlowSlicePoint (b : D.ConnectorBandIndex) :
    Continuous (D.centralHeightFlowSlicePoint b) := by
  apply Continuous.subtype_mk
  exact (transportedTorusPlaneMap_contDiff Phi).continuous.comp
    ((D.centralCutOrder.continuous_globalBandPlaneFlowCollarMap b D.ConnectorBand
      D.centralHeightFlowData))

/-- At zero time, the complete extended slice is the original cutting circle. -/
theorem centralHeightFlowSlicePoint_zero (b : D.ConnectorBandIndex)
    (u : unitInterval) :
    D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) =
      (D.centralCutOrder.globalBandCircle b).windingLoop.curve
        (D.centralCutOrder.globalBandExtensionParameter b u) := by
  apply Subtype.ext
  change transportedTorusPlaneMap Phi
      (globalBandPlaneFlowCollarMap D.centralCutOrder b D.ConnectorBand
        D.centralHeightFlowData (u, globalBandFlowCollarZeroTime D.ConnectorBand)) = _
  rw [D.centralCutOrder.globalBandPlaneFlowCollarMap_zeroTime,
    D.centralCutOrder.transportedTorusPlaneMap_globalBandFlowBasePoint]

theorem centralHeightFlowSlicePoint_zero_injective (b : D.ConnectorBandIndex) :
    Function.Injective (fun u ↦ D.centralHeightFlowSlicePoint b
      (u, globalBandFlowCollarZeroTime D.ConnectorBand)) := by
  intro u v huv
  have hcurve :
      (D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandExtensionParameter b u) =
        (D.centralCutOrder.globalBandCircle b).windingLoop.curve
          (D.centralCutOrder.globalBandExtensionParameter b v) := by
    simpa only [D.centralHeightFlowSlicePoint_zero] using huv
  apply D.centralCutOrder.globalBandExtendedPlanePath_projection_injective b
  simpa only [D.centralCutOrder.globalBandExtendedPlanePath_projection] using hcurve

theorem centralHeightFlowSlicePoint_eq_transportedTimeHomeomorph
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) (u : unitInterval) :
    D.centralHeightFlowSlicePoint b (u, t) =
      D.centralHeightFlowData.transportedTimeHomeomorph (t : ℝ)
        (D.centralHeightFlowSlicePoint b
          (u, globalBandFlowCollarZeroTime D.ConnectorBand)) := by
  have hzero : D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) =
      transportedTorusHomeomorph Phi
        (planeExpPair (D.centralCutOrder.globalBandFlowBasePoint b u)) := by
    apply Subtype.ext
    rw [D.centralHeightFlowSlicePoint_zero]
    change ((D.centralCutOrder.globalBandCircle b).windingLoop.curve
        (D.centralCutOrder.globalBandExtensionParameter b u) : R3) =
      transportedTorusMap Phi
        (planeExpPair (D.centralCutOrder.globalBandFlowBasePoint b u))
    calc
      _ = transportedTorusPlaneMap Phi
          (D.centralCutOrder.globalBandFlowBasePoint b u) :=
        (D.centralCutOrder.transportedTorusPlaneMap_globalBandFlowBasePoint b u).symm
      _ = _ := transportedTorusPlaneMap_eq_expPair Phi _
  rw [D.centralHeightFlowData.transportedTimeHomeomorph_apply]
  unfold RegularBandNormalizedGradientFlowData.transportedFlow
  rw [hzero, (transportedTorusHomeomorph Phi).symm_apply_apply,
    D.centralHeightFlowData.quotientFlow_planeExpPair]
  apply Subtype.ext
  exact transportedTorusPlaneMap_eq_expPair Phi _

theorem centralHeightFlowSlicePoint_fixedTime_injective
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) :
    Function.Injective (fun u ↦ D.centralHeightFlowSlicePoint b (u, t)) := by
  intro u v huv
  apply D.centralHeightFlowSlicePoint_zero_injective b
  apply (D.centralHeightFlowData.transportedTimeHomeomorph (t : ℝ)).injective
  rw [← D.centralHeightFlowSlicePoint_eq_transportedTimeHomeomorph b t u,
    ← D.centralHeightFlowSlicePoint_eq_transportedTimeHomeomorph b t v]
  exact huv

private theorem globalBandExtensionParameter_mono (b : D.ConnectorBandIndex)
    {u v : unitInterval} (huv : u ≤ v) :
    D.centralCutOrder.globalBandExtensionParameter b u ≤
      D.centralCutOrder.globalBandExtensionParameter b v := by
  unfold globalBandExtensionParameter
  have huvReal : (u : ℝ) ≤ (v : ℝ) := huv
  simpa only [add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right huvReal
      (D.centralCutOrder.globalBandExtensionSpan_pos b).le)
    (D.centralCutOrder.globalBandExtensionSourceParameter b)

private theorem globalBandExtensionParameter_mem_leftAdmissible
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorLeftInnerProbe b)) :
    D.centralCutOrder.globalBandExtensionParameter b u ∈
      D.centralConnectorLeftAdmissibleParameters b := by
  by_cases hcore : u ≤ D.centralCutOrder.globalBandCoreLeft b
  · apply (D.centralConnectorRealProbeData b).left_admissible
    constructor
    · rw [← D.globalBandExtensionParameter_centralConnectorLeftProbe b]
      exact D.globalBandExtensionParameter_mono b hu.1
    · rw [← D.centralCutOrder.globalBandExtensionParameter_coreLeft b]
      exact D.globalBandExtensionParameter_mono b hcore
  · apply (D.centralConnectorRealProbeData b).leftInner_admissible
    constructor
    · rw [← D.centralCutOrder.globalBandExtensionParameter_coreLeft b]
      exact D.globalBandExtensionParameter_mono b (le_of_not_ge hcore)
    · rw [← D.globalBandExtensionParameter_centralConnectorLeftInnerProbe b]
      exact D.globalBandExtensionParameter_mono b hu.2

private theorem globalBandExtensionParameter_mem_rightAdmissible
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorRightInnerProbe b)
      (D.centralConnectorRightProbe b)) :
    D.centralCutOrder.globalBandExtensionParameter b u ∈
      D.centralConnectorRightAdmissibleParameters b := by
  by_cases hcore : D.centralCutOrder.globalBandCoreRight b ≤ u
  · apply (D.centralConnectorRealProbeData b).right_admissible
    constructor
    · rw [← D.centralCutOrder.globalBandExtensionParameter_coreRight b]
      exact D.globalBandExtensionParameter_mono b hcore
    · rw [← D.globalBandExtensionParameter_centralConnectorRightProbe b]
      exact D.globalBandExtensionParameter_mono b hu.2
  · apply (D.centralConnectorRealProbeData b).rightInner_admissible
    constructor
    · rw [← D.globalBandExtensionParameter_centralConnectorRightInnerProbe b]
      exact D.globalBandExtensionParameter_mono b hu.1
    · rw [← D.centralCutOrder.globalBandExtensionParameter_coreRight b]
      exact D.globalBandExtensionParameter_mono b (le_of_not_ge hcore)

private theorem centralConnectorLeftSide_zero_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralCutOrder.globalBandCoreLeft b)) :
    D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  rw [D.centralHeightFlowSlicePoint_zero]
  exact (D.globalBandExtensionParameter_mem_leftAdmissible b u
    ⟨hu.1, hu.2.trans (D.centralConnectorCoreLeft_lt_leftInnerProbe b).le⟩).1

private theorem centralConnectorRightSide_zero_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralCutOrder.globalBandCoreRight b)
      (D.centralConnectorRightProbe b)) :
    D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  rw [D.centralHeightFlowSlicePoint_zero]
  exact (D.globalBandExtensionParameter_mem_rightAdmissible b u
    ⟨(D.centralConnectorRightInnerProbe_lt_coreRight b).le.trans hu.1, hu.2⟩).1

private theorem centralHeightFlowSliceLift_zero_eq_planePoint
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowSliceLift b (globalBandFlowCollarZeroTime D.ConnectorBand) u =
      D.centralConnectorPlanePoint b
        (D.centralCutOrder.globalBandExtensionParameter b u) := by
  unfold centralHeightFlowSliceLift centralConnectorPlanePoint
  rw [D.centralCutOrder.globalBandPlaneFlowCollarMap_zeroTime]
  rfl

private theorem centralConnectorLeftSide_zero_mem_seamChart
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorLeftInnerProbe b)) :
    D.centralHeightFlowSliceLift b (globalBandFlowCollarZeroTime D.ConnectorBand) u ∈
      (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source := by
  rw [D.centralHeightFlowSliceLift_zero_eq_planePoint]
  exact (D.globalBandExtensionParameter_mem_leftAdmissible b u hu).2

private theorem centralConnectorRightSide_zero_mem_seamChart
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorRightInnerProbe b)
      (D.centralConnectorRightProbe b)) :
    D.centralHeightFlowSliceLift b (globalBandFlowCollarZeroTime D.ConnectorBand) u ∈
      (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source := by
  rw [D.centralHeightFlowSliceLift_zero_eq_planePoint]
  exact (D.globalBandExtensionParameter_mem_rightAdmissible b u hu).2

private def centralConnectorLeftSeamChartFlowParameters
    (b : D.ConnectorBandIndex) : Set (unitInterval × D.ConnectorFlowTimes) :=
  (fun p ↦ D.centralHeightFlowSliceLift b p.2 p.1) ⁻¹'
    (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
      S.cut.seamRegular).source

private def centralConnectorRightSeamChartFlowParameters
    (b : D.ConnectorBandIndex) : Set (unitInterval × D.ConnectorFlowTimes) :=
  (fun p ↦ D.centralHeightFlowSliceLift b p.2 p.1) ⁻¹'
    (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
      S.cut.seamRegular).source

private theorem isOpen_centralConnectorLeftSeamChartFlowParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorLeftSeamChartFlowParameters b) :=
  (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
    S.cut.seamRegular).open_source.preimage
      (D.centralCutOrder.continuous_globalBandPlaneFlowCollarMap b D.ConnectorBand
        D.centralHeightFlowData)

private theorem isOpen_centralConnectorRightSeamChartFlowParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorRightSeamChartFlowParameters b) :=
  (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
    S.cut.seamRegular).open_source.preimage
      (D.centralCutOrder.continuous_globalBandPlaneFlowCollarMap b D.ConnectorBand
        D.centralHeightFlowData)

private theorem centralConnectorLeftSide_zero_subset_seamChart
    (b : D.ConnectorBandIndex) :
    Icc (D.centralConnectorLeftProbe b) (D.centralConnectorLeftInnerProbe b) ×ˢ
        {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆
      D.centralConnectorLeftSeamChartFlowParameters b := by
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have ht0 : t = globalBandFlowCollarZeroTime D.ConnectorBand :=
    Set.mem_singleton_iff.mp ht
  subst t
  exact D.centralConnectorLeftSide_zero_mem_seamChart b u hu

private theorem centralConnectorRightSide_zero_subset_seamChart
    (b : D.ConnectorBandIndex) :
    Icc (D.centralConnectorRightInnerProbe b) (D.centralConnectorRightProbe b) ×ˢ
        {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆
      D.centralConnectorRightSeamChartFlowParameters b := by
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have ht0 : t = globalBandFlowCollarZeroTime D.ConnectorBand :=
    Set.mem_singleton_iff.mp ht
  subst t
  exact D.centralConnectorRightSide_zero_mem_seamChart b u hu

private def centralConnectorSeamArmChartTimes
    (b : D.ConnectorBandIndex) : Set D.ConnectorFlowTimes :=
  (fun t ↦ D.centralLeftOuterArmLift b (D.openChartNarrowedTime t)) ⁻¹'
      (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source ∩
    (fun t ↦ D.centralRightOuterArmLift b (D.openChartNarrowedTime t)) ⁻¹'
      (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source

private theorem isOpen_centralConnectorSeamArmChartTimes
    (b : D.ConnectorBandIndex) : IsOpen (D.centralConnectorSeamArmChartTimes b) :=
  ((D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
    S.cut.seamRegular).open_source.preimage
      ((D.continuous_centralLeftOuterArmLift b).comp
        D.continuous_openChartNarrowedTime)).inter
    ((D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
      S.cut.seamRegular).open_source.preimage
        ((D.continuous_centralRightOuterArmLift b).comp
          D.continuous_openChartNarrowedTime))

private theorem zero_mem_centralConnectorSeamArmChartTimes
    (b : D.ConnectorBandIndex) :
    globalBandFlowCollarZeroTime D.ConnectorBand ∈
      D.centralConnectorSeamArmChartTimes b := by
  have htime : D.openChartNarrowedTime
      (globalBandFlowCollarZeroTime D.ConnectorBand) =
        globalBandFlowCollarZeroTime D.heightData.band := rfl
  constructor
  · change D.centralLeftOuterArmLift b (D.openChartNarrowedTime
        (globalBandFlowCollarZeroTime D.ConnectorBand)) ∈
      (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source
    rw [htime]
    unfold centralLeftOuterArmLift globalBandFlowCollarZeroTime
    rw [D.centralSeamFlowData.2.flow_zero]
    exact D.centralCutOrder.globalBandLeftFlowSeamLift_mem_standardChartSource b
      D.scale_pos S.cut.seamRegular
  · change D.centralRightOuterArmLift b (D.openChartNarrowedTime
        (globalBandFlowCollarZeroTime D.ConnectorBand)) ∈
      (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
        S.cut.seamRegular).source
    rw [htime]
    unfold centralRightOuterArmLift globalBandFlowCollarZeroTime
    rw [D.centralSeamFlowData.2.flow_zero]
    exact D.centralCutOrder.globalBandRightFlowSeamLift_mem_standardChartSource b
      D.scale_pos S.cut.seamRegular

private theorem exists_uniformConnectorTimeRadius
    (a b : unitInterval) (O : Set (unitInterval × D.ConnectorFlowTimes))
    (hO : IsOpen O)
    (hzero : Icc a b ×ˢ {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆ O) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ Icc a b, (u, t) ∈ O := by
  obtain ⟨U, V, hUopen, hVopen, htrimU, hzeroV, hUV⟩ := generalized_tube_lemma
    (s := Icc a b)
    (t := {globalBandFlowCollarZeroTime D.ConnectorBand})
    (n := O)
    (isCompact_Icc : IsCompact (Icc a b))
    (isCompact_singleton : IsCompact
      ({globalBandFlowCollarZeroTime D.ConnectorBand} : Set D.ConnectorFlowTimes))
    hO hzero
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hVopen
    (globalBandFlowCollarZeroTime D.ConnectorBand)
    (hzeroV (Set.mem_singleton _))
  refine ⟨η, hη, fun t ht u hu ↦ hUV ⟨htrimU hu, hball ?_⟩⟩
  change dist (t : ℝ) 0 < η
  simpa only [Real.dist_eq, sub_zero] using ht

private theorem exists_centralConnectorLeftSeamSliceTimeRadius
    (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ Icc (D.centralConnectorLeftProbe b) (D.centralConnectorLeftInnerProbe b),
        D.centralHeightFlowSliceLift b t u ∈
          (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source := by
  exact D.exists_uniformConnectorTimeRadius
    (D.centralConnectorLeftProbe b) (D.centralConnectorLeftInnerProbe b)
    (D.centralConnectorLeftSeamChartFlowParameters b)
    (D.isOpen_centralConnectorLeftSeamChartFlowParameters b)
    (D.centralConnectorLeftSide_zero_subset_seamChart b)

private theorem exists_centralConnectorRightSeamSliceTimeRadius
    (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ Icc (D.centralConnectorRightInnerProbe b) (D.centralConnectorRightProbe b),
        D.centralHeightFlowSliceLift b t u ∈
          (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source := by
  exact D.exists_uniformConnectorTimeRadius
    (D.centralConnectorRightInnerProbe b) (D.centralConnectorRightProbe b)
    (D.centralConnectorRightSeamChartFlowParameters b)
    (D.isOpen_centralConnectorRightSeamChartFlowParameters b)
    (D.centralConnectorRightSide_zero_subset_seamChart b)

private theorem exists_centralConnectorSeamArmChartTimeRadius
    (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      D.centralLeftOuterArmLift b (D.openChartNarrowedTime t) ∈
          (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source ∧
        D.centralRightOuterArmLift b (D.openChartNarrowedTime t) ∈
          (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp
    (D.isOpen_centralConnectorSeamArmChartTimes b)
    (globalBandFlowCollarZeroTime D.ConnectorBand)
    (D.zero_mem_centralConnectorSeamArmChartTimes b)
  refine ⟨η, hη, fun t ht ↦ hball ?_⟩
  change dist (t : ℝ) 0 < η
  simpa only [Real.dist_eq, sub_zero] using ht

/-- For one band, one time neighborhood retains both side slices and both moving seam arms in
their corresponding inverse-function charts. -/
theorem exists_centralConnectorSeamComparisonTimeRadius (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      (∀ u ∈ Icc (D.centralConnectorLeftProbe b)
          (D.centralConnectorLeftInnerProbe b),
        D.centralHeightFlowSliceLift b t u ∈
          (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source) ∧
      (∀ u ∈ Icc (D.centralConnectorRightInnerProbe b)
          (D.centralConnectorRightProbe b),
        D.centralHeightFlowSliceLift b t u ∈
          (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source) ∧
      D.centralLeftOuterArmLift b (D.openChartNarrowedTime t) ∈
          (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source ∧
        D.centralRightOuterArmLift b (D.openChartNarrowedTime t) ∈
          (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
            S.cut.seamRegular).source := by
  obtain ⟨ηL, hηL, hleft⟩ := D.exists_centralConnectorLeftSeamSliceTimeRadius b
  obtain ⟨ηR, hηR, hright⟩ := D.exists_centralConnectorRightSeamSliceTimeRadius b
  obtain ⟨ηA, hηA, harms⟩ := D.exists_centralConnectorSeamArmChartTimeRadius b
  refine ⟨min (min ηL ηR) ηA, lt_min (lt_min hηL hηR) hηA, fun t ht ↦ ?_⟩
  have htL : |(t : ℝ)| < ηL := ht.trans_le <|
    (min_le_left (min ηL ηR) ηA).trans (min_le_left ηL ηR)
  have htR : |(t : ℝ)| < ηR := ht.trans_le <|
    (min_le_left (min ηL ηR) ηA).trans (min_le_right ηL ηR)
  have htA : |(t : ℝ)| < ηA := ht.trans_le (min_le_right (min ηL ηR) ηA)
  exact ⟨hleft t htL, hright t htR, (harms t htA).1, (harms t htA).2⟩

/-- A selected seam-comparison radius for one connector band. -/
noncomputable def centralConnectorSeamComparisonTimeRadius
    (b : D.ConnectorBandIndex) : ℝ :=
  Classical.choose (D.exists_centralConnectorSeamComparisonTimeRadius b)

theorem centralConnectorSeamComparisonTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorSeamComparisonTimeRadius b :=
  (Classical.choose_spec (D.exists_centralConnectorSeamComparisonTimeRadius b)).1

theorem centralConnectorSeamComparisonTimeRadius_spec (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.centralConnectorSeamComparisonTimeRadius b) :
    (∀ u ∈ Icc (D.centralConnectorLeftProbe b)
        (D.centralConnectorLeftInnerProbe b),
      D.centralHeightFlowSliceLift b t u ∈
        (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
          S.cut.seamRegular).source) ∧
    (∀ u ∈ Icc (D.centralConnectorRightInnerProbe b)
        (D.centralConnectorRightProbe b),
      D.centralHeightFlowSliceLift b t u ∈
        (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
          S.cut.seamRegular).source) ∧
    D.centralLeftOuterArmLift b (D.openChartNarrowedTime t) ∈
        (D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
          S.cut.seamRegular).source ∧
      D.centralRightOuterArmLift b (D.openChartNarrowedTime t) ∈
        (D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
          S.cut.seamRegular).source :=
  (Classical.choose_spec (D.exists_centralConnectorSeamComparisonTimeRadius b)).2 t ht

private theorem centralConnectorCore_zero_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralCutOrder.globalBandCoreLeft b)
      (D.centralCutOrder.globalBandCoreRight b)) :
    D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  have huRange : u ∈ Set.range (Icc.convexComb
      (D.centralCutOrder.globalBandCoreLeft b)
      (D.centralCutOrder.globalBandCoreRight b)) := by
    rw [Path.range_subpathAux,
      uIcc_of_le (D.centralCutOrder.globalBandCoreLeft_lt_coreRight b).le]
    exact hu
  obtain ⟨v, rfl⟩ := huRange
  let T := D.centralCutOrder.globalBandOpenTubularChartFamily.band b
  have hEq : D.centralHeightFlowSlicePoint b
        (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
          (D.centralCutOrder.globalBandCoreRight b) v,
            globalBandFlowCollarZeroTime D.ConnectorBand) =
      ((T.strip (bandSeamPath v) : T.surfacePatch) : transportedTorus Phi) := by
    apply Subtype.ext
    calc
      (D.centralHeightFlowSlicePoint b
          (Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
            (D.centralCutOrder.globalBandCoreRight b) v,
              globalBandFlowCollarZeroTime D.ConnectorBand) : R3) =
          ((D.centralCutOrder.globalBandPath b v : transportedTorus Phi) : R3) :=
        D.transportedTorusPlaneMap_centralHeightFlowCoreSliceLift_zero b v
      _ = (((T.strip (bandSeamPath v) : T.surfacePatch) :
          transportedTorus Phi) : R3) := (T.core_alignment v).symm
  rw [hEq]
  exact (T.strip (bandSeamPath v)).property

/-- The complete zero-time interval between the two probes lies in the chosen open band chart. -/
theorem centralConnectorProbeInterval_zero_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorRightProbe b)) :
    D.centralHeightFlowSlicePoint b
        (u, globalBandFlowCollarZeroTime D.ConnectorBand) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  by_cases hleft : u ≤ D.centralCutOrder.globalBandCoreLeft b
  · exact D.centralConnectorLeftSide_zero_mem_surfacePatch b u ⟨hu.1, hleft⟩
  · by_cases hright : u ≤ D.centralCutOrder.globalBandCoreRight b
    · exact D.centralConnectorCore_zero_mem_surfacePatch b u
        ⟨le_of_not_ge hleft, hright⟩
    · exact D.centralConnectorRightSide_zero_mem_surfacePatch b u
        ⟨le_of_not_ge hright, hu.2⟩

private def centralConnectorSurfacePatchFlowParameters
    (b : D.ConnectorBandIndex) : Set (unitInterval × D.ConnectorFlowTimes) :=
  D.centralHeightFlowSlicePoint b ⁻¹'
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch

private theorem isOpen_centralConnectorSurfacePatchFlowParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorSurfacePatchFlowParameters b) :=
  (D.centralCutOrder.globalBandOpenTubularChartFamily_surfacePatch_open b).preimage
    (D.continuous_centralHeightFlowSlicePoint b)

private theorem centralConnectorProbeInterval_zero_subset_surfacePatch
    (b : D.ConnectorBandIndex) :
    Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b) ×ˢ
        {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆
      D.centralConnectorSurfacePatchFlowParameters b := by
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have ht0 : t = globalBandFlowCollarZeroTime D.ConnectorBand :=
    Set.mem_singleton_iff.mp ht
  subst t
  exact D.centralConnectorProbeInterval_zero_mem_surfacePatch b u hu

/-- For one band, a time neighborhood keeps the complete probe-to-probe slice in the chosen
open tubular chart. -/
theorem exists_centralConnectorSurfacePatchTimeRadius (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b),
        D.centralHeightFlowSlicePoint b (u, t) ∈
          (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  obtain ⟨U, V, hUopen, hVopen, htrimU, hzeroV, hUV⟩ := generalized_tube_lemma
    (isCompact_Icc : IsCompact
      (Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b)))
    (isCompact_singleton : IsCompact
      ({globalBandFlowCollarZeroTime D.ConnectorBand} : Set D.ConnectorFlowTimes))
    (D.isOpen_centralConnectorSurfacePatchFlowParameters b)
    (D.centralConnectorProbeInterval_zero_subset_surfacePatch b)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hVopen
    (globalBandFlowCollarZeroTime D.ConnectorBand)
    (hzeroV (Set.mem_singleton _))
  refine ⟨η, hη, fun t ht u hu ↦ hUV ⟨htrimU hu, hball ?_⟩⟩
  change dist (t : ℝ) 0 < η
  simpa only [Real.dist_eq, sub_zero] using ht

/-- A selected chart-retention radius for one connector band. -/
noncomputable def centralConnectorSurfacePatchTimeRadius
    (b : D.ConnectorBandIndex) : ℝ :=
  Classical.choose (D.exists_centralConnectorSurfacePatchTimeRadius b)

theorem centralConnectorSurfacePatchTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorSurfacePatchTimeRadius b :=
  (Classical.choose_spec (D.exists_centralConnectorSurfacePatchTimeRadius b)).1

theorem centralConnectorSurfacePatchTimeRadius_spec (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.centralConnectorSurfacePatchTimeRadius b)
    (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorRightProbe b)) :
    D.centralHeightFlowSlicePoint b (u, t) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch :=
  (Classical.choose_spec (D.exists_centralConnectorSurfacePatchTimeRadius b)).2 t ht u hu

/-- At zero flow time the defect is exactly the original cutting-circle outer polynomial. -/
theorem centralHeightFlowOuterDefect_zeroTime_eq (b : D.ConnectorBandIndex)
    (u : unitInterval) :
    D.centralHeightFlowOuterDefect b (globalBandFlowCollarZeroTime D.ConnectorBand) u =
      D.centralGraph.cutCircleOuterPolynomialDifference
        (D.centralCutOrder.globalGapOfBand b).1.1
          (D.centralCutOrder.globalBandExtensionParameter b u) := by
  unfold centralHeightFlowOuterDefect globalBandFlowOuterDefect
  rw [D.centralCutOrder.globalBandPlaneFlowCollarMap_zeroTime]
  unfold superellipsoidPolynomialLift cutCircleOuterPolynomialDifference
  rw [D.centralCutOrder.transportedTorusPlaneMap_globalBandFlowBasePoint]
  rfl

private def centralConnectorFullNegativeFlowParameters
    (b : D.ConnectorBandIndex) : Set (unitInterval × D.ConnectorFlowTimes) :=
  {p | D.centralHeightFlowOuterDefect b p.2 p.1 < 0}

private theorem isOpen_centralConnectorFullNegativeFlowParameters
    (b : D.ConnectorBandIndex) :
    IsOpen (D.centralConnectorFullNegativeFlowParameters b) :=
  isOpen_lt
    (D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
      D.centralHeightFlowData)
    continuous_const

private theorem centralConnectorFullInterval_zero_subset_negative
    (b : D.ConnectorBandIndex) :
    Icc (D.centralConnectorLeftInnerProbe b) (D.centralConnectorRightInnerProbe b) ×ˢ
        {globalBandFlowCollarZeroTime D.ConnectorBand} ⊆
      D.centralConnectorFullNegativeFlowParameters b := by
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have ht0 : t = globalBandFlowCollarZeroTime D.ConnectorBand :=
    Set.mem_singleton_iff.mp ht
  subst t
  change D.centralHeightFlowOuterDefect b
    (globalBandFlowCollarZeroTime D.ConnectorBand) u < 0
  rw [D.centralHeightFlowOuterDefect_zeroTime_eq]
  apply D.centralBandOuterDefect_neg b
  constructor
  · exact (D.centralConnectorRealProbeData b).leftInner_mem.1.trans_le <| by
      rw [← D.globalBandExtensionParameter_centralConnectorLeftInnerProbe b]
      exact D.globalBandExtensionParameter_mono b hu.1
  · have hright : D.centralCutOrder.globalBandExtensionParameter b u ≤
        (D.centralConnectorRealProbeData b).rightInner := by
      rw [← D.globalBandExtensionParameter_centralConnectorRightInnerProbe b]
      exact D.globalBandExtensionParameter_mono b hu.2
    exact hright.trans_lt (D.centralConnectorRealProbeData b).rightInner_mem.2

/-- For one band, a time radius preserves strict negativity on the complete interval between
the two inner seam probes. -/
theorem exists_centralConnectorFullNegativeTimeRadius (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ (t : D.ConnectorFlowTimes), |(t : ℝ)| < η →
      ∀ u ∈ Icc (D.centralConnectorLeftInnerProbe b)
        (D.centralConnectorRightInnerProbe b),
        D.centralHeightFlowOuterDefect b t u < 0 := by
  exact D.exists_uniformConnectorTimeRadius
    (D.centralConnectorLeftInnerProbe b) (D.centralConnectorRightInnerProbe b)
    (D.centralConnectorFullNegativeFlowParameters b)
    (D.isOpen_centralConnectorFullNegativeFlowParameters b)
    (D.centralConnectorFullInterval_zero_subset_negative b)

noncomputable def centralConnectorFullNegativeTimeRadius
    (b : D.ConnectorBandIndex) : ℝ :=
  Classical.choose (D.exists_centralConnectorFullNegativeTimeRadius b)

theorem centralConnectorFullNegativeTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorFullNegativeTimeRadius b :=
  (Classical.choose_spec (D.exists_centralConnectorFullNegativeTimeRadius b)).1

theorem centralConnectorFullNegativeTimeRadius_spec (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.centralConnectorFullNegativeTimeRadius b)
    (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftInnerProbe b)
      (D.centralConnectorRightInnerProbe b)) :
    D.centralHeightFlowOuterDefect b t u < 0 :=
  (Classical.choose_spec (D.exists_centralConnectorFullNegativeTimeRadius b)).2 t ht u hu

theorem centralHeightFlowOuterDefect_leftProbe_zero_pos (b : D.ConnectorBandIndex) :
    0 < D.centralHeightFlowOuterDefect b
      (globalBandFlowCollarZeroTime D.ConnectorBand) (D.centralConnectorLeftProbe b) := by
  rw [D.centralHeightFlowOuterDefect_zeroTime_eq,
    D.globalBandExtensionParameter_centralConnectorLeftProbe]
  exact (D.centralConnectorRealProbeData b).left_positive

theorem centralHeightFlowOuterDefect_rightProbe_zero_pos (b : D.ConnectorBandIndex) :
    0 < D.centralHeightFlowOuterDefect b
      (globalBandFlowCollarZeroTime D.ConnectorBand) (D.centralConnectorRightProbe b) := by
  rw [D.centralHeightFlowOuterDefect_zeroTime_eq,
    D.globalBandExtensionParameter_centralConnectorRightProbe]
  exact (D.centralConnectorRealProbeData b).right_positive

theorem continuous_centralHeightFlowOuterDefect_leftProbe (b : D.ConnectorBandIndex) :
    Continuous (fun t : D.ConnectorFlowTimes ↦
      D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b)) := by
  exact (D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
    D.centralHeightFlowData).comp (continuous_const.prodMk continuous_id)

theorem continuous_centralHeightFlowOuterDefect_rightProbe (b : D.ConnectorBandIndex) :
    Continuous (fun t : D.ConnectorFlowTimes ↦
      D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b)) := by
  exact (D.centralCutOrder.continuous_globalBandFlowOuterDefect b D.ConnectorBand
    D.centralHeightFlowData).comp (continuous_const.prodMk continuous_id)

/-- A time neighborhood preserves the positive outer sign at both selected probes. -/
theorem exists_centralConnectorPositiveProbeTimeRadius (b : D.ConnectorBandIndex) :
    ∃ η > 0, ∀ t : D.ConnectorFlowTimes, |(t : ℝ)| < η →
      0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b) := by
  let U : Set D.ConnectorFlowTimes :=
    {t | 0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b)} ∩
      {t | 0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b)}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const (D.continuous_centralHeightFlowOuterDefect_leftProbe b)).inter
      (isOpen_lt continuous_const (D.continuous_centralHeightFlowOuterDefect_rightProbe b))
  have hzero : globalBandFlowCollarZeroTime D.ConnectorBand ∈ U :=
    ⟨D.centralHeightFlowOuterDefect_leftProbe_zero_pos b,
      D.centralHeightFlowOuterDefect_rightProbe_zero_pos b⟩
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hUopen _ hzero
  refine ⟨η, hη, fun t ht ↦ hball ?_⟩
  change dist (t : ℝ) 0 < η
  simpa only [Real.dist_eq, sub_zero] using ht

/-- A selected positive-probe radius for one connector band. -/
noncomputable def centralConnectorPositiveProbeTimeRadius
    (b : D.ConnectorBandIndex) : ℝ :=
  Classical.choose (D.exists_centralConnectorPositiveProbeTimeRadius b)

theorem centralConnectorPositiveProbeTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorPositiveProbeTimeRadius b :=
  (Classical.choose_spec (D.exists_centralConnectorPositiveProbeTimeRadius b)).1

theorem centralConnectorPositiveProbeTimeRadius_spec (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.centralConnectorPositiveProbeTimeRadius b) :
    0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b) :=
  (Classical.choose_spec (D.exists_centralConnectorPositiveProbeTimeRadius b)).2 t ht

/-- The per-band time radius simultaneously preserves signs and membership in the strip chart. -/
noncomputable def centralConnectorBandTimeRadius (b : D.ConnectorBandIndex) : ℝ :=
  min (D.centralConnectorPositiveProbeTimeRadius b)
    (min (D.centralConnectorSurfacePatchTimeRadius b)
      (min (D.centralConnectorSeamComparisonTimeRadius b)
        (D.centralConnectorFullNegativeTimeRadius b)))

theorem centralConnectorBandTimeRadius_pos (b : D.ConnectorBandIndex) :
    0 < D.centralConnectorBandTimeRadius b :=
  lt_min (D.centralConnectorPositiveProbeTimeRadius_pos b)
    (lt_min (D.centralConnectorSurfacePatchTimeRadius_pos b)
      (lt_min (D.centralConnectorSeamComparisonTimeRadius_pos b)
        (D.centralConnectorFullNegativeTimeRadius_pos b)))

private def centralConnectorTimeRadiusCandidates : Finset ℝ :=
  insert D.uniformCentralConnectorNegativeTimeRadius
    (Finset.univ.image D.centralConnectorBandTimeRadius)

private theorem centralConnectorTimeRadiusCandidates_nonempty :
    D.centralConnectorTimeRadiusCandidates.Nonempty :=
  ⟨D.uniformCentralConnectorNegativeTimeRadius, Finset.mem_insert_self _ _⟩

/-- One positive flow-time radius preserves both the inner negative core and the two positive
probes for every band. -/
noncomputable def uniformCentralConnectorTimeRadius : ℝ :=
  D.centralConnectorTimeRadiusCandidates.inf'
    D.centralConnectorTimeRadiusCandidates_nonempty id

theorem uniformCentralConnectorTimeRadius_pos :
    0 < D.uniformCentralConnectorTimeRadius := by
  apply (Finset.lt_inf'_iff D.centralConnectorTimeRadiusCandidates_nonempty).2
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact D.uniformCentralConnectorNegativeTimeRadius_pos
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    exact D.centralConnectorBandTimeRadius_pos b

theorem uniformCentralConnectorTimeRadius_le_negative :
    D.uniformCentralConnectorTimeRadius ≤
      D.uniformCentralConnectorNegativeTimeRadius := by
  apply Finset.inf'_le id
  exact Finset.mem_insert_self _ _

private theorem uniformCentralConnectorTimeRadius_le_band (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorTimeRadius ≤ D.centralConnectorBandTimeRadius b := by
  apply Finset.inf'_le id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

theorem uniformCentralConnectorTimeRadius_le_positive (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorTimeRadius ≤
      D.centralConnectorPositiveProbeTimeRadius b := by
  apply le_trans (D.uniformCentralConnectorTimeRadius_le_band b)
  exact min_le_left _ _

theorem uniformCentralConnectorTimeRadius_le_surfacePatch (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorTimeRadius ≤
      D.centralConnectorSurfacePatchTimeRadius b := by
  apply le_trans (D.uniformCentralConnectorTimeRadius_le_band b)
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem uniformCentralConnectorTimeRadius_le_seamComparison (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorTimeRadius ≤
      D.centralConnectorSeamComparisonTimeRadius b := by
  apply le_trans (D.uniformCentralConnectorTimeRadius_le_band b)
  exact (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)

theorem uniformCentralConnectorTimeRadius_le_fullNegative (b : D.ConnectorBandIndex) :
    D.uniformCentralConnectorTimeRadius ≤
      D.centralConnectorFullNegativeTimeRadius b := by
  apply le_trans (D.uniformCentralConnectorTimeRadius_le_band b)
  exact (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_right _ _)

theorem uniformCentralConnectorTimeRadius_le_epsilon :
    D.uniformCentralConnectorTimeRadius ≤ D.ConnectorBand.ε :=
  D.uniformCentralConnectorTimeRadius_le_negative.trans
    D.uniformCentralConnectorNegativeTimeRadius_le_epsilon

/-- Canonical small negative height used by every lower connector. -/
noncomputable def centralLowerConnectorTime : D.ConnectorFlowTimes :=
  ⟨-D.uniformCentralConnectorTimeRadius / 2, by
    have hpos := D.uniformCentralConnectorTimeRadius_pos
    have hle := D.uniformCentralConnectorTimeRadius_le_epsilon
    constructor <;> linarith⟩

/-- Canonical small positive height used by every upper connector. -/
noncomputable def centralUpperConnectorTime : D.ConnectorFlowTimes :=
  ⟨D.uniformCentralConnectorTimeRadius / 2, by
    have hpos := D.uniformCentralConnectorTimeRadius_pos
    have hle := D.uniformCentralConnectorTimeRadius_le_epsilon
    constructor <;> linarith⟩

theorem centralLowerConnectorTime_neg : (D.centralLowerConnectorTime : ℝ) < 0 := by
  change -D.uniformCentralConnectorTimeRadius / 2 < 0
  linarith [D.uniformCentralConnectorTimeRadius_pos]

theorem centralUpperConnectorTime_pos : 0 < (D.centralUpperConnectorTime : ℝ) := by
  change 0 < D.uniformCentralConnectorTimeRadius / 2
  linarith [D.uniformCentralConnectorTimeRadius_pos]

private theorem abs_centralLowerConnectorTime_lt_radius :
    |(D.centralLowerConnectorTime : ℝ)| < D.uniformCentralConnectorTimeRadius := by
  rw [abs_of_neg D.centralLowerConnectorTime_neg]
  change -(-D.uniformCentralConnectorTimeRadius / 2) <
    D.uniformCentralConnectorTimeRadius
  linarith [D.uniformCentralConnectorTimeRadius_pos]

private theorem abs_centralUpperConnectorTime_lt_radius :
    |(D.centralUpperConnectorTime : ℝ)| < D.uniformCentralConnectorTimeRadius := by
  rw [abs_of_pos D.centralUpperConnectorTime_pos]
  change D.uniformCentralConnectorTimeRadius / 2 < D.uniformCentralConnectorTimeRadius
  linarith [D.uniformCentralConnectorTimeRadius_pos]

theorem centralLowerConnector_probe_positive (b : D.ConnectorBandIndex) :
    0 < D.centralHeightFlowOuterDefect b D.centralLowerConnectorTime
        (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b D.centralLowerConnectorTime
        (D.centralConnectorRightProbe b) := by
  apply D.centralConnectorPositiveProbeTimeRadius_spec b
  exact D.abs_centralLowerConnectorTime_lt_radius.trans_le
    (D.uniformCentralConnectorTimeRadius_le_positive b)

theorem centralUpperConnector_probe_positive (b : D.ConnectorBandIndex) :
    0 < D.centralHeightFlowOuterDefect b D.centralUpperConnectorTime
        (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b D.centralUpperConnectorTime
        (D.centralConnectorRightProbe b) := by
  apply D.centralConnectorPositiveProbeTimeRadius_spec b
  exact D.abs_centralUpperConnectorTime_lt_radius.trans_le
    (D.uniformCentralConnectorTimeRadius_le_positive b)

theorem centralConnectorLeftCrossing_eq_outerArm
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.uniformCentralConnectorTimeRadius)
    (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorLeftProbe b)
      (D.centralConnectorLeftInnerProbe b))
    (hzero : D.centralHeightFlowOuterDefect b t u = 0) :
    D.centralHeightFlowSliceLift b t u =
      D.centralLeftOuterArmLift b (D.openChartNarrowedTime t) := by
  have hcharts := D.centralConnectorSeamComparisonTimeRadius_spec b t
    (ht.trans_le (D.uniformCentralConnectorTimeRadius_le_seamComparison b))
  let E := D.centralCutOrder.globalBandLeftStandardSeamLocalHomeomorph b D.scale_pos
    S.cut.seamRegular
  apply E.injOn (hcharts.1 u hu) hcharts.2.2.1
  simp only [E, globalBandLeftStandardSeamLocalHomeomorph,
    leftStandardSeamLocalHomeomorph_apply]
  apply Prod.ext
  · change superellipsoidPolynomialLift Phi frame c
        (D.centralHeightFlowSliceLift b t u) - S.outer.scale ^ 256 = 0 at hzero
    rw [sub_eq_zero.mp hzero, D.centralLeftOuterArmLift_level b]
  · rw [D.orientedCoordinateLift_centralHeightFlowSliceLift b t u,
      D.centralLeftOuterArmLift_height b]
    rfl

theorem centralConnectorRightCrossing_eq_outerArm
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (ht : |(t : ℝ)| < D.uniformCentralConnectorTimeRadius)
    (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorRightInnerProbe b)
      (D.centralConnectorRightProbe b))
    (hzero : D.centralHeightFlowOuterDefect b t u = 0) :
    D.centralHeightFlowSliceLift b t u =
      D.centralRightOuterArmLift b (D.openChartNarrowedTime t) := by
  have hcharts := D.centralConnectorSeamComparisonTimeRadius_spec b t
    (ht.trans_le (D.uniformCentralConnectorTimeRadius_le_seamComparison b))
  let E := D.centralCutOrder.globalBandRightStandardSeamLocalHomeomorph b D.scale_pos
    S.cut.seamRegular
  apply E.injOn (hcharts.2.1 u hu) hcharts.2.2.2
  simp only [E, globalBandRightStandardSeamLocalHomeomorph,
    rightStandardSeamLocalHomeomorph_apply]
  apply Prod.ext
  · change superellipsoidPolynomialLift Phi frame c
        (D.centralHeightFlowSliceLift b t u) - S.outer.scale ^ 256 = 0 at hzero
    rw [sub_eq_zero.mp hzero, D.centralRightOuterArmLift_level b]
  · rw [D.orientedCoordinateLift_centralHeightFlowSliceLift b t u,
      D.centralRightOuterArmLift_height b]
    rfl

theorem centralConnector_core_negative (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) (ht : |(t : ℝ)| < D.uniformCentralConnectorTimeRadius)
    (u : unitInterval) (hu : u ∈ centralConnectorInteriorParameters) :
    D.centralHeightFlowCoreOuterDefect b (u, t) < 0 := by
  apply D.uniformCentralConnectorNegativeTimeRadius_spec b t
  · exact ht.trans_le D.uniformCentralConnectorTimeRadius_le_negative
  · exact hu

/-- Left endpoint of the compact negative core in the full extended-arc parameter. -/
noncomputable def centralConnectorInnerLeftParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
    (D.centralCutOrder.globalBandCoreRight b) connectorInnerLeft

/-- Right endpoint of the compact negative core in the full extended-arc parameter. -/
noncomputable def centralConnectorInnerRightParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
    (D.centralCutOrder.globalBandCoreRight b) connectorInnerRight

/-- Positive probe values and a negative inner interval give one crossing on each side. -/
theorem exists_centralConnectorCrossings (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (hprobe : 0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorLeftProbe b) ∧
      0 < D.centralHeightFlowOuterDefect b t (D.centralConnectorRightProbe b))
    (hnegative : ∀ u ∈ Icc (D.centralConnectorLeftInnerProbe b)
      (D.centralConnectorRightInnerProbe b),
      D.centralHeightFlowOuterDefect b t u < 0) :
    (∃ u ∈ Ioo (D.centralConnectorLeftProbe b)
        (D.centralConnectorLeftInnerProbe b),
      D.centralHeightFlowOuterDefect b t u = 0) ∧
    (∃ u ∈ Ioo (D.centralConnectorRightInnerProbe b)
        (D.centralConnectorRightProbe b),
      D.centralHeightFlowOuterDefect b t u = 0) := by
  let f : unitInterval → ℝ := D.centralHeightFlowOuterDefect b t
  have hf : Continuous f := D.continuous_centralHeightFlowOuterDefect b t
  have hleftProbe : f (D.centralConnectorLeftProbe b) > 0 := hprobe.1
  have hrightProbe : f (D.centralConnectorRightProbe b) > 0 := hprobe.2
  have hinnerLeft : f (D.centralConnectorLeftInnerProbe b) < 0 :=
    hnegative _ ⟨le_rfl, (D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).le⟩
  have hinnerRight : f (D.centralConnectorRightInnerProbe b) < 0 :=
    hnegative _ ⟨(D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).le, le_rfl⟩
  constructor
  · obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc'
      ((D.centralConnectorLeftProbe_lt_coreLeft b).trans
        (D.centralConnectorCoreLeft_lt_leftInnerProbe b)).le
      hf.continuousOn ⟨hinnerLeft.le, hleftProbe.le⟩
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩, ?_⟩
    · intro hueq
      subst u
      exact (ne_of_gt hleftProbe) hfu
    · intro hueq
      subst u
      exact (ne_of_lt hinnerLeft) hfu
    · exact hfu
  · obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc
      ((D.centralConnectorRightInnerProbe_lt_coreRight b).trans
        (D.centralConnectorCoreRight_lt_rightProbe b)).le
      hf.continuousOn ⟨hinnerRight.le, hrightProbe.le⟩
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩, ?_⟩
    · intro hueq
      subst u
      exact (ne_of_lt hinnerRight) hfu
    · intro hueq
      subst u
      exact (ne_of_gt hrightProbe) hfu
    · exact hfu

theorem exists_centralLowerConnectorCrossings (b : D.ConnectorBandIndex) :
    (∃ u ∈ Ioo (D.centralConnectorLeftProbe b)
        (D.centralConnectorLeftInnerProbe b),
      D.centralHeightFlowOuterDefect b D.centralLowerConnectorTime u = 0) ∧
    (∃ u ∈ Ioo (D.centralConnectorRightInnerProbe b)
        (D.centralConnectorRightProbe b),
      D.centralHeightFlowOuterDefect b D.centralLowerConnectorTime u = 0) := by
  apply D.exists_centralConnectorCrossings b D.centralLowerConnectorTime
    (D.centralLowerConnector_probe_positive b)
  intro u hu
  exact D.centralConnectorFullNegativeTimeRadius_spec b D.centralLowerConnectorTime
    (D.abs_centralLowerConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) u hu

theorem exists_centralUpperConnectorCrossings (b : D.ConnectorBandIndex) :
    (∃ u ∈ Ioo (D.centralConnectorLeftProbe b)
        (D.centralConnectorLeftInnerProbe b),
      D.centralHeightFlowOuterDefect b D.centralUpperConnectorTime u = 0) ∧
    (∃ u ∈ Ioo (D.centralConnectorRightInnerProbe b)
        (D.centralConnectorRightProbe b),
      D.centralHeightFlowOuterDefect b D.centralUpperConnectorTime u = 0) := by
  apply D.exists_centralConnectorCrossings b D.centralUpperConnectorTime
    (D.centralUpperConnector_probe_positive b)
  intro u hu
  exact D.centralConnectorFullNegativeTimeRadius_spec b D.centralUpperConnectorTime
    (D.abs_centralUpperConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) u hu

/-- Closed zero set on the left transition from the positive probe to the negative core. -/
def centralConnectorLeftZeroSet (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Set unitInterval :=
  Icc (D.centralConnectorLeftProbe b) (D.centralConnectorLeftInnerProbe b) ∩
    {u | D.centralHeightFlowOuterDefect b t u = 0}

/-- Closed zero set on the right transition from the negative core to the positive probe. -/
def centralConnectorRightZeroSet (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : Set unitInterval :=
  Icc (D.centralConnectorRightInnerProbe b) (D.centralConnectorRightProbe b) ∩
    {u | D.centralHeightFlowOuterDefect b t u = 0}

theorem isCompact_centralConnectorLeftZeroSet (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : IsCompact (D.centralConnectorLeftZeroSet b t) := by
  exact isCompact_Icc.inter_right
    (isClosed_eq (D.continuous_centralHeightFlowOuterDefect b t) continuous_const)

theorem isCompact_centralConnectorRightZeroSet (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes) : IsCompact (D.centralConnectorRightZeroSet b t) := by
  exact isCompact_Icc.inter_right
    (isClosed_eq (D.continuous_centralHeightFlowOuterDefect b t) continuous_const)

theorem centralLowerConnectorLeftZeroSet_nonempty (b : D.ConnectorBandIndex) :
    (D.centralConnectorLeftZeroSet b D.centralLowerConnectorTime).Nonempty := by
  obtain ⟨u, hu, hzero⟩ := (D.exists_centralLowerConnectorCrossings b).1
  exact ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩⟩

theorem centralLowerConnectorRightZeroSet_nonempty (b : D.ConnectorBandIndex) :
    (D.centralConnectorRightZeroSet b D.centralLowerConnectorTime).Nonempty := by
  obtain ⟨u, hu, hzero⟩ := (D.exists_centralLowerConnectorCrossings b).2
  exact ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩⟩

theorem centralUpperConnectorLeftZeroSet_nonempty (b : D.ConnectorBandIndex) :
    (D.centralConnectorLeftZeroSet b D.centralUpperConnectorTime).Nonempty := by
  obtain ⟨u, hu, hzero⟩ := (D.exists_centralUpperConnectorCrossings b).1
  exact ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩⟩

theorem centralUpperConnectorRightZeroSet_nonempty (b : D.ConnectorBandIndex) :
    (D.centralConnectorRightZeroSet b D.centralUpperConnectorTime).Nonempty := by
  obtain ⟨u, hu, hzero⟩ := (D.exists_centralUpperConnectorCrossings b).2
  exact ⟨u, ⟨⟨hu.1.le, hu.2.le⟩, hzero⟩⟩

/-- Greatest left zero, so no later left-transition point can meet the outer level. -/
noncomputable def greatestCentralConnectorLeftCrossingParameter
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (hne : (D.centralConnectorLeftZeroSet b t).Nonempty) : unitInterval :=
  Classical.choose ((D.isCompact_centralConnectorLeftZeroSet b t).exists_isGreatest hne)

theorem greatestCentralConnectorLeftCrossingParameter_spec
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (hne : (D.centralConnectorLeftZeroSet b t).Nonempty) :
    IsGreatest (D.centralConnectorLeftZeroSet b t)
      (D.greatestCentralConnectorLeftCrossingParameter b t hne) :=
  Classical.choose_spec ((D.isCompact_centralConnectorLeftZeroSet b t).exists_isGreatest hne)

/-- Least right zero, so no earlier right-transition point can meet the outer level. -/
noncomputable def leastCentralConnectorRightCrossingParameter
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (hne : (D.centralConnectorRightZeroSet b t).Nonempty) : unitInterval :=
  Classical.choose ((D.isCompact_centralConnectorRightZeroSet b t).exists_isLeast hne)

theorem leastCentralConnectorRightCrossingParameter_spec
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (hne : (D.centralConnectorRightZeroSet b t).Nonempty) :
    IsLeast (D.centralConnectorRightZeroSet b t)
      (D.leastCentralConnectorRightCrossingParameter b t hne) :=
  Classical.choose_spec ((D.isCompact_centralConnectorRightZeroSet b t).exists_isLeast hne)

private theorem centralConnector_actualCore_negative (b : D.ConnectorBandIndex)
    (t : D.ConnectorFlowTimes)
    (hcore : ∀ u ∈ centralConnectorInteriorParameters,
      D.centralHeightFlowCoreOuterDefect b (u, t) < 0)
    (u : unitInterval)
    (hu : u ∈ Icc (D.centralConnectorInnerLeftParameter b)
      (D.centralConnectorInnerRightParameter b)) :
    D.centralHeightFlowOuterDefect b t u < 0 := by
  have hinnerOrder : D.centralConnectorInnerLeftParameter b ≤
      D.centralConnectorInnerRightParameter b := by
    change (D.centralConnectorInnerLeftParameter b : ℝ) ≤
      (D.centralConnectorInnerRightParameter b : ℝ)
    unfold centralConnectorInnerLeftParameter centralConnectorInnerRightParameter
    simp only [Icc.coe_convexComb]
    have hlr := D.centralCutOrder.globalBandCoreLeft_lt_coreRight b
    have huv := connectorInnerLeft_le_right
    have hproduct : 0 ≤ ((connectorInnerRight : ℝ) - connectorInnerLeft) *
        ((D.centralCutOrder.globalBandCoreRight b : ℝ) -
          D.centralCutOrder.globalBandCoreLeft b) :=
      mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hlr.le)
    nlinarith
  have huRange : u ∈ Set.range (Icc.convexComb
      (D.centralConnectorInnerLeftParameter b)
      (D.centralConnectorInnerRightParameter b)) := by
    rw [Path.range_subpathAux, uIcc_of_le hinnerOrder]
    exact hu
  obtain ⟨v, rfl⟩ := huRange
  let q := Icc.convexComb connectorInnerLeft connectorInnerRight v
  have hq : q ∈ centralConnectorInteriorParameters := by
    change q ∈ Icc connectorInnerLeft connectorInnerRight
    rw [← uIcc_of_le connectorInnerLeft_le_right, ← Path.range_subpathAux]
    exact Set.mem_range_self v
  have hnested :
      Icc.convexComb (D.centralCutOrder.globalBandCoreLeft b)
          (D.centralCutOrder.globalBandCoreRight b) q =
        Icc.convexComb (D.centralConnectorInnerLeftParameter b)
          (D.centralConnectorInnerRightParameter b) v := by
    apply Subtype.ext
    simp only [q, Icc.coe_convexComb]
    unfold centralConnectorInnerLeftParameter centralConnectorInnerRightParameter
    simp only [Icc.coe_convexComb]
    ring
  rw [← hnested]
  exact hcore q hq

theorem centralConnector_betweenExtremalCrossings_neg
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes)
    (hleft : (D.centralConnectorLeftZeroSet b t).Nonempty)
    (hright : (D.centralConnectorRightZeroSet b t).Nonempty)
    (hnegative : ∀ u ∈ Icc (D.centralConnectorLeftInnerProbe b)
      (D.centralConnectorRightInnerProbe b),
      D.centralHeightFlowOuterDefect b t u < 0)
    (u : unitInterval)
    (hu : u ∈ Ioo (D.greatestCentralConnectorLeftCrossingParameter b t hleft)
      (D.leastCentralConnectorRightCrossingParameter b t hright)) :
    D.centralHeightFlowOuterDefect b t u < 0 := by
  let L := D.greatestCentralConnectorLeftCrossingParameter b t hleft
  let R := D.leastCentralConnectorRightCrossingParameter b t hright
  let f : unitInterval → ℝ := D.centralHeightFlowOuterDefect b t
  have hf : Continuous f := D.continuous_centralHeightFlowOuterDefect b t
  have hL := D.greatestCentralConnectorLeftCrossingParameter_spec b t hleft
  have hR := D.leastCentralConnectorRightCrossingParameter_spec b t hright
  have hinnerLeft : f (D.centralConnectorLeftInnerProbe b) < 0 :=
    hnegative _ ⟨le_rfl, (D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).le⟩
  have hinnerRight : f (D.centralConnectorRightInnerProbe b) < 0 :=
    hnegative _ ⟨(D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).le, le_rfl⟩
  by_cases hul : u < D.centralConnectorLeftInnerProbe b
  · by_contra hnot
    have hnonneg : 0 ≤ f u := le_of_not_gt hnot
    by_cases hzero : f u = 0
    · have huSet : u ∈ D.centralConnectorLeftZeroSet b t := by
        exact ⟨⟨hL.1.1.1.trans hu.1.le, hul.le⟩, hzero⟩
      exact (not_le_of_gt hu.1) (hL.2 huSet)
    · have hpos : 0 < f u := lt_of_le_of_ne hnonneg (Ne.symm hzero)
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hul.le hf.continuousOn
        ⟨hinnerLeft.le, hpos.le⟩
      have hzSet : z ∈ D.centralConnectorLeftZeroSet b t := by
        exact ⟨⟨hL.1.1.1.trans (hu.1.le.trans hz.1), hz.2⟩, hfz⟩
      exact (not_le_of_gt (hu.1.trans_le hz.1)) (hL.2 hzSet)
  · have hleftCore : D.centralConnectorLeftInnerProbe b ≤ u := le_of_not_gt hul
    by_cases hur : u ≤ D.centralConnectorRightInnerProbe b
    · exact hnegative u ⟨hleftCore, hur⟩
    · have hrightCore : D.centralConnectorRightInnerProbe b < u := lt_of_not_ge hur
      by_contra hnot
      have hnonneg : 0 ≤ f u := le_of_not_gt hnot
      by_cases hzero : f u = 0
      · have huSet : u ∈ D.centralConnectorRightZeroSet b t := by
          exact ⟨⟨hrightCore.le, hu.2.le.trans hR.1.1.2⟩, hzero⟩
        exact (not_le_of_gt hu.2) (hR.2 huSet)
      · have hpos : 0 < f u := lt_of_le_of_ne hnonneg (Ne.symm hzero)
        obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hrightCore.le hf.continuousOn
          ⟨hinnerRight.le, hpos.le⟩
        have hzSet : z ∈ D.centralConnectorRightZeroSet b t := by
          exact ⟨⟨hz.1, hz.2.trans (hu.2.le.trans hR.1.1.2)⟩, hfz⟩
        exact (not_le_of_gt (hz.2.trans_lt hu.2)) (hR.2 hzSet)

/-- Extremal outer-level parameters for the lower connector. -/
noncomputable def centralLowerLeftCrossingParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  D.greatestCentralConnectorLeftCrossingParameter b D.centralLowerConnectorTime
    (D.centralLowerConnectorLeftZeroSet_nonempty b)

noncomputable def centralLowerRightCrossingParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  D.leastCentralConnectorRightCrossingParameter b D.centralLowerConnectorTime
    (D.centralLowerConnectorRightZeroSet_nonempty b)

/-- Extremal outer-level parameters for the upper connector. -/
noncomputable def centralUpperLeftCrossingParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  D.greatestCentralConnectorLeftCrossingParameter b D.centralUpperConnectorTime
    (D.centralUpperConnectorLeftZeroSet_nonempty b)

noncomputable def centralUpperRightCrossingParameter (b : D.ConnectorBandIndex) :
    unitInterval :=
  D.leastCentralConnectorRightCrossingParameter b D.centralUpperConnectorTime
    (D.centralUpperConnectorRightZeroSet_nonempty b)

theorem centralLowerLeftCrossingParameter_mem (b : D.ConnectorBandIndex) :
    D.centralLowerLeftCrossingParameter b ∈
      D.centralConnectorLeftZeroSet b D.centralLowerConnectorTime :=
  (D.greatestCentralConnectorLeftCrossingParameter_spec b D.centralLowerConnectorTime
    (D.centralLowerConnectorLeftZeroSet_nonempty b)).1

theorem centralLowerRightCrossingParameter_mem (b : D.ConnectorBandIndex) :
    D.centralLowerRightCrossingParameter b ∈
      D.centralConnectorRightZeroSet b D.centralLowerConnectorTime :=
  (D.leastCentralConnectorRightCrossingParameter_spec b D.centralLowerConnectorTime
    (D.centralLowerConnectorRightZeroSet_nonempty b)).1

theorem centralUpperLeftCrossingParameter_mem (b : D.ConnectorBandIndex) :
    D.centralUpperLeftCrossingParameter b ∈
      D.centralConnectorLeftZeroSet b D.centralUpperConnectorTime :=
  (D.greatestCentralConnectorLeftCrossingParameter_spec b D.centralUpperConnectorTime
    (D.centralUpperConnectorLeftZeroSet_nonempty b)).1

theorem centralUpperRightCrossingParameter_mem (b : D.ConnectorBandIndex) :
    D.centralUpperRightCrossingParameter b ∈
      D.centralConnectorRightZeroSet b D.centralUpperConnectorTime :=
  (D.leastCentralConnectorRightCrossingParameter_spec b D.centralUpperConnectorTime
    (D.centralUpperConnectorRightZeroSet_nonempty b)).1

theorem centralLowerLeftCrossingLift_eq_outerArm (b : D.ConnectorBandIndex) :
    D.centralHeightFlowSliceLift b D.centralLowerConnectorTime
        (D.centralLowerLeftCrossingParameter b) =
      D.centralLeftOuterArmLift b
        (D.openChartNarrowedTime D.centralLowerConnectorTime) := by
  apply D.centralConnectorLeftCrossing_eq_outerArm b D.centralLowerConnectorTime
    D.abs_centralLowerConnectorTime_lt_radius
  · exact (D.centralLowerLeftCrossingParameter_mem b).1
  · exact (D.centralLowerLeftCrossingParameter_mem b).2

theorem centralLowerRightCrossingLift_eq_outerArm (b : D.ConnectorBandIndex) :
    D.centralHeightFlowSliceLift b D.centralLowerConnectorTime
        (D.centralLowerRightCrossingParameter b) =
      D.centralRightOuterArmLift b
        (D.openChartNarrowedTime D.centralLowerConnectorTime) := by
  apply D.centralConnectorRightCrossing_eq_outerArm b D.centralLowerConnectorTime
    D.abs_centralLowerConnectorTime_lt_radius
  · exact (D.centralLowerRightCrossingParameter_mem b).1
  · exact (D.centralLowerRightCrossingParameter_mem b).2

theorem centralUpperLeftCrossingLift_eq_outerArm (b : D.ConnectorBandIndex) :
    D.centralHeightFlowSliceLift b D.centralUpperConnectorTime
        (D.centralUpperLeftCrossingParameter b) =
      D.centralLeftOuterArmLift b
        (D.openChartNarrowedTime D.centralUpperConnectorTime) := by
  apply D.centralConnectorLeftCrossing_eq_outerArm b D.centralUpperConnectorTime
    D.abs_centralUpperConnectorTime_lt_radius
  · exact (D.centralUpperLeftCrossingParameter_mem b).1
  · exact (D.centralUpperLeftCrossingParameter_mem b).2

theorem centralUpperRightCrossingLift_eq_outerArm (b : D.ConnectorBandIndex) :
    D.centralHeightFlowSliceLift b D.centralUpperConnectorTime
        (D.centralUpperRightCrossingParameter b) =
      D.centralRightOuterArmLift b
        (D.openChartNarrowedTime D.centralUpperConnectorTime) := by
  apply D.centralConnectorRightCrossing_eq_outerArm b D.centralUpperConnectorTime
    D.abs_centralUpperConnectorTime_lt_radius
  · exact (D.centralUpperRightCrossingParameter_mem b).1
  · exact (D.centralUpperRightCrossingParameter_mem b).2

theorem centralLowerCrossingParameter_order (b : D.ConnectorBandIndex) :
    D.centralLowerLeftCrossingParameter b < D.centralLowerRightCrossingParameter b :=
  (D.centralLowerLeftCrossingParameter_mem b).1.2.trans_lt <|
    (D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).trans_le
      (D.centralLowerRightCrossingParameter_mem b).1.1

theorem centralUpperCrossingParameter_order (b : D.ConnectorBandIndex) :
    D.centralUpperLeftCrossingParameter b < D.centralUpperRightCrossingParameter b :=
  (D.centralUpperLeftCrossingParameter_mem b).1.2.trans_lt <|
    (D.centralConnectorLeftInnerProbe_lt_rightInnerProbe b).trans_le
      (D.centralUpperRightCrossingParameter_mem b).1.1

/-- Affine parameter along the trimmed lower height-flow connector. -/
def centralLowerConnectorParameter (b : D.ConnectorBandIndex)
    (u : unitInterval) : unitInterval :=
  Icc.convexComb (D.centralLowerLeftCrossingParameter b)
    (D.centralLowerRightCrossingParameter b) u

/-- Affine parameter along the trimmed upper height-flow connector. -/
def centralUpperConnectorParameter (b : D.ConnectorBandIndex)
    (u : unitInterval) : unitInterval :=
  Icc.convexComb (D.centralUpperLeftCrossingParameter b)
    (D.centralUpperRightCrossingParameter b) u

theorem continuous_centralLowerConnectorParameter (b : D.ConnectorBandIndex) :
    Continuous (D.centralLowerConnectorParameter b) :=
  Icc.continuous_convexComb _ _

theorem continuous_centralUpperConnectorParameter (b : D.ConnectorBandIndex) :
    Continuous (D.centralUpperConnectorParameter b) :=
  Icc.continuous_convexComb _ _

private theorem centralLowerConnectorParameter_mem_probeInterval
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralLowerConnectorParameter b u ∈
      Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b) := by
  have hp : D.centralLowerConnectorParameter b u ∈
      Icc (D.centralLowerLeftCrossingParameter b)
        (D.centralLowerRightCrossingParameter b) := by
    rw [← uIcc_of_le (D.centralLowerCrossingParameter_order b).le,
      ← Path.range_subpathAux]
    exact Set.mem_range_self u
  exact ⟨(D.centralLowerLeftCrossingParameter_mem b).1.1.trans hp.1,
    hp.2.trans (D.centralLowerRightCrossingParameter_mem b).1.2⟩

private theorem centralUpperConnectorParameter_mem_probeInterval
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralUpperConnectorParameter b u ∈
      Icc (D.centralConnectorLeftProbe b) (D.centralConnectorRightProbe b) := by
  have hp : D.centralUpperConnectorParameter b u ∈
      Icc (D.centralUpperLeftCrossingParameter b)
        (D.centralUpperRightCrossingParameter b) := by
    rw [← uIcc_of_le (D.centralUpperCrossingParameter_order b).le,
      ← Path.range_subpathAux]
    exact Set.mem_range_self u
  exact ⟨(D.centralUpperLeftCrossingParameter_mem b).1.1.trans hp.1,
    hp.2.trans (D.centralUpperRightCrossingParameter_mem b).1.2⟩

private theorem centralLowerConnectorParameter_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowSlicePoint b
        (D.centralLowerConnectorParameter b u, D.centralLowerConnectorTime) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  apply D.centralConnectorSurfacePatchTimeRadius_spec b D.centralLowerConnectorTime
  · exact D.abs_centralLowerConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_surfacePatch b)
  · exact D.centralLowerConnectorParameter_mem_probeInterval b u

private theorem centralUpperConnectorParameter_mem_surfacePatch
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.centralHeightFlowSlicePoint b
        (D.centralUpperConnectorParameter b u, D.centralUpperConnectorTime) ∈
      (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).surfacePatch := by
  apply D.centralConnectorSurfacePatchTimeRadius_spec b D.centralUpperConnectorTime
  · exact D.abs_centralUpperConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_surfacePatch b)
  · exact D.centralUpperConnectorParameter_mem_probeInterval b u

/-- The lower trimmed slice as a path in the canonical strip coordinates. -/
def centralHeightFlowLowerConnector (b : D.ConnectorBandIndex) : Path
    (D.centralLeftOuterArmCoordinate b D.centralLowerConnectorTime)
    (D.centralRightOuterArmCoordinate b D.centralLowerConnectorTime) where
  toFun := fun u ↦
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
      ⟨D.centralHeightFlowSlicePoint b
        (D.centralLowerConnectorParameter b u, D.centralLowerConnectorTime),
          D.centralLowerConnectorParameter_mem_surfacePatch b u⟩
  continuous_toFun := by
    apply (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.continuous.comp
    apply Continuous.subtype_mk
    exact (D.continuous_centralHeightFlowSlicePoint b).comp
      ((D.continuous_centralLowerConnectorParameter b).prodMk continuous_const)
  source' := by
    simp only [centralLowerConnectorParameter, Icc.convexComb_zero]
    unfold centralLeftOuterArmCoordinate
    apply congrArg (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (transportedTorusPlaneMap Phi)
      (D.centralLowerLeftCrossingLift_eq_outerArm b)
  target' := by
    simp only [centralLowerConnectorParameter, Icc.convexComb_one]
    unfold centralRightOuterArmCoordinate
    apply congrArg (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (transportedTorusPlaneMap Phi)
      (D.centralLowerRightCrossingLift_eq_outerArm b)

/-- The upper trimmed slice as a path in the canonical strip coordinates. -/
def centralHeightFlowUpperConnector (b : D.ConnectorBandIndex) : Path
    (D.centralLeftOuterArmCoordinate b D.centralUpperConnectorTime)
    (D.centralRightOuterArmCoordinate b D.centralUpperConnectorTime) where
  toFun := fun u ↦
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
      ⟨D.centralHeightFlowSlicePoint b
        (D.centralUpperConnectorParameter b u, D.centralUpperConnectorTime),
          D.centralUpperConnectorParameter_mem_surfacePatch b u⟩
  continuous_toFun := by
    apply (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.continuous.comp
    apply Continuous.subtype_mk
    exact (D.continuous_centralHeightFlowSlicePoint b).comp
      ((D.continuous_centralUpperConnectorParameter b).prodMk continuous_const)
  source' := by
    simp only [centralUpperConnectorParameter, Icc.convexComb_zero]
    unfold centralLeftOuterArmCoordinate
    apply congrArg (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (transportedTorusPlaneMap Phi)
      (D.centralUpperLeftCrossingLift_eq_outerArm b)
  target' := by
    simp only [centralUpperConnectorParameter, Icc.convexComb_one]
    unfold centralRightOuterArmCoordinate
    apply congrArg (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (transportedTorusPlaneMap Phi)
      (D.centralUpperRightCrossingLift_eq_outerArm b)

theorem canonicalBandMap_centralHeightFlowLowerConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralHeightFlowLowerConnector b u) =
      transportedTorusPlaneMap Phi
        (D.centralHeightFlowSliceLift b D.centralLowerConnectorTime
          (D.centralLowerConnectorParameter b u)) := by
  unfold canonicalBandMap centralHeightFlowLowerConnector
  change ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
        ⟨D.centralHeightFlowSlicePoint b
          (D.centralLowerConnectorParameter b u, D.centralLowerConnectorTime),
            D.centralLowerConnectorParameter_mem_surfacePatch b u⟩)).1.1 = _
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  rfl

theorem canonicalBandMap_centralHeightFlowUpperConnector
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralHeightFlowUpperConnector b u) =
      transportedTorusPlaneMap Phi
        (D.centralHeightFlowSliceLift b D.centralUpperConnectorTime
          (D.centralUpperConnectorParameter b u)) := by
  unfold canonicalBandMap centralHeightFlowUpperConnector
  change ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip
      ((D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm
        ⟨D.centralHeightFlowSlicePoint b
          (D.centralUpperConnectorParameter b u, D.centralUpperConnectorTime),
            D.centralUpperConnectorParameter_mem_surfacePatch b u⟩)).1.1 = _
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  rfl

theorem centralLowerConnectorParameter_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralLowerConnectorParameter b) := by
  intro u v huv
  have hvalue := congrArg Subtype.val huv
  simp only [centralLowerConnectorParameter, Icc.coe_convexComb] at hvalue
  apply Subtype.ext
  have hgap : 0 < (D.centralLowerRightCrossingParameter b : ℝ) -
      D.centralLowerLeftCrossingParameter b :=
    sub_pos.mpr (D.centralLowerCrossingParameter_order b)
  nlinarith

theorem centralUpperConnectorParameter_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralUpperConnectorParameter b) := by
  intro u v huv
  have hvalue := congrArg Subtype.val huv
  simp only [centralUpperConnectorParameter, Icc.coe_convexComb] at hvalue
  apply Subtype.ext
  have hgap : 0 < (D.centralUpperRightCrossingParameter b : ℝ) -
      D.centralUpperLeftCrossingParameter b :=
    sub_pos.mpr (D.centralUpperCrossingParameter_order b)
  nlinarith

theorem centralHeightFlowLowerConnector_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralHeightFlowLowerConnector b) := by
  intro u v huv
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective huv
  have hpoint := congrArg Subtype.val hsurface
  apply D.centralLowerConnectorParameter_injective b
  apply D.centralHeightFlowSlicePoint_fixedTime_injective b
    D.centralLowerConnectorTime
  exact hpoint

theorem centralHeightFlowUpperConnector_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralHeightFlowUpperConnector b) := by
  intro u v huv
  have hsurface :=
    (D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.symm.injective huv
  have hpoint := congrArg Subtype.val hsurface
  apply D.centralUpperConnectorParameter_injective b
  apply D.centralHeightFlowSlicePoint_fixedTime_injective b
    D.centralUpperConnectorTime
  exact hpoint

private theorem centralLowerConnectorParameter_mem_openCrossingInterval
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    D.centralLowerConnectorParameter b u ∈
      Ioo (D.centralLowerLeftCrossingParameter b)
        (D.centralLowerRightCrossingParameter b) := by
  change (D.centralLowerLeftCrossingParameter b : ℝ) <
      D.centralLowerConnectorParameter b u ∧
    (D.centralLowerConnectorParameter b u : ℝ) <
      D.centralLowerRightCrossingParameter b
  unfold centralLowerConnectorParameter
  simp only [Icc.coe_convexComb]
  have huPos : (0 : ℝ) < u := lt_of_le_of_ne u.2.1 <| by
    exact fun h ↦ hu0 (Subtype.ext h.symm)
  have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 <| by
    exact fun h ↦ hu1 (Subtype.ext h)
  have horder : (D.centralLowerLeftCrossingParameter b : ℝ) <
      D.centralLowerRightCrossingParameter b := D.centralLowerCrossingParameter_order b
  have hleft := mul_pos huPos (sub_pos.mpr horder)
  have hright := mul_pos (sub_pos.mpr huLt) (sub_pos.mpr horder)
  constructor <;> nlinarith

private theorem centralUpperConnectorParameter_mem_openCrossingInterval
    (b : D.ConnectorBandIndex) (u : unitInterval)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    D.centralUpperConnectorParameter b u ∈
      Ioo (D.centralUpperLeftCrossingParameter b)
        (D.centralUpperRightCrossingParameter b) := by
  change (D.centralUpperLeftCrossingParameter b : ℝ) <
      D.centralUpperConnectorParameter b u ∧
    (D.centralUpperConnectorParameter b u : ℝ) <
      D.centralUpperRightCrossingParameter b
  unfold centralUpperConnectorParameter
  simp only [Icc.coe_convexComb]
  have huPos : (0 : ℝ) < u := lt_of_le_of_ne u.2.1 <| by
    exact fun h ↦ hu0 (Subtype.ext h.symm)
  have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 <| by
    exact fun h ↦ hu1 (Subtype.ext h)
  have horder : (D.centralUpperLeftCrossingParameter b : ℝ) <
      D.centralUpperRightCrossingParameter b := D.centralUpperCrossingParameter_order b
  have hleft := mul_pos huPos (sub_pos.mpr horder)
  have hright := mul_pos (sub_pos.mpr huLt) (sub_pos.mpr horder)
  constructor <;> nlinarith

/-- The open lower connector interval lies strictly inside the outer body. -/
theorem centralLowerConnectorInterior_neg (b : D.ConnectorBandIndex)
    (u : unitInterval)
    (hu : u ∈ Ioo (D.centralLowerLeftCrossingParameter b)
      (D.centralLowerRightCrossingParameter b)) :
    D.centralHeightFlowOuterDefect b D.centralLowerConnectorTime u < 0 := by
  apply D.centralConnector_betweenExtremalCrossings_neg b D.centralLowerConnectorTime
    (D.centralLowerConnectorLeftZeroSet_nonempty b)
    (D.centralLowerConnectorRightZeroSet_nonempty b) _ u hu
  intro v hv
  exact D.centralConnectorFullNegativeTimeRadius_spec b D.centralLowerConnectorTime
    (D.abs_centralLowerConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) v hv

/-- The open upper connector interval lies strictly inside the outer body. -/
theorem centralUpperConnectorInterior_neg (b : D.ConnectorBandIndex)
    (u : unitInterval)
    (hu : u ∈ Ioo (D.centralUpperLeftCrossingParameter b)
      (D.centralUpperRightCrossingParameter b)) :
    D.centralHeightFlowOuterDefect b D.centralUpperConnectorTime u < 0 := by
  apply D.centralConnector_betweenExtremalCrossings_neg b D.centralUpperConnectorTime
    (D.centralUpperConnectorLeftZeroSet_nonempty b)
    (D.centralUpperConnectorRightZeroSet_nonempty b) _ u hu
  intro v hv
  exact D.centralConnectorFullNegativeTimeRadius_spec b D.centralUpperConnectorTime
    (D.abs_centralUpperConnectorTime_lt_radius.trans_le
      (D.uniformCentralConnectorTimeRadius_le_fullNegative b)) v hv

/-- Away from the central cutting height, a slice point is on the barrier exactly when it is on
the outer superellipsoid level. -/
theorem transportedTorusPlaneMap_centralHeightFlowSliceLift_mem_carrier_iff
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) (ht : (t : ℝ) ≠ 0)
    (u : unitInterval) :
    transportedTorusPlaneMap Phi (D.centralHeightFlowSliceLift b t u) ∈
        D.centralGraph.carrier ↔
      D.centralHeightFlowOuterDefect b t u = 0 := by
  change
    transportedTorusPlaneMap Phi
        (globalBandPlaneFlowCollarMap D.centralCutOrder b D.ConnectorBand
          D.centralHeightFlowData (u, t)) ∈ D.centralGraph.carrier ↔
      globalBandFlowOuterDefect D.centralCutOrder b D.ConnectorBand
        D.centralHeightFlowData (u, t) = 0
  rw [D.centralCutOrder.transportedTorusPlaneMap_globalBandPlaneFlowCollarMap_mem_carrier_iff
    b D.ConnectorBand D.scale_pos D.centralHeightFlowData (u, t)]
  constructor
  · rintro (houter | ⟨_, hzero⟩)
    · exact houter
    · exact (ht hzero).elim
  · exact Or.inl

theorem centralHeightFlowLowerConnector_mem_carrier_iff
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralHeightFlowLowerConnector b u) ∈
        D.centralGraph.carrier ↔
      u = 0 ∨ u = 1 := by
  rw [D.canonicalBandMap_centralHeightFlowLowerConnector,
    D.transportedTorusPlaneMap_centralHeightFlowSliceLift_mem_carrier_iff]
  · constructor
    · intro hzero
      by_contra hu
      push Not at hu
      exact (ne_of_lt (D.centralLowerConnectorInterior_neg b _
        (D.centralLowerConnectorParameter_mem_openCrossingInterval b u hu.1 hu.2))) hzero
    · rintro (rfl | rfl)
      · simpa [centralLowerConnectorParameter] using
          (D.centralLowerLeftCrossingParameter_mem b).2
      · simpa [centralLowerConnectorParameter] using
          (D.centralLowerRightCrossingParameter_mem b).2
  · exact ne_of_lt D.centralLowerConnectorTime_neg

theorem centralHeightFlowUpperConnector_mem_carrier_iff
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralHeightFlowUpperConnector b u) ∈
        D.centralGraph.carrier ↔
      u = 0 ∨ u = 1 := by
  rw [D.canonicalBandMap_centralHeightFlowUpperConnector,
    D.transportedTorusPlaneMap_centralHeightFlowSliceLift_mem_carrier_iff]
  · constructor
    · intro hzero
      by_contra hu
      push Not at hu
      exact (ne_of_lt (D.centralUpperConnectorInterior_neg b _
        (D.centralUpperConnectorParameter_mem_openCrossingInterval b u hu.1 hu.2))) hzero
    · rintro (rfl | rfl)
      · simpa [centralUpperConnectorParameter] using
          (D.centralUpperLeftCrossingParameter_mem b).2
      · simpa [centralUpperConnectorParameter] using
          (D.centralUpperRightCrossingParameter_mem b).2
  · exact ne_of_gt D.centralUpperConnectorTime_pos

private def connectorFlowTimeSegment (s t : D.ConnectorFlowTimes) : Path s t where
  toFun := fun u ↦ Icc.convexComb s t u
  continuous_toFun := Icc.continuous_convexComb s t
  source' := Icc.convexComb_zero s t
  target' := Icc.convexComb_one s t

theorem coe_connectorFlowTimeSegment (s t : D.ConnectorFlowTimes)
    (u : unitInterval) :
    (D.connectorFlowTimeSegment s t u : ℝ) =
      (1 - (u : ℝ)) * s + (u : ℝ) * t := by
  change ((Icc.convexComb s t u : D.ConnectorFlowTimes) : ℝ) = _
  exact Icc.coe_convexComb s t u

private theorem lowerUpperConvexEquation_left_eq_one (u v : unitInterval)
    (hvalue : (1 - (u : ℝ)) * D.centralLowerConnectorTime =
      (v : ℝ) * D.centralUpperConnectorTime) :
    u = 1 := by
  have hleftFactor : 0 ≤ 1 - (u : ℝ) := by linarith [u.2.2]
  have hleftNonpos :
      (1 - (u : ℝ)) * D.centralLowerConnectorTime ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hleftFactor D.centralLowerConnectorTime_neg.le
  have hrightNonneg :
      0 ≤ (v : ℝ) * D.centralUpperConnectorTime :=
    mul_nonneg v.2.1 D.centralUpperConnectorTime_pos.le
  have hleftNonneg :
      0 ≤ (1 - (u : ℝ)) * D.centralLowerConnectorTime := by
    rw [hvalue]
    exact hrightNonneg
  have hproduct : (1 - (u : ℝ)) * D.centralLowerConnectorTime = 0 :=
    le_antisymm hleftNonpos hleftNonneg
  have hfactor : 1 - (u : ℝ) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right (ne_of_lt D.centralLowerConnectorTime_neg)
  apply Subtype.ext
  exact (sub_eq_zero.mp hfactor).symm

private theorem connectorFlowTimeSegment_injective
    {s t : D.ConnectorFlowTimes} (hst : s ≠ t) :
    Function.Injective (D.connectorFlowTimeSegment s t) := by
  intro u v huv
  have hvalue := congrArg Subtype.val huv
  unfold connectorFlowTimeSegment at hvalue
  change (1 - (u : ℝ)) * s + (u : ℝ) * t =
    (1 - (v : ℝ)) * s + (v : ℝ) * t at hvalue
  apply Subtype.ext
  have hgap : (t : ℝ) - s ≠ 0 := by
    exact sub_ne_zero.mpr fun h ↦ hst (Subtype.ext h.symm)
  have hmul : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hgap)

theorem centralOuterArmTime_surjective : Function.Surjective D.centralOuterArmTime := by
  intro t
  let ε := D.openChartNarrowedData.heightData.band.ε
  have hε : 0 < ε := D.openChartNarrowedData.heightData.band.ε_pos
  have hden : 0 < 2 * ε := mul_pos (by norm_num) hε
  let u : unitInterval := ⟨((t : ℝ) + ε) / (2 * ε), by
    constructor
    · exact div_nonneg (by linarith [t.2.1]) hden.le
    · apply (div_le_one hden).mpr
      linarith [t.2.2]⟩
  refine ⟨u, Subtype.ext ?_⟩
  change -ε + (((t : ℝ) + ε) / (2 * ε)) * (2 * ε) = t
  field_simp [ne_of_gt hε]
  ring

/-- The left outer branch from the selected lower height to the left seam vertex. -/
def centralLeftLowerHeightFlowBranchPath (b : D.ConnectorBandIndex) : Path
    (D.centralLeftOuterArmCoordinate b D.centralLowerConnectorTime) bandLeftVertex :=
  (((D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand)).map
        (D.continuous_centralLeftOuterArmCoordinate b)).cast rfl
          (D.centralLeftOuterArmCoordinate_zero b).symm)

/-- The right outer branch from the selected lower height to the right seam vertex. -/
def centralRightLowerHeightFlowBranchPath (b : D.ConnectorBandIndex) : Path
    (D.centralRightOuterArmCoordinate b D.centralLowerConnectorTime) bandRightVertex :=
  (((D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand)).map
        (D.continuous_centralRightOuterArmCoordinate b)).cast rfl
          (D.centralRightOuterArmCoordinate_zero b).symm)

/-- The left outer branch from the left seam vertex to the selected upper height. -/
def centralLeftUpperHeightFlowBranchPath (b : D.ConnectorBandIndex) : Path bandLeftVertex
    (D.centralLeftOuterArmCoordinate b D.centralUpperConnectorTime) :=
  (((D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime).map
        (D.continuous_centralLeftOuterArmCoordinate b)).cast
          (D.centralLeftOuterArmCoordinate_zero b).symm rfl)

/-- The right outer branch from the right seam vertex to the selected upper height. -/
def centralRightUpperHeightFlowBranchPath (b : D.ConnectorBandIndex) : Path bandRightVertex
    (D.centralRightOuterArmCoordinate b D.centralUpperConnectorTime) :=
  (((D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime).map
        (D.continuous_centralRightOuterArmCoordinate b)).cast
          (D.centralRightOuterArmCoordinate_zero b).symm rfl)

theorem centralLeftLowerHeightFlowBranchPath_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralLeftLowerHeightFlowBranchPath b) := by
  change Function.Injective (fun u ↦ D.centralLeftOuterArmCoordinate b
    (D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand) u))
  exact (D.centralLeftOuterArmCoordinate_injective b).comp <|
    D.connectorFlowTimeSegment_injective <|
      ne_of_lt D.centralLowerConnectorTime_neg

theorem centralRightLowerHeightFlowBranchPath_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralRightLowerHeightFlowBranchPath b) := by
  change Function.Injective (fun u ↦ D.centralRightOuterArmCoordinate b
    (D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand) u))
  exact (D.centralRightOuterArmCoordinate_injective b).comp <|
    D.connectorFlowTimeSegment_injective <|
      ne_of_lt D.centralLowerConnectorTime_neg

theorem centralLeftUpperHeightFlowBranchPath_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralLeftUpperHeightFlowBranchPath b) := by
  change Function.Injective (fun u ↦ D.centralLeftOuterArmCoordinate b
    (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime u))
  exact (D.centralLeftOuterArmCoordinate_injective b).comp <|
    D.connectorFlowTimeSegment_injective <|
      fun h ↦ (ne_of_gt D.centralUpperConnectorTime_pos)
        (congrArg Subtype.val h).symm

theorem centralRightUpperHeightFlowBranchPath_injective
    (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralRightUpperHeightFlowBranchPath b) := by
  change Function.Injective (fun u ↦ D.centralRightOuterArmCoordinate b
    (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime u))
  exact (D.centralRightOuterArmCoordinate_injective b).comp <|
    D.connectorFlowTimeSegment_injective <|
      fun h ↦ (ne_of_gt D.centralUpperConnectorTime_pos)
        (congrArg Subtype.val h).symm

theorem centralLeftLowerHeightFlowBranchPath_range_subset_outerArm
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralLeftLowerHeightFlowBranchPath b) ⊆
      Set.range (D.centralLeftOuterArmPath b) := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := D.centralOuterArmTime_surjective
    (D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand) u)
  refine ⟨v, ?_⟩
  change D.centralLeftOuterArmCoordinate b _ = D.centralLeftOuterArmCoordinate b _
  rw [hv]

theorem centralRightLowerHeightFlowBranchPath_range_subset_outerArm
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralRightLowerHeightFlowBranchPath b) ⊆
      Set.range (D.centralRightOuterArmPath b) := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := D.centralOuterArmTime_surjective
    (D.connectorFlowTimeSegment D.centralLowerConnectorTime
      (globalBandFlowCollarZeroTime D.ConnectorBand) u)
  refine ⟨v, ?_⟩
  change D.centralRightOuterArmCoordinate b _ = D.centralRightOuterArmCoordinate b _
  rw [hv]

theorem centralLeftUpperHeightFlowBranchPath_range_subset_outerArm
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralLeftUpperHeightFlowBranchPath b) ⊆
      Set.range (D.centralLeftOuterArmPath b) := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := D.centralOuterArmTime_surjective
    (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime u)
  refine ⟨v, ?_⟩
  change D.centralLeftOuterArmCoordinate b _ = D.centralLeftOuterArmCoordinate b _
  rw [hv]

theorem centralRightUpperHeightFlowBranchPath_range_subset_outerArm
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralRightUpperHeightFlowBranchPath b) ⊆
      Set.range (D.centralRightOuterArmPath b) := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := D.centralOuterArmTime_surjective
    (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
      D.centralUpperConnectorTime u)
  refine ⟨v, ?_⟩
  change D.centralRightOuterArmCoordinate b _ = D.centralRightOuterArmCoordinate b _
  rw [hv]

private theorem inter_eq_singleton_of_subset_left' {X : Type*}
    {s t u : Set X} {p : X} (hs : s ⊆ t) (htu : t ∩ u = {p})
    (hps : p ∈ s) (hpu : p ∈ u) : s ∩ u = {p} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ t ∩ u := ⟨hs hx.1, hx.2⟩
    rw [htu] at hx'
    exact hx'
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨hps, hpu⟩

theorem centralLeftLowerHeightFlowBranchPath_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralLeftLowerHeightFlowBranchPath b) ∩ Set.range bandSeamPath =
      {bandLeftVertex} := by
  apply inter_eq_singleton_of_subset_left'
    (D.centralLeftLowerHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralLeftOuterArmPath_inter_bandSeamPath b)
  · exact ⟨1, (D.centralLeftLowerHeightFlowBranchPath b).target⟩
  · exact ⟨0, bandSeamPath.source⟩

theorem centralRightLowerHeightFlowBranchPath_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralRightLowerHeightFlowBranchPath b) ∩ Set.range bandSeamPath =
      {bandRightVertex} := by
  apply inter_eq_singleton_of_subset_left'
    (D.centralRightLowerHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightOuterArmPath_inter_bandSeamPath b)
  · exact ⟨1, (D.centralRightLowerHeightFlowBranchPath b).target⟩
  · exact ⟨1, bandSeamPath.target⟩

theorem centralLeftUpperHeightFlowBranchPath_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralLeftUpperHeightFlowBranchPath b) ∩ Set.range bandSeamPath =
      {bandLeftVertex} := by
  apply inter_eq_singleton_of_subset_left'
    (D.centralLeftUpperHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralLeftOuterArmPath_inter_bandSeamPath b)
  · exact ⟨0, (D.centralLeftUpperHeightFlowBranchPath b).source⟩
  · exact ⟨0, bandSeamPath.source⟩

theorem centralRightUpperHeightFlowBranchPath_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralRightUpperHeightFlowBranchPath b) ∩ Set.range bandSeamPath =
      {bandRightVertex} := by
  apply inter_eq_singleton_of_subset_left'
    (D.centralRightUpperHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightOuterArmPath_inter_bandSeamPath b)
  · exact ⟨0, (D.centralRightUpperHeightFlowBranchPath b).source⟩
  · exact ⟨1, bandSeamPath.target⟩

theorem centralLowerHeightFlowBranchPaths_disjoint (b : D.ConnectorBandIndex) :
    Disjoint (Set.range (D.centralLeftLowerHeightFlowBranchPath b))
      (Set.range (D.centralRightLowerHeightFlowBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftLowerHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightLowerHeightFlowBranchPath_range_subset_outerArm b)

theorem centralUpperHeightFlowBranchPaths_disjoint (b : D.ConnectorBandIndex) :
    Disjoint (Set.range (D.centralLeftUpperHeightFlowBranchPath b))
      (Set.range (D.centralRightUpperHeightFlowBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftUpperHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightUpperHeightFlowBranchPath_range_subset_outerArm b)

theorem centralLeftLowerBranch_disjoint_centralRightUpperBranch
    (b : D.ConnectorBandIndex) :
    Disjoint (Set.range (D.centralLeftLowerHeightFlowBranchPath b))
      (Set.range (D.centralRightUpperHeightFlowBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftLowerHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightUpperHeightFlowBranchPath_range_subset_outerArm b)

theorem centralLeftUpperBranch_disjoint_centralRightLowerBranch
    (b : D.ConnectorBandIndex) :
    Disjoint (Set.range (D.centralLeftUpperHeightFlowBranchPath b))
      (Set.range (D.centralRightLowerHeightFlowBranchPath b)) :=
  (D.centralLeftOuterArmPath_disjoint_centralRightOuterArmPath b).mono
    (D.centralLeftUpperHeightFlowBranchPath_range_subset_outerArm b)
    (D.centralRightLowerHeightFlowBranchPath_range_subset_outerArm b)

theorem centralLeftLowerBranch_inter_centralLeftUpperBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralLeftLowerHeightFlowBranchPath b) ∩
        Set.range (D.centralLeftUpperHeightFlowBranchPath b) =
      {bandLeftVertex} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hpoint : D.centralLeftLowerHeightFlowBranchPath b u =
        D.centralLeftUpperHeightFlowBranchPath b v := hu.trans hv.symm
    have htime :
        D.connectorFlowTimeSegment D.centralLowerConnectorTime
            (globalBandFlowCollarZeroTime D.ConnectorBand) u =
          D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
            D.centralUpperConnectorTime v := by
      apply D.centralLeftOuterArmCoordinate_injective b
      exact hpoint
    have htimeValue := congrArg Subtype.val htime
    rw [D.coe_connectorFlowTimeSegment, D.coe_connectorFlowTimeSegment] at htimeValue
    change (1 - (u : ℝ)) * D.centralLowerConnectorTime + (u : ℝ) * 0 =
      (1 - (v : ℝ)) * 0 + (v : ℝ) * D.centralUpperConnectorTime at htimeValue
    norm_num at htimeValue
    have huOne : u = (1 : unitInterval) :=
      D.lowerUpperConvexEquation_left_eq_one u v htimeValue
    have hzero :
        D.connectorFlowTimeSegment D.centralLowerConnectorTime
            (globalBandFlowCollarZeroTime D.ConnectorBand) u =
          globalBandFlowCollarZeroTime D.ConnectorBand := by
      rw [huOne]
      exact (D.connectorFlowTimeSegment D.centralLowerConnectorTime
        (globalBandFlowCollarZeroTime D.ConnectorBand)).target
    apply Set.mem_singleton_iff.mpr
    calc
      x = D.centralLeftLowerHeightFlowBranchPath b u := hu.symm
      _ = D.centralLeftOuterArmCoordinate b
          (globalBandFlowCollarZeroTime D.ConnectorBand) := by
        change D.centralLeftOuterArmCoordinate b _ = _
        rw [hzero]
      _ = bandLeftVertex := D.centralLeftOuterArmCoordinate_zero b
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, (D.centralLeftLowerHeightFlowBranchPath b).target⟩,
      ⟨0, (D.centralLeftUpperHeightFlowBranchPath b).source⟩⟩

theorem centralRightLowerBranch_inter_centralRightUpperBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralRightLowerHeightFlowBranchPath b) ∩
        Set.range (D.centralRightUpperHeightFlowBranchPath b) =
      {bandRightVertex} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hpoint : D.centralRightLowerHeightFlowBranchPath b u =
        D.centralRightUpperHeightFlowBranchPath b v := hu.trans hv.symm
    have htime :
        D.connectorFlowTimeSegment D.centralLowerConnectorTime
            (globalBandFlowCollarZeroTime D.ConnectorBand) u =
          D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
            D.centralUpperConnectorTime v := by
      apply D.centralRightOuterArmCoordinate_injective b
      exact hpoint
    have htimeValue := congrArg Subtype.val htime
    rw [D.coe_connectorFlowTimeSegment, D.coe_connectorFlowTimeSegment] at htimeValue
    change (1 - (u : ℝ)) * D.centralLowerConnectorTime + (u : ℝ) * 0 =
      (1 - (v : ℝ)) * 0 + (v : ℝ) * D.centralUpperConnectorTime at htimeValue
    norm_num at htimeValue
    have huOne : u = (1 : unitInterval) :=
      D.lowerUpperConvexEquation_left_eq_one u v htimeValue
    have hzero :
        D.connectorFlowTimeSegment D.centralLowerConnectorTime
            (globalBandFlowCollarZeroTime D.ConnectorBand) u =
          globalBandFlowCollarZeroTime D.ConnectorBand := by
      rw [huOne]
      exact (D.connectorFlowTimeSegment D.centralLowerConnectorTime
        (globalBandFlowCollarZeroTime D.ConnectorBand)).target
    apply Set.mem_singleton_iff.mpr
    calc
      x = D.centralRightLowerHeightFlowBranchPath b u := hu.symm
      _ = D.centralRightOuterArmCoordinate b
          (globalBandFlowCollarZeroTime D.ConnectorBand) := by
        change D.centralRightOuterArmCoordinate b _ = _
        rw [hzero]
      _ = bandRightVertex := D.centralRightOuterArmCoordinate_zero b
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, (D.centralRightLowerHeightFlowBranchPath b).target⟩,
      ⟨0, (D.centralRightUpperHeightFlowBranchPath b).source⟩⟩

theorem centralHeightFlowConnectors_disjoint (b : D.ConnectorBandIndex) :
    Disjoint (Set.range (D.centralHeightFlowLowerConnector b))
      (Set.range (D.centralHeightFlowUpperConnector b)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu⟩ ⟨v, hv⟩
  have hpoint : D.centralHeightFlowLowerConnector b u =
      D.centralHeightFlowUpperConnector b v := hu.trans hv.symm
  have hmap := congrArg (D.canonicalBandMap b) hpoint
  rw [D.canonicalBandMap_centralHeightFlowLowerConnector,
    D.canonicalBandMap_centralHeightFlowUpperConnector] at hmap
  have hheight := congrArg (ambientCoordinate (frame 2)) hmap
  change orientedCoordinateLift Phi frame 2
      (D.centralHeightFlowSliceLift b D.centralLowerConnectorTime
        (D.centralLowerConnectorParameter b u)) =
    orientedCoordinateLift Phi frame 2
      (D.centralHeightFlowSliceLift b D.centralUpperConnectorTime
        (D.centralUpperConnectorParameter b v)) at hheight
  rw [D.orientedCoordinateLift_centralHeightFlowSliceLift,
    D.orientedCoordinateLift_centralHeightFlowSliceLift] at hheight
  linarith [D.centralLowerConnectorTime_neg, D.centralUpperConnectorTime_pos]

theorem canonicalBandMap_centralLeftOuterArmCoordinate_mem_carrier
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) :
    D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b t) ∈ D.centralGraph.carrier := by
  have h := D.centralLeftOuterArmLift_mem_carrier b (D.openChartNarrowedTime t)
  unfold canonicalBandMap centralLeftOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  exact h

theorem canonicalBandMap_centralRightOuterArmCoordinate_mem_carrier
    (b : D.ConnectorBandIndex) (t : D.ConnectorFlowTimes) :
    D.canonicalBandMap b (D.centralRightOuterArmCoordinate b t) ∈ D.centralGraph.carrier := by
  have h := D.centralRightOuterArmLift_mem_carrier b (D.openChartNarrowedTime t)
  unfold canonicalBandMap centralRightOuterArmCoordinate
  rw [(D.centralCutOrder.globalBandOpenTubularChartFamily.band b).strip.apply_symm_apply]
  exact h

theorem canonicalBandMap_centralLeftLowerHeightFlowBranchPath_mem_carrier
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralLeftLowerHeightFlowBranchPath b u) ∈
      D.centralGraph.carrier := by
  change D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b
      (D.connectorFlowTimeSegment D.centralLowerConnectorTime
        (globalBandFlowCollarZeroTime D.ConnectorBand) u)) ∈ D.centralGraph.carrier
  exact D.canonicalBandMap_centralLeftOuterArmCoordinate_mem_carrier b _

theorem canonicalBandMap_centralRightLowerHeightFlowBranchPath_mem_carrier
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralRightLowerHeightFlowBranchPath b u) ∈
      D.centralGraph.carrier := by
  change D.canonicalBandMap b (D.centralRightOuterArmCoordinate b
      (D.connectorFlowTimeSegment D.centralLowerConnectorTime
        (globalBandFlowCollarZeroTime D.ConnectorBand) u)) ∈ D.centralGraph.carrier
  exact D.canonicalBandMap_centralRightOuterArmCoordinate_mem_carrier b _

theorem canonicalBandMap_centralLeftUpperHeightFlowBranchPath_mem_carrier
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralLeftUpperHeightFlowBranchPath b u) ∈
      D.centralGraph.carrier := by
  change D.canonicalBandMap b (D.centralLeftOuterArmCoordinate b
      (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
        D.centralUpperConnectorTime u)) ∈ D.centralGraph.carrier
  exact D.canonicalBandMap_centralLeftOuterArmCoordinate_mem_carrier b _

theorem canonicalBandMap_centralRightUpperHeightFlowBranchPath_mem_carrier
    (b : D.ConnectorBandIndex) (u : unitInterval) :
    D.canonicalBandMap b (D.centralRightUpperHeightFlowBranchPath b u) ∈
      D.centralGraph.carrier := by
  change D.canonicalBandMap b (D.centralRightOuterArmCoordinate b
      (D.connectorFlowTimeSegment (globalBandFlowCollarZeroTime D.ConnectorBand)
        D.centralUpperConnectorTime u)) ∈ D.centralGraph.carrier
  exact D.canonicalBandMap_centralRightOuterArmCoordinate_mem_carrier b _

private theorem connector_inter_carrierPath_subset_endpoints
    {a b c d : Plane} (i : D.ConnectorBandIndex)
    (connector : Path a b)
    (hconnector : ∀ u, D.canonicalBandMap i (connector u) ∈
      D.centralGraph.carrier ↔ u = 0 ∨ u = 1)
    (p : Path c d)
    (hp : ∀ u, D.canonicalBandMap i (p u) ∈ D.centralGraph.carrier) :
    Set.range connector ∩ Set.range p ⊆ {a, b} := by
  rintro x ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  have hpaths : connector u = p v := hu.trans hv.symm
  have hcarrier : D.canonicalBandMap i (connector u) ∈ D.centralGraph.carrier := by
    rw [hpaths]
    exact hp v
  rcases (hconnector u).mp hcarrier with rfl | rfl
  · exact Or.inl (hu.symm.trans connector.source)
  · exact Or.inr (hu.symm.trans connector.target)

private theorem connector_inter_carrierPath_eq_source
    {a b c d : Plane} (i : D.ConnectorBandIndex)
    (connector : Path a b)
    (hconnector : ∀ u, D.canonicalBandMap i (connector u) ∈
      D.centralGraph.carrier ↔ u = 0 ∨ u = 1)
    (p : Path c d)
    (hp : ∀ u, D.canonicalBandMap i (p u) ∈ D.centralGraph.carrier)
    (ha : a ∈ Set.range p) (hb : b ∉ Set.range p) :
    Set.range connector ∩ Set.range p = {a} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases D.connector_inter_carrierPath_subset_endpoints i connector hconnector p hp hx with
      hxa | hxb
    · exact Set.mem_singleton_iff.mpr hxa
    · exact (hb (hxb ▸ hx.2)).elim
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0, connector.source⟩, ha⟩

private theorem connector_inter_carrierPath_eq_target
    {a b c d : Plane} (i : D.ConnectorBandIndex)
    (connector : Path a b)
    (hconnector : ∀ u, D.canonicalBandMap i (connector u) ∈
      D.centralGraph.carrier ↔ u = 0 ∨ u = 1)
    (p : Path c d)
    (hp : ∀ u, D.canonicalBandMap i (p u) ∈ D.centralGraph.carrier)
    (ha : a ∉ Set.range p) (hb : b ∈ Set.range p) :
    Set.range connector ∩ Set.range p = {b} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases D.connector_inter_carrierPath_subset_endpoints i connector hconnector p hp hx with
      hxa | hxb
    · exact (ha (hxa ▸ hx.2)).elim
    · exact Set.mem_singleton_iff.mpr hxb
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨1, connector.target⟩, hb⟩

private theorem connector_inter_carrierPath_eq_empty
    {a b c d : Plane} (i : D.ConnectorBandIndex)
    (connector : Path a b)
    (hconnector : ∀ u, D.canonicalBandMap i (connector u) ∈
      D.centralGraph.carrier ↔ u = 0 ∨ u = 1)
    (p : Path c d)
    (hp : ∀ u, D.canonicalBandMap i (p u) ∈ D.centralGraph.carrier)
    (ha : a ∉ Set.range p) (hb : b ∉ Set.range p) :
    Set.range connector ∩ Set.range p = ∅ := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases D.connector_inter_carrierPath_subset_endpoints i connector hconnector p hp hx with
      hxa | hxb
    · exact (ha (hxa ▸ hx.2)).elim
    · exact (hb (hxb ▸ hx.2)).elim
  · exact Set.empty_subset _

private theorem path_source_not_mem_of_range_inter_eq_target
    {a b c d : Plane} (p : Path a b) (hp : Function.Injective p)
    (q : Path c d) (hinter : Set.range p ∩ Set.range q = {b}) :
    a ∉ Set.range q := by
  intro ha
  have hab : a = b := by
    apply Set.mem_singleton_iff.mp
    rw [← hinter]
    exact ⟨⟨0, p.source⟩, ha⟩
  have hzeroOne : (0 : unitInterval) = 1 := by
    apply hp
    exact p.source.trans (hab.trans p.target.symm)
  exact zero_ne_one hzeroOne

private theorem path_target_not_mem_of_range_inter_eq_source
    {a b c d : Plane} (p : Path a b) (hp : Function.Injective p)
    (q : Path c d) (hinter : Set.range p ∩ Set.range q = {a}) :
    b ∉ Set.range q := by
  intro hb
  have hba : b = a := by
    apply Set.mem_singleton_iff.mp
    rw [← hinter]
    exact ⟨⟨1, p.target⟩, hb⟩
  have honeZero : (1 : unitInterval) = 0 := by
    apply hp
    exact p.target.trans (hba.trans p.source.symm)
  exact one_ne_zero honeZero

theorem range_centralHeightFlowLowerConnector_inter_leftBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerConnector b) ∩
        Set.range (D.centralLeftLowerHeightFlowBranchPath b) =
      {D.centralLeftOuterArmCoordinate b D.centralLowerConnectorTime} := by
  apply D.connector_inter_carrierPath_eq_source b
    (D.centralHeightFlowLowerConnector b)
    (D.centralHeightFlowLowerConnector_mem_carrier_iff b)
    (D.centralLeftLowerHeightFlowBranchPath b)
    (D.canonicalBandMap_centralLeftLowerHeightFlowBranchPath_mem_carrier b)
  · exact ⟨0, (D.centralLeftLowerHeightFlowBranchPath b).source⟩
  · intro hright
    exact Set.disjoint_left.mp (D.centralLowerHeightFlowBranchPaths_disjoint b)
      hright ⟨0, (D.centralRightLowerHeightFlowBranchPath b).source⟩

theorem range_centralHeightFlowLowerConnector_inter_rightBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerConnector b) ∩
        Set.range (D.centralRightLowerHeightFlowBranchPath b) =
      {D.centralRightOuterArmCoordinate b D.centralLowerConnectorTime} := by
  apply D.connector_inter_carrierPath_eq_target b
    (D.centralHeightFlowLowerConnector b)
    (D.centralHeightFlowLowerConnector_mem_carrier_iff b)
    (D.centralRightLowerHeightFlowBranchPath b)
    (D.canonicalBandMap_centralRightLowerHeightFlowBranchPath_mem_carrier b)
  · intro hleft
    exact Set.disjoint_left.mp (D.centralLowerHeightFlowBranchPaths_disjoint b)
      ⟨0, (D.centralLeftLowerHeightFlowBranchPath b).source⟩ hleft
  · exact ⟨0, (D.centralRightLowerHeightFlowBranchPath b).source⟩

theorem range_centralHeightFlowUpperConnector_inter_leftBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowUpperConnector b) ∩
        Set.range (D.centralLeftUpperHeightFlowBranchPath b) =
      {D.centralLeftOuterArmCoordinate b D.centralUpperConnectorTime} := by
  apply D.connector_inter_carrierPath_eq_source b
    (D.centralHeightFlowUpperConnector b)
    (D.centralHeightFlowUpperConnector_mem_carrier_iff b)
    (D.centralLeftUpperHeightFlowBranchPath b)
    (D.canonicalBandMap_centralLeftUpperHeightFlowBranchPath_mem_carrier b)
  · exact ⟨1, (D.centralLeftUpperHeightFlowBranchPath b).target⟩
  · intro hright
    exact Set.disjoint_left.mp (D.centralUpperHeightFlowBranchPaths_disjoint b)
      hright ⟨1, (D.centralRightUpperHeightFlowBranchPath b).target⟩

theorem range_centralHeightFlowUpperConnector_inter_rightBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowUpperConnector b) ∩
        Set.range (D.centralRightUpperHeightFlowBranchPath b) =
      {D.centralRightOuterArmCoordinate b D.centralUpperConnectorTime} := by
  apply D.connector_inter_carrierPath_eq_target b
    (D.centralHeightFlowUpperConnector b)
    (D.centralHeightFlowUpperConnector_mem_carrier_iff b)
    (D.centralRightUpperHeightFlowBranchPath b)
    (D.canonicalBandMap_centralRightUpperHeightFlowBranchPath_mem_carrier b)
  · intro hleft
    exact Set.disjoint_left.mp (D.centralUpperHeightFlowBranchPaths_disjoint b)
      ⟨1, (D.centralLeftUpperHeightFlowBranchPath b).target⟩ hleft
  · exact ⟨1, (D.centralRightUpperHeightFlowBranchPath b).target⟩

theorem range_centralHeightFlowLowerConnector_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerConnector b) ∩ Set.range bandSeamPath = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowLowerConnector b)
    (D.centralHeightFlowLowerConnector_mem_carrier_iff b)
    bandSeamPath (D.canonicalBandMap_bandSeamPath_mem_carrier b)
  · exact path_source_not_mem_of_range_inter_eq_target
      (D.centralLeftLowerHeightFlowBranchPath b)
      (D.centralLeftLowerHeightFlowBranchPath_injective b) bandSeamPath
      (D.centralLeftLowerHeightFlowBranchPath_inter_bandSeamPath b)
  · exact path_source_not_mem_of_range_inter_eq_target
      (D.centralRightLowerHeightFlowBranchPath b)
      (D.centralRightLowerHeightFlowBranchPath_injective b) bandSeamPath
      (D.centralRightLowerHeightFlowBranchPath_inter_bandSeamPath b)

theorem range_centralHeightFlowUpperConnector_inter_bandSeamPath
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowUpperConnector b) ∩ Set.range bandSeamPath = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowUpperConnector b)
    (D.centralHeightFlowUpperConnector_mem_carrier_iff b)
    bandSeamPath (D.canonicalBandMap_bandSeamPath_mem_carrier b)
  · exact path_target_not_mem_of_range_inter_eq_source
      (D.centralLeftUpperHeightFlowBranchPath b)
      (D.centralLeftUpperHeightFlowBranchPath_injective b) bandSeamPath
      (D.centralLeftUpperHeightFlowBranchPath_inter_bandSeamPath b)
  · exact path_target_not_mem_of_range_inter_eq_source
      (D.centralRightUpperHeightFlowBranchPath b)
      (D.centralRightUpperHeightFlowBranchPath_injective b) bandSeamPath
      (D.centralRightUpperHeightFlowBranchPath_inter_bandSeamPath b)

theorem range_centralHeightFlowLowerConnector_inter_leftUpperBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerConnector b) ∩
        Set.range (D.centralLeftUpperHeightFlowBranchPath b) = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowLowerConnector b)
    (D.centralHeightFlowLowerConnector_mem_carrier_iff b)
    (D.centralLeftUpperHeightFlowBranchPath b)
    (D.canonicalBandMap_centralLeftUpperHeightFlowBranchPath_mem_carrier b)
  · exact path_source_not_mem_of_range_inter_eq_target
      (D.centralLeftLowerHeightFlowBranchPath b)
      (D.centralLeftLowerHeightFlowBranchPath_injective b)
      (D.centralLeftUpperHeightFlowBranchPath b)
      (D.centralLeftLowerBranch_inter_centralLeftUpperBranch b)
  · intro hright
    exact Set.disjoint_left.mp (D.centralLeftUpperBranch_disjoint_centralRightLowerBranch b)
      hright ⟨0, (D.centralRightLowerHeightFlowBranchPath b).source⟩

theorem range_centralHeightFlowLowerConnector_inter_rightUpperBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerConnector b) ∩
        Set.range (D.centralRightUpperHeightFlowBranchPath b) = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowLowerConnector b)
    (D.centralHeightFlowLowerConnector_mem_carrier_iff b)
    (D.centralRightUpperHeightFlowBranchPath b)
    (D.canonicalBandMap_centralRightUpperHeightFlowBranchPath_mem_carrier b)
  · intro hleft
    exact Set.disjoint_left.mp (D.centralLeftLowerBranch_disjoint_centralRightUpperBranch b)
      ⟨0, (D.centralLeftLowerHeightFlowBranchPath b).source⟩ hleft
  · exact path_source_not_mem_of_range_inter_eq_target
      (D.centralRightLowerHeightFlowBranchPath b)
      (D.centralRightLowerHeightFlowBranchPath_injective b)
      (D.centralRightUpperHeightFlowBranchPath b)
      (D.centralRightLowerBranch_inter_centralRightUpperBranch b)

theorem range_centralHeightFlowUpperConnector_inter_leftLowerBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowUpperConnector b) ∩
        Set.range (D.centralLeftLowerHeightFlowBranchPath b) = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowUpperConnector b)
    (D.centralHeightFlowUpperConnector_mem_carrier_iff b)
    (D.centralLeftLowerHeightFlowBranchPath b)
    (D.canonicalBandMap_centralLeftLowerHeightFlowBranchPath_mem_carrier b)
  · apply path_target_not_mem_of_range_inter_eq_source
      (D.centralLeftUpperHeightFlowBranchPath b)
      (D.centralLeftUpperHeightFlowBranchPath_injective b)
      (D.centralLeftLowerHeightFlowBranchPath b)
    rw [Set.inter_comm]
    exact D.centralLeftLowerBranch_inter_centralLeftUpperBranch b
  · intro hright
    exact Set.disjoint_left.mp (D.centralLeftLowerBranch_disjoint_centralRightUpperBranch b)
      hright ⟨1, (D.centralRightUpperHeightFlowBranchPath b).target⟩

theorem range_centralHeightFlowUpperConnector_inter_rightLowerBranch
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowUpperConnector b) ∩
        Set.range (D.centralRightLowerHeightFlowBranchPath b) = ∅ := by
  apply D.connector_inter_carrierPath_eq_empty b
    (D.centralHeightFlowUpperConnector b)
    (D.centralHeightFlowUpperConnector_mem_carrier_iff b)
    (D.centralRightLowerHeightFlowBranchPath b)
    (D.canonicalBandMap_centralRightLowerHeightFlowBranchPath_mem_carrier b)
  · intro hleft
    exact Set.disjoint_left.mp (D.centralLeftUpperBranch_disjoint_centralRightLowerBranch b)
      ⟨1, (D.centralLeftUpperHeightFlowBranchPath b).target⟩ hleft
  · apply path_target_not_mem_of_range_inter_eq_source
      (D.centralRightUpperHeightFlowBranchPath b)
      (D.centralRightUpperHeightFlowBranchPath_injective b)
      (D.centralRightLowerHeightFlowBranchPath b)
    rw [Set.inter_comm]
    exact D.centralRightLowerBranch_inter_centralRightUpperBranch b

/-- The completed lower route through the height-flow connector. -/
def centralHeightFlowLowerThetaRoute (b : D.ConnectorBandIndex) :
    Path bandLeftVertex bandRightVertex :=
  (((D.centralLeftLowerHeightFlowBranchPath b).symm.trans
    (D.centralHeightFlowLowerConnector b)).trans
      (D.centralRightLowerHeightFlowBranchPath b))

/-- The completed upper route through the height-flow connector. -/
def centralHeightFlowUpperThetaRoute (b : D.ConnectorBandIndex) :
    Path bandLeftVertex bandRightVertex :=
  (((D.centralLeftUpperHeightFlowBranchPath b).trans
    (D.centralHeightFlowUpperConnector b)).trans
      (D.centralRightUpperHeightFlowBranchPath b).symm)

private theorem path_symm_injective {a b : Plane} (p : Path a b)
    (hp : Function.Injective p) : Function.Injective p.symm := by
  intro u v huv
  apply unitInterval.symm_bijective.injective
  apply hp
  simpa only [Path.symm_apply, Function.comp_apply] using huv

theorem centralHeightFlowLowerThetaRoute_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralHeightFlowLowerThetaRoute b) := by
  have hleftConnector :
      Set.range (D.centralLeftLowerHeightFlowBranchPath b).symm ∩
          Set.range (D.centralHeightFlowLowerConnector b) =
        {D.centralLeftOuterArmCoordinate b D.centralLowerConnectorTime} := by
    rw [Path.symm_range, Set.inter_comm]
    exact D.range_centralHeightFlowLowerConnector_inter_leftBranch b
  have hfirst : Function.Injective
      ((D.centralLeftLowerHeightFlowBranchPath b).symm.trans
        (D.centralHeightFlowLowerConnector b)) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      (D.centralLeftLowerHeightFlowBranchPath b).symm
      (D.centralHeightFlowLowerConnector b)
      (path_symm_injective _ (D.centralLeftLowerHeightFlowBranchPath_injective b))
      (D.centralHeightFlowLowerConnector_injective b) hleftConnector
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    ((D.centralLeftLowerHeightFlowBranchPath b).symm.trans
      (D.centralHeightFlowLowerConnector b))
    (D.centralRightLowerHeightFlowBranchPath b) hfirst
    (D.centralRightLowerHeightFlowBranchPath_injective b)
  rw [Path.trans_range, Set.union_inter_distrib_right,
    Path.symm_range,
    Set.disjoint_iff_inter_eq_empty.mp (D.centralLowerHeightFlowBranchPaths_disjoint b),
    D.range_centralHeightFlowLowerConnector_inter_rightBranch b,
    Set.empty_union]

theorem centralHeightFlowUpperThetaRoute_injective (b : D.ConnectorBandIndex) :
    Function.Injective (D.centralHeightFlowUpperThetaRoute b) := by
  have hleftConnector :
      Set.range (D.centralLeftUpperHeightFlowBranchPath b) ∩
          Set.range (D.centralHeightFlowUpperConnector b) =
        {D.centralLeftOuterArmCoordinate b D.centralUpperConnectorTime} := by
    rw [Set.inter_comm]
    exact D.range_centralHeightFlowUpperConnector_inter_leftBranch b
  have hfirst : Function.Injective
      ((D.centralLeftUpperHeightFlowBranchPath b).trans
        (D.centralHeightFlowUpperConnector b)) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      (D.centralLeftUpperHeightFlowBranchPath b)
      (D.centralHeightFlowUpperConnector b)
      (D.centralLeftUpperHeightFlowBranchPath_injective b)
      (D.centralHeightFlowUpperConnector_injective b) hleftConnector
  apply LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
    ((D.centralLeftUpperHeightFlowBranchPath b).trans
      (D.centralHeightFlowUpperConnector b))
    (D.centralRightUpperHeightFlowBranchPath b).symm hfirst
    (path_symm_injective _ (D.centralRightUpperHeightFlowBranchPath_injective b))
  rw [Path.trans_range, Set.union_inter_distrib_right,
    Path.symm_range,
    Set.disjoint_iff_inter_eq_empty.mp (D.centralUpperHeightFlowBranchPaths_disjoint b),
    D.range_centralHeightFlowUpperConnector_inter_rightBranch b,
    Set.empty_union]

theorem range_bandSeamPath_inter_centralHeightFlowLowerThetaRoute
    (b : D.ConnectorBandIndex) :
    Set.range bandSeamPath ∩ Set.range (D.centralHeightFlowLowerThetaRoute b) =
      {bandLeftVertex, bandRightVertex} := by
  rw [centralHeightFlowLowerThetaRoute, Path.trans_range, Path.trans_range,
    Path.symm_range, Set.inter_union_distrib_left, Set.inter_union_distrib_left,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralLeftLowerHeightFlowBranchPath b)),
    D.centralLeftLowerHeightFlowBranchPath_inter_bandSeamPath b,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralHeightFlowLowerConnector b)),
    D.range_centralHeightFlowLowerConnector_inter_bandSeamPath b,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralRightLowerHeightFlowBranchPath b)),
    D.centralRightLowerHeightFlowBranchPath_inter_bandSeamPath b]
  simp only [Set.union_empty, Set.singleton_union]

theorem range_bandSeamPath_inter_centralHeightFlowUpperThetaRoute
    (b : D.ConnectorBandIndex) :
    Set.range bandSeamPath ∩ Set.range (D.centralHeightFlowUpperThetaRoute b) =
      {bandLeftVertex, bandRightVertex} := by
  rw [centralHeightFlowUpperThetaRoute, Path.trans_range, Path.trans_range,
    Path.symm_range, Set.inter_union_distrib_left, Set.inter_union_distrib_left,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralLeftUpperHeightFlowBranchPath b)),
    D.centralLeftUpperHeightFlowBranchPath_inter_bandSeamPath b,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralHeightFlowUpperConnector b)),
    D.range_centralHeightFlowUpperConnector_inter_bandSeamPath b,
    Set.inter_comm (Set.range bandSeamPath)
      (Set.range (D.centralRightUpperHeightFlowBranchPath b)),
    D.centralRightUpperHeightFlowBranchPath_inter_bandSeamPath b]
  simp only [Set.union_empty, Set.singleton_union]

theorem range_centralHeightFlowLowerThetaRoute_inter_upperThetaRoute
    (b : D.ConnectorBandIndex) :
    Set.range (D.centralHeightFlowLowerThetaRoute b) ∩
        Set.range (D.centralHeightFlowUpperThetaRoute b) =
      {bandLeftVertex, bandRightVertex} := by
  ext x
  constructor
  · intro hx
    rw [centralHeightFlowLowerThetaRoute, Path.trans_range, Path.trans_range,
      Path.symm_range] at hx
    rw [centralHeightFlowUpperThetaRoute, Path.trans_range, Path.trans_range,
      Path.symm_range] at hx
    rcases hx with ⟨(hll | hlc) | hrl, (hlu | huc) | hru⟩
    · left
      exact Set.mem_singleton_iff.mp
        (D.centralLeftLowerBranch_inter_centralLeftUpperBranch b ▸ ⟨hll, hlu⟩)
    · have hempty : x ∈ (∅ : Set Plane) := by
        rw [← D.range_centralHeightFlowUpperConnector_inter_leftLowerBranch b,
          Set.inter_comm]
        exact ⟨hll, huc⟩
      exact hempty.elim
    · exact (Set.disjoint_left.mp
        (D.centralLeftLowerBranch_disjoint_centralRightUpperBranch b) hll hru).elim
    · have hempty : x ∈ (∅ : Set Plane) := by
        rw [← D.range_centralHeightFlowLowerConnector_inter_leftUpperBranch b]
        exact ⟨hlc, hlu⟩
      exact hempty.elim
    · exact (Set.disjoint_left.mp (D.centralHeightFlowConnectors_disjoint b) hlc huc).elim
    · have hempty : x ∈ (∅ : Set Plane) := by
        rw [← D.range_centralHeightFlowLowerConnector_inter_rightUpperBranch b]
        exact ⟨hlc, hru⟩
      exact hempty.elim
    · exact (Set.disjoint_left.mp
        (D.centralLeftUpperBranch_disjoint_centralRightLowerBranch b) hlu hrl).elim
    · have hempty : x ∈ (∅ : Set Plane) := by
        rw [← D.range_centralHeightFlowUpperConnector_inter_rightLowerBranch b,
          Set.inter_comm]
        exact ⟨hrl, huc⟩
      exact hempty.elim
    · right
      exact Set.mem_singleton_iff.mp
        (D.centralRightLowerBranch_inter_centralRightUpperBranch b ▸ ⟨hrl, hru⟩)
  · intro hx
    rcases hx with hleft | hright
    · subst x
      exact ⟨⟨0, (D.centralHeightFlowLowerThetaRoute b).source⟩,
        ⟨0, (D.centralHeightFlowUpperThetaRoute b).source⟩⟩
    · subst x
      exact ⟨⟨1, (D.centralHeightFlowLowerThetaRoute b).target⟩,
        ⟨1, (D.centralHeightFlowUpperThetaRoute b).target⟩⟩

/-- The seam and two canonical height-flow return routes. -/
def centralHeightFlowCompletedThetaPath (b : D.ConnectorBandIndex) :
    Fin 3 → Path bandLeftVertex bandRightVertex
  | 0 => bandSeamPath
  | 1 => D.centralHeightFlowLowerThetaRoute b
  | 2 => D.centralHeightFlowUpperThetaRoute b

/-- The completed height-flow theta transported to the Euclidean Schoenflies plane. -/
def centralHeightFlowCompletedPlaneThetaPath (b : D.ConnectorBandIndex) :
    Fin 3 → Path (coveringPlaneCoordinates.symm bandLeftVertex)
      (coveringPlaneCoordinates.symm bandRightVertex) :=
  fun i ↦ (D.centralHeightFlowCompletedThetaPath b i).map
    coveringPlaneCoordinates.symm.continuous

private theorem mappedHeightFlowPath_injective {a b : Plane} (p : Path a b)
    (hp : Function.Injective p) :
    Function.Injective (p.map coveringPlaneCoordinates.symm.continuous) := by
  intro u v huv
  apply hp
  apply coveringPlaneCoordinates.symm.injective
  simpa only [Path.map_coe, Function.comp_apply] using huv

private theorem mappedHeightFlowPath_range_inter {a b : Plane} (p q : Path a b)
    (hinter : Set.range p ∩ Set.range q = {a, b}) :
    Set.range (p.map coveringPlaneCoordinates.symm.continuous) ∩
        Set.range (q.map coveringPlaneCoordinates.symm.continuous) =
      {coveringPlaneCoordinates.symm a, coveringPlaneCoordinates.symm b} := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    change coveringPlaneCoordinates.symm (p u) = x at hu
    change coveringPlaneCoordinates.symm (q v) = x at hv
    have hpq : p u = q v := coveringPlaneCoordinates.symm.injective
      (hu.trans hv.symm)
    have horig : p u ∈ Set.range p ∩ Set.range q :=
      ⟨⟨u, rfl⟩, ⟨v, hpq.symm⟩⟩
    rw [hinter] at horig
    rcases horig with ha | hb
    · exact Or.inl (hu.symm.trans (congrArg coveringPlaneCoordinates.symm ha))
    · exact Or.inr (hu.symm.trans (congrArg coveringPlaneCoordinates.symm hb))
  · rintro (rfl | rfl)
    · exact ⟨⟨0, (p.map coveringPlaneCoordinates.symm.continuous).source⟩,
        ⟨0, (q.map coveringPlaneCoordinates.symm.continuous).source⟩⟩
    · exact ⟨⟨1, (p.map coveringPlaneCoordinates.symm.continuous).target⟩,
        ⟨1, (q.map coveringPlaneCoordinates.symm.continuous).target⟩⟩

theorem centralHeightFlowCompletedThetaSystem (b : D.ConnectorBandIndex) :
    ThreePathSystem (D.centralHeightFlowCompletedPlaneThetaPath b) where
  injective := by
    intro i
    fin_cases i
    · exact mappedHeightFlowPath_injective bandSeamPath bandSeamPath_injective
    · exact mappedHeightFlowPath_injective (D.centralHeightFlowLowerThetaRoute b)
        (D.centralHeightFlowLowerThetaRoute_injective b)
    · exact mappedHeightFlowPath_injective (D.centralHeightFlowUpperThetaRoute b)
        (D.centralHeightFlowUpperThetaRoute_injective b)
  range_inter := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact mappedHeightFlowPath_range_inter bandSeamPath
        (D.centralHeightFlowLowerThetaRoute b)
        (D.range_bandSeamPath_inter_centralHeightFlowLowerThetaRoute b)
    · exact mappedHeightFlowPath_range_inter bandSeamPath
        (D.centralHeightFlowUpperThetaRoute b)
        (D.range_bandSeamPath_inter_centralHeightFlowUpperThetaRoute b)
    · apply mappedHeightFlowPath_range_inter
      rw [Set.inter_comm]
      exact D.range_bandSeamPath_inter_centralHeightFlowLowerThetaRoute b
    · exact (hij rfl).elim
    · exact mappedHeightFlowPath_range_inter (D.centralHeightFlowLowerThetaRoute b)
        (D.centralHeightFlowUpperThetaRoute b)
        (D.range_centralHeightFlowLowerThetaRoute_inter_upperThetaRoute b)
    · apply mappedHeightFlowPath_range_inter
      rw [Set.inter_comm]
      exact D.range_bandSeamPath_inter_centralHeightFlowUpperThetaRoute b
    · apply mappedHeightFlowPath_range_inter
      rw [Set.inter_comm]
      exact D.range_centralHeightFlowLowerThetaRoute_inter_upperThetaRoute b
    · exact (hij rfl).elim

theorem centralHeightFlowCompletedTheta_exists_outer_cycle_decomposition
    (b : D.ConnectorBandIndex) :
    closure (D.centralHeightFlowCompletedThetaSystem b).circle01.inside =
        closure (D.centralHeightFlowCompletedThetaSystem b).circle02.inside ∪
          closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside ∨
      closure (D.centralHeightFlowCompletedThetaSystem b).circle02.inside =
        closure (D.centralHeightFlowCompletedThetaSystem b).circle01.inside ∪
          closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside ∨
      closure (D.centralHeightFlowCompletedThetaSystem b).circle12.inside =
        closure (D.centralHeightFlowCompletedThetaSystem b).circle01.inside ∪
          closure (D.centralHeightFlowCompletedThetaSystem b).circle02.inside :=
  (D.centralHeightFlowCompletedThetaSystem b).exists_outer_cycle_decomposition

/-- Package the canonical height-flow theta from a compact planar filling of its lower-upper
cycle. -/
def centralHeightFlowFilledThetaSystemData (b : D.ConnectorBandIndex)
    (R : (D.centralHeightFlowCompletedThetaSystem b).FilledOuterRegionData) :
    FilledThetaSystemData (D.centralHeightFlowCompletedPlaneThetaPath b) :=
  R.toFilledThetaSystemData

end SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData
end Submission.Topology
