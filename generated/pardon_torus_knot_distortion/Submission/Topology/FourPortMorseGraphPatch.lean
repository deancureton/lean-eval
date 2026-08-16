import Submission.Torus.NormalTube

/-!
# The local four-port Morse graph in the transported-torus collar

This module is deliberately independent of any global strip decomposition.
It gives the fixed local model used at one four-port switch.  On the quadratic
disk `Q`, the functions `x² - 1` and `1 - y²` agree on the frontier.  Their
linear interpolation changes the torus intersection from two vertical arcs
to two horizontal arcs through one saddle graph, while every ambient graph
remains embedded in the explicit transported-torus normal tube.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-- The elementary coordinate plane for the four-port model. -/
abbrev FourPortPlane := ℝ × ℝ

/-- Squared Euclidean coordinate radius.  We use this polynomial rather than
the product metric's closed ball. -/
def fourPortRadiusSq (u : FourPortPlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- The closed quadratic disk supporting the local switch. -/
def fourPortQuadraticRegion : Set FourPortPlane :=
  {u | fourPortRadiusSq u ≤ 2}

/-- The compact parameter disk as a type. -/
abbrev FourPortQuadraticDisk := fourPortQuadraticRegion

theorem continuous_fourPortRadiusSq : Continuous fourPortRadiusSq := by
  unfold fourPortRadiusSq
  fun_prop

theorem isClosed_fourPortQuadraticRegion :
    IsClosed fourPortQuadraticRegion := by
  exact isClosed_le continuous_fourPortRadiusSq continuous_const

theorem fourPortQuadraticRegion_subset_square :
    fourPortQuadraticRegion ⊆
      Icc (-(2 : ℝ)) 2 ×ˢ Icc (-(2 : ℝ)) 2 := by
  rintro ⟨x, y⟩ hxy
  change x ^ 2 + y ^ 2 ≤ 2 at hxy
  constructor <;> constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

theorem isCompact_fourPortQuadraticRegion :
    IsCompact fourPortQuadraticRegion :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    isClosed_fourPortQuadraticRegion fourPortQuadraticRegion_subset_square

instance : CompactSpace FourPortQuadraticDisk :=
  isCompact_iff_compactSpace.mp isCompact_fourPortQuadraticRegion

/-- Initial graph height: its zero set is the two vertical ports. -/
def fourPortVerticalHeight (u : FourPortPlane) : ℝ :=
  u.1 ^ 2 - 1

/-- Final graph height: its zero set is the two horizontal ports. -/
def fourPortHorizontalHeight (u : FourPortPlane) : ℝ :=
  1 - u.2 ^ 2

/-- Linear Morse interpolation between the two resolutions. -/
def fourPortMorseHeight (t : ℝ) (u : FourPortPlane) : ℝ :=
  (1 - t) * fourPortVerticalHeight u + t * fourPortHorizontalHeight u

theorem continuous_fourPortMorseHeight (t : ℝ) :
    Continuous (fourPortMorseHeight t) := by
  unfold fourPortMorseHeight fourPortVerticalHeight fourPortHorizontalHeight
  fun_prop

@[simp]
theorem fourPortMorseHeight_zero (u : FourPortPlane) :
    fourPortMorseHeight 0 u = fourPortVerticalHeight u := by
  simp [fourPortMorseHeight]

@[simp]
theorem fourPortMorseHeight_one (u : FourPortPlane) :
    fourPortMorseHeight 1 u = fourPortHorizontalHeight u := by
  simp [fourPortMorseHeight]

theorem fourPortMorseHeight_half (u : FourPortPlane) :
    fourPortMorseHeight (1 / 2) u = (u.1 ^ 2 - u.2 ^ 2) / 2 := by
  simp [fourPortMorseHeight, fourPortVerticalHeight,
    fourPortHorizontalHeight]
  ring

/-- On the boundary of the quadratic disk, the two endpoint graphs agree. -/
theorem fourPortVerticalHeight_eq_horizontalHeight_of_mem_frontier
    {u : FourPortPlane} (hu : u ∈ frontier fourPortQuadraticRegion) :
    fourPortVerticalHeight u = fourPortHorizontalHeight u := by
  have hlevel := frontier_le_subset_eq continuous_fourPortRadiusSq
    continuous_const hu
  change fourPortRadiusSq u = 2 at hlevel
  change u.1 ^ 2 + u.2 ^ 2 = 2 at hlevel
  simp only [fourPortVerticalHeight, fourPortHorizontalHeight]
  linarith

/-- Every interpolating graph is fixed on the frontier. -/
theorem fourPortMorseHeight_eq_verticalHeight_of_mem_frontier
    (t : ℝ) {u : FourPortPlane}
    (hu : u ∈ frontier fourPortQuadraticRegion) :
    fourPortMorseHeight t u = fourPortVerticalHeight u := by
  rw [fourPortMorseHeight,
    fourPortVerticalHeight_eq_horizontalHeight_of_mem_frontier hu]
  ring

theorem fourPortMorseHeight_frontier_eqOn (t : ℝ) :
    Set.EqOn (fourPortMorseHeight t) fourPortVerticalHeight
      (frontier fourPortQuadraticRegion) :=
  fun _ hu ↦ fourPortMorseHeight_eq_verticalHeight_of_mem_frontier t hu

theorem fourPortVerticalHeight_eq_zero_iff (u : FourPortPlane) :
    fourPortVerticalHeight u = 0 ↔ u.1 = 1 ∨ u.1 = -1 := by
  have hsquare : fourPortVerticalHeight u = 0 ↔ u.1 ^ 2 = 1 := by
    simp only [fourPortVerticalHeight]
    constructor <;> intro h <;> linarith
  rw [hsquare, sq_eq_one_iff]

theorem fourPortHorizontalHeight_eq_zero_iff (u : FourPortPlane) :
    fourPortHorizontalHeight u = 0 ↔ u.2 = 1 ∨ u.2 = -1 := by
  have hsquare : fourPortHorizontalHeight u = 0 ↔ u.2 ^ 2 = 1 := by
    simp only [fourPortHorizontalHeight]
    constructor <;> intro h <;> linarith
  rw [hsquare, sq_eq_one_iff]

/-- Exact two-vertical-segment carrier. -/
def fourPortVerticalCarrier : Set FourPortPlane :=
  {u | (u.1 = 1 ∨ u.1 = -1) ∧ u.2 ∈ Icc (-(1 : ℝ)) 1}

/-- Exact two-horizontal-segment carrier. -/
def fourPortHorizontalCarrier : Set FourPortPlane :=
  {u | (u.2 = 1 ∨ u.2 = -1) ∧ u.1 ∈ Icc (-(1 : ℝ)) 1}

theorem mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff
    (u : FourPortPlane) :
    u ∈ fourPortQuadraticRegion ∧ fourPortVerticalHeight u = 0 ↔
      u ∈ fourPortVerticalCarrier := by
  rcases u with ⟨x, y⟩
  simp only [fourPortQuadraticRegion, Set.mem_ofPred_eq, fourPortRadiusSq,
    fourPortVerticalHeight_eq_zero_iff, fourPortVerticalCarrier,
    mem_Icc]
  constructor
  · rintro ⟨hQ, hx⟩
    refine ⟨hx, ?_⟩
    rcases hx with rfl | rfl <;> constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    refine ⟨?_, hx⟩
    rcases hx with rfl | rfl <;> nlinarith [mul_nonneg (sub_nonneg.mpr hy.1)
      (sub_nonneg.mpr hy.2)]

theorem mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff
    (u : FourPortPlane) :
    u ∈ fourPortQuadraticRegion ∧ fourPortHorizontalHeight u = 0 ↔
      u ∈ fourPortHorizontalCarrier := by
  rcases u with ⟨x, y⟩
  simp only [fourPortQuadraticRegion, Set.mem_ofPred_eq, fourPortRadiusSq,
    fourPortHorizontalHeight_eq_zero_iff, fourPortHorizontalCarrier,
    mem_Icc]
  constructor
  · rintro ⟨hQ, hy⟩
    refine ⟨hy, ?_⟩
    rcases hy with rfl | rfl <;> constructor <;> nlinarith
  · rintro ⟨hy, hx⟩
    refine ⟨?_, hy⟩
    rcases hy with rfl | rfl <;> nlinarith [mul_nonneg (sub_nonneg.mpr hx.1)
      (sub_nonneg.mpr hx.2)]

theorem fourPort_vertical_zeroSet_exact :
    fourPortQuadraticRegion ∩ fourPortVerticalHeight ⁻¹' {0} =
      fourPortVerticalCarrier := by
  ext u
  simpa only [mem_inter_iff, mem_preimage, mem_singleton_iff] using
    mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u

theorem fourPort_horizontal_zeroSet_exact :
    fourPortQuadraticRegion ∩ fourPortHorizontalHeight ⁻¹' {0} =
      fourPortHorizontalCarrier := by
  ext u
  simpa only [mem_inter_iff, mem_preimage, mem_singleton_iff] using
    mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u

/-! ## Embedding the graph in the explicit transported-torus tube -/

/-- Shift the small quadratic disk into one fundamental angular square. -/
def fourPortTorusBaseMap (u : FourPortQuadraticDisk) : Circle × Circle :=
  (Circle.exp (u.1.1 + 2), Circle.exp (u.1.2 + 2))

private theorem fourPort_first_shift_mem_Ico (u : FourPortQuadraticDisk) :
    u.1.1 + 2 ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hu := u.property
  change u.1.1 ^ 2 + u.1.2 ^ 2 ≤ 2 at hu
  constructor
  · nlinarith [sq_nonneg u.1.2]
  · nlinarith [sq_nonneg u.1.2, Real.pi_gt_three]

private theorem fourPort_second_shift_mem_Ico (u : FourPortQuadraticDisk) :
    u.1.2 + 2 ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hu := u.property
  change u.1.1 ^ 2 + u.1.2 ^ 2 ≤ 2 at hu
  constructor
  · nlinarith [sq_nonneg u.1.1]
  · nlinarith [sq_nonneg u.1.1, Real.pi_gt_three]

theorem fourPortTorusBaseMap_continuous :
    Continuous fourPortTorusBaseMap := by
  unfold fourPortTorusBaseMap
  fun_prop

theorem fourPortTorusBaseMap_injective :
    Function.Injective fourPortTorusBaseMap := by
  intro u v huv
  have hfirst : Circle.exp (u.1.1 + 2) = Circle.exp (v.1.1 + 2) :=
    congrArg Prod.fst huv
  have hsecond : Circle.exp (u.1.2 + 2) = Circle.exp (v.1.2 + 2) :=
    congrArg Prod.snd huv
  have hfirstArg : u.1.1 + 2 = v.1.1 + 2 :=
    Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      (fourPort_first_shift_mem_Ico u) (fourPort_first_shift_mem_Ico v) hfirst
  have hsecondArg : u.1.2 + 2 = v.1.2 + 2 :=
    Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      (fourPort_second_shift_mem_Ico u) (fourPort_second_shift_mem_Ico v) hsecond
  apply Subtype.ext
  exact Prod.ext (by linarith) (by linarith)

theorem fourPortTorusBaseMap_isClosedEmbedding :
    Topology.IsClosedEmbedding fourPortTorusBaseMap :=
  fourPortTorusBaseMap_continuous.isClosedEmbedding
    fourPortTorusBaseMap_injective

/-- Time interval for the local Morse switch. -/
abbrev FourPortMorseTime := Set.Icc (0 : ℝ) 1

theorem fourPortMorseHeight_mem_Icc (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) :
    fourPortMorseHeight t u.1 ∈ Icc (-(1 : ℝ)) 1 := by
  have hu := u.property
  change u.1.1 ^ 2 + u.1.2 ^ 2 ≤ 2 at hu
  have hp : fourPortVerticalHeight u.1 ∈ Icc (-(1 : ℝ)) 1 := by
    simp only [fourPortVerticalHeight, mem_Icc]
    constructor <;> nlinarith [sq_nonneg u.1.1, sq_nonneg u.1.2]
  have hs : fourPortHorizontalHeight u.1 ∈ Icc (-(1 : ℝ)) 1 := by
    simp only [fourPortHorizontalHeight, mem_Icc]
    constructor <;> nlinarith [sq_nonneg u.1.1, sq_nonneg u.1.2]
  simp only [fourPortMorseHeight, mem_Icc]
  constructor <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hp.1),
      mul_nonneg t.property.1 (sub_nonneg.mpr hs.1),
      mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hp.2),
      mul_nonneg t.property.1 (sub_nonneg.mpr hs.2)]

/-- The graph's signed normal coordinate, scaled into the half-width tube. -/
def fourPortNormalCoordinate (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) :
    Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  ⟨(1 / 4 : ℝ) * fourPortMorseHeight t u.1, by
    have h := fourPortMorseHeight_mem_Icc t u
    constructor <;> nlinarith [h.1, h.2]⟩

/-- Tube coordinates of one interpolating graph. -/
def fourPortTubeCoordinates (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) : StandardTorusNormalTube :=
  (fourPortTorusBaseMap u, fourPortNormalCoordinate t u)

theorem fourPortTubeCoordinates_continuous (t : FourPortMorseTime) :
    Continuous (fourPortTubeCoordinates t) := by
  apply fourPortTorusBaseMap_continuous.prodMk
  apply Continuous.subtype_mk
  exact (continuous_const.mul <|
    (continuous_fourPortMorseHeight t).comp continuous_subtype_val)

theorem fourPortTubeCoordinates_injective (t : FourPortMorseTime) :
    Function.Injective (fourPortTubeCoordinates t) := by
  intro u v huv
  apply fourPortTorusBaseMap_injective
  exact congrArg Prod.fst huv

theorem fourPortTubeCoordinates_isClosedEmbedding (t : FourPortMorseTime) :
    Topology.IsClosedEmbedding (fourPortTubeCoordinates t) :=
  (fourPortTubeCoordinates_continuous t).isClosedEmbedding
    (fourPortTubeCoordinates_injective t)

/-- The ambient graph inside the transported-torus normal collar. -/
def fourPortMorseGraph (Phi : AmbientIsotopy) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) : R3 :=
  transportedTorusNormalTubeMap Phi (fourPortTubeCoordinates t u)

theorem fourPortMorseGraph_isEmbedding (Phi : AmbientIsotopy)
    (t : FourPortMorseTime) :
    Topology.IsEmbedding (fourPortMorseGraph Phi t) :=
  (transportedTorusNormalTubeMap_isEmbedding Phi).comp
    (fourPortTubeCoordinates_isClosedEmbedding t).isEmbedding

/-- The ambient graph meets the transported torus exactly at the zero set of
the interpolating Morse height. -/
theorem fourPortMorseGraph_mem_transportedTorus_iff
    (Phi : AmbientIsotopy) (t : FourPortMorseTime)
    (u : FourPortQuadraticDisk) :
    fourPortMorseGraph Phi t u ∈ transportedTorus Phi ↔
      fourPortMorseHeight t u.1 = 0 := by
  rw [fourPortMorseGraph,
    transportedTorusNormalTubeMap_mem_transportedTorus_iff]
  rw [Subtype.ext_iff]
  change ((1 / 4 : ℝ) * fourPortMorseHeight t u.1 : ℝ) = 0 ↔ _
  norm_num

/-- At time zero the torus intersection is exactly the vertical carrier. -/
theorem fourPortMorseGraph_zero_mem_transportedTorus_iff
    (Phi : AmbientIsotopy) (u : FourPortQuadraticDisk) :
    fourPortMorseGraph Phi ⟨0, by norm_num⟩ u ∈ transportedTorus Phi ↔
      u.1 ∈ fourPortVerticalCarrier := by
  rw [fourPortMorseGraph_mem_transportedTorus_iff,
    fourPortMorseHeight_zero]
  constructor
  · intro h
    exact (mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u.1).mp
      ⟨u.property, h⟩
  · intro h
    exact ((mem_fourPortQuadraticRegion_and_verticalHeight_zero_iff u.1).mpr h).2

/-- At time one the torus intersection is exactly the horizontal carrier. -/
theorem fourPortMorseGraph_one_mem_transportedTorus_iff
    (Phi : AmbientIsotopy) (u : FourPortQuadraticDisk) :
    fourPortMorseGraph Phi ⟨1, by norm_num⟩ u ∈ transportedTorus Phi ↔
      u.1 ∈ fourPortHorizontalCarrier := by
  rw [fourPortMorseGraph_mem_transportedTorus_iff,
    fourPortMorseHeight_one]
  constructor
  · intro h
    exact (mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u.1).mp
      ⟨u.property, h⟩
  · intro h
    exact ((mem_fourPortQuadraticRegion_and_horizontalHeight_zero_iff u.1).mpr h).2

end Submission.Topology
