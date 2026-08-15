import Submission.Topology.LocalFlatness

/-!
# A winding carrier for subsets of the transported torus

A subset of a torus can be called a genus carrier only with a precise meaning.  Here the meaning
is that it contains two complete, explicitly parametrized torus-slope loops whose winding vectors
have nonzero determinant.  This is stronger than merely not fitting in a disk and is directly
suited to the product-circle coordinates already constructed for the transported torus.

The predicate is upward monotone.  It holds for the whole transported torus, but it cannot hold
for a subset contained in one of the planar charts from `LocalFlatness`: a nonzero integral
winding traverses an entire circle, whereas the source of a real coordinate chart on a circle is
proper.  The latter fact is proved here from compactness, rather than assumed as hidden surface
classification.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Function Topology

noncomputable section

namespace Submission.Topology

open Submission.Torus

/-! ## Integral slope loops -/

/-- A point on an integral-slope loop, bundled as a point of the transported torus. -/
def transportedSlopePoint (Phi : AmbientIsotopy) (m n : ℤ)
    (phase₁ phase₂ t : ℝ) : transportedTorus Phi :=
  transportedTorusHomeomorph Phi
    (Circle.exp ((m : ℝ) * t + phase₁),
      Circle.exp ((n : ℝ) * t + phase₂))

/-- The determinant of two winding vectors in longitude-meridian coordinates. -/
def windingDet (m₁ n₁ m₂ n₂ : ℤ) : ℤ :=
  m₁ * n₂ - n₁ * m₂

/-- Concrete evidence that `s` carries both independent directions of the transported torus. -/
structure TorusCarrierWitness (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) where
  m₁ : ℤ
  n₁ : ℤ
  m₂ : ℤ
  n₂ : ℤ
  phase₁₁ : ℝ
  phase₁₂ : ℝ
  phase₂₁ : ℝ
  phase₂₂ : ℝ
  firstLoop_mem : ∀ t, transportedSlopePoint Phi m₁ n₁ phase₁₁ phase₁₂ t ∈ s
  secondLoop_mem : ∀ t, transportedSlopePoint Phi m₂ n₂ phase₂₁ phase₂₂ t ∈ s
  independent : windingDet m₁ n₁ m₂ n₂ ≠ 0

/-- A mathematically explicit genus-carrier predicate: the subset contains two torus-slope loops
with linearly independent integral winding vectors. -/
def CarriesTorusGenus (Phi : AmbientIsotopy)
    (s : Set (transportedTorus Phi)) : Prop :=
  Nonempty (TorusCarrierWitness Phi s)

/-! ## Monotonicity -/

/-- A winding carrier remains a carrier after enlarging the subset. -/
def TorusCarrierWitness.mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (W : TorusCarrierWitness Phi s)
    (hst : s ⊆ t) : TorusCarrierWitness Phi t where
  m₁ := W.m₁
  n₁ := W.n₁
  m₂ := W.m₂
  n₂ := W.n₂
  phase₁₁ := W.phase₁₁
  phase₁₂ := W.phase₁₂
  phase₂₁ := W.phase₂₁
  phase₂₂ := W.phase₂₂
  firstLoop_mem u := hst (W.firstLoop_mem u)
  secondLoop_mem u := hst (W.secondLoop_mem u)
  independent := W.independent

/-- Exact upward monotonicity used for nested regions. -/
theorem CarriesTorusGenus.mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (hs : CarriesTorusGenus Phi s) : CarriesTorusGenus Phi t := by
  obtain ⟨W⟩ := hs
  exact ⟨W.mono hst⟩

/-- Contrapositive monotonicity: every subset of a noncarrier is a noncarrier. -/
theorem not_carriesTorusGenus_mono {Phi : AmbientIsotopy}
    {s t : Set (transportedTorus Phi)} (hst : s ⊆ t)
    (ht : ¬ CarriesTorusGenus Phi t) : ¬ CarriesTorusGenus Phi s :=
  fun hs ↦ ht (hs.mono hst)

/-- Along a decreasing family, carrier status can only propagate toward the larger, earlier
sets. -/
theorem carriesTorusGenus_of_antitone {Phi : AmbientIsotopy}
    {I : Type*} [Preorder I] (s : I → Set (transportedTorus Phi))
    (hs : Antitone s) {i j : I} (hij : i ≤ j)
    (hj : CarriesTorusGenus Phi (s j)) : CarriesTorusGenus Phi (s i) :=
  hj.mono (hs hij)

/-! ## The whole torus carries two independent directions -/

/-- The longitude and meridian give determinant-one carrier data for the whole torus. -/
theorem univ_carriesTorusGenus (Phi : AmbientIsotopy) :
    CarriesTorusGenus Phi Set.univ := by
  refine ⟨{
    m₁ := 1
    n₁ := 0
    m₂ := 0
    n₂ := 1
    phase₁₁ := 0
    phase₁₂ := 0
    phase₂₁ := 0
    phase₂₂ := 0
    firstLoop_mem := fun _ ↦ mem_univ _
    secondLoop_mem := fun _ ↦ mem_univ _
    independent := by norm_num [windingDet]
  }⟩

/-! ## A slope loop cannot fit in one product chart -/

/-- No chosen circle chart covers the whole circle.  Indeed, a global source would make its
open target both compact and nonempty; connectedness of `ℝ` would then make the target all of
`ℝ`, contradicting that `ℝ` is unbounded. -/
theorem circleChartAt_source_ne_univ (z : Circle) :
    (circleChartAt z).source ≠ Set.univ := by
  intro hsource
  have hcontinuous : Continuous (circleChartAt z) := by
    rw [← continuousOn_univ]
    simpa only [hsource] using (circleChartAt z).continuousOn
  have htargetcompact : IsCompact (circleChartAt z).target := by
    rw [← (circleChartAt z).image_source_eq_target, hsource, image_univ]
    exact isCompact_range hcontinuous
  have htargetuniv : (circleChartAt z).target = Set.univ :=
    IsClopen.eq_univ
      ⟨htargetcompact.isClosed, (circleChartAt z).open_target⟩
      ⟨circleChartAt z z,
        (circleChartAt z).map_source (by rw [hsource]; exact mem_univ z)⟩
  apply (not_bddAbove_univ (α := ℝ))
  rw [← htargetuniv]
  exact htargetcompact.bddAbove

/-- Every nonzero integral angular slope traverses the entire circle. -/
theorem circleExp_intAffine_surjective (n : ℤ) (hn : n ≠ 0) (phase : ℝ) :
    Function.Surjective (fun t : ℝ ↦ Circle.exp ((n : ℝ) * t + phase)) := by
  intro z
  obtain ⟨theta, rfl⟩ := Circle.exp_surjective z
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨(theta - phase) / (n : ℝ), ?_⟩
  change Circle.exp ((n : ℝ) * ((theta - phase) / (n : ℝ)) + phase) =
    Circle.exp theta
  congr 1
  field_simp
  ring

/-- If a complete integral-slope circle path lies in one real circle chart, its winding is zero. -/
theorem winding_eq_zero_of_forall_mem_circleChartAt_source
    (z : Circle) (n : ℤ) (phase : ℝ)
    (h : ∀ t : ℝ,
      Circle.exp ((n : ℝ) * t + phase) ∈ (circleChartAt z).source) :
    n = 0 := by
  by_contra hn
  apply circleChartAt_source_ne_univ z
  rw [eq_univ_iff_forall]
  intro w
  obtain ⟨t, rfl⟩ := circleExp_intAffine_surjective n hn phase w
  exact h t

/-- A complete slope loop contained in one transported-torus chart has zero winding in both
circle coordinates. -/
theorem windings_eq_zero_of_forall_mem_transportedTorusChart_source
    (Phi : AmbientIsotopy) (x : transportedTorus Phi)
    (m n : ℤ) (phase₁ phase₂ : ℝ)
    (h : ∀ t : ℝ, transportedSlopePoint Phi m n phase₁ phase₂ t ∈
      (transportedTorusChart Phi x).source) :
    m = 0 ∧ n = 0 := by
  let center := (transportedTorusHomeomorph Phi).symm x
  have hfirst : ∀ t : ℝ, Circle.exp ((m : ℝ) * t + phase₁) ∈
      (circleChartAt center.1).source := by
    intro t
    have ht := h t
    rw [transportedTorusChart, OpenPartialHomeomorph.trans_source] at ht
    have hp := ht.2
    rw [circleProductChartAt, OpenPartialHomeomorph.prod_source] at hp
    simpa only [transportedSlopePoint, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.symm_apply_apply] using hp.1
  have hsecond : ∀ t : ℝ, Circle.exp ((n : ℝ) * t + phase₂) ∈
      (circleChartAt center.2).source := by
    intro t
    have ht := h t
    rw [transportedTorusChart, OpenPartialHomeomorph.trans_source] at ht
    have hp := ht.2
    rw [circleProductChartAt, OpenPartialHomeomorph.prod_source] at hp
    simpa only [transportedSlopePoint, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.symm_apply_apply] using hp.2
  exact ⟨winding_eq_zero_of_forall_mem_circleChartAt_source center.1 m phase₁ hfirst,
    winding_eq_zero_of_forall_mem_circleChartAt_source center.2 n phase₂ hsecond⟩

/-- A subset contained in one local planar chart cannot carry two independent torus windings. -/
theorem not_carriesTorusGenus_of_subset_transportedTorusChart_source
    (Phi : AmbientIsotopy) (s : Set (transportedTorus Phi))
    (x : transportedTorus Phi)
    (hs : s ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesTorusGenus Phi s := by
  rintro ⟨W⟩
  obtain ⟨hm₁, hn₁⟩ :=
    windings_eq_zero_of_forall_mem_transportedTorusChart_source
      Phi x W.m₁ W.n₁ W.phase₁₁ W.phase₁₂
      (fun t ↦ hs (W.firstLoop_mem t))
  obtain ⟨hm₂, hn₂⟩ :=
    windings_eq_zero_of_forall_mem_transportedTorusChart_source
      Phi x W.m₂ W.n₂ W.phase₂₁ W.phase₂₂
      (fun t ↦ hs (W.secondLoop_mem t))
  exact W.independent (by simp [windingDet, hm₁, hn₁, hm₂, hn₂])

/-- There is one positive radius such that every subset of any surface ball of that radius is a
noncarrier.  This is the form directly applicable after bounding the diameter of a box piece. -/
theorem exists_uniform_pos_ball_noncarrier
    (Phi : AmbientIsotopy) :
    ∃ δ > 0, ∀ (y : transportedTorus Phi) (s : Set (transportedTorus Phi)),
      s ⊆ Metric.ball y δ → ¬ CarriesTorusGenus Phi s := by
  obtain ⟨δ, hδ, hchart⟩ :=
    exists_uniform_pos_ball_subset_transportedTorusChart_source Phi
  refine ⟨δ, hδ, ?_⟩
  intro y s hs
  obtain ⟨x, hball⟩ := hchart y
  exact not_carriesTorusGenus_of_subset_transportedTorusChart_source
    Phi s x (hs.trans hball)

/-! ## Ambient regions -/

/-- The part of an ambient set lying on the transported torus, represented in the surface
subtype. -/
def transportedTorusPart (Phi : AmbientIsotopy) (a : Set R3) :
    Set (transportedTorus Phi) :=
  Subtype.val ⁻¹' a

/-- An ambient region carries torus genus when its intersection with the transported torus
contains a winding carrier. -/
def CarriesTransportedTorusGenus (Phi : AmbientIsotopy) (a : Set R3) : Prop :=
  CarriesTorusGenus Phi (transportedTorusPart Phi a)

/-- Ambient-set monotonicity, suitable for nested boxes. -/
theorem CarriesTransportedTorusGenus.mono {Phi : AmbientIsotopy}
    {a b : Set R3} (hab : a ⊆ b) (ha : CarriesTransportedTorusGenus Phi a) :
    CarriesTransportedTorusGenus Phi b :=
  CarriesTorusGenus.mono (preimage_mono hab) ha

/-- Ambient contrapositive monotonicity: a subset of a noncarrying region does not carry. -/
theorem not_carriesTransportedTorusGenus_mono {Phi : AmbientIsotopy}
    {a b : Set R3} (hab : a ⊆ b) (hb : ¬ CarriesTransportedTorusGenus Phi b) :
    ¬ CarriesTransportedTorusGenus Phi a :=
  fun ha ↦ hb (CarriesTransportedTorusGenus.mono hab ha)

/-- For nested ambient boxes, a smaller box carrying genus forces every containing earlier box
to carry genus. -/
theorem carriesTransportedTorusGenus_of_antitone
    {Phi : AmbientIsotopy} {I : Type*} [Preorder I]
    (a : I → Set R3) (ha : Antitone a) {i j : I} (hij : i ≤ j)
    (hj : CarriesTransportedTorusGenus Phi (a j)) :
    CarriesTransportedTorusGenus Phi (a i) :=
  CarriesTransportedTorusGenus.mono (ha hij) hj

/-- The transported torus, regarded as an ambient subset, carries its longitude and meridian. -/
theorem transportedTorus_carriesTransportedTorusGenus (Phi : AmbientIsotopy) :
    CarriesTransportedTorusGenus Phi (transportedTorus Phi) := by
  apply (univ_carriesTorusGenus Phi).mono
  intro x _
  exact x.property

/-- An ambient region whose torus part lies in one local planar chart is not a carrier. -/
theorem not_carriesTransportedTorusGenus_of_part_subset_chart
    (Phi : AmbientIsotopy) (a : Set R3) (x : transportedTorus Phi)
    (ha : transportedTorusPart Phi a ⊆ (transportedTorusChart Phi x).source) :
    ¬ CarriesTransportedTorusGenus Phi a :=
  not_carriesTorusGenus_of_subset_transportedTorusChart_source Phi _ x ha

end Submission.Topology
