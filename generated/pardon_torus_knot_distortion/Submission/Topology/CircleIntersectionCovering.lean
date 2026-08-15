import Submission.Topology.TransverseBranchIFT

/-!
# Compact circle-parameter intersection loci

Both curve parameters are bundled as `Circle`.  Consequently the total
intersection locus of a homotopy is a closed subset of the compact space
`[0,1] × Circle × Circle`; there is no half-open fundamental-domain seam.
Local transversality is recorded as the local-homeomorphism conclusion of the
circle-chart implicit-function theorem.  Compactness then upgrades the time
projection to a covering map, whose monodromy matches endpoint fibers.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-- The `(p,q)` curve intrinsically parameterized by the source circle. -/
def circleTorusKnot (p q : ℕ) (z : Circle) : Circle × Circle :=
  (z ^ p, z ^ q)

lemma continuous_circleTorusKnot (p q : ℕ) :
    Continuous (circleTorusKnot p q) := by
  unfold circleTorusKnot
  fun_prop

lemma circle_exp_nat_mul (n : ℕ) (t : ℝ) :
    Circle.exp ((n : ℝ) * t) = Circle.exp t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Circle.exp_add, pow_succ, ih]
      simp

lemma torusKnotLift_eq_circleTorusKnot_exp (p q : ℕ) (t : ℝ) :
    Submission.Torus.torusKnotLift p q t =
      circleTorusKnot p q (Circle.exp t) := by
  apply Prod.ext
  · exact circle_exp_nat_mul p t
  · exact circle_exp_nat_mul q t

/-- Knot parameters intrinsically on the source circle. -/
def circleLoopIntersectionParameters (p q : ℕ)
    (beta : Circle → Circle × Circle) : Set Circle :=
  {z | circleTorusKnot p q z ∈ Set.range beta}

lemma range_circle_parametrization (beta : Circle → Circle × Circle) :
    Set.range (fun t : ℝ ↦ beta (Circle.exp t)) = Set.range beta := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp t, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := Circle.exp_surjective w
    exact ⟨t, congrArg beta ht⟩

theorem real_intersectionParameters_iff_circle
    (p q : ℕ) (beta : Circle → Circle × Circle) (t : ℝ) :
    t ∈ torusLoopIntersectionParameters p q
        (fun u ↦ beta (Circle.exp u)) ↔
      t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
        Circle.exp t ∈ circleLoopIntersectionParameters p q beta := by
  unfold torusLoopIntersectionParameters circleLoopIntersectionParameters
  change (t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
    Submission.Torus.torusKnotLift p q t ∈
      Set.range (fun u ↦ beta (Circle.exp u))) ↔
    t ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
      circleTorusKnot p q (Circle.exp t) ∈ Set.range beta
  rw [torusKnotLift_eq_circleTorusKnot_exp,
    range_circle_parametrization]

/-- Triples `(s,a,b)` for which knot parameter `a` and loop parameter `b`
give the same point at homotopy time `s`. -/
abbrev circleIntersectionLocus (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle) : Type :=
  {z : unitInterval × (Circle × Circle) //
    circleTorusKnot p q z.2.1 = H z.1 z.2.2}

def circleIntersectionProjection {p q : ℕ}
    {H : ℝ → Circle → Circle × Circle} :
    circleIntersectionLocus p q H → unitInterval :=
  fun z ↦ z.1.1

theorem isClosed_circleIntersectionPredicate
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (hH : Continuous (Function.uncurry H)) :
    IsClosed {z : unitInterval × (Circle × Circle) |
      circleTorusKnot p q z.2.1 = H z.1 z.2.2} := by
  apply isClosed_eq
  · have ha : Continuous
        (fun z : unitInterval × (Circle × Circle) ↦ z.2.1) := by fun_prop
    exact (continuous_circleTorusKnot p q).comp ha
  · have hsb : Continuous
        (fun z : unitInterval × (Circle × Circle) ↦ ((z.1 : ℝ), z.2.2)) := by
      fun_prop
    exact hH.comp hsb

theorem isCompact_circleIntersectionPredicate
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (hH : Continuous (Function.uncurry H)) :
    IsCompact {z : unitInterval × (Circle × Circle) |
      circleTorusKnot p q z.2.1 = H z.1 z.2.2} :=
  (isClosed_circleIntersectionPredicate p q H hH).isCompact

/-- The compact intersection locus carries a canonical compact-space
instance, used locally to invoke the compact local-homeomorphism theorem. -/
theorem circleIntersectionLocusCompactSpace
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (hH : Continuous (Function.uncurry H)) :
    CompactSpace (circleIntersectionLocus p q H) :=
  (isClosed_circleIntersectionPredicate p q H hH).isClosedEmbedding_subtypeVal.compactSpace

/-- The exact global output of circle-chart transversality: local graph charts
for the compact zero locus make time projection a covering. -/
theorem circleIntersectionProjection_isCovering
    (p q : ℕ) (H : ℝ → Circle → Circle × Circle)
    (hH : Continuous (Function.uncurry H))
    (hlocal : IsLocalHomeomorph
      (circleIntersectionProjection (p := p) (q := q) (H := H))) :
    IsCoveringMap
      (circleIntersectionProjection (p := p) (q := q) (H := H)) := by
  let _ : CompactSpace (circleIntersectionLocus p q H) :=
    circleIntersectionLocusCompactSpace p q H hH
  exact isLocalHomeomorph_iff_isCoveringMap.mp hlocal

/-- An explicit, honest transversality package.  In local angular charts,
`regularZero_localGraphs` proves `local_graph`; the chart compatibility step
is precisely the `isLocalHomeomorph_projection` field. -/
structure CircleIntersectionTransversality (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle) where
  continuous_homotopy : Continuous (Function.uncurry H)
  isLocalHomeomorph_projection : IsLocalHomeomorph
    (circleIntersectionProjection (p := p) (q := q) (H := H))

theorem CircleIntersectionTransversality.covering
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (T : CircleIntersectionTransversality p q H) :
    IsCoveringMap
      (circleIntersectionProjection (p := p) (q := q) (H := H)) :=
  circleIntersectionProjection_isCovering p q H T.continuous_homotopy
    T.isLocalHomeomorph_projection

/-- Monodromy of the compact circle intersection locus gives a bijection of
the endpoint fibers without choosing a cut in either circle parameter. -/
def CircleIntersectionTransversality.endpointTransport
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (T : CircleIntersectionTransversality p q H) :
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)}) →
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)}) :=
  T.covering.monodromy (.mk unitIntervalIdentityPath)

lemma CircleIntersectionTransversality.endpointTransport_bijective
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (T : CircleIntersectionTransversality p q H) :
    Function.Bijective T.endpointTransport :=
  T.covering.monodromy_bijective (.mk unitIntervalIdentityPath)

/-! ## Returning finite circle parameters to one real period -/

/-- The canonical representative in `[0,2π)` of a circle point. -/
def circlePhaseRepresentative (z : Circle) : ℝ :=
  if (z : ℂ).arg < 0 then (z : ℂ).arg + 2 * Real.pi else (z : ℂ).arg

lemma circlePhaseRepresentative_mem (z : Circle) :
    circlePhaseRepresentative z ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  unfold circlePhaseRepresentative
  split_ifs with harg
  · constructor
    · nlinarith [Complex.neg_pi_lt_arg (z : ℂ), Real.pi_pos]
    · linarith
  · constructor
    · exact le_of_not_gt harg
    · nlinarith [Complex.arg_le_pi (z : ℂ), Real.pi_pos]

lemma exp_circlePhaseRepresentative (z : Circle) :
    Circle.exp (circlePhaseRepresentative z) = z := by
  unfold circlePhaseRepresentative
  split_ifs
  · calc
      Circle.exp ((z : ℂ).arg + 2 * Real.pi) =
          Circle.exp ((z : ℂ).arg) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨1, by ring⟩
      _ = z := Circle.exp_arg z
  · exact Circle.exp_arg z

lemma circlePhaseRepresentative_injective :
    Function.Injective circlePhaseRepresentative := by
  intro z w hzw
  have hexp := congrArg Circle.exp hzw
  simpa only [exp_circlePhaseRepresentative] using hexp

lemma circlePhaseRepresentative_exp_of_mem_Ico {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    circlePhaseRepresentative (Circle.exp t) = t := by
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    (circlePhaseRepresentative_mem _) ht
  rw [exp_circlePhaseRepresentative]

/-- Set-level equivalence between intrinsic circle knot parameters and the
legacy real parameters in one half-open period.  The half-open interval is now
used only as a finite output encoding, never as the topology of the locus. -/
def circleParameterEquivReal
    (p q : ℕ) (beta : Circle → Circle × Circle) :
    {z // z ∈ circleLoopIntersectionParameters p q beta} ≃
      {t // t ∈ torusLoopIntersectionParameters p q
        (fun u ↦ beta (Circle.exp u))} where
  toFun z := ⟨circlePhaseRepresentative z.1, by
    apply (real_intersectionParameters_iff_circle p q beta _).2
    exact ⟨circlePhaseRepresentative_mem z.1, by
      simpa only [exp_circlePhaseRepresentative] using z.2⟩⟩
  invFun t := ⟨Circle.exp t.1,
    (real_intersectionParameters_iff_circle p q beta t.1).1 t.2 |>.2⟩
  left_inv z := by
    apply Subtype.ext
    exact exp_circlePhaseRepresentative z.1
  right_inv t := by
    apply Subtype.ext
    exact circlePhaseRepresentative_exp_of_mem_Ico
      ((real_intersectionParameters_iff_circle p q beta t.1).1 t.2).1

def circleFinsetToReal (S : Finset Circle) : Finset ℝ :=
  S.image circlePhaseRepresentative

lemma circleFinsetToReal_card (S : Finset Circle) :
    (circleFinsetToReal S).card = S.card := by
  rw [circleFinsetToReal, Finset.card_image_iff.mpr]
  exact circlePhaseRepresentative_injective.injOn

theorem coe_circleFinsetToReal_eq_realIntersection
    (p q : ℕ) (beta : Circle → Circle × Circle) (S : Finset Circle)
    (hS : (S : Set Circle) = circleLoopIntersectionParameters p q beta) :
    (circleFinsetToReal S : Set ℝ) =
      torusLoopIntersectionParameters p q
        (fun u ↦ beta (Circle.exp u)) := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_coe, circleFinsetToReal, Finset.mem_image] at ht
    obtain ⟨z, hzS, rfl⟩ := ht
    apply (real_intersectionParameters_iff_circle p q beta _).2
    exact ⟨circlePhaseRepresentative_mem z, by
      rw [exp_circlePhaseRepresentative]
      rw [← hS]
      exact hzS⟩
  · intro ht
    have ht' := (real_intersectionParameters_iff_circle p q beta t).1 ht
    simp only [Finset.mem_coe, circleFinsetToReal, Finset.mem_image]
    refine ⟨Circle.exp t, ?_, ?_⟩
    · show Circle.exp t ∈ (S : Set Circle)
      rw [hS]
      exact ht'.2
    · exact circlePhaseRepresentative_exp_of_mem_Ico ht'.1

end Submission.PardonDistortion
