import Submission.Topology.DiskWinding
import Submission.Torus.AmbientTransfer

/-!
# Compressing slopes and representativity of a transported torus knot

This file isolates the elementary part of the representativity calculation.
An explicitly parametrized compressing disk has a boundary slope `(m, n)` in
the product coordinates on the transported torus.  Its geometric intersection
number with the `(p, q)` knot is the absolute determinant
`|p * n - q * m|`.  Consequently either primitive coordinate-axis slope meets
the knot at least `min p q` times.

The remaining three-dimensional input is deliberately exposed as the predicate
`HasAxisSlopeClassification`: every genuine compressing disk on either side of
the torus has one of those two primitive axis slopes.  Proving that predicate
requires separation of the complement and the solid-torus classification; it
is not concealed in the definitions below.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-! ## Explicit coordinate-circle intersections -/

/-- The `k`th parameter, for `k : Fin q`, at which the `(p, q)` curve meets
the standard longitude whose meridian coordinate is one. -/
def longitudeIntersectionTime (q : ℕ) (k : Fin q) : ℝ :=
  2 * Real.pi * (k : ℝ) / (q : ℝ)

/-- The finite set of longitude-intersection parameters in one period. -/
def longitudeIntersectionParameterSet (q : ℕ) : Set ℝ :=
  Set.range (longitudeIntersectionTime q)

/-- The analogous parameters for intersections with the standard meridian. -/
def meridianIntersectionTime (p : ℕ) (k : Fin p) : ℝ :=
  2 * Real.pi * (k : ℝ) / (p : ℝ)

/-- The finite set of meridian-intersection parameters in one period. -/
def meridianIntersectionParameterSet (p : ℕ) : Set ℝ :=
  Set.range (meridianIntersectionTime p)

lemma longitudeIntersectionTime_mem_Ico {q : ℕ} (k : Fin q) :
    longitudeIntersectionTime q k ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hqNat : 0 < q := Nat.pos_of_ne_zero (fun hq ↦ by
    subst q
    exact Fin.elim0 k)
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqNat
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkq : (k : ℝ) < q := by exact_mod_cast k.isLt
  constructor
  · unfold longitudeIntersectionTime
    exact div_nonneg (mul_nonneg (by positivity) hk0) hq.le
  · unfold longitudeIntersectionTime
    rw [div_lt_iff₀ hq]
    nlinarith [Real.pi_pos]

lemma meridianIntersectionTime_mem_Ico {p : ℕ} (k : Fin p) :
    meridianIntersectionTime p k ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hpNat : 0 < p := Nat.pos_of_ne_zero (fun hp ↦ by
    subst p
    exact Fin.elim0 k)
  have hp : 0 < (p : ℝ) := by exact_mod_cast hpNat
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkp : (k : ℝ) < p := by exact_mod_cast k.isLt
  constructor
  · unfold meridianIntersectionTime
    exact div_nonneg (mul_nonneg (by positivity) hk0) hp.le
  · unfold meridianIntersectionTime
    rw [div_lt_iff₀ hp]
    nlinarith [Real.pi_pos]

lemma longitudeIntersectionTime_injective (q : ℕ) :
    Function.Injective (longitudeIntersectionTime q) := by
  intro i j hij
  have hqNat : 0 < q := Nat.pos_of_ne_zero (fun hq ↦ by
    subst q
    exact Fin.elim0 i)
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqNat
  unfold longitudeIntersectionTime at hij
  have hk : (i : ℝ) = (j : ℝ) := by
    field_simp [hq.ne'] at hij
    exact hij
  exact Fin.ext (by exact_mod_cast hk)

lemma meridianIntersectionTime_injective (p : ℕ) :
    Function.Injective (meridianIntersectionTime p) := by
  intro i j hij
  have hpNat : 0 < p := Nat.pos_of_ne_zero (fun hp ↦ by
    subst p
    exact Fin.elim0 i)
  have hp : 0 < (p : ℝ) := by exact_mod_cast hpNat
  unfold meridianIntersectionTime at hij
  have hk : (i : ℝ) = (j : ℝ) := by
    field_simp [hp.ne'] at hij
    exact hij
  exact Fin.ext (by exact_mod_cast hk)

theorem longitudeIntersectionParameterSet_ncard (q : ℕ) :
    (longitudeIntersectionParameterSet q).ncard = q := by
  rw [longitudeIntersectionParameterSet,
    Set.ncard_range_of_injective (longitudeIntersectionTime_injective q)]
  simp

theorem meridianIntersectionParameterSet_ncard (p : ℕ) :
    (meridianIntersectionParameterSet p).ncard = p := by
  rw [meridianIntersectionParameterSet,
    Set.ncard_range_of_injective (meridianIntersectionTime_injective p)]
  simp

lemma torusKnotLift_longitude_intersection (p q : ℕ) (k : Fin q) :
    (Submission.Torus.torusKnotLift p q
      (longitudeIntersectionTime q k)).2 = 1 := by
  rw [Submission.Torus.torusKnotLift_snd]
  rw [← Circle.exp_zero]
  apply Circle.exp_eq_exp.mpr
  refine ⟨(k : ℤ), ?_⟩
  unfold longitudeIntersectionTime
  have hq : (q : ℝ) ≠ 0 := by
    have hqNat : q ≠ 0 := fun hq ↦ by
      subst q
      exact Fin.elim0 k
    exact_mod_cast hqNat
  push_cast
  field_simp
  ring

lemma torusKnotLift_meridian_intersection (p q : ℕ) (k : Fin p) :
    (Submission.Torus.torusKnotLift p q
      (meridianIntersectionTime p k)).1 = 1 := by
  rw [Submission.Torus.torusKnotLift_fst]
  rw [← Circle.exp_zero]
  apply Circle.exp_eq_exp.mpr
  refine ⟨(k : ℤ), ?_⟩
  unfold meridianIntersectionTime
  have hp : (p : ℝ) ≠ 0 := by
    have hpNat : p ≠ 0 := fun hp ↦ by
      subst p
      exact Fin.elim0 k
    exact_mod_cast hpNat
  push_cast
  field_simp
  ring

/-- The coordinate longitude on the transported torus. -/
def transportedLongitude (Phi : AmbientIsotopy) (z : Circle) : R3 :=
  Submission.Torus.transportedTorusMap Phi (z, 1)

/-- The coordinate meridian on the transported torus. -/
def transportedMeridian (Phi : AmbientIsotopy) (w : Circle) : R3 :=
  Submission.Torus.transportedTorusMap Phi (1, w)

/-- The finite family of actual intersection points with the transported
longitude.  Coprimality makes all `q` of these points distinct. -/
def longitudeIntersectionPoint (Phi : AmbientIsotopy) (p q : ℕ)
    (k : Fin q) : R3 :=
  Submission.Torus.transportedTorusMap Phi
    (Submission.Torus.torusKnotLift p q (longitudeIntersectionTime q k))

/-- The analogous finite family on the transported meridian. -/
def meridianIntersectionPoint (Phi : AmbientIsotopy) (p q : ℕ)
    (k : Fin p) : R3 :=
  Submission.Torus.transportedTorusMap Phi
    (Submission.Torus.torusKnotLift p q (meridianIntersectionTime p k))

theorem longitudeIntersectionPoint_injective (Phi : AmbientIsotopy)
    (p q : ℕ) (hc : p.Coprime q) :
    Function.Injective (longitudeIntersectionPoint Phi p q) := by
  intro i j hij
  apply longitudeIntersectionTime_injective q
  apply Submission.Torus.torusKnotLift_injOn p q hc
    (longitudeIntersectionTime_mem_Ico i)
    (longitudeIntersectionTime_mem_Ico j)
  apply Submission.Torus.transportedTorusMap_injective Phi
  exact hij

theorem meridianIntersectionPoint_injective (Phi : AmbientIsotopy)
    (p q : ℕ) (hc : p.Coprime q) :
    Function.Injective (meridianIntersectionPoint Phi p q) := by
  intro i j hij
  apply meridianIntersectionTime_injective p
  apply Submission.Torus.torusKnotLift_injOn p q hc
    (meridianIntersectionTime_mem_Ico i)
    (meridianIntersectionTime_mem_Ico j)
  apply Submission.Torus.transportedTorusMap_injective Phi
  exact hij

theorem longitudeIntersectionPoint_ncard (Phi : AmbientIsotopy)
    (p q : ℕ) (hc : p.Coprime q) :
    (Set.range (longitudeIntersectionPoint Phi p q)).ncard = q := by
  rw [Set.ncard_range_of_injective
    (longitudeIntersectionPoint_injective Phi p q hc)]
  simp

theorem meridianIntersectionPoint_ncard (Phi : AmbientIsotopy)
    (p q : ℕ) (hc : p.Coprime q) :
    (Set.range (meridianIntersectionPoint Phi p q)).ncard = p := by
  rw [Set.ncard_range_of_injective
    (meridianIntersectionPoint_injective Phi p q hc)]
  simp

theorem longitudeIntersectionPoint_mem_both (Phi : AmbientIsotopy)
    (p q : ℕ) (k : Fin q) :
    longitudeIntersectionPoint Phi p q k ∈
      Set.range (fun t ↦ Submission.Torus.transportedTorusMap Phi
        (Submission.Torus.torusKnotLift p q t)) ∩
      Set.range (transportedLongitude Phi) := by
  constructor
  · exact ⟨longitudeIntersectionTime q k, rfl⟩
  · refine ⟨(Submission.Torus.torusKnotLift p q
      (longitudeIntersectionTime q k)).1, ?_⟩
    unfold longitudeIntersectionPoint transportedLongitude
    apply congrArg (Submission.Torus.transportedTorusMap Phi)
    exact Prod.ext rfl (torusKnotLift_longitude_intersection p q k).symm

theorem meridianIntersectionPoint_mem_both (Phi : AmbientIsotopy)
    (p q : ℕ) (k : Fin p) :
    meridianIntersectionPoint Phi p q k ∈
      Set.range (fun t ↦ Submission.Torus.transportedTorusMap Phi
        (Submission.Torus.torusKnotLift p q t)) ∩
      Set.range (transportedMeridian Phi) := by
  constructor
  · exact ⟨meridianIntersectionTime p k, rfl⟩
  · refine ⟨(Submission.Torus.torusKnotLift p q
      (meridianIntersectionTime p k)).2, ?_⟩
    unfold meridianIntersectionPoint transportedMeridian
    apply congrArg (Submission.Torus.transportedTorusMap Phi)
    exact Prod.ext (torusKnotLift_meridian_intersection p q k).symm rfl

/-- Each explicit longitude-intersection point also lies on the original knot
when the benchmark's ambient-isotopy witness is supplied. -/
theorem longitudeIntersectionPoint_mem_curve_and_longitude
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (k : Fin q) :
    longitudeIntersectionPoint Phi p q k ∈
      Set.range K.curve ∩ Set.range (transportedLongitude Phi) := by
  have hboth := longitudeIntersectionPoint_mem_both Phi p q k
  constructor
  · rw [Submission.Torus.curve_range_eq_transportedTorusKnot_range
      p q K Phi sigma hclass]
    exact hboth.1
  · exact hboth.2

/-- The analogous bridge from explicit meridian intersections to the original
ambiently transported knot. -/
theorem meridianIntersectionPoint_mem_curve_and_meridian
    (p q : ℕ) (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hclass : ∀ t, Phi.H 1 (K.curve t) =
      standardTorusCurve p q (sigma.f t)) (k : Fin p) :
    meridianIntersectionPoint Phi p q k ∈
      Set.range K.curve ∩ Set.range (transportedMeridian Phi) := by
  have hboth := meridianIntersectionPoint_mem_both Phi p q k
  constructor
  · rw [Submission.Torus.curve_range_eq_transportedTorusKnot_range
      p q K Phi sigma hclass]
    exact hboth.1
  · exact hboth.2

/-! ## Slope intersection number -/

/-- The signed intersection determinant of the `(p, q)` slope and `(m, n)`
slope, in longitude-meridian coordinates. -/
def slopeIntersectionDet (p q : ℕ) (m n : ℤ) : ℤ :=
  (p : ℤ) * n - (q : ℤ) * m

/-- Its unsigned geometric intersection number. -/
def slopeIntersectionNumber (p q : ℕ) (m n : ℤ) : ℕ :=
  (slopeIntersectionDet p q m n).natAbs

/-- A primitive coordinate-axis slope: an oriented longitude or meridian. -/
def IsPrimitiveAxisSlope (m n : ℤ) : Prop :=
  (m.natAbs = 1 ∧ n = 0) ∨ (m = 0 ∧ n.natAbs = 1)

theorem slopeIntersectionNumber_eq_q_of_longitude
    (p q : ℕ) (m n : ℤ) (hm : m.natAbs = 1) (hn : n = 0) :
    slopeIntersectionNumber p q m n = q := by
  subst n
  simp [slopeIntersectionNumber, slopeIntersectionDet,
    Int.natAbs_mul, hm]

theorem slopeIntersectionNumber_eq_p_of_meridian
    (p q : ℕ) (m n : ℤ) (hm : m = 0) (hn : n.natAbs = 1) :
    slopeIntersectionNumber p q m n = p := by
  subst m
  simp [slopeIntersectionNumber, slopeIntersectionDet,
    Int.natAbs_mul, hn]

theorem min_le_slopeIntersectionNumber_of_axis
    (p q : ℕ) (m n : ℤ) (haxis : IsPrimitiveAxisSlope m n) :
    min p q ≤ slopeIntersectionNumber p q m n := by
  rcases haxis with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · rw [slopeIntersectionNumber_eq_q_of_longitude p q m n hm hn]
    exact min_le_right _ _
  · rw [slopeIntersectionNumber_eq_p_of_meridian p q m n hm hn]
    exact min_le_left _ _

/-! ## A concrete compression interface -/

/-- A loop of slope `(m, n)` in the product coordinates of the transported
torus. -/
def transportedSlopeLoop (Phi : AmbientIsotopy) (m n : ℤ)
    (phase₁ phase₂ t : ℝ) : R3 :=
  Submission.Torus.transportedTorusMap Phi
    (Circle.exp ((m : ℝ) * t + phase₁),
      Circle.exp ((n : ℝ) * t + phase₂))

/-- An embedded disk whose boundary is an essential, explicitly sloped loop
on the transported torus and whose open interior misses the torus. -/
structure CompressingDiskWitness (Phi : AmbientIsotopy) where
  m : ℤ
  n : ℤ
  phase₁ : ℝ
  phase₂ : ℝ
  disk : ClosedUnitDisk → R3
  isEmbedding : Topology.IsEmbedding disk
  boundary : ∀ t : ℝ, disk (unitDiskBoundary t) =
    transportedSlopeLoop Phi m n phase₁ phase₂ t
  interior_disjoint : ∀ z : ClosedUnitDisk, ‖(z : ℂ)‖ < 1 →
    disk z ∉ Submission.Torus.transportedTorus Phi
  essential : m ≠ 0 ∨ n ≠ 0

lemma CompressingDiskWitness.continuous {Phi : AmbientIsotopy}
    (D : CompressingDiskWitness Phi) : Continuous D.disk :=
  D.isEmbedding.continuous

/-- A compressing disk cannot accidentally lie entirely in the torus.  This
sanity check is a direct application of the disk-winding obstruction. -/
theorem CompressingDiskWitness.not_range_subset_torus {Phi : AmbientIsotopy}
    (D : CompressingDiskWitness Phi) :
    ¬ Set.range D.disk ⊆ Submission.Torus.transportedTorus Phi := by
  intro hsubset
  let g : ClosedUnitDisk → Submission.Torus.transportedTorus Phi :=
    fun z ↦ ⟨D.disk z, hsubset ⟨z, rfl⟩⟩
  have hg : Continuous g := D.continuous.subtype_mk _
  have hboundary : ∀ t : ℝ,
      (Submission.Torus.transportedTorusHomeomorph Phi).symm
        (g (unitDiskBoundary t)) =
      (Circle.exp ((D.m : ℝ) * t + D.phase₁),
        Circle.exp ((D.n : ℝ) * t + D.phase₂)) := by
    intro t
    rw [Homeomorph.symm_apply_eq]
    apply Subtype.ext
    change D.disk (unitDiskBoundary t) =
      Submission.Torus.transportedTorusMap Phi
        (Circle.exp ((D.m : ℝ) * t + D.phase₁),
          Circle.exp ((D.n : ℝ) * t + D.phase₂))
    exact D.boundary t
  obtain ⟨hm, hn⟩ :=
    torus_windings_eq_zero_of_homeomorphicDisk_filling
      (Submission.Torus.transportedTorusHomeomorph Phi)
      D.m D.n D.phase₁ D.phase₂ g hg hboundary
  rcases D.essential with hmne | hnne
  · exact hmne hm
  · exact hnne hn

/-- The precise three-dimensional classification theorem needed by the
representativity argument.  It is kept as a hypothesis until complement-side
solid-torus topology is available. -/
def HasAxisSlopeClassification (Phi : AmbientIsotopy) : Prop :=
  ∀ D : CompressingDiskWitness Phi, IsPrimitiveAxisSlope D.m D.n

/-- Representativity, expressed solely in the slope coordinates that the
explicit torus chart provides. -/
def HasSlopeRepresentativityAtLeast (Phi : AmbientIsotopy)
    (p q lower : ℕ) : Prop :=
  ∀ D : CompressingDiskWitness Phi,
    lower ≤ slopeIntersectionNumber p q D.m D.n

/-- Once compressing boundaries are classified as primitive coordinate-axis
slopes, the transported `(p, q)` knot has representativity at least
`min p q`. -/
theorem transportedTorus_hasSlopeRepresentativityAtLeast_min
    (Phi : AmbientIsotopy) (p q : ℕ)
    (hclassification : HasAxisSlopeClassification Phi) :
    HasSlopeRepresentativityAtLeast Phi p q (min p q) := by
  intro D
  exact min_le_slopeIntersectionNumber_of_axis p q D.m D.n
    (hclassification D)

end Submission.PardonDistortion
