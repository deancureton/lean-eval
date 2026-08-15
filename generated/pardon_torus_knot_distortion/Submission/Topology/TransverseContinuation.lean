import Submission.Topology.IntersectionCertificate

/-!
# Continuing transverse intersection branches

This file isolates an honest geometric output of the implicit-function
theorem: throughout a transverse homotopy, every intersection lies on a
unique continuous branch, and distinct branches never collide.  From these
hypotheses we construct the endpoint bijection required by
`RegularIntersectionContinuation`.

Local signs are *not* assumed constant.  They are assumed continuous as
integer-valued functions along each branch, and their constancy is proved
using connectedness of the parameter interval and discreteness of `ℤ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace Submission.PardonDistortion

/-- A continuous integer-valued quantity cannot change along a real interval. -/
lemma continuousOn_Icc_int_eq_endpoints (sigma : ℝ → ℤ)
    (hsigma : ContinuousOn sigma (Icc (0 : ℝ) 1)) : sigma 0 = sigma 1 := by
  exact isPreconnected_Icc.constant hsigma (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)

/-- Global branches of the intersection locus of a transverse homotopy.

The `covers` and `disjoint` fields are the global conclusion obtained by
patching the local implicit-function theorem over the compact homotopy
interval.  In particular they rule out tangencies, births, deaths, and branch
collisions.  `localSign` records the usual oriented local intersection sign;
only continuity and unit magnitude are required. -/
structure TransverseBranchFamily (p q : ℕ)
    (gamma₀ gamma₁ : ℝ → Circle × Circle) (m n : ℤ)
    (C : TransverseIntersectionCertificate p q gamma₀ m n) where
  homotopy : ℝ → ℝ → Circle × Circle
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = gamma₀
  homotopy_one : homotopy 1 = gamma₁
  branch : {t // t ∈ C.parameters} → ℝ → ℝ
  continuous_branch : ∀ x, ContinuousOn (branch x) (Icc (0 : ℝ) 1)
  branch_zero : ∀ x, branch x 0 = x.1
  branch_mem : ∀ x {s}, s ∈ Icc (0 : ℝ) 1 →
    branch x s ∈ torusLoopIntersectionParameters p q (homotopy s)
  covers : ∀ {s}, s ∈ Icc (0 : ℝ) 1 →
    ∀ t ∈ torusLoopIntersectionParameters p q (homotopy s),
      ∃ x, branch x s = t
  disjoint : ∀ {s}, s ∈ Icc (0 : ℝ) 1 →
    Function.Injective (fun x ↦ branch x s)
  localSign : {t // t ∈ C.parameters} → ℝ → ℤ
  continuous_localSign : ∀ x,
    ContinuousOn (localSign x) (Icc (0 : ℝ) 1)
  localSign_zero : ∀ x, localSign x 0 = C.sign x.1
  localSign_natAbs : ∀ x {s}, s ∈ Icc (0 : ℝ) 1 →
    (localSign x s).natAbs = 1

/-- The portion of the intersection locus lying over the compact homotopy
interval. -/
def homotopyIntersectionLocus (p q : ℕ)
    (H : ℝ → ℝ → Circle × Circle) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (0 : ℝ) 1 ∧
    z.2 ∈ torusLoopIntersectionParameters p q (H z.1)}

theorem TransverseBranchFamily.intersectionLocus_eq_iUnion_graph
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    homotopyIntersectionLocus p q B.homotopy =
      ⋃ x : {t // t ∈ C.parameters},
        (fun s ↦ (s, B.branch x s)) '' Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨hs, ht⟩ := hz
    obtain ⟨x, hx⟩ := B.covers hs z.2 ht
    simp only [mem_iUnion, mem_image]
    refine ⟨x, z.1, hs, ?_⟩
    exact Prod.ext rfl hx
  · simp only [mem_iUnion, mem_image]
    rintro ⟨x, s, hs, rfl⟩
    exact ⟨hs, B.branch_mem x hs⟩

/-- Compactness of the global intersection locus follows rather than being
an extra hypothesis: it is a finite union of compact branch graphs. -/
theorem TransverseBranchFamily.isCompact_intersectionLocus
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    IsCompact (homotopyIntersectionLocus p q B.homotopy) := by
  rw [B.intersectionLocus_eq_iUnion_graph]
  apply isCompact_iUnion
  intro x
  exact isCompact_Icc.image_of_continuousOn
    (continuousOn_id.prodMk (B.continuous_branch x))

def TransverseBranchFamily.targetParameters
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) : Finset ℝ :=
  Finset.univ.image (fun x : {t // t ∈ C.parameters} ↦ B.branch x 1)

lemma TransverseBranchFamily.mem_targetParameters
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    B.branch x 1 ∈ B.targetParameters := by
  simp [TransverseBranchFamily.targetParameters]

theorem TransverseBranchFamily.targetParameters_eq
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    (B.targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q gamma₁ := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_coe, TransverseBranchFamily.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    simpa only [B.homotopy_one] using
      B.branch_mem x (right_mem_Icc.mpr zero_le_one)
  · intro ht
    have ht' : t ∈ torusLoopIntersectionParameters p q (B.homotopy 1) := by
      rwa [B.homotopy_one]
    obtain ⟨x, hx⟩ := B.covers (right_mem_Icc.mpr zero_le_one) t ht'
    simp only [Finset.mem_coe, TransverseBranchFamily.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨x, hx⟩

def TransverseBranchFamily.endpointMap
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    {t // t ∈ C.parameters} → {t // t ∈ B.targetParameters} :=
  fun x ↦ ⟨B.branch x 1, B.mem_targetParameters x⟩

lemma TransverseBranchFamily.endpointMap_bijective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    Function.Bijective B.endpointMap := by
  constructor
  · intro x y hxy
    apply B.disjoint (right_mem_Icc.mpr zero_le_one)
    exact congrArg Subtype.val hxy
  · rintro ⟨t, ht⟩
    simp only [TransverseBranchFamily.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    exact ⟨x, rfl⟩

def TransverseBranchFamily.endpointEquiv
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    {t // t ∈ C.parameters} ≃ {t // t ∈ B.targetParameters} :=
  Equiv.ofBijective B.endpointMap B.endpointMap_bijective

theorem TransverseBranchFamily.targetParameters_card
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    B.targetParameters.card = C.parameters.card := by
  simpa using (Fintype.card_congr B.endpointEquiv).symm

theorem TransverseBranchFamily.targetIntersection_finite
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    (torusLoopIntersectionParameters p q gamma₁).Finite := by
  rw [← B.targetParameters_eq]
  exact Finset.finite_toSet B.targetParameters

def TransverseBranchFamily.targetSign
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) (t : ℝ) : ℤ :=
  if ht : t ∈ B.targetParameters then
    B.localSign (B.endpointEquiv.symm ⟨t, ht⟩) 1
  else 0

lemma TransverseBranchFamily.localSign_eq_endpoints
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    B.localSign x 0 = B.localSign x 1 :=
  continuousOn_Icc_int_eq_endpoints _ (B.continuous_localSign x)

lemma TransverseBranchFamily.targetSign_natAbs
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C)
    (t : ℝ) (ht : t ∈ B.targetParameters) :
    (B.targetSign t).natAbs = 1 := by
  simp only [TransverseBranchFamily.targetSign, dif_pos ht]
  exact B.localSign_natAbs _ (right_mem_Icc.mpr zero_le_one)

lemma TransverseBranchFamily.sign_preserved
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    C.sign x.1 = B.targetSign (B.endpointEquiv x).1 := by
  rw [TransverseBranchFamily.targetSign]
  simp only [dif_pos (B.endpointEquiv x).2]
  change C.sign x.1 = B.localSign (B.endpointEquiv.symm (B.endpointEquiv x)) 1
  rw [Equiv.symm_apply_apply]
  exact (B.localSign_zero x).symm.trans (B.localSign_eq_endpoints x)

/-- Global transverse branches produce the finite signed continuation
certificate required by the preceding module. -/
def TransverseBranchFamily.toRegularIntersectionContinuation
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    RegularIntersectionContinuation p q gamma₀ gamma₁ m n C where
  homotopy := B.homotopy
  continuous_homotopy := B.continuous_homotopy
  periodic_homotopy := B.periodic_homotopy
  homotopy_zero := B.homotopy_zero
  homotopy_one := B.homotopy_one
  targetParameters := B.targetParameters
  targetParameters_eq := B.targetParameters_eq
  matching := B.endpointEquiv
  targetSign := B.targetSign
  targetSign_natAbs := B.targetSign_natAbs
  sign_preserved := B.sign_preserved

/-- Signed intersection count is invariant under a homotopy whose transverse
intersection locus is exhausted by global noncolliding branches. -/
def TransverseBranchFamily.targetCertificate
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    TransverseIntersectionCertificate p q gamma₁ m n :=
  B.toRegularIntersectionContinuation.targetCertificate

theorem TransverseBranchFamily.signed_count_invariant
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : TransverseBranchFamily p q gamma₀ gamma₁ m n C) :
    (∑ t ∈ B.targetParameters, B.targetSign t) =
      ∑ t ∈ C.parameters, C.sign t := by
  change (∑ t ∈ B.targetCertificate.parameters,
    B.targetCertificate.sign t) = ∑ t ∈ C.parameters, C.sign t
  rw [B.targetCertificate.signed_sum, C.signed_sum]

end Submission.PardonDistortion
