import Submission.Topology.TransverseContinuation
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# From a covering intersection locus to endpoint branch matching

The parametric implicit-function theorem turns a nonvertical regular zero set
into a local graph over the homotopy parameter.  Properness over the compact
interval then promotes the projection to a finite covering.  This file starts
from that precise covering conclusion and proves the remaining global step:
monodromy over the unit interval gives a bijection of endpoint intersections,
and a continuous integer-valued local sign is preserved.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Filter
open scoped Topology

noncomputable section

namespace Submission.PardonDistortion

/-! ## The local parametric implicit-function step -/

/-- A strictly differentiable scalar equation whose derivative in the second
variable is invertible is locally *exactly* the graph of a continuous implicit
function.  For a scalar second variable, invertibility is the precise linear
form of the usual nonzero partial-derivative hypothesis. -/
theorem regularZero_eventually_eq_graph
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hzero : F u = 0) (hF : HasStrictFDerivAt F F' u)
    (hvertical : (F' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ g : ℝ → ℝ, ContinuousAt g u.1 ∧ g u.1 = u.2 ∧
      ∀ᶠ v in 𝓝 u, (F v = 0 ↔ g v.1 = v.2) := by
  let g := hF.implicitFunctionOfProdDomain hvertical
  have hgraph := hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hvertical
  have hg : g u.1 = u.2 := by
    exact (hgraph.self_of_nhds.mp rfl)
  refine ⟨g, (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain
    hvertical).continuousAt, hg, ?_⟩
  filter_upwards [hgraph] with v hv
  simpa only [hzero] using hv

/-- Pointwise invertibility of the vertical derivative supplies a local graph
chart at every zero.  A uniform lower bound on the scalar vertical derivative
is a standard sufficient condition for the `IsInvertible` field here. -/
theorem regularZero_localGraphs
    (F : ℝ × ℝ → ℝ)
    (hregular : ∀ u, F u = 0 →
      ∃ F' : ℝ × ℝ →L[ℝ] ℝ, HasStrictFDerivAt F F' u ∧
        (F' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∀ u, F u = 0 → ∃ g : ℝ → ℝ,
      ContinuousAt g u.1 ∧ g u.1 = u.2 ∧
        ∀ᶠ v in 𝓝 u, (F v = 0 ↔ g v.1 = v.2) := by
  intro u hu
  obtain ⟨F', hF, hvertical⟩ := hregular u hu
  exact regularZero_eventually_eq_graph hu hF hvertical

/-- The intersection locus, with homotopy time bundled in the unit interval. -/
abbrev unitIntersectionLocus (p q : ℕ)
    (H : ℝ → ℝ → Circle × Circle) : Type :=
  {z : unitInterval × ℝ //
    z.2 ∈ torusLoopIntersectionParameters p q (H z.1)}

def unitIntersectionProjection {p q : ℕ}
    {H : ℝ → ℝ → Circle × Circle} :
    unitIntersectionLocus p q H → unitInterval :=
  fun z ↦ z.1.1

/-- Compactness plus the local-homeomorphism conclusion of the IFT promotes
the zero-locus projection to a covering map. -/
theorem unitIntersectionProjection_isCovering
    {p q : ℕ} {H : ℝ → ℝ → Circle × Circle}
    [CompactSpace (unitIntersectionLocus p q H)]
    (hlocal : IsLocalHomeomorph
      (unitIntersectionProjection (p := p) (q := q) (H := H))) :
    IsCoveringMap (unitIntersectionProjection (p := p) (q := q) (H := H)) := by
  exact isLocalHomeomorph_iff_isCoveringMap.mp hlocal

/-- The straight path from homotopy time zero to time one. -/
def unitIntervalIdentityPath : Path (0 : unitInterval) 1 where
  toContinuousMap := ⟨id, continuous_id⟩
  source' := rfl
  target' := rfl

/-- An honest global consequence of a proper parametric IFT.

`covering` says the regular zero locus projects as a covering of the homotopy
interval.  The local sign is continuous on the zero locus and agrees with the
source certificate.  Unlike a pre-enumerated branch family, this structure
does not assume any endpoint matching. -/
structure CoveringTransverseHomotopy (p q : ℕ)
    (gamma₀ gamma₁ : ℝ → Circle × Circle) (m n : ℤ)
    (C : TransverseIntersectionCertificate p q gamma₀ m n) where
  homotopy : ℝ → ℝ → Circle × Circle
  continuous_homotopy : Continuous (Function.uncurry homotopy)
  periodic_homotopy : ∀ s, Function.Periodic (homotopy s) (2 * Real.pi)
  homotopy_zero : homotopy 0 = gamma₀
  homotopy_one : homotopy 1 = gamma₁
  covering : IsCoveringMap
    (unitIntersectionProjection (p := p) (q := q) (H := homotopy))
  localSign : unitIntersectionLocus p q homotopy → ℤ
  continuous_localSign : Continuous localSign
  localSign_natAbs : ∀ z, (localSign z).natAbs = 1
  localSign_source : ∀ (x : {t // t ∈ C.parameters}),
    localSign ⟨((0 : unitInterval), x.1), by
      have hx : x.1 ∈ torusLoopIntersectionParameters p q gamma₀ := by
        rw [← C.parameters_eq]
        exact x.2
      change x.1 ∈ torusLoopIntersectionParameters p q (homotopy 0)
      rw [homotopy_zero]
      exact hx⟩ = C.sign x.1

def CoveringTransverseHomotopy.sourceLocusPoint
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    unitIntersectionLocus p q B.homotopy :=
  ⟨((0 : unitInterval), x.1), by
    have hx : x.1 ∈ torusLoopIntersectionParameters p q gamma₀ := by
      rw [← C.parameters_eq]
      exact x.2
    change x.1 ∈ torusLoopIntersectionParameters p q (B.homotopy 0)
    rw [B.homotopy_zero]
    exact hx⟩

def CoveringTransverseHomotopy.sourceFiberPoint
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    unitIntersectionProjection (p := p) (q := q) (H := B.homotopy) ⁻¹'
      {(0 : unitInterval)} :=
  ⟨B.sourceLocusPoint x, rfl⟩

lemma CoveringTransverseHomotopy.sourceFiberPoint_injective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Injective B.sourceFiberPoint := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1.1.2) hxy

lemma CoveringTransverseHomotopy.sourceFiberPoint_surjective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Surjective B.sourceFiberPoint := by
  rintro ⟨z, hz⟩
  change z.1.1 = (0 : unitInterval) at hz
  have htime : z.1.1 = (0 : unitInterval) := hz
  have htH := z.2
  rw [htime] at htH
  change z.1.2 ∈ torusLoopIntersectionParameters p q (B.homotopy 0) at htH
  have htGamma : z.1.2 ∈ torusLoopIntersectionParameters p q gamma₀ := by
    rwa [B.homotopy_zero] at htH
  have htC : z.1.2 ∈ C.parameters := by
    show z.1.2 ∈ (C.parameters : Set ℝ)
    rw [C.parameters_eq]
    exact htGamma
  let x : {t // t ∈ C.parameters} := ⟨z.1.2, htC⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact htime.symm
  · rfl

lemma CoveringTransverseHomotopy.sourceFiberPoint_bijective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Bijective B.sourceFiberPoint :=
  ⟨B.sourceFiberPoint_injective, B.sourceFiberPoint_surjective⟩

/-- Transport in the covering along the straight unit-interval path. -/
def CoveringTransverseHomotopy.fiberTransport
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    (unitIntersectionProjection (p := p) (q := q) (H := B.homotopy) ⁻¹'
      {(0 : unitInterval)}) →
      (unitIntersectionProjection (p := p) (q := q) (H := B.homotopy) ⁻¹'
        {(1 : unitInterval)}) :=
  B.covering.monodromy (.mk unitIntervalIdentityPath)

lemma CoveringTransverseHomotopy.fiberTransport_bijective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Bijective B.fiberTransport :=
  B.covering.monodromy_bijective (.mk unitIntervalIdentityPath)

def CoveringTransverseHomotopy.endpointParameter
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) : ℝ :=
  (B.fiberTransport (B.sourceFiberPoint x)).1.1.2

def CoveringTransverseHomotopy.targetParameters
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) : Finset ℝ :=
  Finset.univ.image B.endpointParameter

lemma CoveringTransverseHomotopy.endpointParameter_injective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Injective B.endpointParameter := by
  intro x y hxy
  apply B.sourceFiberPoint_injective
  apply B.fiberTransport_bijective.1
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hx := (B.fiberTransport (B.sourceFiberPoint x)).2
    have hy := (B.fiberTransport (B.sourceFiberPoint y)).2
    change (B.fiberTransport (B.sourceFiberPoint x)).1.1.1 =
      (1 : unitInterval) at hx
    change (B.fiberTransport (B.sourceFiberPoint y)).1.1.1 =
      (1 : unitInterval) at hy
    exact hx.trans hy.symm
  · exact hxy

theorem CoveringTransverseHomotopy.targetParameters_eq
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    (B.targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q gamma₁ := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_coe, CoveringTransverseHomotopy.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    have htime := (B.fiberTransport (B.sourceFiberPoint x)).2
    change (B.fiberTransport (B.sourceFiberPoint x)).1.1.1 =
      (1 : unitInterval) at htime
    have hend := (B.fiberTransport (B.sourceFiberPoint x)).1.2
    rw [htime] at hend
    have : B.endpointParameter x ∈
        torusLoopIntersectionParameters p q (B.homotopy 1) := by
      exact hend
    rwa [B.homotopy_one] at this
  · intro ht
    have htH : t ∈ torusLoopIntersectionParameters p q (B.homotopy 1) := by
      rwa [B.homotopy_one]
    let z : unitIntersectionLocus p q B.homotopy :=
      ⟨((1 : unitInterval), t), htH⟩
    let e : unitIntersectionProjection (p := p) (q := q)
        (H := B.homotopy) ⁻¹' {(1 : unitInterval)} := ⟨z, rfl⟩
    obtain ⟨e₀, he₀⟩ := B.fiberTransport_bijective.2 e
    obtain ⟨x, hx⟩ := B.sourceFiberPoint_surjective e₀
    simp only [Finset.mem_coe, CoveringTransverseHomotopy.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨x, ?_⟩
    unfold CoveringTransverseHomotopy.endpointParameter
    rw [hx]
    exact congrArg (fun w ↦ w.1.1.2) he₀

def CoveringTransverseHomotopy.endpointMap
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    {t // t ∈ C.parameters} → {t // t ∈ B.targetParameters} :=
  fun x ↦ ⟨B.endpointParameter x, by
    simp [CoveringTransverseHomotopy.targetParameters]⟩

lemma CoveringTransverseHomotopy.endpointMap_bijective
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    Function.Bijective B.endpointMap := by
  constructor
  · intro x y hxy
    apply B.endpointParameter_injective
    exact congrArg Subtype.val hxy
  · rintro ⟨t, ht⟩
    simp only [CoveringTransverseHomotopy.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    exact ⟨x, rfl⟩

def CoveringTransverseHomotopy.endpointEquiv
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    {t // t ∈ C.parameters} ≃ {t // t ∈ B.targetParameters} :=
  Equiv.ofBijective B.endpointMap B.endpointMap_bijective

lemma CoveringTransverseHomotopy.localSign_fiberTransport
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    B.localSign (B.sourceFiberPoint x).1 =
      B.localSign (B.fiberTransport (B.sourceFiberPoint x)).1 := by
  let gamma : C(unitInterval, unitInterval) :=
    unitIntervalIdentityPath.toContinuousMap
  have hzero : gamma 0 = unitIntersectionProjection (p := p) (q := q)
      (H := B.homotopy) (B.sourceFiberPoint x).1 := rfl
  let lift := B.covering.liftPath gamma (B.sourceFiberPoint x).1 hzero
  have hcont : Continuous (fun s ↦ B.localSign (lift s)) :=
    B.continuous_localSign.comp lift.continuous
  have hconst : B.localSign (lift 0) = B.localSign (lift 1) :=
    (inferInstance : PreconnectedSpace unitInterval).constant hcont
  have hstart : lift 0 = (B.sourceFiberPoint x).1 := by
    exact B.covering.liftPath_zero gamma (B.sourceFiberPoint x).1 hzero
  have hend : lift 1 = (B.fiberTransport (B.sourceFiberPoint x)).1 := by
    rfl
  rw [hstart, hend] at hconst
  exact hconst

def CoveringTransverseHomotopy.targetSign
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (t : ℝ) : ℤ :=
  if ht : t ∈ B.targetParameters then
    B.localSign (B.fiberTransport
      (B.sourceFiberPoint (B.endpointEquiv.symm ⟨t, ht⟩))).1
  else 0

lemma CoveringTransverseHomotopy.targetSign_natAbs
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (t : ℝ) (ht : t ∈ B.targetParameters) :
    (B.targetSign t).natAbs = 1 := by
  simp only [CoveringTransverseHomotopy.targetSign, dif_pos ht]
  exact B.localSign_natAbs _

lemma CoveringTransverseHomotopy.sign_preserved
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C)
    (x : {t // t ∈ C.parameters}) :
    C.sign x.1 = B.targetSign (B.endpointEquiv x).1 := by
  rw [CoveringTransverseHomotopy.targetSign]
  simp only [dif_pos (B.endpointEquiv x).2]
  change C.sign x.1 = B.localSign
    (B.fiberTransport (B.sourceFiberPoint
      (B.endpointEquiv.symm (B.endpointEquiv x)))).1
  rw [Equiv.symm_apply_apply]
  rw [← B.localSign_fiberTransport x]
  exact (B.localSign_source x).symm

/-- Covering-space monodromy supplies the global endpoint continuation that
was an explicit hypothesis in `TransverseContinuation`. -/
def CoveringTransverseHomotopy.toRegularIntersectionContinuation
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
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

def CoveringTransverseHomotopy.targetCertificate
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    TransverseIntersectionCertificate p q gamma₁ m n :=
  B.toRegularIntersectionContinuation.targetCertificate

theorem CoveringTransverseHomotopy.signed_count_invariant
    {p q : ℕ} {gamma₀ gamma₁ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    (B : CoveringTransverseHomotopy p q gamma₀ gamma₁ m n C) :
    (∑ t ∈ B.targetParameters, B.targetSign t) =
      ∑ t ∈ C.parameters, C.sign t := by
  change (∑ t ∈ B.targetCertificate.parameters,
    B.targetCertificate.sign t) = ∑ t ∈ C.parameters, C.sign t
  rw [B.targetCertificate.signed_sum, C.signed_sum]

end Submission.PardonDistortion
