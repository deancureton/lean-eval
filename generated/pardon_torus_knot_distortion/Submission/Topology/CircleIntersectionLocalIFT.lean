import Submission.Topology.CircleIntersectionCovering

/-!
# Local IFT charts for the circle intersection locus

The scalar implicit-function theorem produces, in angular coordinates, a
unique continuous zero branch over an open time interval.  This file packages
that exact chart output and constructs an `OpenPartialHomeomorph` for the time
projection.  Hence a compatible local graph at every zero proves the
`IsLocalHomeomorph` field used by the compact circle-covering construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Filter
open scoped Topology

noncomputable section

namespace Submission.PardonDistortion

lemma continuous_circleIntersectionProjection
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle} :
    Continuous (circleIntersectionProjection (p := p) (q := q) (H := H)) := by
  unfold circleIntersectionProjection
  fun_prop

/-- A local graph chart through one point of the circle intersection locus.
`exhaustive` is the uniqueness conclusion of the angular-coordinate IFT. -/
structure CircleIntersectionLocalGraph (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle)
    (z : circleIntersectionLocus p q H) where
  baseSet : Set unitInterval
  open_baseSet : IsOpen baseSet
  time_mem : circleIntersectionProjection z ∈ baseSet
  lift : unitInterval → circleIntersectionLocus p q H
  continuous_lift : Continuous lift
  projection_lift : ∀ s ∈ baseSet,
    circleIntersectionProjection (lift s) = s
  exhaustive : ∀ w : circleIntersectionLocus p q H,
    circleIntersectionProjection w ∈ baseSet →
      lift (circleIntersectionProjection w) = w

def CircleIntersectionLocalGraph.toOpenPartialHomeomorph
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {z : circleIntersectionLocus p q H}
    (G : CircleIntersectionLocalGraph p q H z) :
    OpenPartialHomeomorph (circleIntersectionLocus p q H) unitInterval where
  toFun := circleIntersectionProjection
  invFun := G.lift
  source := circleIntersectionProjection ⁻¹' G.baseSet
  target := G.baseSet
  map_source' := fun w hw ↦ hw
  map_target' := fun s hs ↦ by
    show circleIntersectionProjection (G.lift s) ∈ G.baseSet
    rw [G.projection_lift s hs]
    exact hs
  left_inv' := fun w hw ↦ G.exhaustive w hw
  right_inv' := fun s hs ↦ G.projection_lift s hs
  open_source := G.open_baseSet.preimage continuous_circleIntersectionProjection
  open_target := G.open_baseSet
  continuousOn_toFun := continuous_circleIntersectionProjection.continuousOn
  continuousOn_invFun := G.continuous_lift.continuousOn

lemma CircleIntersectionLocalGraph.mem_source
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {z : circleIntersectionLocus p q H}
    (G : CircleIntersectionLocalGraph p q H z) :
    z ∈ G.toOpenPartialHomeomorph.source :=
  G.time_mem

lemma CircleIntersectionLocalGraph.coe_toOpenPartialHomeomorph
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {z : circleIntersectionLocus p q H}
    (G : CircleIntersectionLocalGraph p q H z) :
    (G.toOpenPartialHomeomorph :
      circleIntersectionLocus p q H → unitInterval) =
        circleIntersectionProjection :=
  rfl

/-- Compatible local IFT graph charts at every zero. -/
structure CircleIntersectionLocalGraphAtlas (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle) where
  graph : ∀ z : circleIntersectionLocus p q H,
    CircleIntersectionLocalGraph p q H z

theorem CircleIntersectionLocalGraphAtlas.isLocalHomeomorph_projection
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (A : CircleIntersectionLocalGraphAtlas p q H) :
    IsLocalHomeomorph
      (circleIntersectionProjection (p := p) (q := q) (H := H)) := by
  intro z
  exact ⟨(A.graph z).toOpenPartialHomeomorph,
    (A.graph z).mem_source,
    (A.graph z).coe_toOpenPartialHomeomorph.symm⟩

/-- The local graph atlas and continuity of the homotopy produce the exact
transversality package consumed by `CircleIntersectionCovering`. -/
theorem CircleIntersectionLocalGraphAtlas.toTransversality
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (A : CircleIntersectionLocalGraphAtlas p q H)
    (hH : Continuous (Function.uncurry H)) :
    CircleIntersectionTransversality p q H where
  continuous_homotopy := hH
  isLocalHomeomorph_projection := A.isLocalHomeomorph_projection

/-! ## Angular derivative input -/

/-- At a zero in angular coordinates, strict differentiability and an
invertible vertical derivative give the local scalar graph used above.  This
is the direct bridge to the nonzero transverse determinant hypothesis: for a
one-dimensional vertical variable, invertibility is equivalent to a nonzero
vertical derivative. -/
theorem angularRegularZero_localGraph
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hzero : F u = 0) (hF : HasStrictFDerivAt F F' u)
    (htransverse :
      (F' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ g : ℝ → ℝ, ContinuousAt g u.1 ∧ g u.1 = u.2 ∧
      ∀ᶠ v in 𝓝 u, (F v = 0 ↔ g v.1 = v.2) :=
  regularZero_eventually_eq_graph hzero hF htransverse

/-- The dimensionally correct angular-chart form for two curves on a torus.
There are two angular unknowns `(a,b)` and two coordinate equations.  The
vertical `2×2` derivative is invertible exactly when its determinant is
nonzero, i.e. when the two curve tangent vectors are transverse. -/
theorem angularTransverseIntersection_localGraph
    {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {u : ℝ × (ℝ × ℝ)}
    {F' : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ}
    (hzero : F u = 0) (hF : HasStrictFDerivAt F F' u)
    (hdet : (F' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).IsInvertible) :
    ∃ g : ℝ → ℝ × ℝ, ContinuousAt g u.1 ∧ g u.1 = u.2 ∧
      ∀ᶠ v in 𝓝 u, (F v = 0 ↔ g v.1 = v.2) := by
  let g := hF.implicitFunctionOfProdDomain hdet
  have hgraph := hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hdet
  have hg : g u.1 = u.2 := hgraph.self_of_nhds.mp rfl
  refine ⟨g, (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hdet).continuousAt,
    hg, ?_⟩
  filter_upwards [hgraph] with v hv
  simpa only [hzero] using hv

/-! ## Oriented local graphs -/

/-- Local IFT graphs together with the oriented local intersection sign.
Continuity into the discrete space `ℤ` is the coordinate-independent form of
sign constancy under a transverse deformation. -/
structure OrientedCircleIntersectionLocalGraphAtlas (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle)
    extends CircleIntersectionLocalGraphAtlas p q H where
  localSign : circleIntersectionLocus p q H → ℤ
  continuous_localSign : Continuous localSign
  localSign_natAbs : ∀ z, (localSign z).natAbs = 1

theorem OrientedCircleIntersectionLocalGraphAtlas.localSign_endpointTransport
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (A : OrientedCircleIntersectionLocalGraphAtlas p q H)
    (hH : Continuous (Function.uncurry H))
    (e : circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)}) :
    A.localSign e.1 = A.localSign
      ((A.toCircleIntersectionLocalGraphAtlas.toTransversality hH).endpointTransport e).1 := by
  let T : CircleIntersectionTransversality p q H :=
    A.toCircleIntersectionLocalGraphAtlas.toTransversality hH
  let gamma : C(unitInterval, unitInterval) :=
    unitIntervalIdentityPath.toContinuousMap
  have hzero : gamma 0 = circleIntersectionProjection (p := p) (q := q)
      (H := H) e.1 := by
    change (0 : unitInterval) = circleIntersectionProjection e.1
    exact e.2.symm
  let lift := T.covering.liftPath gamma e.1 hzero
  have hcont : Continuous (fun s ↦ A.localSign (lift s)) :=
    A.continuous_localSign.comp lift.continuous
  have hconst : A.localSign (lift 0) = A.localSign (lift 1) :=
    (inferInstance : PreconnectedSpace unitInterval).constant hcont
  have hstart : lift 0 = e.1 := by
    exact T.covering.liftPath_zero gamma e.1 hzero
  have hend : lift 1 = (T.endpointTransport e).1 := by
    rfl
  rw [hstart, hend] at hconst
  exact hconst

lemma OrientedCircleIntersectionLocalGraphAtlas.endpointSign_natAbs
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (A : OrientedCircleIntersectionLocalGraphAtlas p q H)
    (z : circleIntersectionLocus p q H) :
    (A.localSign z).natAbs = 1 :=
  A.localSign_natAbs z

/-! ## Connecting a known affine source certificate -/

/-- Fiber identifications at the two endpoints.  At the source this is proved
from the explicit affine certificate; at the target it follows from uniqueness
of the loop parameter (for example, an embedded loop).  No endpoint matching
is included: that is supplied by covering monodromy. -/
structure CircleCoveringEndpointBridge (p q : ℕ)
    (H : ℝ → Circle → Circle × Circle)
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    (C : TransverseIntersectionCertificate p q gamma₀ m n)
    (T : CircleIntersectionTransversality p q H) where
  homotopy_zero : (fun u ↦ H 0 (Circle.exp u)) = gamma₀
  sourceFiberEquiv : {t // t ∈ C.parameters} ≃
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)})
  targetFiberEquiv :
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)}) ≃
    {z // z ∈ circleLoopIntersectionParameters p q (H 1)}

def CircleIntersectionTransversality.endpointFiberEquiv
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    (T : CircleIntersectionTransversality p q H) :
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(0 : unitInterval)}) ≃
    (circleIntersectionProjection (p := p) (q := q) (H := H) ⁻¹'
      {(1 : unitInterval)}) :=
  Equiv.ofBijective T.endpointTransport T.endpointTransport_bijective

/-- The affine source parameters are globally matched to the target real
parameters by circle-covering monodromy, followed only at the endpoint by the
canonical `[0,2π)` representative. -/
def CircleCoveringEndpointBridge.realEndpointEquiv
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    {t // t ∈ C.parameters} ≃
      {t // t ∈ torusLoopIntersectionParameters p q
        (fun u ↦ H 1 (Circle.exp u))} :=
  B.sourceFiberEquiv.trans <| (T.endpointFiberEquiv.trans <|
    B.targetFiberEquiv.trans <| circleParameterEquivReal p q (H 1))

def CircleCoveringEndpointBridge.targetParameters
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) : Finset ℝ :=
  Finset.univ.image (fun x : {t // t ∈ C.parameters} ↦
    (B.realEndpointEquiv x).1)

theorem CircleCoveringEndpointBridge.targetParameters_eq
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    (B.targetParameters : Set ℝ) =
      torusLoopIntersectionParameters p q
        (fun u ↦ H 1 (Circle.exp u)) := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_coe, CircleCoveringEndpointBridge.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    exact (B.realEndpointEquiv x).2
  · intro ht
    let y : {t // t ∈ torusLoopIntersectionParameters p q
        (fun u ↦ H 1 (Circle.exp u))} := ⟨t, ht⟩
    let x := B.realEndpointEquiv.symm y
    simp only [Finset.mem_coe, CircleCoveringEndpointBridge.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨x, ?_⟩
    exact congrArg Subtype.val (B.realEndpointEquiv.apply_symm_apply y)

theorem CircleCoveringEndpointBridge.targetParameters_card
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    B.targetParameters.card = C.parameters.card := by
  rw [CircleCoveringEndpointBridge.targetParameters,
    Finset.card_image_iff.mpr]
  · simp
  · exact (Subtype.val_injective.comp B.realEndpointEquiv.injective).injOn

def CircleCoveringEndpointBridge.targetMap
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    {t // t ∈ C.parameters} → {t // t ∈ B.targetParameters} :=
  fun x ↦ ⟨(B.realEndpointEquiv x).1, by
    simp [CircleCoveringEndpointBridge.targetParameters]⟩

lemma CircleCoveringEndpointBridge.targetMap_bijective
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    Function.Bijective B.targetMap := by
  constructor
  · intro x y hxy
    apply B.realEndpointEquiv.injective
    apply Subtype.ext
    have hv := congrArg Subtype.val hxy
    change (B.realEndpointEquiv x).1 = (B.realEndpointEquiv y).1 at hv
    exact hv
  · rintro ⟨t, ht⟩
    simp only [CircleCoveringEndpointBridge.targetParameters,
      Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨x, rfl⟩ := ht
    exact ⟨x, rfl⟩

def CircleCoveringEndpointBridge.targetEquiv
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    {t // t ∈ C.parameters} ≃ {t // t ∈ B.targetParameters} :=
  Equiv.ofBijective B.targetMap B.targetMap_bijective

def CircleCoveringEndpointBridge.targetSign
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) (t : ℝ) : ℤ :=
  if ht : t ∈ B.targetParameters then
    C.sign (B.targetEquiv.symm ⟨t, ht⟩).1
  else 0

lemma CircleCoveringEndpointBridge.targetSign_natAbs
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T)
    (t : ℝ) (ht : t ∈ B.targetParameters) :
    (B.targetSign t).natAbs = 1 := by
  simp only [CircleCoveringEndpointBridge.targetSign, dif_pos ht]
  exact C.sign_natAbs _ (B.targetEquiv.symm ⟨t, ht⟩).2

lemma CircleCoveringEndpointBridge.sign_preserved
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T)
    (x : {t // t ∈ C.parameters}) :
    C.sign x.1 = B.targetSign (B.targetEquiv x).1 := by
  rw [CircleCoveringEndpointBridge.targetSign]
  simp only [dif_pos (B.targetEquiv x).2]
  change C.sign x.1 = C.sign (B.targetEquiv.symm (B.targetEquiv x)).1
  rw [Equiv.symm_apply_apply]

/-- The circle-covering endpoint bridge now produces the existing regular
continuation interface, including a complete target certificate. -/
def CircleCoveringEndpointBridge.toRegularIntersectionContinuation
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    RegularIntersectionContinuation p q gamma₀
      (fun u ↦ H 1 (Circle.exp u)) m n C where
  homotopy := fun s u ↦ H s (Circle.exp u)
  continuous_homotopy := by
    exact T.continuous_homotopy.comp
      (continuous_fst.prodMk (Circle.exp.continuous.comp continuous_snd))
  periodic_homotopy := by
    intro s u
    exact congrArg (H s) (Circle.periodic_exp u)
  homotopy_zero := B.homotopy_zero
  homotopy_one := rfl
  targetParameters := B.targetParameters
  targetParameters_eq := B.targetParameters_eq
  matching := B.targetEquiv
  targetSign := B.targetSign
  targetSign_natAbs := B.targetSign_natAbs
  sign_preserved := B.sign_preserved

def CircleCoveringEndpointBridge.targetCertificate
    {p q : ℕ} {H : ℝ → Circle → Circle × Circle}
    {gamma₀ : ℝ → Circle × Circle} {m n : ℤ}
    {C : TransverseIntersectionCertificate p q gamma₀ m n}
    {T : CircleIntersectionTransversality p q H}
    (B : CircleCoveringEndpointBridge p q H C T) :
    TransverseIntersectionCertificate p q
      (fun u ↦ H 1 (Circle.exp u)) m n :=
  B.toRegularIntersectionContinuation.targetCertificate

end Submission.PardonDistortion
