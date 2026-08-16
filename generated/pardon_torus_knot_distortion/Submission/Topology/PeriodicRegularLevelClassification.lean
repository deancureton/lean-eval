import Submission.Topology.RegularLevelTangentODE

/-!
# Regular levels of smooth periodic planar functions

A smooth planar function which descends through the product exponential has compact quotient
levels.  At a regular value, its complete rotated-gradient orbits classify every connected
component of the quotient level as a circle.
-/

open Set Topology
open scoped Manifold Topology

noncomputable section

namespace Submission.SurfaceRegularValue

open Submission.Topology

/-- A level of a function defined on product-circle coordinates. -/
def periodicQuotientLevelSet (g : Circle × Circle → ℝ) (y : ℝ) :
    Set (Circle × Circle) :=
  g ⁻¹' {y}

theorem isCompact_periodicQuotientLevelSet {g : Circle × Circle → ℝ}
    (hg : Continuous g) (y : ℝ) : IsCompact (periodicQuotientLevelSet g y) :=
  (isClosed_singleton.preimage hg).isCompact

/-- Restriction of the product exponential from a descended planar fiber to its quotient level. -/
def periodicPlaneFiberToQuotientLevel {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) (y : ℝ) :
    (f ⁻¹' {y}) → periodicQuotientLevelSet g y :=
  fun uv ↦ ⟨planeExpPair uv, by
    change g (planeExpPair uv) = y
    rw [← hdesc]
    exact uv.property⟩

theorem periodicPlaneFiberToQuotientLevel_surjective
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) (y : ℝ) :
    Function.Surjective (periodicPlaneFiberToQuotientLevel hdesc y) := by
  intro z
  obtain ⟨uv, huv⟩ := planeExpPair_surjective z.1
  have huvLevel : f uv = y := by
    rw [hdesc, huv]
    exact z.property
  exact ⟨⟨uv, huvLevel⟩, Subtype.ext huv⟩

theorem preimage_periodicQuotientLevelSet_expPair
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) (y : ℝ) :
    planeExpPair ⁻¹' periodicQuotientLevelSet g y = f ⁻¹' {y} := by
  ext uv
  change g (planeExpPair uv) = y ↔ f uv = y
  rw [hdesc]

def periodicPlaneFiberPreimageHomeomorph
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) (y : ℝ) :
    (f ⁻¹' {y}) ≃ₜ (planeExpPair ⁻¹' periodicQuotientLevelSet g y) :=
  Homeomorph.setCongr (preimage_periodicQuotientLevelSet_expPair hdesc y).symm

theorem periodicPlaneFiberToQuotientLevel_isLocalHomeomorph
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) (y : ℝ) :
    IsLocalHomeomorph (periodicPlaneFiberToQuotientLevel hdesc y) := by
  have hrestrict : IsLocalHomeomorph
      (preimageRestriction planeExpPair (periodicQuotientLevelSet g y)) :=
    isLocalHomeomorph_preimageRestriction planeExpPair_isLocalHomeomorph _
  have hcomp := hrestrict.comp (periodicPlaneFiberPreimageHomeomorph hdesc y).isLocalHomeomorph
  convert hcomp using 1
  funext uv
  apply Subtype.ext
  rfl

theorem isLocallyLineModeled_periodicQuotientLevel_of_regularValue
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {y : ℝ} (hy : IsRegularValue f y) :
    IsLocallyLineModeled (periodicQuotientLevelSet g y) := by
  apply isLocallyLineModeled_of_surjective_localHomeomorph
    (periodicPlaneFiberToQuotientLevel_isLocalHomeomorph hdesc y)
    (periodicPlaneFiberToQuotientLevel_surjective hdesc y)
  exact isLocallyLineModeled_regularFiber hf hy

theorem periodicFunction_add_planeDeckVector
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    (uv : Plane) (m n : ℤ) :
    f (uv + planeDeckVector m n) = f uv := by
  rw [hdesc, hdesc, planeExpPair_add_planeDeckVector]

theorem fderiv_periodicFunction_add_planeDeckVector
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    (uv : Plane) (m n : ℤ) :
    fderiv ℝ f (uv + planeDeckVector m n) = fderiv ℝ f uv := by
  let deck := planeDeckVector m n
  have hfun : (fun z ↦ f (z + deck)) = f := by
    funext z
    exact periodicFunction_add_planeDeckVector hdesc z m n
  calc
    fderiv ℝ f (uv + deck) = fderiv ℝ (fun z ↦ f (z + deck)) uv :=
      (fderiv_comp_add_right deck).symm
    _ = fderiv ℝ f uv := congrArg (fun q : Plane → ℝ ↦ fderiv ℝ q uv) hfun

theorem rotatedDerivativeField_periodicFunction_add_planeDeckVector
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    (uv : Plane) (m n : ℤ) :
    rotatedDerivativeField f (uv + planeDeckVector m n) =
      rotatedDerivativeField f uv := by
  simp only [rotatedDerivativeField,
    fderiv_periodicFunction_add_planeDeckVector hdesc]

/-- Periodicity extends the compact fundamental-square Picard time to the whole plane. -/
theorem exists_uniformPlaneIntegralCurves_of_periodicQuotient
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ 2 f) (hdesc : ∀ uv, f uv = g (planeExpPair uv)) :
    Nonempty (UniformPlaneIntegralCurves (rotatedDerivativeField f)) := by
  classical
  let v := rotatedDerivativeField f
  have hv : ContDiff ℝ 1 v := contDiff_rotatedDerivativeField hf
  obtain ⟨radius, hradius, hlocal⟩ :=
    exists_uniformPlaneIntegralCurvesOnFundamentalSquare hv
  choose localCurve hlocalZero hlocalIntegral using fun x : Plane ↦
    hlocal (planeFundamentalRepresentative x)
      (planeFundamentalRepresentative_mem_fundamentalSquare x)
  let deck (x : Plane) : Plane :=
    planeDeckVector (planeFundamentalDeckIndex x).1 (planeFundamentalDeckIndex x).2
  let curve (x : Plane) (t : ℝ) : Plane := localCurve x t + deck x
  refine ⟨{
    radius := radius
    radius_pos := hradius
    curve := curve
    curve_zero := ?_
    integral := ?_ }⟩
  · intro x
    change localCurve x 0 + deck x = x
    rw [hlocalZero]
    exact planeFundamentalRepresentative_add_deck x
  · intro x t ht
    change HasDerivWithinAt (fun u ↦ localCurve x u + deck x)
      (v (localCurve x t + deck x)) (Ioo (-radius) radius) t
    exact ((hlocalIntegral x t ht).add_const (deck x)).congr_deriv
      (rotatedDerivativeField_periodicFunction_add_planeDeckVector hdesc
        (localCurve x t) (planeFundamentalDeckIndex x).1
          (planeFundamentalDeckIndex x).2).symm

/-- Deck-aware uniqueness for complete orbits of any descended smooth planar function. -/
theorem completePeriodicRegularLevelIntegralCurves_expPair_translate_eq
    {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
    (hf : ContDiff ℝ 2 f) (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {x₁ x₂ : f ⁻¹' {y}}
    (O₁ : CompleteRegularLevelIntegralCurve f y x₁)
    (O₂ : CompleteRegularLevelIntegralCurve f y x₂)
    {s t : ℝ} (hst : planeExpPair (O₁.curve s) = planeExpPair (O₂.curve t)) :
    ∀ u : ℝ, planeExpPair (O₁.curve (s + u)) = planeExpPair (O₂.curve (t + u)) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hst)
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hst)
  let deck := planeDeckVector m n
  have hstart : O₁.curve s = O₂.curve t + deck := by
    ext
    · simpa [deck, planeDeckVector] using hm
    · simpa [deck, planeDeckVector] using hn
  let v := rotatedDerivativeField f
  let alpha : ℝ → Plane := fun u ↦ O₁.curve (u + s)
  let beta : ℝ → Plane := fun u ↦ O₂.curve (u + t) + deck
  have halpha : IsIntegralCurve alpha (fun _ ↦ v) := by
    simpa [alpha, v, Function.comp_def] using O₁.integral.comp_add s
  have hbeta : IsIntegralCurve beta (fun _ ↦ v) := by
    intro u
    have hshift : HasDerivAt (fun r ↦ O₂.curve (r + t))
        (v (O₂.curve (u + t))) u := by
      simpa [v, Function.comp_def] using
        (O₂.integral.comp_add t : IsIntegralCurve
          (O₂.curve ∘ (· + t)) ((fun _ ↦ v) ∘ (· + t))) u
    exact (hshift.add_const deck).congr_deriv
      (rotatedDerivativeField_periodicFunction_add_planeDeckVector hdesc
        (O₂.curve (u + t)) m n).symm
  have hv : ContDiff ℝ 1 v := contDiff_rotatedDerivativeField hf
  let vm := planeTangentVectorField v
  have hvm : ContDiff ℝ 1 vm := by
    change ContDiff ℝ 1 v
    exact hv
  have hfield : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane).tangent 1 (T% vm) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := Plane)).mpr hvm
  have halphaM : IsMIntegralCurve (I := 𝓘(ℝ, Plane)) alpha vm :=
    (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr halpha
  have hbetaM : IsMIntegralCurve (I := 𝓘(ℝ, Plane)) beta vm :=
    (isMIntegralCurve_iff_isIntegralCurve_plane _ _).mpr hbeta
  have hab : alpha = beta :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      hfield halphaM hbetaM (by simpa [alpha, beta, add_zero] using hstart)
  intro u
  have hu := congrFun hab u
  calc
    planeExpPair (O₁.curve (s + u)) = planeExpPair (alpha u) := by simp [alpha, add_comm]
    _ = planeExpPair (beta u) := congrArg planeExpPair hu
    _ = planeExpPair (O₂.curve (t + u)) := by
      simpa [beta, add_comm] using planeExpPair_add_planeDeckVector (O₂.curve (u + t)) m n

/-- Projection of a complete lifted orbit to a generic descended quotient level. -/
def CompleteRegularLevelIntegralCurve.projectedPeriodicOrbit
    {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) {x : f ⁻¹' {y}}
    (O : CompleteRegularLevelIntegralCurve f y x) :
    ℝ → periodicQuotientLevelSet g y :=
  fun t ↦ periodicPlaneFiberToQuotientLevel hdesc y ⟨O.curve t, O.stays_in_level t⟩

theorem CompleteRegularLevelIntegralCurve.continuous_projectedPeriodicOrbit
    {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) {x : f ⁻¹' {y}}
    (O : CompleteRegularLevelIntegralCurve f y x) :
    Continuous (O.projectedPeriodicOrbit hdesc) := by
  apply Continuous.subtype_mk
  exact planeExpPair_isLocalHomeomorph.continuous.comp
    (continuous_iff_continuousAt.mpr fun t ↦ (O.integral t).continuousAt)

theorem CompleteRegularLevelIntegralCurve.isLocalHomeomorph_projectedPeriodicOrbit
    {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    (hy : IsRegularValue f y) {x : f ⁻¹' {y}}
    (O : CompleteRegularLevelIntegralCurve f y x) :
    IsLocalHomeomorph (O.projectedPeriodicOrbit hdesc) := by
  let liftCurve : ℝ → (f ⁻¹' {y}) := fun t ↦ ⟨O.curve t, O.stays_in_level t⟩
  have hfTwo : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hliftContinuous : Continuous liftCurve := Continuous.subtype_mk
    (continuous_iff_continuousAt.mpr fun t ↦ (O.integral t).continuousAt) _
  have hliftInjective : IsLocallyInjective liftCurve := by
    intro t
    obtain ⟨U, hUopen, htU, hUinj⟩ := O.isLocallyInjective hfTwo hy t
    exact ⟨U, hUopen, htU, fun a ha b hb hab ↦
      hUinj ha hb (congrArg Subtype.val hab)⟩
  have hcoverInjective : IsLocallyInjective
      (periodicPlaneFiberToQuotientLevel hdesc y) :=
    (periodicPlaneFiberToQuotientLevel_isLocalHomeomorph hdesc y).isLocallyInjective
  have hlocalInjective : IsLocallyInjective (O.projectedPeriodicOrbit hdesc) := by
    have hcomp := IsLocallyInjective.comp_of_continuous
      hcoverInjective hliftInjective hliftContinuous
    change IsLocallyInjective (periodicPlaneFiberToQuotientLevel hdesc y ∘ liftCurve)
    exact hcomp
  exact isLocalHomeomorph_of_continuous_locallyInjective_locallyLineModeled
    (isLocallyLineModeled_periodicQuotientLevel_of_regularValue hf hdesc hy)
    (O.continuous_projectedPeriodicOrbit hdesc) hlocalInjective

theorem CompleteRegularLevelIntegralCurve.projectedPeriodicOrbit_mem_componentPiece
    {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
    (hdesc : ∀ uv, f uv = g (planeExpPair uv)) {x : f ⁻¹' {y}}
    (O : CompleteRegularLevelIntegralCurve f y x) (t : ℝ) :
    O.projectedPeriodicOrbit hdesc t ∈ componentPiece
      (ConnectedComponents.mk (O.projectedPeriodicOrbit hdesc 0)) := by
  rw [componentPiece, connectedComponents_preimage_singleton]
  have hconnected : IsConnected (Set.range (O.projectedPeriodicOrbit hdesc)) :=
    isConnected_range (O.continuous_projectedPeriodicOrbit hdesc)
  apply hconnected.subset_connectedComponent
  · exact ⟨0, rfl⟩
  · exact ⟨t, rfl⟩

/-- A complete lifted rotated-gradient orbit together with its exact quotient-component
parametrization.  Unlike `HomogeneousLocalOrbit`, this structure retains the smooth planar lift
which produced the topological orbit. -/
structure PeriodicRegularComponentCompleteOrbit
    (f : Plane → ℝ) (g : Circle × Circle → ℝ) (y : ℝ)
    (c : ConnectedComponents (periodicQuotientLevelSet g y)) where
  basepointLift : f ⁻¹' {y}
  liftedIntegral : CompleteRegularLevelIntegralCurve f y basepointLift
  curve : ℝ → componentPiece c
  curve_eq_expPair : ∀ t,
    (curve t : periodicQuotientLevelSet g y).1 =
      planeExpPair (liftedIntegral.curve t)
  localHomeomorph_curve : IsLocalHomeomorph curve
  surjective_curve : Function.Surjective curve
  translate_eq_of_eq : ∀ {s t : ℝ}, curve s = curve t →
    ∀ u : ℝ, curve (s + u) = curve (t + u)

namespace PeriodicRegularComponentCompleteOrbit

variable {f : Plane → ℝ} {g : Circle × Circle → ℝ} {y : ℝ}
  {c : ConnectedComponents (periodicQuotientLevelSet g y)}

/-- Forget the retained smooth lift and expose the homogeneous orbit used by the existing circle
classification. -/
def toHomogeneousLocalOrbit (O : PeriodicRegularComponentCompleteOrbit f g y c) :
    HomogeneousLocalOrbit (componentPiece c) where
  curve := O.curve
  localHomeomorph_curve := O.localHomeomorph_curve
  surjective_curve := O.surjective_curve
  translate_eq_of_eq := O.translate_eq_of_eq

/-- The retained complete orbit has the same canonical cyclic parametrization as the existing
topological classification route. -/
def cyclicLineParametrization (O : PeriodicRegularComponentCompleteOrbit f g y c)
    [CompactSpace (componentPiece c)] :
    CyclicLineParametrization (componentPiece c) :=
  O.toHomogeneousLocalOrbit.cyclicLineParametrization

end PeriodicRegularComponentCompleteOrbit

/-- Every component of a regular descended quotient level is one complete projected
rotated-gradient orbit, retaining its smooth planar lift. -/
theorem exists_periodicRegularComponentCompleteOrbit
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {y : ℝ} (hy : IsRegularValue f y)
    (c : ConnectedComponents (periodicQuotientLevelSet g y)) :
    Nonempty (PeriodicRegularComponentCompleteOrbit f g y c) := by
  let Level := periodicQuotientLevelSet g y
  let _ : LocallyConnectedSpace Level := locallyConnectedSpace_of_isLocallyLineModeled
    (isLocallyLineModeled_periodicQuotientLevel_of_regularValue hf hdesc hy)
  have hfTwo : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  let uniform := Classical.choice
    (exists_uniformPlaneIntegralCurves_of_periodicQuotient hfTwo hdesc)
  obtain ⟨baseValue, hbaseValue⟩ := componentPiece_nonempty c
  let basepoint : componentPiece c := ⟨baseValue, hbaseValue⟩
  obtain ⟨baseLift, hbaseLift⟩ :=
    periodicPlaneFiberToQuotientLevel_surjective hdesc y basepoint.1
  let lifted := Classical.choice
    (exists_completeRegularLevelIntegralCurve_of_uniformPlane hfTwo uniform baseLift)
  let levelCurve := lifted.projectedPeriodicOrbit hdesc
  have hlevelZero : levelCurve 0 = basepoint.1 := by
    rw [show levelCurve 0 = periodicPlaneFiberToQuotientLevel hdesc y baseLift by
      apply Subtype.ext
      simp [levelCurve, CompleteRegularLevelIntegralCurve.projectedPeriodicOrbit,
        lifted.curve_zero]]
    exact hbaseLift
  have hlevelComponent (t : ℝ) : levelCurve t ∈ componentPiece c := by
    have hmem := lifted.projectedPeriodicOrbit_mem_componentPiece hdesc t
    change levelCurve t ∈ componentPiece (ConnectedComponents.mk (levelCurve 0)) at hmem
    rwa [hlevelZero, show ConnectedComponents.mk basepoint.1 = c from basepoint.2] at hmem
  let curve : ℝ → componentPiece c := fun t ↦ ⟨levelCurve t, hlevelComponent t⟩
  have hlevelLocal : IsLocalHomeomorph levelCurve :=
    lifted.isLocalHomeomorph_projectedPeriodicOrbit hf hdesc hy
  have hcurveLocal : IsLocalHomeomorph curve := by
    apply isLocalHomeomorph_codRestrict_open hlevelLocal (componentPiece c)
      (isClopen_componentPiece c).2
  have orbitAt : ∀ z : Level,
      ∃ (zLift : f ⁻¹' {y}) (Oz : CompleteRegularLevelIntegralCurve f y zLift),
        Oz.projectedPeriodicOrbit hdesc 0 = z := by
    intro z
    obtain ⟨zLift, hzLift⟩ := periodicPlaneFiberToQuotientLevel_surjective hdesc y z
    let Oz := Classical.choice
      (exists_completeRegularLevelIntegralCurve_of_uniformPlane hfTwo uniform zLift)
    refine ⟨zLift, Oz, ?_⟩
    rw [show Oz.projectedPeriodicOrbit hdesc 0 =
      periodicPlaneFiberToQuotientLevel hdesc y zLift by
      apply Subtype.ext
      simp [CompleteRegularLevelIntegralCurve.projectedPeriodicOrbit, Oz.curve_zero]]
    exact hzLift
  have hcurveSurjective : Function.Surjective curve := by
    let rangeCurve : Set (componentPiece c) := Set.range curve
    have hrangeOpen : IsOpen rangeCurve := by
      simpa only [image_univ] using hcurveLocal.isOpenMap Set.univ isOpen_univ
    have hcomplOpen : IsOpen rangeCurveᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨zLift, Oz, hOzZero⟩ := orbitAt z.1
      let zLevelCurve := Oz.projectedPeriodicOrbit hdesc
      have hzComponent (t : ℝ) : zLevelCurve t ∈ componentPiece c := by
        have hmem := Oz.projectedPeriodicOrbit_mem_componentPiece hdesc t
        rw [hOzZero, show ConnectedComponents.mk z.1 = c from z.2] at hmem
        exact hmem
      let zCurve : ℝ → componentPiece c := fun t ↦ ⟨zLevelCurve t, hzComponent t⟩
      have hzLocal : IsLocalHomeomorph zCurve := by
        apply isLocalHomeomorph_codRestrict_open
          (Oz.isLocalHomeomorph_projectedPeriodicOrbit hf hdesc hy)
          (componentPiece c) (isClopen_componentPiece c).2
      refine ⟨Set.range zCurve, ?_, ?_, ⟨0, ?_⟩⟩
      · rintro w ⟨tw, rfl⟩ ⟨s, hs⟩
        have hmeet : planeExpPair (lifted.curve s) = planeExpPair (Oz.curve tw) := by
          have hw := congrArg (fun p : componentPiece c ↦ (p.1 : Circle × Circle)) hs
          simpa [curve, levelCurve, zCurve, zLevelCurve,
            CompleteRegularLevelIntegralCurve.projectedPeriodicOrbit,
            periodicPlaneFiberToQuotientLevel] using hw
        have htranslate := completePeriodicRegularLevelIntegralCurves_expPair_translate_eq
          hfTwo hdesc lifted Oz hmeet (-tw)
        apply hz
        refine ⟨s - tw, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        calc
          planeExpPair (lifted.curve (s - tw)) = planeExpPair (Oz.curve 0) := by
            simpa [sub_eq_add_neg] using htranslate
          _ = (z : Level).1 := congrArg Subtype.val hOzZero
      · simpa only [image_univ] using hzLocal.isOpenMap Set.univ isOpen_univ
      · apply Subtype.ext
        exact hOzZero
    have hrangeClosed : IsClosed rangeCurve := by
      rw [← isOpen_compl_iff]
      simpa only [compl_compl] using hcomplOpen
    have hrangeClopen : IsClopen rangeCurve := ⟨hrangeClosed, hrangeOpen⟩
    let _ : PreconnectedSpace (componentPiece c) :=
      isPreconnected_iff_preconnectedSpace.mp (isConnected_componentPiece c).2
    have hrangeUniv : rangeCurve = Set.univ :=
      hrangeClopen.eq_univ ⟨curve 0, ⟨0, rfl⟩⟩
    intro z
    have hzRange : z ∈ rangeCurve := hrangeUniv.symm ▸ mem_univ z
    exact hzRange
  refine ⟨{
    basepointLift := baseLift
    liftedIntegral := lifted
    curve := curve
    curve_eq_expPair := fun _ ↦ rfl
    localHomeomorph_curve := hcurveLocal
    surjective_curve := hcurveSurjective
    translate_eq_of_eq := ?_ }⟩
  intro s t hst u
  apply Subtype.ext
  apply Subtype.ext
  have hmeet : planeExpPair (lifted.curve s) = planeExpPair (lifted.curve t) :=
    congrArg (fun p : componentPiece c ↦ (p.1 : Circle × Circle)) hst
  exact completePeriodicRegularLevelIntegralCurves_expPair_translate_eq
    hfTwo hdesc lifted lifted hmeet u

/-- Every component of a regular descended quotient level is one homogeneous complete orbit. -/
theorem exists_homogeneousLocalOrbit_periodicRegularLevel
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {y : ℝ} (hy : IsRegularValue f y)
    (c : ConnectedComponents (periodicQuotientLevelSet g y)) :
    Nonempty (HomogeneousLocalOrbit (componentPiece c)) := by
  let O := Classical.choice
    (exists_periodicRegularComponentCompleteOrbit hf hdesc hy c)
  exact ⟨O.toHomogeneousLocalOrbit⟩

/-- A regular value of a smooth planar function descended through the product exponential has a
componentwise circle classification on the quotient torus. -/
def componentCircleClassification_periodicRegularLevel
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : Continuous g)
    (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {y : ℝ} (hy : IsRegularValue f y) :
    ComponentCircleClassification (periodicQuotientLevelSet g y) := by
  let _ : CompactSpace (periodicQuotientLevelSet g y) :=
    isCompact_iff_compactSpace.mp (isCompact_periodicQuotientLevelSet hg y)
  let _ : LocallyConnectedSpace (periodicQuotientLevelSet g y) :=
    locallyConnectedSpace_of_isLocallyLineModeled
      (isLocallyLineModeled_periodicQuotientLevel_of_regularValue hf hdesc hy)
  apply componentCircleClassificationOfCyclicParametrizations
  intro c
  let _ : CompactSpace (componentPiece c) :=
    isCompact_iff_compactSpace.mp (isClopen_componentPiece c).isClosed.isCompact
  let orbit := Classical.choice
    (exists_homogeneousLocalOrbit_periodicRegularLevel hf hdesc hy c)
  exact orbit.cyclicLineParametrization

end Submission.SurfaceRegularValue
