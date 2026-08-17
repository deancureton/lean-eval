import Submission.Topology.CoveringInjectiveCarrier
import Submission.Topology.TwoArcCircle

/-!
# Covering-injective neighborhoods of coherent theta lifts

Three embedded torus arcs with the same endpoints form a theta graph when distinct arcs meet
only at those endpoints.  If the three arcs have plane lifts with common lifted endpoints,
the torus covering projection is injective on their lifted union.  Compactness and local
injectivity then enlarge that union to a covering-injective open neighborhood.

The separate `ZeroWindingThetaData` records the natural input from geometry: the two circles
formed by a reference edge and either other edge have zero winding.  The construction below
turns those equalities into `CoherentPlaneLiftData` by a deck translation and coordinate-lift
uniqueness; no global attachment conclusion is assumed here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

/-- Three injective arcs with common endpoints and no intersections away from the endpoints. -/
structure TorusThetaPathSystem (Phi : AmbientIsotopy) where
  source : transportedTorus Phi
  target : transportedTorus Phi
  edge : Fin 3 → Path source target
  edge_injective : ∀ i, Function.Injective (edge i)
  edge_range_inter : ∀ {i j}, i ≠ j →
    Set.range (edge i) ∩ Set.range (edge j) = {source, target}

namespace TorusThetaPathSystem

variable {T : TorusThetaPathSystem Phi}

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- The torus carrier of all three theta edges. -/
def carrier : Set (transportedTorus Phi) :=
  ⋃ i, Set.range (T.edge i)

/-- The canonical circle made from the reference edge and one of the other two edges. -/
def referenceCycleMap (j : Fin 2) : Circle → transportedTorus Phi :=
  TwoArcCircle.circleMap (T.edge 0) (T.edge j.succ).symm

/-- The two canonical reference cycles, bundled with the winding data used elsewhere in the
project.  Exact agreement with `referenceCycleMap` prevents an unrelated zero-winding circle
from satisfying the contract. -/
structure ZeroWindingThetaData where
  circle : Fin 2 → EmbeddedTorusIntersectionCircle Phi
  circle_eq : ∀ j z, (circle j).circle z = (T.referenceCycleMap j z : R3)
  zeroWinding : ∀ j, (circle j).windingLoop.windingPair = (0, 0)

/-- Circle parameter traversing the reference edge from source to target. -/
def referenceParameter (t : unitInterval) : Circle :=
  TwoArcCircle.circleHomeomorph (TwoArcCircle.firstCoordinate t)

/-- Circle parameter traversing the other edge from target back to source. -/
def otherParameter (t : unitInterval) : Circle :=
  TwoArcCircle.circleHomeomorph (TwoArcCircle.secondCoordinate t)

private theorem firstCoordinate_eq_coe (t : unitInterval) :
    TwoArcCircle.firstCoordinate t = ((t : ℝ) : AddCircle (2 : ℝ)) := by
  apply (AddCircle.equivIco (2 : ℝ) (0 : ℝ)).injective
  rw [TwoArcCircle.firstCoordinate, Equiv.apply_symm_apply,
    AddCircle.equivIco_coe_eq]
  constructor <;> norm_num <;> linarith [t.2.1, t.2.2]

private theorem referenceParameter_eq_exp (t : unitInterval) :
    referenceParameter t = Circle.exp (Real.pi * (t : ℝ)) := by
  rw [referenceParameter, firstCoordinate_eq_coe,
    TwoArcCircle.circleHomeomorph, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]
  ring_nf

private theorem otherParameter_eq_exp (t : unitInterval) :
    otherParameter t = Circle.exp (Real.pi * ((t : ℝ) + 1)) := by
  rw [otherParameter, TwoArcCircle.secondCoordinate,
    TwoArcCircle.circleHomeomorph, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]
  ring_nf

theorem continuous_referenceParameter : Continuous referenceParameter := by
  apply (Circle.exp.continuous.comp
    (continuous_const.mul continuous_subtype_val)).congr
  intro t
  exact (referenceParameter_eq_exp t).symm

theorem continuous_otherParameter : Continuous otherParameter := by
  apply (Circle.exp.continuous.comp
    (continuous_const.mul (continuous_subtype_val.add continuous_const))).congr
  intro t
  exact (otherParameter_eq_exp t).symm

@[simp] theorem referenceCycleMap_referenceParameter
    (j : Fin 2) (t : unitInterval) :
    T.referenceCycleMap j (referenceParameter t) = T.edge 0 t := by
  rw [referenceCycleMap, referenceParameter, TwoArcCircle.circleMap,
    Function.comp_apply, TwoArcCircle.circleHomeomorph.symm_apply_apply,
    TwoArcCircle.addCircleMap_firstCoordinate]

@[simp] theorem referenceCycleMap_otherParameter
    (j : Fin 2) (t : unitInterval) :
    T.referenceCycleMap j (otherParameter t) = (T.edge j.succ).symm t := by
  rw [referenceCycleMap, otherParameter, TwoArcCircle.circleMap,
    Function.comp_apply, TwoArcCircle.circleHomeomorph.symm_apply_apply,
    TwoArcCircle.addCircleMap_secondCoordinate]

/-- Three plane path lifts on common source and target sheets. -/
structure CoherentPlaneLiftData where
  sourceLift : TorusCoveringPlane
  targetLift : TorusCoveringPlane
  edgeLift : Fin 3 → Path sourceLift targetLift
  projection : ∀ i t,
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (edgeLift i t) =
      T.edge i t

namespace ZeroWindingThetaData

variable (Z : T.ZeroWindingThetaData)

/-- The closed plane lift supplied by zero winding for one reference cycle. -/
def cyclePlaneLift (j : Fin 2) : Circle → TorusCoveringPlane :=
  (Z.circle j).zeroWindingPlaneCircle (Z.zeroWinding j)

theorem continuous_cyclePlaneLift (j : Fin 2) : Continuous (Z.cyclePlaneLift j) :=
  (Z.circle j).continuous_zeroWindingPlaneCircle (Z.zeroWinding j)

theorem projection_cyclePlaneLift (j : Fin 2) (z : Circle) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.cyclePlaneLift j z) = T.referenceCycleMap j z := by
  apply Subtype.ext
  rw [EmbeddedTorusIntersectionCircle.coe_torusCoveringProjectionToTorus,
    cyclePlaneLift,
    (Z.circle j).torusCoveringProjection_zeroWindingPlaneCircle (Z.zeroWinding j)]
  exact Z.circle_eq j z

/-- The plane lift of the common reference edge coming from one zero-winding cycle. -/
def referencePlanePath (j : Fin 2) : Path
    (Z.cyclePlaneLift j (referenceParameter 0))
    (Z.cyclePlaneLift j (referenceParameter 1)) where
  toFun := fun t ↦ Z.cyclePlaneLift j (referenceParameter t)
  continuous_toFun := (Z.continuous_cyclePlaneLift j).comp
    continuous_referenceParameter
  source' := rfl
  target' := rfl

/-- The other lifted edge, still oriented from target back to source. -/
def reverseOtherPlanePath (j : Fin 2) : Path
    (Z.cyclePlaneLift j (otherParameter 0))
    (Z.cyclePlaneLift j (otherParameter 1)) where
  toFun := fun t ↦ Z.cyclePlaneLift j (otherParameter t)
  continuous_toFun := (Z.continuous_cyclePlaneLift j).comp
    continuous_otherParameter
  source' := rfl
  target' := rfl

theorem projection_referencePlanePath (j : Fin 2) (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.referencePlanePath j t) = T.edge 0 t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.cyclePlaneLift j (referenceParameter t)) = T.edge 0 t
  rw [Z.projection_cyclePlaneLift,
    T.referenceCycleMap_referenceParameter]

theorem projection_reverseOtherPlanePath (j : Fin 2) (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.reverseOtherPlanePath j t) = (T.edge j.succ).symm t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.cyclePlaneLift j (otherParameter t)) = (T.edge j.succ).symm t
  rw [Z.projection_cyclePlaneLift,
    T.referenceCycleMap_otherParameter]

private theorem exp_apply_eq_of_projection_eq
    {x y : TorusCoveringPlane}
    (h : EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi y)
    (k : Fin 2) : Circle.exp (x k) = Circle.exp (y k) := by
  change transportedTorusHomeomorph Phi
      (Circle.exp (x 0), Circle.exp (x 1)) =
    transportedTorusHomeomorph Phi
      (Circle.exp (y 0), Circle.exp (y 1)) at h
  have hprod := (transportedTorusHomeomorph Phi).injective h
  fin_cases k
  · exact congrArg Prod.fst hprod
  · exact congrArg Prod.snd hprod

/-- Two continuous plane lifts of the same torus path agree once they agree at the source. -/
private theorem planeLift_eq_of_projection_eq
    (p q : unitInterval → TorusCoveringPlane)
    (hp : Continuous p) (hq : Continuous q)
    (hprojection : ∀ t,
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (p t) =
        EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi (q t))
    (hsource : p 0 = q 0) : p = q := by
  funext t
  rw [WithLp.ext_iff]
  funext k
  let clamp : ℝ → unitInterval := Set.projIcc 0 1 zero_le_one
  have hclamp : Continuous clamp := continuous_projIcc
  let gamma : C(ℝ, Circle) :=
    ⟨fun s ↦ Circle.exp (p (clamp s) k), Circle.exp.continuous.comp <|
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) k).comp (hp.comp hclamp)⟩
  let pLift : C(ℝ, ℝ) :=
    ⟨fun s ↦ p (clamp s) k,
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) k).comp (hp.comp hclamp)⟩
  let qLift : C(ℝ, ℝ) :=
    ⟨fun s ↦ q (clamp s) k,
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 ↦ ℝ) k).comp (hq.comp hclamp)⟩
  have hpLift : pLift 0 = p 0 k ∧ Circle.exp ∘ pLift = gamma := by
    constructor
    · simp [pLift, clamp]
    · rfl
  have hqLift : qLift 0 = p 0 k ∧ Circle.exp ∘ qLift = gamma := by
    constructor
    · simpa [qLift, clamp] using
        congrArg (fun x : TorusCoveringPlane ↦ x k) hsource.symm
    · funext s
      exact exp_apply_eq_of_projection_eq (hprojection (clamp s)).symm k
  have heq : pLift = qLift :=
    (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gamma 0 (p 0 k) (by simp [gamma, clamp])).unique hpLift hqLift
  have ht := congrArg (fun f : C(ℝ, ℝ) ↦ f (t : ℝ)) heq
  simpa [pLift, qLift, clamp, Set.projIcc_of_mem zero_le_one t.2] using ht

/-- Deck translation aligning the second plane circle with the first at the common source. -/
def alignmentShift : TorusCoveringPlane :=
  Z.referencePlanePath 0 0 - Z.referencePlanePath 1 0

theorem projection_add_alignmentShift (x : TorusCoveringPlane) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (x + Z.alignmentShift) =
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi x := by
  unfold EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus
  apply congrArg (transportedTorusHomeomorph Phi)
  change (Circle.exp ((x + Z.alignmentShift) 0),
      Circle.exp ((x + Z.alignmentShift) 1)) =
    (Circle.exp (x 0), Circle.exp (x 1))
  apply Prod.ext
  · have hbase := exp_apply_eq_of_projection_eq
        (Z.projection_referencePlanePath 0 0 |>.trans
          (Z.projection_referencePlanePath 1 0).symm) 0
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hbase
    apply Circle.exp_eq_exp.mpr
    refine ⟨n, ?_⟩
    change x 0 + (Z.referencePlanePath 0 0 0 -
      Z.referencePlanePath 1 0 0) = x 0 + (n : ℝ) * (2 * Real.pi)
    linarith
  · have hbase := exp_apply_eq_of_projection_eq
        (Z.projection_referencePlanePath 0 0 |>.trans
          (Z.projection_referencePlanePath 1 0).symm) 1
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hbase
    apply Circle.exp_eq_exp.mpr
    refine ⟨n, ?_⟩
    change x 1 + (Z.referencePlanePath 0 0 1 -
      Z.referencePlanePath 1 0 1) = x 1 + (n : ℝ) * (2 * Real.pi)
    linarith

/-- The translated second reference lift, with its source copied to the first lift's source. -/
def alignedSecondReferencePlanePath : Path
    (Z.referencePlanePath 0 0)
    (Z.referencePlanePath 1 1 + Z.alignmentShift) where
  toFun := fun t ↦ Z.referencePlanePath 1 t + Z.alignmentShift
  continuous_toFun := (Z.referencePlanePath 1).continuous.add continuous_const
  source' := by
    simp only [alignmentShift]
    abel
  target' := rfl

theorem projection_alignedSecondReferencePlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.alignedSecondReferencePlanePath t) = T.edge 0 t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.referencePlanePath 1 t + Z.alignmentShift) = T.edge 0 t
  rw [Z.projection_add_alignmentShift,
    Z.projection_referencePlanePath]

/-- Uniqueness of coordinate lifts aligns the complete reference edge, not only its source. -/
theorem alignedSecondReferencePlanePath_eq (t : unitInterval) :
    Z.alignedSecondReferencePlanePath t = Z.referencePlanePath 0 t := by
  have heq := planeLift_eq_of_projection_eq
    Z.alignedSecondReferencePlanePath (Z.referencePlanePath 0)
    Z.alignedSecondReferencePlanePath.continuous
    (Z.referencePlanePath 0).continuous
    (fun s ↦ (Z.projection_alignedSecondReferencePlanePath s).trans
      (Z.projection_referencePlanePath 0 s).symm)
    (Z.alignedSecondReferencePlanePath.source.trans
      (Z.referencePlanePath 0).source.symm)
  exact congrFun heq t

private theorem referenceParameter_one_eq_otherParameter_zero :
    referenceParameter 1 = otherParameter 0 := by
  rw [referenceParameter_eq_exp, otherParameter_eq_exp]
  congr 1
  norm_num

private theorem referenceParameter_zero_eq_otherParameter_one :
    referenceParameter 0 = otherParameter 1 := by
  rw [referenceParameter_eq_exp, otherParameter_eq_exp]
  apply Circle.exp_eq_exp.mpr
  refine ⟨(-1 : ℤ), ?_⟩
  norm_num
  ring

/-- The other edge of one lifted zero-winding cycle, reoriented from source to target. -/
def otherPlanePath (j : Fin 2) : Path
    (Z.referencePlanePath j 0) (Z.referencePlanePath j 1) where
  toFun := fun t ↦ Z.cyclePlaneLift j (otherParameter (unitInterval.symm t))
  continuous_toFun := (Z.continuous_cyclePlaneLift j).comp <|
    continuous_otherParameter.comp unitInterval.continuous_symm
  source' := by
    rw [show Z.referencePlanePath j 0 =
      Z.cyclePlaneLift j (referenceParameter 0) from rfl]
    simpa only [unitInterval.symm_zero] using congrArg (Z.cyclePlaneLift j)
      referenceParameter_zero_eq_otherParameter_one.symm
  target' := by
    rw [show Z.referencePlanePath j 1 =
      Z.cyclePlaneLift j (referenceParameter 1) from rfl]
    simpa only [unitInterval.symm_one] using congrArg (Z.cyclePlaneLift j)
      referenceParameter_one_eq_otherParameter_zero.symm

theorem projection_otherPlanePath (j : Fin 2) (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.otherPlanePath j t) = T.edge j.succ t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.cyclePlaneLift j (otherParameter (unitInterval.symm t))) =
    T.edge j.succ t
  rw [Z.projection_cyclePlaneLift,
    T.referenceCycleMap_otherParameter]
  simp [Path.symm_apply, Function.comp_apply]

/-- Translate the third edge by the same deck vector which aligned its reference edge. -/
def alignedSecondOtherPlanePath : Path
    (Z.referencePlanePath 0 0) (Z.referencePlanePath 0 1) where
  toFun := fun t ↦ Z.otherPlanePath 1 t + Z.alignmentShift
  continuous_toFun := (Z.otherPlanePath 1).continuous.add continuous_const
  source' := by
    calc
      Z.otherPlanePath 1 0 + Z.alignmentShift =
          Z.referencePlanePath 1 0 + Z.alignmentShift :=
        congrArg (fun x ↦ x + Z.alignmentShift) (Z.otherPlanePath 1).source
      _ = Z.referencePlanePath 0 0 := Z.alignedSecondReferencePlanePath_eq 0
  target' := by
    calc
      Z.otherPlanePath 1 1 + Z.alignmentShift =
          Z.referencePlanePath 1 1 + Z.alignmentShift :=
        congrArg (fun x ↦ x + Z.alignmentShift) (Z.otherPlanePath 1).target
      _ = Z.referencePlanePath 0 1 := Z.alignedSecondReferencePlanePath_eq 1

theorem projection_alignedSecondOtherPlanePath (t : unitInterval) :
    EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
        (Z.alignedSecondOtherPlanePath t) = T.edge 2 t := by
  change EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi
      (Z.otherPlanePath 1 t + Z.alignmentShift) = T.edge 2 t
  rw [Z.projection_add_alignmentShift]
  simpa using Z.projection_otherPlanePath 1 t

/-- The two zero-winding reference cycles canonically produce three coherent plane lifts. -/
noncomputable def toCoherentPlaneLiftData : T.CoherentPlaneLiftData where
  sourceLift := Z.referencePlanePath 0 0
  targetLift := Z.referencePlanePath 0 1
  edgeLift := ![Z.referencePlanePath 0, Z.otherPlanePath 0,
    Z.alignedSecondOtherPlanePath]
  projection := by
    intro i t
    fin_cases i
    · exact Z.projection_referencePlanePath 0 t
    · exact Z.projection_otherPlanePath 0 t
    · exact Z.projection_alignedSecondOtherPlanePath t

theorem nonempty_coherentPlaneLiftData (Z : T.ZeroWindingThetaData) :
    Nonempty T.CoherentPlaneLiftData :=
  ⟨toCoherentPlaneLiftData Z⟩

end ZeroWindingThetaData

namespace CoherentPlaneLiftData

variable (L : T.CoherentPlaneLiftData)

/-- The compact union of the three coherent plane lifts. -/
def carrier : Set TorusCoveringPlane :=
  ⋃ i, Set.range (L.edgeLift i)

theorem isCompact_carrier : IsCompact L.carrier := by
  rw [carrier]
  apply isCompact_iUnion
  intro i
  rw [← Set.image_univ]
  exact isCompact_univ.image (L.edgeLift i).continuous

/-- Exact endpoint incidence downstairs makes the covering projection injective on the coherent
lifted theta graph. -/
theorem projection_injOn_carrier :
    Set.InjOn
      (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi)
      L.carrier := by
  rintro x hx y hy hxy
  obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, v, rfl⟩ := Set.mem_iUnion.mp hy
  have hedge : T.edge i u = T.edge j v := by
    rw [← L.projection i u, ← L.projection j v]
    exact hxy
  by_cases hij : i = j
  · subst j
    rw [T.edge_injective i hedge]
  · have hcommon : T.edge i u ∈
        Set.range (T.edge i) ∩ Set.range (T.edge j) :=
      ⟨⟨u, rfl⟩, ⟨v, hedge.symm⟩⟩
    rw [T.edge_range_inter hij] at hcommon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcommon
    rcases hcommon with hsource | htarget
    · have hu : u = 0 := T.edge_injective i <|
        hsource.trans (T.edge i).source.symm
      have hv : v = 0 := T.edge_injective j <|
        (hedge.symm.trans hsource).trans (T.edge j).source.symm
      subst u
      subst v
      rw [(L.edgeLift i).source, (L.edgeLift j).source]
    · have hu : u = 1 := T.edge_injective i <|
        htarget.trans (T.edge i).target.symm
      have hv : v = 1 := T.edge_injective j <|
        (hedge.symm.trans htarget).trans (T.edge j).target.symm
      subst u
      subst v
      rw [(L.edgeLift i).target, (L.edgeLift j).target]

/-- Every point of the torus theta carrier is the projection of the coherent lifted carrier. -/
theorem thetaCarrier_subset_projection_image :
    T.carrier ⊆
      EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' L.carrier := by
  intro x hx
  obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
  refine ⟨L.edgeLift i t, Set.mem_iUnion.mpr ⟨i, t, rfl⟩, ?_⟩
  exact L.projection i t

/-- A coherent lifted theta graph has an open covering-injective plane neighborhood whose
projection contains the entire torus theta carrier. -/
theorem exists_open_injOn_coveringProjection :
    ∃ U : Set TorusCoveringPlane,
      IsOpen U ∧ L.carrier ⊆ U ∧
        Set.InjOn
          (EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi) U ∧
        T.carrier ⊆
          EmbeddedTorusIntersectionCircle.torusCoveringProjectionToTorus Phi '' U := by
  have hlocal :=
    (EmbeddedTorusIntersectionCircle.isLocalHomeomorph_torusCoveringProjectionToTorus Phi)
      |>.isLocallyInjective
  obtain ⟨U, hU, hLU, hinj⟩ :=
    L.projection_injOn_carrier.exists_isOpen_superset L.isCompact_carrier
      (fun _ _ ↦
        (EmbeddedTorusIntersectionCircle.isLocalHomeomorph_torusCoveringProjectionToTorus
          Phi).continuous.continuousAt)
      (fun x _ ↦ (isLocallyInjective_iff_nhds.mp hlocal x))
  refine ⟨U, hU, hLU, hinj, ?_⟩
  exact L.thetaCarrier_subset_projection_image.trans <| Set.image_mono hLU

end CoherentPlaneLiftData
end TorusThetaPathSystem
end Submission.Topology
