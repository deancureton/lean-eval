import Submission.Topology.SuperellipsoidCanonicalEndpointGraphs
import Submission.Topology.SuperellipsoidGlobalBandTubularChart
import Submission.Topology.SuperellipsoidInwardClosedGapPackage
import Submission.Topology.SuperellipsoidOuterClosedGapPackage

/-!
# Canonical finite arcs for the central superellipsoid barrier

The central barrier consists of active lower and upper outer gaps, seam-free outer circles,
active inward cutting gaps, and seam-free inward cutting circles.  This file first supplies the
small missing bridge from an embedded torus circle to a closed path with exactly the same range,
then packages those five finite kinds of edge into one canonical index type.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

namespace EmbeddedTorusIntersectionCircle

variable {Phi : AmbientIsotopy}

/-- A closed path which traverses the real-periodic parametrization of an embedded circle once. -/
def fullPath (C : EmbeddedTorusIntersectionCircle Phi) :
    Path (C.windingLoop.curve 0) (C.windingLoop.curve 0) where
  toContinuousMap :=
    ⟨fun u ↦ C.windingLoop.curve ((2 * Real.pi) * (u : ℝ)),
      C.windingLoop.continuous_curve.comp
        (continuous_const.mul continuous_subtype_val)⟩
  source' := by simp
  target' := by
    convert C.windingLoop.periodic_curve 0 using 1
    all_goals norm_num

@[simp] theorem fullPath_apply (C : EmbeddedTorusIntersectionCircle Phi) (u : unitInterval) :
    C.fullPath u = C.windingLoop.curve ((2 * Real.pi) * (u : ℝ)) :=
  rfl

/-- The closed full path has exactly the carrier of the original embedded circle. -/
theorem range_fullPath (C : EmbeddedTorusIntersectionCircle Phi) :
    Set.range (fun u ↦ (C.fullPath u : R3)) = Set.range C.circle := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Circle.exp ((2 * Real.pi) * (u : ℝ)), ?_⟩
    simpa only [fullPath_apply] using C.parametrization ((2 * Real.pi) * (u : ℝ))
  · rintro ⟨z, rfl⟩
    let s := circlePhaseRepresentative z
    have hs := circlePhaseRepresentative_mem z
    let u : unitInterval := ⟨s / (2 * Real.pi), by
      constructor
      · exact div_nonneg hs.1 Real.two_pi_pos.le
      · rw [div_le_one Real.two_pi_pos]
        exact hs.2.le⟩
    refine ⟨u, ?_⟩
    change (C.windingLoop.curve ((2 * Real.pi) * (u : ℝ)) : R3) = C.circle z
    have hparameter : (2 * Real.pi) * (u : ℝ) = s := by
      dsimp [u]
      field_simp [ne_of_gt Real.two_pi_pos]
    rw [hparameter, ← C.parametrization, exp_circlePhaseRepresentative]

end EmbeddedTorusIntersectionCircle

namespace FiniteSuperellipsoidBarrierGraph

universe u

/-- The five kinds of canonical edge in a cyclically ordered finite barrier graph. -/
abbrev CanonicalBarrierEdge
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) :=
  outerOrder.GlobalLowerOuterGap ⊕ outerOrder.GlobalUpperOuterGap ⊕
    outerOrder.InactiveOuterCircle ⊕ cutOrder.GlobalInwardGap ⊕ G.InwardWholeCutCircle

noncomputable instance canonicalBarrierEdgeFintype
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) :
    Fintype (CanonicalBarrierEdge G outerOrder cutOrder) := by
  dsimp only [CanonicalBarrierEdge]
  infer_instance

/-- A path bundled with its ambient endpoints, avoiding dependent endpoint bookkeeping when
case-splitting over the five canonical edge kinds. -/
structure AmbientBarrierArc where
  sourcePoint : R3
  targetPoint : R3
  path : Path sourcePoint targetPoint

namespace AmbientBarrierArc

/-- Regard any ambient path as a bundled barrier arc. -/
def ofPath {x y : R3} (path : Path x y) : AmbientBarrierArc where
  sourcePoint := x
  targetPoint := y
  path := path

/-- Map a path in the transported torus to its ambient barrier arc. -/
def ofTorusPath {Phi : AmbientIsotopy} {x y : transportedTorus Phi} (path : Path x y) :
    AmbientBarrierArc :=
  ofPath (path.map continuous_subtype_val)

@[simp] theorem ofTorusPath_sourcePoint
    {Phi : AmbientIsotopy} {x y : transportedTorus Phi} (path : Path x y) :
    (ofTorusPath path).sourcePoint = (path 0 : R3) := by
  change (x : R3) = (path 0 : R3)
  exact congrArg Subtype.val (Path.source path).symm

@[simp] theorem ofTorusPath_targetPoint
    {Phi : AmbientIsotopy} {x y : transportedTorus Phi} (path : Path x y) :
    (ofTorusPath path).targetPoint = (path 1 : R3) := by
  change (y : R3) = (path 1 : R3)
  exact congrArg Subtype.val (Path.target path).symm

end AmbientBarrierArc

/-- The actual ambient path represented by each of the five canonical barrier-edge kinds. -/
noncomputable def canonicalBarrierArc
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) :
    CanonicalBarrierEdge G outerOrder cutOrder → AmbientBarrierArc
  | Sum.inl g => AmbientBarrierArc.ofTorusPath (outerOrder.globalLowerOuterPath g)
  | Sum.inr (Sum.inl g) => AmbientBarrierArc.ofTorusPath (outerOrder.globalUpperOuterPath g)
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      AmbientBarrierArc.ofTorusPath (G.outer.circle i.1).fullPath
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl g))) =>
      AmbientBarrierArc.ofTorusPath (cutOrder.globalInwardExcursionPath g)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) =>
      AmbientBarrierArc.ofTorusPath (G.cut.circle j.1.1).fullPath

/-- Canonical source point of a finite barrier edge. -/
def canonicalBarrierSourcePoint
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) : R3 :=
  (canonicalBarrierArc G outerOrder cutOrder e).sourcePoint

/-- Canonical target point of a finite barrier edge. -/
def canonicalBarrierTargetPoint
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) : R3 :=
  (canonicalBarrierArc G outerOrder cutOrder e).targetPoint

/-- Canonical ambient path of a finite barrier edge. -/
def canonicalBarrierPath
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) :
    Path (canonicalBarrierSourcePoint G outerOrder cutOrder e)
      (canonicalBarrierTargetPoint G outerOrder cutOrder e) :=
  (canonicalBarrierArc G outerOrder cutOrder e).path

/-- Every canonical edge is either a closed whole-circle edge or has both endpoints on the
finite seam. -/
theorem canonicalBarrier_closed_or_endpoints_mem_seam
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) :
    canonicalBarrierSourcePoint G outerOrder cutOrder e =
        canonicalBarrierTargetPoint G outerOrder cutOrder e ∨
      canonicalBarrierSourcePoint G outerOrder cutOrder e ∈
          superellipsoidTorusSeam Phi frame c R d ∧
        canonicalBarrierTargetPoint G outerOrder cutOrder e ∈
          superellipsoidTorusSeam Phi frame c R d := by
  rcases e with g | g | i | g | j
  · right
    constructor
    · rw [show canonicalBarrierSourcePoint G outerOrder cutOrder (Sum.inl g) =
          ((outerOrder.globalLowerOuterPath g 0 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierSourcePoint, canonicalBarrierArc]]
      have h := (outerOrder.globalLowerEndpointEquiv (g, (0 : Fin 2))).2
      rw [outerOrder.globalLowerEndpointEquiv_val_eq_path_endpoint] at h
      change ((outerOrder.globalLowerOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval 0) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero] using h
    · rw [show canonicalBarrierTargetPoint G outerOrder cutOrder (Sum.inl g) =
          ((outerOrder.globalLowerOuterPath g 1 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierTargetPoint, canonicalBarrierArc]]
      have h := (outerOrder.globalLowerEndpointEquiv (g, (1 : Fin 2))).2
      rw [outerOrder.globalLowerEndpointEquiv_val_eq_path_endpoint] at h
      change ((outerOrder.globalLowerOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval 1) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one] using h
  · right
    constructor
    · rw [show canonicalBarrierSourcePoint G outerOrder cutOrder (Sum.inr (Sum.inl g)) =
          ((outerOrder.globalUpperOuterPath g 0 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierSourcePoint, canonicalBarrierArc]]
      have h := (outerOrder.globalUpperEndpointEquiv (g, (0 : Fin 2))).2
      rw [outerOrder.globalUpperEndpointEquiv_val_eq_path_endpoint] at h
      change ((outerOrder.globalUpperOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval 0) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_zero] using h
    · rw [show canonicalBarrierTargetPoint G outerOrder cutOrder (Sum.inr (Sum.inl g)) =
          ((outerOrder.globalUpperOuterPath g 1 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierTargetPoint, canonicalBarrierArc]]
      have h := (outerOrder.globalUpperEndpointEquiv (g, (1 : Fin 2))).2
      rw [outerOrder.globalUpperEndpointEquiv_val_eq_path_endpoint] at h
      change ((outerOrder.globalUpperOuterPath g
        (OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval 1) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [OuterCircleTransverseHeightCyclicOrderFamily.finTwoUnitInterval_one] using h
  · left
    rfl
  · right
    constructor
    · rw [show canonicalBarrierSourcePoint G outerOrder cutOrder
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))) =
          ((cutOrder.globalInwardExcursionPath g 0 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierSourcePoint, canonicalBarrierArc]]
      have h := (cutOrder.globalEndpointEquiv (g, (0 : Fin 2))).2
      rw [cutOrder.globalEndpointEquiv_val_eq_path_endpoint] at h
      change ((cutOrder.globalInwardExcursionPath g
        (CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval 0) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_zero] using h
    · rw [show canonicalBarrierTargetPoint G outerOrder cutOrder
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))) =
          ((cutOrder.globalInwardExcursionPath g 1 : transportedTorus Phi) : R3) by
          simp [canonicalBarrierTargetPoint, canonicalBarrierArc]]
      have h := (cutOrder.globalEndpointEquiv (g, (1 : Fin 2))).2
      rw [cutOrder.globalEndpointEquiv_val_eq_path_endpoint] at h
      change ((cutOrder.globalInwardExcursionPath g
        (CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval 1) :
          transportedTorus Phi) : R3) ∈ superellipsoidTorusSeam Phi frame c R d at h
      simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_one] using h
  · left
    rfl

/-- Every point of every canonical edge lies in the literal finite barrier carrier. -/
theorem canonicalBarrierPath_mem_carrier
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) (u : unitInterval) :
    canonicalBarrierPath G outerOrder cutOrder e u ∈ G.carrier := by
  rcases e with g | g | i | g | j
  · change ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) ∈ G.carrier
    exact Or.inl (Set.mem_iUnion.mpr ⟨g.1.1,
      outerOrder.gapPath_mem_outerCircle (outerOrder.lowerGapAsGlobalOuterGap g) u⟩)
  · change ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) ∈ G.carrier
    exact Or.inl (Set.mem_iUnion.mpr ⟨g.1.1,
      outerOrder.gapPath_mem_outerCircle (outerOrder.upperGapAsGlobalOuterGap g) u⟩)
  · change ((G.outer.circle i.1).windingLoop.curve ((2 * Real.pi) * (u : ℝ)) : R3) ∈
      G.carrier
    refine Or.inl (Set.mem_iUnion.mpr ⟨i.1, ?_⟩)
    exact ⟨Circle.exp ((2 * Real.pi) * (u : ℝ)),
      (G.outer.circle i.1).parametrization _⟩
  · change ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3) ∈
      G.carrier
    by_cases hu0 : (u : ℝ) = 0
    · have hu : u = (0 : unitInterval) := Subtype.ext hu0
      subst u
      have hseam := (cutOrder.globalEndpointEquiv (g, (0 : Fin 2))).2
      change (cutOrder.globalEndpointEquiv (g, (0 : Fin 2))).1 ∈
        superellipsoidTorusSeam Phi frame c R d at hseam
      rw [cutOrder.globalEndpointEquiv_val_eq_path_endpoint] at hseam
      have houter : ((cutOrder.globalInwardExcursionPath g 0 : transportedTorus Phi) : R3) ∈
          superellipsoidOuterTorusSection Phi frame c R := by
        simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_zero,
          superellipsoidOuterTorusSection] using hseam.1
      have houterUnion :
          ((cutOrder.globalInwardExcursionPath g 0 : transportedTorus Phi) : R3) ∈
            (⋃ i : outerIndex, Set.range (G.outer.circle i).circle) := by
        exact (Set.ext_iff.mp G.outer.section_exact _).mp houter
      exact Or.inl houterUnion
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = (1 : unitInterval) := Subtype.ext hu1
        subst u
        have hseam := (cutOrder.globalEndpointEquiv (g, (1 : Fin 2))).2
        change (cutOrder.globalEndpointEquiv (g, (1 : Fin 2))).1 ∈
          superellipsoidTorusSeam Phi frame c R d at hseam
        rw [cutOrder.globalEndpointEquiv_val_eq_path_endpoint] at hseam
        have houter :
            ((cutOrder.globalInwardExcursionPath g 1 : transportedTorus Phi) : R3) ∈
              superellipsoidOuterTorusSection Phi frame c R := by
          simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_one,
            superellipsoidOuterTorusSection] using hseam.1
        have houterUnion :
            ((cutOrder.globalInwardExcursionPath g 1 : transportedTorus Phi) : R3) ∈
              (⋃ i : outerIndex, Set.range (G.outer.circle i).circle) := by
          exact (Set.ext_iff.mp G.outer.section_exact _).mp houter
        exact Or.inl houterUnion
      · refine Or.inr (Set.mem_iUnion.mpr ⟨g.1.1, ?_⟩)
        exact ⟨cutOrder.globalInwardExcursionPath_mem_cutCircle g u,
          cutOrder.globalInwardExcursionPath_mem_body g u hu0 hu1⟩
  · let t := (2 * Real.pi) * (u : ℝ)
    change ((G.cut.circle j.1.1).windingLoop.curve t : R3) ∈ G.carrier
    refine Or.inr (Set.mem_iUnion.mpr ⟨j.1.1, ?_⟩)
    refine ⟨⟨Circle.exp t, (G.cut.circle j.1.1).parametrization t⟩, ?_⟩
    exact (G.cutCircleOuterPolynomialDifference_neg_iff_body j.1.1 hR t).mp
      (G.inwardWholeCutCircle_all_inward hR.le j t)

/-- The range of every canonical edge is contained in the finite barrier carrier. -/
theorem range_canonicalBarrierPath_subset_carrier
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) :
    Set.range (canonicalBarrierPath G outerOrder cutOrder e) ⊆ G.carrier := by
  rintro _ ⟨u, rfl⟩
  exact canonicalBarrierPath_mem_carrier G outerOrder cutOrder hR e u

/-- The open interior of a nonclosed canonical edge avoids every seam vertex. -/
theorem canonicalBarrierPath_interior_not_mem_seam
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (e : CanonicalBarrierEdge G outerOrder cutOrder) (u : unitInterval)
    (hendpoints : canonicalBarrierSourcePoint G outerOrder cutOrder e ≠
      canonicalBarrierTargetPoint G outerOrder cutOrder e)
    (hu0 : (u : ℝ) ≠ 0) (hu1 : (u : ℝ) ≠ 1) :
    canonicalBarrierPath G outerOrder cutOrder e u ∉
      superellipsoidTorusSeam Phi frame c R d := by
  rcases e with g | g | i | g | j
  · intro hx
    change ((outerOrder.globalLowerOuterPath g u : transportedTorus Phi) : R3) ∈
      superellipsoidTorusSeam Phi frame c R d at hx
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨_, hx⟩
    let ge := outerOrder.globalLowerEndpointEquiv.symm p
    apply outerOrder.globalLower_path_endpoint_ne_interior ge.1 g ge.2 u hu0 hu1
    rw [← outerOrder.globalLowerEndpointEquiv_val_eq_path_endpoint]
    exact congrArg Subtype.val (outerOrder.globalLowerEndpointEquiv.apply_symm_apply p)
  · intro hx
    change ((outerOrder.globalUpperOuterPath g u : transportedTorus Phi) : R3) ∈
      superellipsoidTorusSeam Phi frame c R d at hx
    let p : SuperellipsoidSeamVertex Phi frame c R d := ⟨_, hx⟩
    let ge := outerOrder.globalUpperEndpointEquiv.symm p
    apply outerOrder.globalUpper_path_endpoint_ne_interior ge.1 g ge.2 u hu0 hu1
    rw [← outerOrder.globalUpperEndpointEquiv_val_eq_path_endpoint]
    exact congrArg Subtype.val (outerOrder.globalUpperEndpointEquiv.apply_symm_apply p)
  · exact False.elim (hendpoints rfl)
  · intro hx
    change ((cutOrder.globalInwardExcursionPath g u : transportedTorus Phi) : R3) ∈
      superellipsoidTorusSeam Phi frame c R d at hx
    rw [cutOrder.globalInwardExcursionPath_apply] at hx
    exact G.no_cutCircleSeam_between_cyclic g.1.1
      (cutOrder.order g.1).crossings_nonempty (cutOrder.globalGapFinIndex g)
      (cutOrder.globalInwardExcursionParameter_mem_gap g u hu0 hu1) hx
  · exact False.elim (hendpoints rfl)

/-- The lower/upper active gaps and seam-free whole-circle edges cover every outer circle. -/
theorem outerCircleCarrier_subset_iUnion_range_canonicalBarrierPath
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) :
    (⋃ i : outerIndex, Set.range (G.outer.circle i).circle) ⊆
      ⋃ e : CanonicalBarrierEdge G outerOrder cutOrder,
        Set.range (canonicalBarrierPath G outerOrder cutOrder e) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  by_cases hactive : (outerOrder.regular i).crossings.Nonempty
  · let ia : outerOrder.ActiveOuterCircle := ⟨i, hactive⟩
    rcases le_total (x.ofLp (frame 2)) d with hlower | hupper
    · have hxLower :
          x ∈ (⋃ j : outerOrder.ActiveOuterCircle,
              Set.range (G.outer.circle j.1).circle) ∩ lowerClosedHalfspace frame d := by
        exact ⟨Set.mem_iUnion.mpr ⟨ia, hi⟩, hlower⟩
      have hxGaps :=
        (Set.ext_iff.mp outerOrder.iUnion_range_globalLowerOuterPath_eq x).mpr hxLower
      obtain ⟨g, u, rfl⟩ := Set.mem_iUnion.mp hxGaps
      refine Set.mem_iUnion.mpr ⟨Sum.inl g, u, ?_⟩
      rfl
    · have hxUpper :
          x ∈ (⋃ j : outerOrder.ActiveOuterCircle,
              Set.range (G.outer.circle j.1).circle) ∩ upperClosedHalfspace frame d := by
        exact ⟨Set.mem_iUnion.mpr ⟨ia, hi⟩, hupper⟩
      have hxGaps :=
        (Set.ext_iff.mp outerOrder.iUnion_range_globalUpperOuterPath_eq x).mpr hxUpper
      obtain ⟨g, u, rfl⟩ := Set.mem_iUnion.mp hxGaps
      refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl g), u, ?_⟩
      rfl
  · let ii : outerOrder.InactiveOuterCircle := ⟨i, hactive⟩
    have hi' : x ∈ Set.range (G.outer.circle ii.1).circle := by
      simpa only [ii] using hi
    have hxFull : x ∈ Set.range (fun u ↦ ((G.outer.circle ii.1).fullPath u : R3)) :=
      (Set.ext_iff.mp (G.outer.circle ii.1).range_fullPath x).mpr hi'
    obtain ⟨u, rfl⟩ := hxFull
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inl ii)), u, ?_⟩
    rfl

/-- Active inward gaps and seam-free inward whole circles cover every cut-circle point inside
the open superellipsoid body. -/
theorem cutInsideCarrier_subset_iUnion_range_canonicalBarrierPath
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R) :
    (⋃ j : cutIndex, G.cutInsideRange j) ⊆
      ⋃ e : CanonicalBarrierEdge G outerOrder cutOrder,
        Set.range (canonicalBarrierPath G outerOrder cutOrder e) := by
  intro x hx
  obtain ⟨j, ⟨z, hz⟩, hxBody⟩ := Set.mem_iUnion.mp hx
  by_cases hactive : (G.cutCircleSeamCrossings j).Nonempty
  · let ja : G.ActiveCutCircle := ⟨j, hactive⟩
    have hxClosed : x ∈ closedSuperellipsoidBody frame c R := by
      change superellipsoidGauge frame c x ≤ R
      exact le_of_lt hxBody
    have hxActive :
        x ∈ (⋃ k : G.ActiveCutCircle, Set.range (G.cut.circle k.1).circle) ∩
          closedSuperellipsoidBody frame c R :=
      ⟨Set.mem_iUnion.mpr ⟨ja, ⟨z, hz⟩⟩, hxClosed⟩
    have hxGaps :=
      (Set.ext_iff.mp (cutOrder.iUnion_range_globalInwardExcursionPath_eq hR) x).mpr
        hxActive
    obtain ⟨g, u, hux⟩ := Set.mem_iUnion.mp hxGaps
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl g))), u, ?_⟩
    exact hux
  · let ji : G.InactiveCutCircle := ⟨j, hactive⟩
    rcases G.inactiveCut_all_inward_or_all_outward hR.le ji with hinward | houtward
    · let jw : G.InwardWholeCutCircle := ⟨ji, hinward 0⟩
      have hz' : x ∈ Set.range (G.cut.circle jw.1.1).circle := by
        simpa only [jw, ji] using ⟨z, hz⟩
      have hxFull : x ∈ Set.range (fun u ↦ ((G.cut.circle jw.1.1).fullPath u : R3)) :=
        (Set.ext_iff.mp (G.cut.circle jw.1.1).range_fullPath x).mpr hz'
      obtain ⟨u, hux⟩ := hxFull
      refine Set.mem_iUnion.mpr
        ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr jw))), u, ?_⟩
      exact hux
    · obtain ⟨t, ht⟩ := Circle.exp_surjective z
      have hxBody' : ((G.cut.circle j).windingLoop.curve t : R3) ∈
          superellipsoidBody frame c R := by
        rw [← (G.cut.circle j).parametrization t, ht]
        exact hz ▸ hxBody
      have hnegative : G.cutCircleOuterPolynomialDifference j t < 0 :=
        (G.cutCircleOuterPolynomialDifference_neg_iff_body j hR t).mpr hxBody'
      exact False.elim ((not_lt_of_ge (houtward t).le) hnegative)

/-- The five canonical edge kinds cover exactly the finite barrier carrier. -/
theorem carrier_eq_iUnion_range_canonicalBarrierPath
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R) :
    G.carrier = ⋃ e : CanonicalBarrierEdge G outerOrder cutOrder,
      Set.range (canonicalBarrierPath G outerOrder cutOrder e) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxOuter | hxCut
    · exact outerCircleCarrier_subset_iUnion_range_canonicalBarrierPath
        G outerOrder cutOrder hxOuter
    · exact cutInsideCarrier_subset_iUnion_range_canonicalBarrierPath
        G outerOrder cutOrder hR hxCut
  · intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    exact range_canonicalBarrierPath_subset_carrier G outerOrder cutOrder hR e he

/-- The canonical cyclic orders produce an honest finite arc presentation of the literal
barrier graph. -/
noncomputable def canonicalBarrierArcPresentation
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] :
    FiniteBarrierArcPresentation G (SuperellipsoidSeamVertex Phi frame c R d)
      (CanonicalBarrierEdge G outerOrder cutOrder) where
  point := fun v ↦ v.1
  point_injective := Subtype.val_injective
  vertex_exact := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  sourcePoint := canonicalBarrierSourcePoint G outerOrder cutOrder
  targetPoint := canonicalBarrierTargetPoint G outerOrder cutOrder
  arc := canonicalBarrierPath G outerOrder cutOrder
  closed_or_endpoints_are_vertices := by
    intro e
    rcases canonicalBarrier_closed_or_endpoints_mem_seam G outerOrder cutOrder e with
      hclosed | ⟨hsource, htarget⟩
    · exact Or.inl hclosed
    · exact Or.inr ⟨⟨⟨_, hsource⟩, rfl⟩, ⟨⟨_, htarget⟩, rfl⟩⟩
  arc_in_graph := range_canonicalBarrierPath_subset_carrier G outerOrder cutOrder hR
  interior_avoids_vertices := by
    intro e t hendpoints ht0 ht1 hpoint
    apply canonicalBarrierPath_interior_not_mem_seam
      G outerOrder cutOrder e t hendpoints ht0 ht1
    obtain ⟨v, hv⟩ := hpoint
    exact hv ▸ v.2
  graph_exact := carrier_eq_iUnion_range_canonicalBarrierPath G outerOrder cutOrder hR

/-- The inward-gap summand of the canonical arc presentation is exactly the globally ordered
band family. -/
noncomputable def canonicalGlobalBandArcPresentationAlignment
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] :
    GlobalBandArcPresentationAlignment cutOrder
      (canonicalBarrierArcPresentation G outerOrder cutOrder hR) where
  point_eq := fun _ ↦ rfl
  excursionEdge := fun b ↦
    Sum.inr (Sum.inr (Sum.inr (Sum.inl (cutOrder.globalGapOfBand b))))
  excursion_source := by
    intro b
    dsimp only [canonicalBarrierArcPresentation]
    rw [show canonicalBarrierSourcePoint G outerOrder cutOrder
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (cutOrder.globalGapOfBand b))))) =
          ((cutOrder.globalBandPath b 0 : transportedTorus Phi) : R3) by
      simp [canonicalBarrierSourcePoint, canonicalBarrierArc,
        CutCircleTransverseCyclicOrderFamily.globalBandPath]]
    unfold PairedSeamEnumeration.firstVertex
    simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_zero] using
      (cutOrder.globalBandPath_endpoint_val b 0).symm
  excursion_target := by
    intro b
    dsimp only [canonicalBarrierArcPresentation]
    rw [show canonicalBarrierTargetPoint G outerOrder cutOrder
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (cutOrder.globalGapOfBand b))))) =
          ((cutOrder.globalBandPath b 1 : transportedTorus Phi) : R3) by
      simp [canonicalBarrierTargetPoint, canonicalBarrierArc,
        CutCircleTransverseCyclicOrderFamily.globalBandPath]]
    unfold PairedSeamEnumeration.secondVertex
    simpa only [CutCircleTransverseCyclicOrderFamily.finTwoUnitInterval_one] using
      (cutOrder.globalBandPath_endpoint_val b 1).symm
  arc_range_eq := fun _ ↦ rfl

/-- Canonical cyclic order and automatic disjoint neighborhoods give the complete excursion
pairing for the canonical barrier presentation. -/
noncomputable def canonicalFiniteBarrierExcursionPairing
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    [Fintype (SuperellipsoidSeamVertex Phi frame c R d)] :
    FiniteBarrierExcursionPairing
      (canonicalBarrierArcPresentation G outerOrder cutOrder hR) :=
  (canonicalGlobalBandArcPresentationAlignment G outerOrder cutOrder hR)
    |>.toFiniteBarrierExcursionPairing

/-! ## Exact reduction of the remaining chart equation -/

/-- Inside one canonical band neighborhood, the literal barrier is exactly the union of the
pieces of all canonical finite edges lying in that neighborhood.  This separates the already
proved finite carrier presentation from the remaining regular-neighborhood straightening. -/
theorem carrier_inter_globalBandOpenNeighborhood_eq_iUnion
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily) (hR : 0 < R)
    (b : Fin cutOrder.toPairedSeamEnumeration.bandCount) :
    G.carrier ∩ cutOrder.globalBandOpenNeighborhood b =
      ⋃ e : CanonicalBarrierEdge G outerOrder cutOrder,
        Set.range (canonicalBarrierPath G outerOrder cutOrder e) ∩
          cutOrder.globalBandOpenNeighborhood b := by
  rw [carrier_eq_iUnion_range_canonicalBarrierPath G outerOrder cutOrder hR]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  tauto

/-- The precise regular-neighborhood input still needed after the canonical finite carrier has
been constructed: in every band, its canonical edge pieces are the chart's standard `T` patch.
Unlike the earlier monolithic carrier equation, this field exposes exactly which finite arcs the
geometric straightening must control. -/
structure CanonicalGlobalBandChartArcExactness
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    (G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex)
    (outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily)
    (cutOrder : G.CutCircleTransverseCyclicOrderFamily)
    (T : cutOrder.GlobalBandTubularChartFamily) where
  local_arc_union_exact : ∀ b,
    (⋃ e : CanonicalBarrierEdge G outerOrder cutOrder,
      Set.range (canonicalBarrierPath G outerOrder cutOrder e) ∩
        cutOrder.globalBandOpenNeighborhood b) = (T.chart b).singularPatch

namespace CanonicalGlobalBandChartArcExactness

/-- Canonical finite-edge exactness supplies the chart realization expected by the paired-band
smoothing interface. -/
theorem toGlobalBandBarrierChartExactness
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily}
    {cutOrder : G.CutCircleTransverseCyclicOrderFamily} {hR : 0 < R}
    [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]
    {T : cutOrder.GlobalBandTubularChartFamily}
    (X : CanonicalGlobalBandChartArcExactness G outerOrder cutOrder T) :
    GlobalBandBarrierChartExactness T
      (canonicalGlobalBandArcPresentationAlignment G outerOrder cutOrder hR) where
  singular_local_exact := by
    intro b
    rw [carrier_inter_globalBandOpenNeighborhood_eq_iUnion
      G outerOrder cutOrder hR b]
    exact X.local_arc_union_exact b

/-- For the canonically chosen tubular strips, finite-edge exactness constructs the complete
barrier-excursion chart realization used by the Boolean moving-sphere family. -/
noncomputable def toCanonicalBarrierExcursionBandChartRealization
    {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {c : R3} {R d : ℝ}
    {outerIndex cutIndex : Type u} [Fintype outerIndex] [Fintype cutIndex]
    {G : FiniteSuperellipsoidBarrierGraph Phi frame c R d outerIndex cutIndex}
    {outerOrder : G.OuterCircleTransverseHeightCyclicOrderFamily}
    {cutOrder : G.CutCircleTransverseCyclicOrderFamily} {hR : 0 < R}
    [Fintype (SuperellipsoidSeamVertex Phi frame c R d)]
    (X : CanonicalGlobalBandChartArcExactness G outerOrder cutOrder
      cutOrder.globalBandTubularChartFamily) :
    BarrierExcursionBandChartRealization
      (canonicalFiniteBarrierExcursionPairing G outerOrder cutOrder hR) :=
  X.toGlobalBandBarrierChartExactness
    |>.toBarrierExcursionBandChartRealization

end CanonicalGlobalBandChartArcExactness

namespace CanonicalCentralBarrierChartData

variable {K : Knot} {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)}
  {c : R3} {r : ℝ} {W : SmoothLoopCarrierWitness Phi (orientedBox frame c r)}
  {S : SuperellipsoidDoubleBubbleSelection K Phi frame c r W}

/-- A simultaneous choice of central band charts together with their exact finite-edge carrier
equation.  The family is retained because relative straightening modifies the initially chosen
open tubular strips. -/
structure ArcExactness
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData S) where
  charts : D.centralCutOrder.GlobalBandTubularChartFamily
  exactness : CanonicalGlobalBandChartArcExactness D.centralGraph D.centralOuterOrder
    D.centralCutOrder charts

/-- Central endpoint regularity and the local chart equation produce the canonical band
realization without any further graph, order, pairing, or chart choices. -/
noncomputable def realization
    (D : SuperellipsoidDoubleBubbleSelection.CanonicalEndpointRegularityData S)
    (X : ArcExactness D) :
    letI := D.centralSeamVertexFintype
    BarrierExcursionBandChartRealization
      (canonicalFiniteBarrierExcursionPairing D.centralGraph D.centralOuterOrder
        D.centralCutOrder D.scale_pos) := by
  letI := D.centralSeamVertexFintype
  exact X.exactness.toGlobalBandBarrierChartExactness
    |>.toBarrierExcursionBandChartRealization

end CanonicalCentralBarrierChartData

end FiniteSuperellipsoidBarrierGraph
end Submission.Topology
