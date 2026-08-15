import Submission.Topology.CoordinatePlane
import Submission.Topology.OneManifoldCircleClassification
import Submission.Topology.InnermostCircleSurgery

/-!
# Circle components of a regular coordinate-plane section

The closed fundamental square is not a quotient: a regular periodic level can meet its boundary,
and opposite boundary points represent the same point of the torus.  This module therefore puts
the level set directly in `Circle × Circle`.  Its transported image is proved homeomorphic to the
actual intersection of the transported torus with the coordinate cutting plane.

The remaining local input is stated precisely by `RegularCoordinateTorusLevel`: the regular
charts of the planar periodic lift must descend through the exponential covering to local line
charts on the quotient level.  Given those charts and cyclic parametrizations of the finitely many
components, the plane section is an exact finite, pairwise-disjoint union of embedded circles.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology
open scoped Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion
open Submission.SurfaceRegularValue
open Submission.Torus

/-! ## The coordinate level on the quotient torus -/

/-- The long framed coordinate, defined directly on the product-circle model of the transported
torus. -/
def torusLongCoordinate (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (z : Circle × Circle) : ℝ :=
  ambientCoordinate (frame 2) (transportedTorusMap Phi z)

theorem continuous_torusLongCoordinate (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) : Continuous (torusLongCoordinate Phi frame) := by
  exact (ambientCoordinate (frame 2)).continuous.comp
    (transportedTorusMap_continuous Phi)

/-- The genuine quotient-torus level corresponding to a coordinate cutting plane. -/
def coordinateTorusLevelSet (Phi : AmbientIsotopy) (frame : Equiv.Perm (Fin 3))
    (d : ℝ) : Set (Circle × Circle) :=
  torusLongCoordinate Phi frame ⁻¹' {d}

theorem isClosed_coordinateTorusLevelSet (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsClosed (coordinateTorusLevelSet Phi frame d) := by
  exact isClosed_singleton.preimage (continuous_torusLongCoordinate Phi frame)

theorem isCompact_coordinateTorusLevelSet (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    IsCompact (coordinateTorusLevelSet Phi frame d) := by
  exact (isClosed_coordinateTorusLevelSet Phi frame d).isCompact

/-- The actual ambient intersection, bundled as a subtype. -/
abbrev CoordinatePlaneTorusIntersection (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :=
  transportedTorus Phi ∩ coordinateCuttingPlane frame d

/-- A quotient-level point gives a point of the ambient plane section. -/
def coordinateLevelToIntersection (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    coordinateTorusLevelSet Phi frame d →
      CoordinatePlaneTorusIntersection Phi frame d :=
  fun z ↦ ⟨transportedTorusMap Phi z, ⟨⟨z, rfl⟩, z.property⟩⟩

/-- The ambient plane section is exactly the quotient-torus coordinate level. -/
def coordinateLevelIntersectionHomeomorph (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    coordinateTorusLevelSet Phi frame d ≃ₜ
      CoordinatePlaneTorusIntersection Phi frame d where
  toFun := coordinateLevelToIntersection Phi frame d
  invFun := fun x ↦ ⟨(transportedTorusHomeomorph Phi).symm ⟨x, x.property.1⟩, by
    change ambientCoordinate (frame 2)
      (transportedTorusMap Phi
        ((transportedTorusHomeomorph Phi).symm ⟨x, x.property.1⟩)) = d
    have hx := congrArg Subtype.val
      ((transportedTorusHomeomorph Phi).apply_symm_apply ⟨x, x.property.1⟩)
    change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm ⟨x, x.property.1⟩) = x at hx
    rw [hx]
    exact x.property.2⟩
  left_inv := fun z ↦ by
    apply Subtype.ext
    exact (transportedTorusHomeomorph Phi).symm_apply_apply z
  right_inv := fun x ↦ by
    apply Subtype.ext
    change transportedTorusMap Phi
      ((transportedTorusHomeomorph Phi).symm ⟨x, x.property.1⟩) = x
    exact congrArg Subtype.val
      ((transportedTorusHomeomorph Phi).apply_symm_apply ⟨x, x.property.1⟩)
  continuous_toFun :=
    ((transportedTorusMap_continuous Phi).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (transportedTorusHomeomorph Phi).symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x ↦ x.property.1)

theorem compactSpace_coordinatePlaneTorusIntersection (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) :
    CompactSpace (CoordinatePlaneTorusIntersection Phi frame d) := by
  let _ : CompactSpace (coordinateTorusLevelSet Phi frame d) :=
    isCompact_iff_compactSpace.mp (isCompact_coordinateTorusLevelSet Phi frame d)
  exact (coordinateLevelIntersectionHomeomorph Phi frame d).compactSpace

/-! ## The exact local input supplied by regularity -/

/-- A selected regular value of the planar periodic lift together with the one missing descent
step: its implicit-function charts pass through the exponential quotient and give local line
charts on the genuine torus level.

Unlike a local-line assertion on the literal closed fundamental square, this condition has the
correct topology at seam points. -/
structure RegularCoordinateTorusLevel (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (a b : ℝ) where
  selection : CompactRegularLevelSelection
    (orientedCoordinateLift Phi frame 2) a b
  quotientLocallyLineModeled : IsLocallyLineModeled
    (coordinateTorusLevelSet Phi frame selection.level)

namespace RegularCoordinateTorusLevel

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {a b : ℝ}

theorem compactSpace (S : RegularCoordinateTorusLevel Phi frame a b) :
    CompactSpace (coordinateTorusLevelSet Phi frame S.selection.level) :=
  isCompact_iff_compactSpace.mp
    (isCompact_coordinateTorusLevelSet Phi frame S.selection.level)

theorem locallyConnectedSpace (S : RegularCoordinateTorusLevel Phi frame a b) :
    LocallyConnectedSpace (coordinateTorusLevelSet Phi frame S.selection.level) :=
  locallyConnectedSpace_of_isLocallyLineModeled S.quotientLocallyLineModeled

theorem finite_connectedComponents (S : RegularCoordinateTorusLevel Phi frame a b) :
    Finite (ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)) := by
  let _ : CompactSpace (coordinateTorusLevelSet Phi frame S.selection.level) :=
    S.compactSpace
  let _ : LocallyConnectedSpace
      (coordinateTorusLevelSet Phi frame S.selection.level) :=
    S.locallyConnectedSpace
  infer_instance

/-- Cyclic parametrizations close the global compact-one-manifold classification gap and provide
the component classification required below. -/
def componentCircleClassificationOfCyclic
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (P : ∀ c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level),
      CyclicLineParametrization (componentPiece c)) :
    ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level) :=
  componentCircleClassificationOfCyclicParametrizations _ P

end RegularCoordinateTorusLevel

/-! ## Exact finite embedded-circle decomposition -/

/-- A finite family of embedded torus circles whose ranges are exactly a coordinate-plane
intersection.  This is the circle part of `FinitePlaneDiskTorusCircleSystem`, before choosing a
bounded plane disk and its planar nesting relation. -/
structure FiniteCoordinatePlaneTorusCircleFamily (Phi : AmbientIsotopy)
    (frame : Equiv.Perm (Fin 3)) (d : ℝ) where
  index : Type*
  finite_index : Finite index
  circle : index → EmbeddedTorusIntersectionCircle Phi
  circle_mem_plane : ∀ i, Set.range (circle i).circle ⊆ coordinateCuttingPlane frame d
  pairwise_disjoint : Pairwise
    (Function.onFun Disjoint fun i ↦ Set.range (circle i).circle)
  intersection_exact : transportedTorus Phi ∩ coordinateCuttingPlane frame d =
    ⋃ i, Set.range (circle i).circle

namespace FiniteCoordinatePlaneTorusCircleFamily

variable {Phi : AmbientIsotopy} {frame : Equiv.Perm (Fin 3)} {d a b : ℝ}

/-- The periodic winding loop induced by a continuous circle in the quotient torus. -/
noncomputable def windingLoopOfCircle (beta : Circle → Circle × Circle)
    (hbeta : Continuous beta) : TransportedWindingLoop Phi Set.univ := by
  let curve : ℝ → transportedTorus Phi := fun t ↦
    transportedTorusHomeomorph Phi (beta (Circle.exp t))
  have hcurve : Continuous curve :=
    (transportedTorusHomeomorph Phi).continuous.comp
      (hbeta.comp Circle.exp.continuous)
  have hperiodic : Function.Periodic curve (2 * Real.pi) := by
    intro t
    unfold curve
    rw [Circle.exp_add_two_pi]
  exact {
    curve := curve
    continuous_curve := hcurve
    periodic_curve := hperiodic
    curve_mem := fun _ ↦ mem_univ _
    lift := Classical.choice
      (exists_torusLoopLift_of_transportedLoop Phi curve hcurve hperiodic)
  }

/-- A classified quotient-level component, transported to ambient space. -/
noncomputable def embeddedCircleOfComponent
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)) :
    EmbeddedTorusIntersectionCircle Phi := by
  let beta : Circle → Circle × Circle := fun z ↦ C.circleEquiv c z
  have hbeta : Continuous beta := by
    change Continuous (fun z ↦ ((C.circleEquiv c z : componentPiece c) :
      coordinateTorusLevelSet Phi frame S.selection.level).1)
    exact continuous_subtype_val.comp (C.isEmbedding c).continuous
  let loop := windingLoopOfCircle (Phi := Phi) beta hbeta
  exact {
    circle := fun z ↦ transportedTorusMap Phi (beta z)
    isEmbedding := by
      apply (transportedTorusMap_isEmbedding Phi).comp
      change IsEmbedding (fun z ↦
        ((C.circleEquiv c z : componentPiece c) :
          coordinateTorusLevelSet Phi frame S.selection.level).1)
      exact IsEmbedding.subtypeVal.comp (C.isEmbedding c)
    windingLoop := loop
    parametrization := fun t ↦ rfl
  }

theorem component_circle_range
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level))
    (c : ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)) :
    Set.range (embeddedCircleOfComponent S C c).circle =
      (fun z : coordinateTorusLevelSet Phi frame S.selection.level ↦
        transportedTorusMap Phi z) '' componentPiece c := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨C.circleEquiv c z, (C.circleEquiv c z).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := (C.circleEquiv c).surjective ⟨z, hz⟩
    refine ⟨w, ?_⟩
    change transportedTorusMap Phi (C.circleEquiv c w) = transportedTorusMap Phi z
    exact congrArg (fun q ↦ transportedTorusMap Phi q.1) hw

/-- The component classification on the genuine quotient level gives an exact finite family of
pairwise-disjoint embedded circles in the ambient coordinate plane. -/
noncomputable def ofClassification
    (S : RegularCoordinateTorusLevel Phi frame a b)
    (C : ComponentCircleClassification
      (coordinateTorusLevelSet Phi frame S.selection.level)) :
    FiniteCoordinatePlaneTorusCircleFamily Phi frame S.selection.level := by
  let _ : Finite (ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)) :=
    S.finite_connectedComponents
  exact {
    index := ConnectedComponents
      (coordinateTorusLevelSet Phi frame S.selection.level)
    finite_index := inferInstance
    circle := embeddedCircleOfComponent S C
    circle_mem_plane := by
      intro c _ hx
      rw [component_circle_range S C c] at hx
      obtain ⟨z, _, rfl⟩ := hx
      exact z.property
    pairwise_disjoint := by
      intro c e hce
      change Disjoint
        (Set.range (embeddedCircleOfComponent S C c).circle)
        (Set.range (embeddedCircleOfComponent S C e).circle)
      rw [component_circle_range S C c, component_circle_range S C e]
      rw [Set.disjoint_left]
      rintro x ⟨z, hzc, rfl⟩ ⟨w, hwe, hw⟩
      have hzw : z = w := by
        apply Subtype.ext
        apply transportedTorusMap_injective Phi
        exact hw.symm
      exact (Set.disjoint_left.mp (pairwise_disjoint_componentPiece hce))
        hzc (hzw ▸ hwe)
    intersection_exact := by
      ext x
      constructor
      · rintro ⟨⟨z, rfl⟩, hxplane⟩
        let q : coordinateTorusLevelSet Phi frame S.selection.level := ⟨z, hxplane⟩
        have hq : q ∈ ⋃ c, componentPiece c := by
          rw [iUnion_componentPiece]
          exact mem_univ q
        simp only [mem_iUnion] at hq ⊢
        obtain ⟨c, hc⟩ := hq
        refine ⟨c, ?_⟩
        rw [component_circle_range S C c]
        exact ⟨q, hc, rfl⟩
      · simp only [mem_iUnion]
        rintro ⟨c, hx⟩
        rw [component_circle_range S C c] at hx
        obtain ⟨z, _, rfl⟩ := hx
        exact ⟨⟨z, rfl⟩, z.property⟩
  }

/-- Turn the complete plane-section family into the finite circle system consumed by innermost
circle surgery.  The only additional data are genuinely planar: a disk containing every section
circle, one essential label, and a well-founded nesting depth.  Exactness of the disk--torus
intersection is derived from the complete plane-section equality. -/
noncomputable def toFinitePlaneDiskTorusCircleSystem
    (F : FiniteCoordinatePlaneTorusCircleFamily Phi frame d)
    [Fintype F.index] [DecidableEq F.index]
    (D : BoundaryParametrizedEmbeddedDiskInR3)
    (disk_mem_plane : Set.range D.disk ⊆ coordinateCuttingPlane frame d)
    (circle_mem_disk : ∀ i, Set.range (F.circle i).circle ⊆ Set.range D.disk)
    (has_essential : ∃ i, (F.circle i).Essential)
    (inside : F.index → F.index → Prop) (depth : F.index → ℕ)
    (inside_depth_lt : ∀ {i j}, inside i j → depth i < depth j) :
    FinitePlaneDiskTorusCircleSystem Phi F.index where
  plane := coordinateCuttingPlane frame d
  planeDisk := D
  disk_mem_plane := disk_mem_plane
  circles := Finset.univ
  circle := F.circle
  circle_mem_disk := fun i _ ↦ circle_mem_disk i
  pairwise_disjoint := by
    intro i _ j _ hij
    exact F.pairwise_disjoint hij
  intersection_exact := by
    ext x
    constructor
    · rintro ⟨hxdisk, hxtorus⟩
      have hxplane := disk_mem_plane hxdisk
      have hxsection : x ∈ transportedTorus Phi ∩ coordinateCuttingPlane frame d :=
        ⟨hxtorus, hxplane⟩
      rw [F.intersection_exact] at hxsection
      simpa only [Finset.mem_univ, iUnion_true] using hxsection
    · intro hx
      simp only [Finset.mem_univ, iUnion_true] at hx
      simp only [mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      have hxsection : x ∈ transportedTorus Phi ∩ coordinateCuttingPlane frame d := by
        rw [F.intersection_exact]
        exact mem_iUnion.mpr ⟨i, hi⟩
      exact ⟨circle_mem_disk i hi, hxsection.1⟩
  has_essential := by
    obtain ⟨i, hi⟩ := has_essential
    exact ⟨i, Finset.mem_univ i, hi⟩
  inside := inside
  depth := depth
  inside_depth_lt := fun _ _ h ↦ inside_depth_lt h

end FiniteCoordinatePlaneTorusCircleFamily

end Submission.Topology
