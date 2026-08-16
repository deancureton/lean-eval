import Submission.Topology.FinitePunctureAxisCarrier
import Mathlib.Analysis.Convex.PathConnected

/-!
# Path connectivity of a finitely punctured product torus

The proof is constructive.  Choose a vertical and a horizontal circle missing every puncture.
From an arbitrary point, first move a short distance in the vertical circle to a height absent
from every puncture.  The short path is chosen inside the complement of the finitely many
punctures on that vertical fiber.  At the new height the entire horizontal circle is available,
and the globally avoiding vertical circle then reaches the common cross basepoint.
-/

open Set Topology
open scoped Topology
open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.Torus
open Submission.PardonDistortion

/-- Complement of finitely many specified points in the product circle. -/
def productFinitePointComplement {ι : Type*} (centers : ι → Circle × Circle) :
    Set (Circle × Circle) :=
  {x | ∀ i, x ≠ centers i}

/-! ## A short circle path avoiding local and global finite families -/

/-- A short path starting at `x`, avoiding a local finite family throughout, whose endpoint also
avoids a second global finite family. -/
structure CircleFiniteEscapePath {κ ι : Type*}
    (localFamily : κ → Circle) (global : ι → Circle) (x : Circle) where
  endpoint : Circle
  endpoint_ne_global : ∀ i, endpoint ≠ global i
  path : Path x endpoint
  path_ne_local : ∀ t j, path t ≠ localFamily j

/-- Every point outside a finite local family has a short escape path which remains outside that
family and ends outside any prescribed finite global family. -/
theorem exists_circleFiniteEscapePath
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (localFamily : κ → Circle) (global : ι → Circle) (x : Circle)
    (hx : ∀ j, x ≠ localFamily j) :
    Nonempty (CircleFiniteEscapePath localFamily global x) := by
  let U : Set Circle := (Set.range localFamily)ᶜ
  have hUOpen : IsOpen U := (Set.finite_range localFamily).isClosed.isOpen_compl
  have hxU : x ∈ U := by
    intro hxrange
    obtain ⟨j, hj⟩ := hxrange
    exact hx j hj.symm
  have hpreimage : Circle.exp ⁻¹' U ∈ 𝓝 ((x : ℂ).arg) := by
    apply Circle.exp.continuous.continuousAt.preimage_mem_nhds
    simpa [Circle.exp_arg] using hUOpen.mem_nhds hxU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpreimage
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  let arc : Set.Ioo (0 : ℝ) η → Circle :=
    fun d ↦ Circle.exp ((x : ℂ).arg + d)
  have harcInjective : Function.Injective arc := by
    intro d e hde
    have hlength : ((x : ℂ).arg + η) - (x : ℂ).arg ≤ 2 * Real.pi := by
      dsimp [η]
      nlinarith [Real.pi_gt_three, min_le_right ε 1]
    have hdIco : (x : ℂ).arg + (d : ℝ) ∈
        Set.Ico (x : ℂ).arg ((x : ℂ).arg + η) := by
      constructor <;> linarith [d.property.1, d.property.2]
    have heIco : (x : ℂ).arg + (e : ℝ) ∈
        Set.Ico (x : ℂ).arg ((x : ℂ).arg + η) := by
      constructor <;> linarith [e.property.1, e.property.2]
    apply Subtype.ext
    exact add_left_cancel <| Circle.exp_injOn_Ico hlength hdIco heIco hde
  let _ : Infinite (Set.Ioo (0 : ℝ) η) := Set.Ioo.infinite hη
  have harcInfinite : (Set.range arc).Infinite :=
    Set.infinite_range_of_injective harcInjective
  obtain ⟨y, ⟨d, rfl⟩, hyGlobal⟩ :=
    harcInfinite.exists_notMem_finite (Set.finite_range global)
  let rawPath : Path (Circle.exp ((x : ℂ).arg))
      (Circle.exp ((x : ℂ).arg + (d : ℝ))) :=
    (Path.segment (x : ℂ).arg ((x : ℂ).arg + (d : ℝ))).map
      Circle.exp.continuous
  let escapePath : Path x (Circle.exp ((x : ℂ).arg + (d : ℝ))) :=
    rawPath.cast (Circle.exp_arg x).symm rfl
  refine ⟨{
    endpoint := Circle.exp ((x : ℂ).arg + (d : ℝ))
    endpoint_ne_global := ?_
    path := escapePath
    path_ne_local := ?_
  }⟩
  · intro i hcenter
    exact hyGlobal ⟨i, hcenter.symm⟩
  · intro t j hlocal
    have hsegment : Path.segment (x : ℂ).arg
        ((x : ℂ).arg + (d : ℝ)) t ∈
        Metric.ball ((x : ℂ).arg) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module]
      have ht0 : 0 ≤ (t : ℝ) := t.property.1
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      have hd0 : 0 < (d : ℝ) := d.property.1
      have hdη : (d : ℝ) < η := d.property.2
      have hηε : η ≤ ε := min_le_left ε 1
      simp only [smul_eq_mul]
      rw [show (1 - (t : ℝ)) * (x : ℂ).arg +
          (t : ℝ) * ((x : ℂ).arg + (d : ℝ)) - (x : ℂ).arg =
          (t : ℝ) * (d : ℝ) by ring, abs_of_nonneg (mul_nonneg ht0 hd0.le)]
      nlinarith [mul_le_mul_of_nonneg_right hdη.le ht0]
    have hU : Circle.exp
        (Path.segment (x : ℂ).arg ((x : ℂ).arg + (d : ℝ)) t) ∈ U :=
      hball hsegment
    exact hU ⟨j, by
      simpa [escapePath, rawPath] using hlocal.symm⟩

/-! ## Joining every point to the avoiding cross -/

namespace AvoidingAxisBase

variable {ι : Type*} [Fintype ι] {centers : ι → Circle × Circle}

/-- The common point of the globally avoiding horizontal and vertical circles. -/
def productBasepoint (B : AvoidingAxisBase centers) : Circle × Circle :=
  (B.first, B.second)

omit [Fintype ι] in theorem productBasepoint_mem (B : AvoidingAxisBase centers) :
    B.productBasepoint ∈ productFinitePointComplement centers := by
  intro i hcenter
  exact B.first_ne i (congrArg Prod.fst hcenter)

/-- Every point of the finite-point complement is joined inside the complement to the globally
avoiding cross basepoint. -/
theorem joinedIn_productBasepoint (B : AvoidingAxisBase centers)
    (x : Circle × Circle) (hx : x ∈ productFinitePointComplement centers) :
    JoinedIn (productFinitePointComplement centers) x B.productBasepoint := by
  classical
  let localIndex := {i : ι // (centers i).1 = x.1}
  let localSecond : localIndex → Circle := fun i ↦ (centers i.1).2
  have hxLocal : ∀ i, x.2 ≠ localSecond i := by
    intro i hsecond
    apply hx i.1
    apply Prod.ext
    · exact i.2.symm
    · exact hsecond
  obtain ⟨escape⟩ := exists_circleFiniteEscapePath localSecond
    (fun i ↦ (centers i).2) x.2 hxLocal
  have hvertical : JoinedIn (productFinitePointComplement centers) x
      (x.1, escape.endpoint) := by
    refine ⟨(Path.refl x.1).prod escape.path, ?_⟩
    intro t i hcenter
    have hfirst : (centers i).1 = x.1 := (congrArg Prod.fst hcenter).symm
    let j : localIndex := ⟨i, hfirst⟩
    exact escape.path_ne_local t j (congrArg Prod.snd hcenter)
  have hhorizontal : JoinedIn (productFinitePointComplement centers)
      (x.1, escape.endpoint) (B.first, escape.endpoint) := by
    refine ⟨(Circle.path x.1 B.first).prod (Path.refl escape.endpoint), ?_⟩
    intro t i hcenter
    exact escape.endpoint_ne_global i (congrArg Prod.snd hcenter)
  have hcross : JoinedIn (productFinitePointComplement centers)
      (B.first, escape.endpoint) B.productBasepoint := by
    refine ⟨(Path.refl B.first).prod (Circle.path escape.endpoint B.second), ?_⟩
    intro t i hcenter
    exact B.first_ne i (congrArg Prod.fst hcenter)
  exact hvertical.trans (hhorizontal.trans hcross)

end AvoidingAxisBase

/-- A product torus with finitely many points removed is path connected. -/
theorem productFinitePointComplement_isPathConnected
    {ι : Type*} [Fintype ι] (centers : ι → Circle × Circle) :
    IsPathConnected (productFinitePointComplement centers) := by
  obtain ⟨B⟩ := exists_avoidingAxisBase centers
  refine ⟨B.productBasepoint, B.productBasepoint_mem, ?_⟩
  intro y hy
  exact (B.joinedIn_productBasepoint y hy).symm

/-! ## Transport to the embedded torus -/

/-- Restriction of the transported-torus homeomorphism to the two finite-point complements. -/
def productFinitePointComplementHomeomorph
    {Phi : AmbientIsotopy} {ι : Type*} (centers : ι → Circle × Circle) :
    productFinitePointComplement centers ≃ₜ
      transportedFinitePointComplement Phi centers where
  toFun x := ⟨transportedTorusHomeomorph Phi x.1, by
    intro i hcenter
    exact x.2 i ((transportedTorusHomeomorph Phi).injective hcenter)⟩
  invFun x := ⟨(transportedTorusHomeomorph Phi).symm x.1, by
    intro i hcenter
    apply x.2 i
    rw [← hcenter, (transportedTorusHomeomorph Phi).apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    exact (transportedTorusHomeomorph Phi).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (transportedTorusHomeomorph Phi).apply_symm_apply x.1
  continuous_toFun :=
    ((transportedTorusHomeomorph Phi).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((transportedTorusHomeomorph Phi).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The transported finite-point source used by radial pushouts is path connected. -/
theorem transportedFinitePointComplement_isPathConnected
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]
    (centers : ι → Circle × Circle) :
    IsPathConnected
      (Set.univ : Set (transportedFinitePointComplement Phi centers)) := by
  let e := productFinitePointComplementHomeomorph (Phi := Phi) centers
  let _ : PathConnectedSpace (productFinitePointComplement centers) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (productFinitePointComplement_isPathConnected centers)
  have hsource : IsPathConnected
      (Set.univ : Set (productFinitePointComplement centers)) :=
    isPathConnected_univ
  have himage : e '' (Set.univ : Set (productFinitePointComplement centers)) = Set.univ :=
    Set.image_univ_of_surjective e.surjective
  rw [← himage]
  exact e.isPathConnected_image.mpr hsource

/-- In particular, the finite-point pushout source is connected. -/
theorem transportedFinitePointComplement_isConnected
    {Phi : AmbientIsotopy} {ι : Type*} [Fintype ι]
    (centers : ι → Circle × Circle) :
    IsConnected
      (Set.univ : Set (transportedFinitePointComplement Phi centers)) :=
  (transportedFinitePointComplement_isPathConnected centers).isConnected

end Submission.Topology
