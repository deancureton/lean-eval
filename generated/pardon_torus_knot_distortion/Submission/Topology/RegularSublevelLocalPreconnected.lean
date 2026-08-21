import Submission.Topology.OpenRegionLensAttachment
import Submission.Topology.PeriodicRegularSublevelFrontier
import Submission.Topology.RegularLevelQuotientCharts
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local connectedness on the strict side of a regular level

An implicit-function chart identifies a regular strict sublevel with a half-ball.  This gives
the local preconnectedness needed to cancel a shared lens face.
-/

open Set Topology

noncomputable section

namespace Submission.SurfaceRegularValue

open Submission.Topology

/-- The strict sublevel has arbitrarily small preconnected traces at every regular boundary
point. -/
theorem isLocallyPreconnectedWithinAt_strictSublevel_of_regularPoint
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} {y : ℝ} (hx : fderiv ℝ f x ≠ 0) :
    IsLocallyPreconnectedWithinAt {z | f z < y} x := by
  intro U hU
  obtain ⟨t, htU, htOpen, hxt⟩ := mem_nhds_iff.mp hU
  let C := Classical.choice (exists_regularLevelChart hf hx)
  let q := C.chart x
  let image : Set (ℝ × (fderiv ℝ f x).toLinearMap.ker) :=
    C.chart '' (C.chart.source ∩ t)
  have hImageOpen : IsOpen image := C.chart.isOpen_image_source_inter htOpen
  have hqImage : q ∈ image := ⟨x, ⟨C.mem_source, hxt⟩, rfl⟩
  obtain ⟨ε, hεPos, hεImage⟩ := Metric.isOpen_iff.mp hImageOpen q hqImage
  let B : Set (ℝ × (fderiv ℝ f x).toLinearMap.ker) := Metric.ball q ε
  let H : Set (ℝ × (fderiv ℝ f x).toLinearMap.ker) :=
    B ∩ (Iio y ×ˢ (Set.univ : Set (fderiv ℝ f x).toLinearMap.ker))
  let V : Set Plane := C.chart.symm '' B
  have hBTarget : B ⊆ C.chart.target := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := hεImage hp
    exact C.chart.map_source hw.1
  have hVOpen : IsOpen V := by
    have himage := C.chart.symm.isOpen_image_source_inter (Metric.isOpen_ball : IsOpen B)
    have hsource : C.chart.symm.source ∩ B = B := inter_eq_right.mpr hBTarget
    rw [hsource] at himage
    exact himage
  have hxV : x ∈ V := by
    refine ⟨q, Metric.mem_ball_self hεPos, ?_⟩
    exact C.chart.left_inv C.mem_source
  have hVU : V ⊆ U := by
    intro z hz
    obtain ⟨p, hpB, rfl⟩ := hz
    obtain ⟨w, ⟨hwSource, hwt⟩, hwp⟩ := hεImage hpB
    apply htU
    have hpTarget : p ∈ C.chart.target := hBTarget hpB
    have hzEq : C.chart.symm p = w := by
      calc
        C.chart.symm p = C.chart.symm (C.chart w) := congrArg C.chart.symm hwp.symm
        _ = w := C.chart.left_inv hwSource
    simpa only [hzEq] using hwt
  have htrace : V ∩ {z | f z < y} = C.chart.symm '' H := by
    ext z
    constructor
    · rintro ⟨⟨p, hpB, rfl⟩, hzSub⟩
      have hpTarget : p ∈ C.chart.target := hBTarget hpB
      refine ⟨p, ⟨hpB, ?_⟩, rfl⟩
      refine ⟨?_, Set.mem_univ _⟩
      change p.1 < y
      rw [← C.chart.right_inv hpTarget, C.fst_eq]
      exact hzSub
    · rintro ⟨p, ⟨hpB, hpSub⟩, rfl⟩
      have hpTarget : p ∈ C.chart.target := hBTarget hpB
      refine ⟨⟨p, hpB, rfl⟩, ?_⟩
      change f (C.chart.symm p) < y
      rw [← C.fst_eq, C.chart.right_inv hpTarget]
      exact hpSub.1
  refine ⟨V, hVOpen.mem_nhds hxV, hVU, ?_⟩
  rw [htrace]
  apply ((convex_ball q ε).inter
    (Convex.prod (convex_Iio y)
      (convex_univ : Convex ℝ
        (Set.univ : Set (fderiv ℝ f x).toLinearMap.ker)))).isPreconnected.image
    C.chart.symm
  exact C.chart.symm.continuousOn.mono (fun p hp ↦ hBTarget hp.1)

end Submission.SurfaceRegularValue

namespace Submission.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local preconnected traces descend through a local homeomorphism when the target set has the
specified full preimage. -/
theorem IsLocallyPreconnectedWithinAt.map_of_localHomeomorph
    {p : X → Y} {s : Set X} {t : Set Y} {x : X}
    (hp : IsLocalHomeomorph p) (hst : p ⁻¹' t = s)
    (h : IsLocallyPreconnectedWithinAt s x) :
    IsLocallyPreconnectedWithinAt t (p x) := by
  intro U hU
  obtain ⟨e, hxe, he⟩ := hp x
  have hpreimage : p ⁻¹' U ∩ e.source ∈ 𝓝 x :=
    Filter.inter_mem (hp.continuous.continuousAt.preimage_mem_nhds hU)
      (e.open_source.mem_nhds hxe)
  obtain ⟨V, hV, hVsub, hVconnected⟩ := h _ hpreimage
  let W : Set Y := e '' V
  have hW : W ∈ 𝓝 (p x) := by
    change e '' V ∈ 𝓝 (p x)
    rw [he]
    exact e.image_mem_nhds hxe hV
  have hWsub : W ⊆ U := by
    rintro _ ⟨v, hv, rfl⟩
    have hvPreimage := (hVsub hv).1
    change p v ∈ U at hvPreimage
    simpa only [he] using hvPreimage
  have htrace : W ∩ t = e '' (V ∩ s) := by
    ext y
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvt⟩
      refine ⟨v, ⟨hv, ?_⟩, rfl⟩
      rw [← hst]
      change p v ∈ t
      simpa only [he] using hvt
    · rintro ⟨v, ⟨hv, hvs⟩, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, ?_⟩
      have hvPreimage : v ∈ p ⁻¹' t := by
        rw [hst]
        exact hvs
      change p v ∈ t at hvPreimage
      simpa only [he] using hvPreimage
  refine ⟨W, hW, hWsub, ?_⟩
  rw [htrace]
  exact hVconnected.image e
    (e.continuousOn.mono fun v hv ↦ (hVsub hv.1).2)

open Submission.SurfaceRegularValue

/-- A regular periodic strict sublevel has locally preconnected traces on the quotient torus. -/
theorem isLocallyPreconnectedWithinAt_periodicQuotientSublevel
    {f : Plane → ℝ} {g : Circle × Circle → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hdesc : ∀ uv, f uv = g (planeExpPair uv))
    {y : ℝ} (hy : IsRegularValue f y) {z : Circle × Circle}
    (hz : g z = y) :
    IsLocallyPreconnectedWithinAt (periodicQuotientSublevel g y) z := by
  obtain ⟨uv, rfl⟩ := planeExpPair_surjective z
  have huv : f uv = y := by rw [hdesc]; exact hz
  apply IsLocallyPreconnectedWithinAt.map_of_localHomeomorph
    planeExpPair_isLocalHomeomorph
  · ext w
    change g (planeExpPair w) < y ↔ f w < y
    rw [hdesc]
  · exact
      isLocallyPreconnectedWithinAt_strictSublevel_of_regularPoint hf
        (hy uv huv)

/-- Local preconnected traces are preserved by a homeomorphism. -/
theorem IsLocallyPreconnectedWithinAt.homeomorph
    {s : Set X} {x : X} (e : X ≃ₜ Y)
    (h : IsLocallyPreconnectedWithinAt s x) :
    IsLocallyPreconnectedWithinAt (e '' s) (e x) := by
  apply h.map_of_localHomeomorph e.isLocalHomeomorph
  ext z
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨w, hw, hzw⟩
    exact e.injective hzw ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

end Submission.Topology
