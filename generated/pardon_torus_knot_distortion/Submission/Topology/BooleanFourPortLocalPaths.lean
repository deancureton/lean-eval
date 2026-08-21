import Submission.Topology.BooleanFourPortLocalPairing
import Submission.Topology.PairedSeamBandSmoothing

/-!
# Choice-dependent paths in finitely many four-port charts

The four corners of every paired seam-band chart realize the abstract four-port vertices.  The
Boolean local matching is realized by the two vertical paths at `false` and the two horizontal
paths at `true`.
-/

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- The planar corner selected by side and level labels. -/
def fourPortCorner (side level : Fin 2) : Plane :=
  if side = 0 then
    if level = 0 then bandLeftBottom else bandLeftTop
  else if level = 0 then bandRightBottom else bandRightTop

theorem fourPortCorner_pair_injective :
    Function.Injective (fun p : Fin 2 × Fin 2 ↦ fourPortCorner p.1 p.2) := by
  rintro ⟨side, level⟩ ⟨side', level'⟩ h
  fin_cases side <;> fin_cases level <;>
    fin_cases side' <;> fin_cases level'
  all_goals
    simp [fourPortCorner, bandLeftBottom, bandLeftTop,
      bandRightBottom, bandRightTop] at h ⊢ <;> norm_num at h

/-- The ambient point represented by one labelled corner of a four-port chart. -/
def fourPortChartPoint {n : ℕ} (chart : Fin n → PairedSeamBandChart) :
    FourPortVertex n → R3
  | (b, side, level) => (chart b).chart (fourPortCorner side level)

@[simp] theorem fourPortChartPoint_zero_zero {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (b : Fin n) :
    fourPortChartPoint chart (b, 0, 0) = (chart b).leftBottom := by
  simp [fourPortChartPoint, fourPortCorner, PairedSeamBandChart.leftBottom]

@[simp] theorem fourPortChartPoint_zero_one {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (b : Fin n) :
    fourPortChartPoint chart (b, 0, 1) = (chart b).leftTop := by
  simp [fourPortChartPoint, fourPortCorner, PairedSeamBandChart.leftTop]

@[simp] theorem fourPortChartPoint_one_zero {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (b : Fin n) :
    fourPortChartPoint chart (b, 1, 0) = (chart b).rightBottom := by
  simp [fourPortChartPoint, fourPortCorner, PairedSeamBandChart.rightBottom]

@[simp] theorem fourPortChartPoint_one_one {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (b : Fin n) :
    fourPortChartPoint chart (b, 1, 1) = (chart b).rightTop := by
  simp [fourPortChartPoint, fourPortCorner, PairedSeamBandChart.rightTop]

/-- The dependent vertical or horizontal path selected by one local edge. -/
noncomputable def booleanFourPortLocalPath {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (choice : Fin n → Bool)
    (e : FourPortLocalEdge n) :
    Path
      (fourPortChartPoint chart ((fourPortLocalPairing choice).endpointEquiv (e, 0)))
      (fourPortChartPoint chart ((fourPortLocalPairing choice).endpointEquiv (e, 1))) := by
  rcases e with ⟨b, edge⟩
  by_cases hb : choice b = true
  · exact Fin.cases
      (by
        have hsource : fourPortChartPoint chart
            ((fourPortLocalPairing choice).endpointEquiv ((b, 0), 0)) =
            (chart b).leftBottom := by
          change fourPortChartPoint chart
            (fourPortLocalEndpointEquiv choice ((b, 0), 0)) = _
          rw [fourPortLocalEndpointEquiv_true hb]
          exact fourPortChartPoint_zero_zero chart b
        have htarget : fourPortChartPoint chart
            ((fourPortLocalPairing choice).endpointEquiv ((b, 0), 1)) =
            (chart b).rightBottom := by
          change fourPortChartPoint chart
            (fourPortLocalEndpointEquiv choice ((b, 0), 1)) = _
          rw [fourPortLocalEndpointEquiv_true hb]
          exact fourPortChartPoint_one_zero chart b
        exact (chart b).bottomPath.cast hsource htarget)
      (fun edge : Fin 1 ↦ Fin.cases
        (by
          have hsource : fourPortChartPoint chart
              ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 0)) =
              (chart b).leftTop := by
            change fourPortChartPoint chart
              (fourPortLocalEndpointEquiv choice ((b, 1), 0)) = _
            rw [fourPortLocalEndpointEquiv_true hb]
            exact fourPortChartPoint_zero_one chart b
          have htarget : fourPortChartPoint chart
              ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 1)) =
              (chart b).rightTop := by
            change fourPortChartPoint chart
              (fourPortLocalEndpointEquiv choice ((b, 1), 1)) = _
            rw [fourPortLocalEndpointEquiv_true hb]
            exact fourPortChartPoint_one_one chart b
          exact (chart b).topPath.cast hsource htarget)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge
  · have hb' : choice b = false := by
      cases h : choice b <;> simp_all
    exact Fin.cases
      (by
        have hsource : fourPortChartPoint chart
            ((fourPortLocalPairing choice).endpointEquiv ((b, 0), 0)) =
            (chart b).leftBottom := by
          change fourPortChartPoint chart
            (fourPortLocalEndpointEquiv choice ((b, 0), 0)) = _
          rw [fourPortLocalEndpointEquiv_false hb']
          exact fourPortChartPoint_zero_zero chart b
        have htarget : fourPortChartPoint chart
            ((fourPortLocalPairing choice).endpointEquiv ((b, 0), 1)) =
            (chart b).leftTop := by
          change fourPortChartPoint chart
            (fourPortLocalEndpointEquiv choice ((b, 0), 1)) = _
          rw [fourPortLocalEndpointEquiv_false hb']
          exact fourPortChartPoint_zero_one chart b
        exact (chart b).leftPath.cast hsource htarget)
      (fun edge : Fin 1 ↦ Fin.cases
        (by
          have hsource : fourPortChartPoint chart
              ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 0)) =
              (chart b).rightBottom := by
            change fourPortChartPoint chart
              (fourPortLocalEndpointEquiv choice ((b, 1), 0)) = _
            rw [fourPortLocalEndpointEquiv_false hb']
            exact fourPortChartPoint_one_zero chart b
          have htarget : fourPortChartPoint chart
              ((fourPortLocalPairing choice).endpointEquiv ((b, 1), 1)) =
              (chart b).rightTop := by
            change fourPortChartPoint chart
              (fourPortLocalEndpointEquiv choice ((b, 1), 1)) = _
            rw [fourPortLocalEndpointEquiv_false hb']
            exact fourPortChartPoint_one_one chart b
          exact (chart b).rightPath.cast hsource htarget)
        (fun edge : Fin 0 ↦ Fin.elim0 edge) edge)
      edge

/-- The vertical or horizontal local chart paths selected by a Boolean resolution. -/
noncomputable def booleanFourPortLocalEndpointPaths {n : ℕ}
    (chart : Fin n → PairedSeamBandChart) (choice : Fin n → Bool) :
    FiniteAlternatingEndpointSystem.EndpointPathFamily
      (fourPortLocalPairing choice) (fourPortChartPoint chart) where
  path := booleanFourPortLocalPath chart choice

end Submission.Topology
