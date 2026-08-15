import Submission.Topology.RegularCircleRootPhase

/-!
# Seam-free direct certificates by reparametrizing a torus loop

Translation of a periodic embedded loop preserves its winding pair and embedded half-open-period
parametrization.  Choosing the finite-root-avoiding phase therefore gives the direct signed
intersection certificate without asking the original parameter seam to avoid the knot.
-/

open Set

noncomputable section

namespace Submission.PardonDistortion

open Submission.Topology

/-- Translation of a periodic loop parameter. -/
def shiftedLoop {X : Type*} (gamma : ℝ → X) (s t : ℝ) : X :=
  gamma (t + s)

/-- Translation of a circle covering lift. -/
def CircleLoopLift.shifted {gamma : ℝ → Circle} (L : CircleLoopLift gamma) (s : ℝ) :
    CircleLoopLift (shiftedLoop gamma s) where
  angle t := L.angle (t + s)
  continuous_angle := L.continuous_angle.comp (continuous_id.add continuous_const)
  exp_angle t := L.exp_angle (t + s)
  winding := L.winding
  angle_add_period t := by
    rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring,
      L.angle_add_period]

/-- Coordinatewise translation of a lifted torus loop. -/
def TorusLoopLift.shifted {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma) (s : ℝ) : TorusLoopLift (shiftedLoop gamma s) where
  first := L.first.shifted s
  second := L.second.shifted s

@[simp] theorem transformedSlopeAngle_shifted
    {gamma : ℝ → Circle × Circle} (p q : ℕ) (L : TorusLoopLift gamma)
    (s t : ℝ) :
    transformedSlopeAngle p q (L.shifted s) t = transformedSlopeAngle p q L (t + s) :=
  rfl

/-- Translating a periodic parametrization preserves injectivity on the canonical half-open
period. -/
theorem shiftedLoop_injOn
    {X : Type*} {gamma : ℝ → X}
    (hperiodic : Function.Periodic gamma (2 * Real.pi))
    (hinjective : Set.InjOn gamma (Ico (0 : ℝ) (2 * Real.pi))) (s : ℝ) :
    Set.InjOn (shiftedLoop gamma s) (Ico (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  let ux := toIcoMod Real.two_pi_pos 0 (x + s)
  let uy := toIcoMod Real.two_pi_pos 0 (y + s)
  let kx := toIcoDiv Real.two_pi_pos 0 (x + s)
  let ky := toIcoDiv Real.two_pi_pos 0 (y + s)
  have hux : ux ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 (x + s)
  have huy : uy ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 (y + s)
  have huxEq : ux + (kx : ℝ) * (2 * Real.pi) = x + s :=
    toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 (x + s)
  have huyEq : uy + (ky : ℝ) * (2 * Real.pi) = y + s :=
    toIcoMod_add_toIcoDiv_mul Real.two_pi_pos 0 (y + s)
  have hgammaX : gamma ux = gamma (x + s) := by
    calc
      gamma ux = gamma (ux + (kx : ℝ) * (2 * Real.pi)) :=
        (hperiodic.int_mul kx ux).symm
      _ = gamma (x + s) := by rw [huxEq]
  have hgammaY : gamma uy = gamma (y + s) := by
    calc
      gamma uy = gamma (uy + (ky : ℝ) * (2 * Real.pi)) :=
        (hperiodic.int_mul ky uy).symm
      _ = gamma (y + s) := by rw [huyEq]
  have huv : ux = uy := hinjective hux huy (hgammaX.trans (hxy.trans hgammaY.symm))
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod Real.two_pi_pos).mp huv
  have hnxy : y - x = (n : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul] at hn
    linarith
  have hnLower : (-1 : ℤ) < n := by
    exact_mod_cast (show (-1 : ℝ) < n from by
      nlinarith [Real.pi_pos, hx.1, hx.2, hy.1, hy.2])
  have hnUpper : n < (1 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < 1 from by
      nlinarith [Real.pi_pos, hx.1, hx.2, hy.1, hy.2])
  have hnZero : n = 0 := by omega
  rw [hnZero, Int.cast_zero, zero_mul] at hnxy
  linarith

/-- A direct certificate for a canonically phase-shifted copy of any raw regular embedded lifted
torus loop.  Its winding pair is definitionally the original pair. -/
def shiftedTransverseIntersectionCertificateOfRawRegular
    (p q : ℕ) (hc : p.Coprime q) {gamma : ℝ → Circle × Circle}
    (L : TorusLoopLift gamma)
    (hfirst : ContDiff ℝ 1 L.first.angle)
    (hsecond : ContDiff ℝ 1 L.second.angle)
    (hregular : ∀ t, Circle.exp (transformedSlopeAngle p q L t) = 1 →
      deriv (transformedSlopeAngle p q L) t ≠ 0)
    (hinjective : Set.InjOn gamma (Ico (0 : ℝ) (2 * Real.pi))) :
    let H := transformedRegularPeriodicCircleLift p q L hfirst hsecond hregular
    TransverseIntersectionCertificate p q (shiftedLoop gamma H.nonrootPhase)
      L.first.winding L.second.winding := by
  let H := transformedRegularPeriodicCircleLift p q L hfirst hsecond hregular
  let s := H.nonrootPhase
  have hregularShift : ∀ t,
      Circle.exp (transformedSlopeAngle p q (L.shifted s) t) = 1 →
        deriv (transformedSlopeAngle p q (L.shifted s)) t ≠ 0 := by
    intro t ht
    rw [transformedSlopeAngle_shifted] at ht
    change deriv (fun x ↦ transformedSlopeAngle p q L (x + s)) t ≠ 0
    rw [deriv_comp_add_const]
    exact hregular (t + s) ht
  apply transverseIntersectionCertificateOfRawRegular p q hc (L.shifted s)
    (hfirst.comp (contDiff_id.add contDiff_const))
    (hsecond.comp (contDiff_id.add contDiff_const)) hregularShift
  · simpa only [transformedSlopeAngle_shifted, zero_add, s, H] using
      H.exp_nonrootPhase_ne_one
  · exact shiftedLoop_injOn L.periodic_gamma hinjective s

end Submission.PardonDistortion
