import AKCQ3OriginalPositiveEulerPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate

/-- The Euler iterates are genuine smooth functions, including at zero. -/
theorem eulerIteratedDerivative_smooth (field : ℝ → ℝ) (smooth : ContDiff ℝ ∞ field) (rank : ℕ) :
    ContDiff ℝ ∞ (eulerIteratedDerivative rank field) := by
  induction rank with
  | zero => exact smooth
  | succ rank previous =>
      exact contDiff_id.mul (contDiff_infty_iff_deriv.mp previous).2

theorem eulerIteratedDerivative_sub (first second : ℝ → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (rank : ℕ) :
    eulerIteratedDerivative rank (fun point => first point-second point) =
      fun point => eulerIteratedDerivative rank first point-eulerIteratedDerivative rank second point := by
  induction rank with
  | zero => rfl
  | succ rank previous =>
      change eulerDerivative (eulerIteratedDerivative rank (fun point => first point-second point)) = _
      rw [previous]
      funext point
      have firstDifferentiable := (eulerIteratedDerivative_smooth first firstSmooth rank).differentiable (by simp) point
      have secondDifferentiable := (eulerIteratedDerivative_smooth second secondSmooth rank).differentiable (by simp) point
      change point * deriv (fun location => eulerIteratedDerivative rank first location-
        eulerIteratedDerivative rank second location) point = _
      have derivative := firstDifferentiable.hasDerivAt.sub secondDifferentiable.hasDerivAt
      simp only [Pi.sub_def] at derivative
      rw [derivative.deriv]
      exact mul_sub _ _ _

/-- Ordinary derivatives along exp(t) are precisely the actual Euler
iterates. This is an identity, not a replacement of the original radius. -/
theorem iteratedDeriv_comp_exp_euler (field : ℝ → ℝ) (smooth : ContDiff ℝ ∞ field) (rank : ℕ) :
    iteratedDeriv rank (fun time => field (Real.exp time)) =
      fun time => eulerIteratedDerivative rank field (Real.exp time) := by
  induction rank with
  | zero => rfl
  | succ rank previous =>
      rw [iteratedDeriv_succ,previous]
      funext time
      have derivative := (((eulerIteratedDerivative_smooth field smooth rank).differentiable (by simp)
        (Real.exp time)).hasDerivAt).comp time (Real.hasDerivAt_exp time)
      simp only [Function.comp_def] at derivative
      rw [derivative.deriv]
      change deriv (eulerIteratedDerivative rank field) (Real.exp time) * Real.exp time =
        Real.exp time * deriv (eulerIteratedDerivative rank field) (Real.exp time)
      exact mul_comm _ _

/-- Positive Euler order vanishes at the axis by the actual outer r factor. -/
theorem eulerIteratedDerivative_zero (field : ℝ → ℝ) (rank : ℕ) :
    eulerIteratedDerivative (rank+1) field 0 = 0 := by
  exact zero_mul _

end Grad.OriginalCartesianTameEstimate
