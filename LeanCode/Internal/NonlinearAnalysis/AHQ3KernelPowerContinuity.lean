import AHQ2CompositionContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

variable {X : Type*} [TopologicalSpace X] {dimension : ℕ}
    (parameters : X → PhaseParameters)
    (kernel : (x : X) → FullTwoFrequencyKernel (parameters x) dimension dimension)
    (continuousEntries : ∀ shift input, Continuous (fun x => (kernel x).entry shift input))
    (low fourth : ℝ) (lowNonnegative : 0 ≤ low)
    (lowBound : ∀ x, fullKernelMoment (parameters x) 0 (kernel x) ≤ low)
    (fourthBound : ∀ x, fullKernelMoment (parameters x) 4 (kernel x) ≤ fourth)

omit [TopologicalSpace X] in
include lowNonnegative lowBound in
theorem fullKernelPower_uniform_zero (exponent : ℕ) (x : X) :
    fullKernelMoment (parameters x) 0 (fullKernelPower (kernel x) exponent) ≤
      ((exponent : ℝ) + 1) ^ 1 * low ^ exponent * low := by
  apply (fullKernelPower_theta_moment_le (parameters x) 0 exponent (kernel x) low (lowBound x)).trans
  exact mul_le_mul_of_nonneg_left (lowBound x)
    (mul_nonneg (pow_nonneg (by positivity) 1) (pow_nonneg lowNonnegative exponent))

include continuousEntries lowNonnegative lowBound fourthBound in
/-- Every literal noncommutative power of the same radius-dependent kernel
has continuous entries. This uses its existing power definition unchanged. -/
theorem fullKernelPower_continuous : ∀ (exponent : ℕ) (shift input : ℤ × ℤ),
    Continuous (fun x => (fullKernelPower (kernel x) exponent).entry shift input) := by
  intro exponent
  induction exponent with
  | zero => exact continuousEntries
  | succ exponent ih =>
    intro shift input
    exact fullKernelComposition_continuous parameters
      (fun x => fullKernelPower (kernel x) exponent) kernel ih continuousEntries
      (((exponent : ℝ) + 1) ^ 1 * low ^ exponent * low) fourth
      (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) 1) (pow_nonneg lowNonnegative exponent)) lowNonnegative)
      (fullKernelPower_uniform_zero parameters kernel low lowNonnegative lowBound exponent)
      fourthBound shift input

end Grad.AnnularKernelContinuity
