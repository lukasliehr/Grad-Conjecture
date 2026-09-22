import AHQ3KernelPowerContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

variable {X : Type*} [TopologicalSpace X] {dimension : ℕ}
    (parameters : X → PhaseParameters)
    (kernel : (x : X) → FullTwoFrequencyKernel (parameters x) dimension dimension)
    (continuousEntries : ∀ shift input, Continuous (fun x => (kernel x).entry shift input))
    (low fourth : ℝ) (lowNonnegative : 0 ≤ low) (lowSmall : low < 1)
    (lowBound : ∀ x, fullKernelMoment (parameters x) 0 (kernel x) ≤ low)
    (fourthBound : ∀ x, fullKernelMoment (parameters x) 4 (kernel x) ≤ fourth)

include continuousEntries lowNonnegative fourthBound in
/-- The actual BKB Neumann tail has continuous entries on any uniformly
small physical parameter family. Only the original zero moment is small. -/
theorem fullKernelNeumannTail_continuous (shift input : ℤ × ℤ) :
    Continuous (fun x => (fullKernelNeumannTail (parameters x) (kernel x) low (lowBound x) lowSmall).entry shift input) := by
  change Continuous (fun x => ∑' exponent : ℕ, (fullKernelPower (kernel x) exponent).entry shift input)
  apply continuous_tsum
    (fun exponent => fullKernelPower_continuous parameters kernel continuousEntries low fourth lowNonnegative lowBound fourthBound exponent shift input)
    ((fullKernelNeumannMajorant_summable 0 low lowNonnegative lowSmall).mul_right low)
  intro exponent x
  exact ((fullKernelPower (kernel x) exponent).entry_le shift input).trans
    ((fullKernelMoment_entryNorm_le (parameters x) (fullKernelPower (kernel x) exponent) shift).trans
      (fullKernelPower_uniform_zero parameters kernel low lowNonnegative lowBound exponent x))

include continuousEntries lowNonnegative fourthBound in
/-- The exact inverse `-(I + K + K² + ...)` inherits continuity without
assuming any higher-moment smallness or changing the analytic width. -/
theorem fullKernelNegativeIdentityInverse_continuous (shift input : ℤ × ℤ) :
    Continuous (fun x => (fullKernelNegativeIdentityInverse (parameters x) (kernel x) low (lowBound x) lowSmall).entry shift input) := by
  have tail := fullKernelNeumannTail_continuous parameters kernel continuousEntries low fourth lowNonnegative lowSmall lowBound fourthBound shift input
  change Continuous (fun x => -((fullIdentityKernel (parameters x) dimension).entry shift input +
    (fullKernelNeumannTail (parameters x) (kernel x) low (lowBound x) lowSmall).entry shift input))
  have identity : Continuous (fun x => (fullIdentityKernel (parameters x) dimension).entry shift input) := by
    by_cases zero : shift = 0
    · simp only [zero]
      exact continuous_const
    · simp only [fullIdentityKernel_entry_ne_zero _ _ _ _ zero]
      exact continuous_const
  exact (identity.add tail).neg

end Grad.AnnularKernelContinuity
