import BCI23OriginalPhysicalSourceConsumer

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- The actual BS33 source kernel has the original total-grade one-high
allocation, with B8 on the high source and B(t+8) on the base source. -/
theorem actualSourceBoundaryLift_oneHigh (parameters : PhaseParameters) (L compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : BoundaryInverseState parameters L compact,
      ∀ (high : NegativeTotalTrace parameters grade 3) (low : NegativeTotalTrace parameters 0 3),
      ‖fullOneHighKernelAction parameters grade (actualSourceBoundaryLiftKernel state) high low‖ ≤
        constant * ((1 + state.val.budget 1) * ‖high‖ + (1 + state.val.budget (grade + 1)) * ‖low‖) := by
  obtain ⟨base, baseNonnegative, baseBound⟩ := actualSourceBoundaryLift_physicalMoments parameters L compact 1
  obtain ⟨top, topNonnegative, topBound⟩ := actualSourceBoundaryLift_physicalMoments parameters L compact (grade + 1)
  refine ⟨2 ^ grade * (base + top), mul_nonneg (by positivity) (add_nonneg baseNonnegative topNonnegative), ?_⟩
  intro state high low
  apply (fullOneHighKernelAction_bound parameters grade (actualSourceBoundaryLiftKernel state) high low).trans
  have first := mul_le_mul_of_nonneg_right (baseBound state) (norm_nonneg high)
  have second := mul_le_mul_of_nonneg_right (topBound state) (norm_nonneg low)
  have budgetBase := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have budgetHigh := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade + 1 + 7)
  have sumBound : fullKernelMoment parameters 1 (actualSourceBoundaryLiftKernel state) * ‖high‖ +
      fullKernelMoment parameters (grade + 1) (actualSourceBoundaryLiftKernel state) * ‖low‖ ≤
      (base + top) * ((1 + state.val.budget 1) * ‖high‖ + (1 + state.val.budget (grade + 1)) * ‖low‖) := by
    change _ ≤ _ at first second
    have firstTerm : 0 ≤ (1 + state.val.budget 1) * ‖high‖ := mul_nonneg (by linarith) (norm_nonneg _)
    have secondTerm : 0 ≤ (1 + state.val.budget (grade + 1)) * ‖low‖ := mul_nonneg (by linarith) (norm_nonneg _)
    change _ ≤ base * (1 + state.val.budget 1) * ‖high‖ at first
    change _ ≤ top * (1 + state.val.budget (grade + 1)) * ‖low‖ at second
    nlinarith [mul_nonneg baseNonnegative secondTerm, mul_nonneg topNonnegative firstTerm]
  exact (mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ (2 : ℝ) ^ grade)).trans_eq (by ring)

end Grad.ActualBoundaryInverse
