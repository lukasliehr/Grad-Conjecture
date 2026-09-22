import AJG10OriginalFullSliceEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- The SAME once-only full covariant and genuine rotated field have a bound
uniform in the inner radius, in the common original rho-weighted storage. -/
theorem sharedFullReconstruction_uniform (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
        (state : AnnularReconstructionState parameters L compact)
        (data : StrongDataCarrier parameters lower positive bounded 0 0)
        (solution : CoupledSpace lower L positive lengthPositive),
        ‖sharedFullCovariant parameters L compact lower positive bounded lengthPositive state data solution‖ +
          ‖sharedFullRotatedCovariant parameters L compact lower positive bounded lengthPositive state data solution‖ ≤
        constant * (1 + physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7) *
          ((11 + 4 * L) * ‖solution‖ + 3 * ‖data‖) := by
  obtain ⟨constant, nonnegative, estimate⟩ := normalizedCompletedCovariants_uniform parameters L compact 0
  refine ⟨constant, nonnegative, ?_⟩
  intro lower positive bounded lengthPositive state data solution
  have same := estimate lower positive bounded state
    (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution)
  change ‖normalizedCovariantAction parameters L compact lower positive bounded state 0 _‖ +
    ‖normalizedRotatedAction parameters L compact lower positive bounded state 0 _‖ ≤
    constant * (1 + physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7) * _ at same
  rw [← fullCovariantAction_same, ← fullRotatedCovariantAction_same] at same
  exact same.trans (mul_le_mul_of_nonneg_left
    (fullStrongSevenInput_bound parameters L lower lengthPositive positive bounded data solution)
    (mul_nonneg nonnegative (add_nonneg (by norm_num) (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))))

end Grad.AnnularPhysicalReconstruction
