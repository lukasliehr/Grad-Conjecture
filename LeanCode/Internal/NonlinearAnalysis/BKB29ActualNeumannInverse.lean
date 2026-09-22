import BKB28ActionComposition

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

theorem fullNegativeKernelAction_identity (parameters : PhaseParameters)
    (angular cell dimension : ℕ) :
    fullNegativeKernelAction parameters angular cell
        (fullIdentityKernel parameters dimension) =
      ContinuousLinearMap.id ℂ (NegativeTrace parameters angular cell dimension) := by
  apply ContinuousLinearMap.ext
  intro field
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  have coefficientSum := fullNegativeKernelAction_coefficient_hasSum
    parameters angular cell (fullIdentityKernel parameters dimension) field mode
  calc
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (fullIdentityKernel parameters dimension) field) mode =
        ∑' shift : ℤ × ℤ,
          (fullIdentityKernel parameters dimension).entry shift
            (twoFrequencyTranslation shift mode)
            (negativeTraceCoefficient parameters angular cell field
              (twoFrequencyTranslation shift mode)) := coefficientSum.tsum_eq.symm
    _ = (fullIdentityKernel parameters dimension).entry (0, 0)
          (twoFrequencyTranslation (0, 0) mode)
          (negativeTraceCoefficient parameters angular cell field
            (twoFrequencyTranslation (0, 0) mode)) := by
      rw [tsum_eq_single (0, 0) (by
        intro shift nonzero
        rw [fullIdentityKernel_entry_ne_zero parameters dimension shift
          (twoFrequencyTranslation shift mode) nonzero]
        rfl)]
    _ = negativeTraceCoefficient parameters angular cell field mode := by
      rw [fullIdentityKernel_entry_zero]
      simp only [twoFrequencyTranslation_apply, sub_zero,
        ContinuousLinearMap.id_apply]
    _ = negativeTraceCoefficient parameters angular cell
          (ContinuousLinearMap.id ℂ
            (NegativeTrace parameters angular cell dimension) field) mode := by
      rw [ContinuousLinearMap.id_apply]

theorem fullNegativeKernelAction_inverse_right {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    (fullNegativeKernelAction parameters angular cell
        (fullKernelNegativeIdentityPerturbation parameters kernel)).comp
        (fullNegativeKernelAction parameters angular cell
          (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall)) =
      ContinuousLinearMap.id ℂ (NegativeTrace parameters angular cell dimension) := by
  rw [← fullNegativeKernelAction_comp]
  rw [fullKernelNegativeIdentity_inverse_right]
  exact fullNegativeKernelAction_identity parameters angular cell dimension

theorem fullNegativeKernelAction_inverse_left {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    (fullNegativeKernelAction parameters angular cell
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall)).comp
        (fullNegativeKernelAction parameters angular cell
          (fullKernelNegativeIdentityPerturbation parameters kernel)) =
      ContinuousLinearMap.id ℂ (NegativeTrace parameters angular cell dimension) := by
  rw [← fullNegativeKernelAction_comp]
  rw [fullKernelNegativeIdentity_inverse_left]
  exact fullNegativeKernelAction_identity parameters angular cell dimension

end Grad.BoundaryKernelAction
