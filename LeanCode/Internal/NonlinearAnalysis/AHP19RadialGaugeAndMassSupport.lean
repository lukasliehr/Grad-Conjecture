import AHP18ExactOuterReconstructionBridge

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)

private abbrev rp := radialKernelParameters parameters r

theorem radialGammaDeviationKernel_angularDiagonal :
    AngularDiagonalKernel (radialGammaDeviationKernel parameters L compact state r) := by
  intro shift frequency nonzero
  unfold radialGammaDeviationKernel radialMatrixKernel
  apply ContinuousLinearMap.ext
  intro value
  rw [boundaryMatrixMultiplicationKernel_entry_apply]
  simp [radialGammaCoefficients, nonzero]

section Gauge
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

theorem radialNegativeGammaInverseKernel_angularDiagonal :
    AngularDiagonalKernel (radialNegativeGammaInverseKernel parameters L compact state r small) :=
  ((radialGammaDeviationKernel_angularDiagonal parameters L compact state r).neg).negativeIdentityInverse
    _ _ _

theorem radialGaugeCorrectionKernel_action_constant (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    IsAngularConstant (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeCorrectionKernel parameters L compact state r small) input) := by
  unfold radialGaugeCorrectionKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply constantMatrixKernel_action_constant
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply (radialNegativeGammaInverseKernel_angularDiagonal parameters L compact state r small).action_constant
  unfold radialGaugeMeanRowsKernel
  rw [fullNegativeKernelAction_comp]
  exact angularMeanKernel_action_constant (rp parameters r) angular cell _

theorem radialGaugeQKernel_derivative (angular cell : ℕ)
    (input derivative : NegativeTrace (rp parameters r) angular cell 3)
    (differentiated : IsAngularDerivative (rp parameters r) angular cell input derivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeQKernel parameters L compact state r small) input) derivative := by
  unfold radialGaugeQKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply]
  exact differentiated.add_constant
    (radialGaugeCorrectionKernel_action_constant parameters L compact state r small angular cell input)
end Gauge

section First
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialMassPerturbationKernel_action_meanFree (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 1) :
    IsAngularMeanFree (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialMassPerturbationKernel parameters L compact state r small) input) := by
  unfold radialMassPerturbationKernel
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree (rp parameters r) angular cell _

theorem radialKnownJStarKernel_action_meanFree (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 7) :
    IsAngularMeanFree (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownJStarKernel parameters L compact state r small) input) := by
  unfold radialKnownJStarKernel
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree (rp parameters r) angular cell _
end First

section Mass
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)

theorem radialMassInverseKernel_action_meanFree (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 1)
    (supported : IsAngularMeanFree (rp parameters r) angular cell input) :
    IsAngularMeanFree (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialMassInverseKernel parameters L compact state r small) input) := by
  unfold radialMassInverseKernel
  apply fullNegativeIdentityInverse_action_meanFree _ _ _ _ _ _ _ _ input supported
  intro argument
  exact radialMassPerturbationKernel_action_meanFree parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell argument

theorem radialRecoveredMassKernel_action_meanFree (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (supported : IsAngularMeanFree (rp parameters r) angular cell (input 0)) :
    IsAngularMeanFree (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialRecoveredMassKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) := by
  unfold radialRecoveredMassKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply radialMassInverseKernel_action_meanFree
  unfold radialMassRightHandKernel
  rw [fullNegativeKernelAction_sub, sevenInputSlotKernel_action]
  exact supported.sub (radialKnownJStarKernel_action_meanFree parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell _)
end Mass

end Grad.AnnularReconstruction
