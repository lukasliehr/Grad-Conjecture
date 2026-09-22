import AHP19RadialGaugeAndMassSupport

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

section First
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)
variable (angular cell : ℕ)

theorem radialUnknownUKernel_derivative
    (input : NegativeTrace (rp parameters r) angular cell 1)
    (supported : IsAngularMeanFree (rp parameters r) angular cell input) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialUnknownUKernel parameters L compact state r small) input)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialUnknownVKernel parameters L compact state r small) input) := by
  unfold radialUnknownUKernel radialUnknownVKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add]
  apply radialGaugeQKernel_derivative
  exact (encodedJKernel_derivative (rp parameters r) angular cell _).add
    (actualUnknownQAKernel_derivative (rp parameters r) angular cell input supported)

theorem radialKnownAStarKernel_derivative
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input))
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownRAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) := by
  unfold radialKnownAStarKernel radialKnownRAStarKernel radialKnownRotatedQStarKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action]
  apply radialGaugeQKernel_derivative
  exact (encodedJKernel_derivative (rp parameters r) angular cell _).add
    (scalarDerivative.constantMatrix _)
end First

/-- The reconstructed angular row is the genuine coefficient derivative on
all full-cell modes, with the exact normalized scalar derivative slots. -/
theorem radialNormalizedCovariantKernel_derivative
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialMassLowRadius parameters L compact)
    (angular cell : ℕ) (input : SevenSlotTrace (rp parameters r) angular cell)
    (supported : IsAngularMeanFree (rp parameters r) angular cell (input 0))
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialNormalizedCovariantKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input))
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialNormalizedRotatedCovariantKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) := by
  unfold radialNormalizedCovariantKernel radialNormalizedRotatedCovariantKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add,
    fullNegativeKernelAction_comp, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply IsAngularDerivative.add
  · apply radialUnknownUKernel_derivative
    exact radialRecoveredMassKernel_action_meanFree parameters L compact state r small
      angular cell input supported
  · exact radialKnownAStarKernel_derivative parameters L compact state r
      (small.trans (min_le_left _ _)) angular cell input scalarDerivative

end Grad.AnnularReconstruction
