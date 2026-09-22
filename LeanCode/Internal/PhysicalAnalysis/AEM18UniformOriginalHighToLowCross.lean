import AEM17ExactHighToLowSupportCancellation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularCurrentLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

def highToLowErrorConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  ((lowBalanceConstant length parameters.gamma + 2) * lowPhysicalRowErrorConstant parameters length compact 0 +
    lowPhysicalRowErrorConstant parameters length compact 1 + 2 * lowPhysicalRowErrorConstant parameters length compact 2) * (4 + 2 * |length|)

theorem highToLowErrorConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) :
    0 ≤ highToLowErrorConstant parameters length compact := by
  have first := lowPhysicalRowErrorConstant_nonnegative parameters length compact 0
  have second := lowPhysicalRowErrorConstant_nonnegative parameters length compact 1
  have third := lowPhysicalRowErrorConstant_nonnegative parameters length compact 2
  have balance : 0 ≤ lowBalanceConstant length parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    linarith
  unfold highToLowErrorConstant
  positivity

theorem highToLowBulkCross_B8 (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive) :
    ‖highToLowBulkCross parameters lower length compact lengthPositive positive bounded state field‖ ≤
      highToLowErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  rw [highToLowBulkCross_error]
  let input := highCrossSevenInput lower length positive lengthPositive field
  let error := fun row => lowPhysicalRowErrorAction parameters length compact lower positive bounded state row input
  let budget := physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have balance : 0 ≤ lowBalanceConstant length parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    linarith
  have first := (lowFirstOutput_bound parameters lower length (error 0)).trans
    (mul_le_mul_of_nonneg_left (lowPhysicalRowErrorAction_B8 parameters length compact lower positive bounded state 0 input) balance)
  have second := (lowCellOutput_bound lower length positive (error 1)).trans
    (lowPhysicalRowErrorAction_B8 parameters length compact lower positive bounded state 1 input)
  have third := (lowAngularOutput_bound lower length positive (error 2)).trans
    (mul_le_mul_of_nonneg_left (lowPhysicalRowErrorAction_B8 parameters length compact lower positive bounded state 2 input) (by norm_num))
  have bpos : 0 ≤ budget := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have c0 := lowPhysicalRowErrorConstant_nonnegative parameters length compact 0
  have c1 := lowPhysicalRowErrorConstant_nonnegative parameters length compact 1
  have c2 := lowPhysicalRowErrorConstant_nonnegative parameters length compact 2
  have inputBound := highCrossSevenInput_bound lower length positive lengthPositive field
  have total : ‖lowFirstOutput parameters lower length (error 0) + lowCellOutput lower length positive (error 1) +
      lowAngularOutput lower length positive (error 2)‖ ≤
      ((lowBalanceConstant length parameters.gamma + 2) * lowPhysicalRowErrorConstant parameters length compact 0 +
        lowPhysicalRowErrorConstant parameters length compact 1 + 2 * lowPhysicalRowErrorConstant parameters length compact 2) * budget * ‖input‖ :=
    (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by dsimp [budget] at *; nlinarith))
  change ‖lowFirstOutput parameters lower length (error 0) + lowCellOutput lower length positive (error 1) +
    lowAngularOutput lower length positive (error 2)‖ ≤ _
  apply total.trans
  calc
    _ ≤ ((lowBalanceConstant length parameters.gamma + 2) * lowPhysicalRowErrorConstant parameters length compact 0 +
      lowPhysicalRowErrorConstant parameters length compact 1 + 2 * lowPhysicalRowErrorConstant parameters length compact 2) * budget *
      ((4 + 2 * |length|) * ‖field‖) := mul_le_mul_of_nonneg_left inputBound (by positivity)
    _ = _ := by unfold highToLowErrorConstant budget; ring


/-- BF18 source with the exact zero incoming coordinate. -/
def highToLowCross (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] LowEnergyData lower :=
  lowBulkDataInjection lower ∘L highToLowBulkCross parameters lower length compact lengthPositive positive bounded state

theorem highToLowCross_incoming_zero (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive) :
    (highToLowCross parameters lower length compact lengthPositive positive bounded state field).ofLp.2 = 0 := rfl

theorem highToLowCross_B8 (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive) :
    ‖highToLowCross parameters lower length compact lengthPositive positive bounded state field‖ ≤
      highToLowErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  unfold highToLowCross
  rw [ContinuousLinearMap.comp_apply, lowBulkDataInjection_norm]
  exact highToLowBulkCross_B8 parameters lower length compact lengthPositive positive bounded state field

end Grad.AnnularCrossMaps
