import AEI15ActualCompletedLowRowErrors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

/-- The literal normalized low physical response from J, c=Rb3 and rV. -/
def lowPhysicalResponse (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).comp (lowPhysicalRowAction parameters length compact lower positive bounded state 0) +
    (lowCellOutput lower length positive).comp (lowPhysicalRowAction parameters length compact lower positive bounded state 1) +
    (lowAngularOutput lower length positive).comp (lowPhysicalRowAction parameters length compact lower positive bounded state 2)).comp
    (lowNormalizedSevenInput parameters lower length lengthPositive positive)

def lowCircularResponse (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).comp (lowCircularRowAction parameters length lower positive bounded 0) +
    (lowCellOutput lower length positive).comp (lowCircularRowAction parameters length lower positive bounded 1) +
    (lowAngularOutput lower length positive).comp (lowCircularRowAction parameters length lower positive bounded 2)).comp
    (lowNormalizedSevenInput parameters lower length lengthPositive positive)

def lowPhysicalResponseError (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).comp (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 0) +
    (lowCellOutput lower length positive).comp (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 1) +
    (lowAngularOutput lower length positive).comp (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 2)).comp
    (lowNormalizedSevenInput parameters lower length lengthPositive positive)

theorem lowPhysicalResponseError_sub (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded state =
      lowPhysicalResponse parameters length compact lower lengthPositive positive bounded state -
        lowCircularResponse parameters length lower lengthPositive positive bounded := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [lowPhysicalResponseError, lowPhysicalResponse, lowCircularResponse, lowPhysicalRowErrorAction_sub,
    ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub]
  abel

def lowCurrentErrorConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  ((lowBalanceConstant length parameters.gamma + 2) * lowPhysicalRowErrorConstant parameters length compact 0 +
    lowPhysicalRowErrorConstant parameters length compact 1 + 2 * lowPhysicalRowErrorConstant parameters length compact 2) * (7 + 2 * length)

theorem lowCurrentErrorConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    0 ≤ lowCurrentErrorConstant parameters length compact := by
  have first := lowPhysicalRowErrorConstant_nonnegative parameters length compact 0
  have second := lowPhysicalRowErrorConstant_nonnegative parameters length compact 1
  have third := lowPhysicalRowErrorConstant_nonnegative parameters length compact 2
  have balance : 0 ≤ lowBalanceConstant length parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    linarith
  unfold lowCurrentErrorConstant
  positivity

theorem lowPhysicalResponseError_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (field : LowEnergyBulk lower) :
    ‖lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded state field‖ ≤
      lowCurrentErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  let input := lowNormalizedSevenInput parameters lower length lengthPositive positive field
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
  have inputBound := lowNormalizedSevenInput_bound parameters lower length lengthPositive positive field
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
      ((7 + 2 * length) * ‖field‖) := mul_le_mul_of_nonneg_left inputBound (by positivity)
    _ = _ := by unfold lowCurrentErrorConstant budget; ring

end Grad.AnnularCurrentLow
