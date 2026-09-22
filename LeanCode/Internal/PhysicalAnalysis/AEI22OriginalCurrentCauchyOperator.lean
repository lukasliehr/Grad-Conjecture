import AEI21OriginalCurrentLowGenerator

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

/-- Original normalized current residual on the independently completed Y. -/
def lowCurrentResidual (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyBulk lower :=
  lowStoredCoordinate lower length positive 1 -
    (lowCurrentBulk parameters length compact lower lengthPositive positive bounded state).comp
      (lowStoredCoordinate lower length positive 0)

/-- The current Cauchy map keeps exactly the original BE18 incoming datum. -/
def lowCurrentDataOperator (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.comp
    ((lowCurrentResidual parameters length compact lower lengthPositive positive bounded.le state).prod
      (lowIncomingTrace lower length positive bounded))

theorem lowBulkDataInjection_norm (lower : ℝ) (field : LowEnergyBulk lower) :
    ‖lowBulkDataInjection lower field‖ = ‖field‖ := by
  have squared := WithLp.prod_norm_sq_eq_of_L2 (lowBulkDataInjection lower field)
  change ‖lowBulkDataInjection lower field‖ ^ 2 = ‖field‖ ^ 2 + ‖(0 : LowEnergyBoundary)‖ ^ 2 at squared
  rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at squared
  nlinarith [norm_nonneg (lowBulkDataInjection lower field), norm_nonneg field]

theorem lowCurrentDataOperator_difference (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) :
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state -
      lowReferenceDataOperator parameters length lower lengthPositive positive bounded) field =
        -(lowBulkDataInjection lower (lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded.le state (field.val 0))) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · change (field.val 1 - lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state (field.val 0)) -
      (field.val 1 - lowReferenceBulk parameters length lower lengthPositive positive (field.val 0)) = _
    rw [lowCurrentBulk_reference_error]
    change (field.val 1 - (lowReferenceBulk parameters length lower lengthPositive positive (field.val 0) +
      lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded.le state (field.val 0))) -
      (field.val 1 - lowReferenceBulk parameters length lower lengthPositive positive (field.val 0)) =
        -lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded.le state (field.val 0)
    abel
  · change lowIncomingTrace lower length positive bounded field - lowIncomingTrace lower length positive bounded field = -(0 : LowEnergyBoundary)
    simp

theorem lowCurrentDataOperator_difference_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    ‖lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state -
      lowReferenceDataOperator parameters length lower lengthPositive positive bounded‖ ≤
      lowCurrentErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 := by
  have coefficient : 0 ≤ lowCurrentErrorConstant parameters length compact *
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 :=
    mul_nonneg (lowCurrentErrorConstant_nonnegative parameters length compact lengthPositive)
      (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8)
  apply ContinuousLinearMap.opNorm_le_bound _ coefficient
  intro field
  rw [lowCurrentDataOperator_difference, norm_neg, lowBulkDataInjection_norm]
  exact (lowPhysicalResponseError_bound parameters length compact lower lengthPositive positive bounded.le state (field.val 0)).trans
    (mul_le_mul_of_nonneg_left (lowStoredCoordinate_bound lower length positive 0 field) coefficient)

end Grad.AnnularCurrentLow
