import AEI22OriginalCurrentCauchyOperator
import Grad.Foundations.PerturbationInverse

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

open Grad.Foundations Grad.AnnularLowVolterra

def lowNormalizedCurrentError (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    lowEnergyGraph lower length positive →L[ℂ] lowEnergyGraph lower length positive :=
  normalizedError (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)

theorem lowNormalizedCurrentError_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    ‖lowNormalizedCurrentError parameters length compact lower lengthPositive positive bounded state‖ ≤
      Real.sqrt (lowReferenceGraphConstant parameters length) * lowCurrentErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 := by
  have bound := normalizedError_norm (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)
  change ‖lowNormalizedCurrentError parameters length compact lower lengthPositive positive bounded state‖ ≤
    ‖lowReferenceInverse parameters length lower lengthPositive positive bounded‖ *
    ‖lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state -
      lowReferenceDataOperator parameters length lower lengthPositive positive bounded‖ at bound
  exact bound.trans ((mul_le_mul (originalLowReferenceInverse_uniform parameters length lengthPositive lower positive bounded)
    (lowCurrentDataOperator_difference_bound parameters length compact lower lengthPositive positive bounded state)
    (ContinuousLinearMap.opNorm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (by ring))

/-- One original B8 radius chosen before the annulus, state and input. -/
def lowCurrentNeighborhood (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  (2 * (1 + Real.sqrt (lowReferenceGraphConstant parameters length) * lowCurrentErrorConstant parameters length compact))⁻¹

theorem lowCurrentNeighborhood_pos (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    0 < lowCurrentNeighborhood parameters length compact := by
  have error := lowCurrentErrorConstant_nonnegative parameters length compact lengthPositive
  unfold lowCurrentNeighborhood
  positivity

theorem lowNormalizedCurrentError_half (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact) :
    ‖lowNormalizedCurrentError parameters length compact lower lengthPositive positive bounded state‖ ≤ 1 / 2 := by
  let coefficient := Real.sqrt (lowReferenceGraphConstant parameters length) * lowCurrentErrorConstant parameters length compact
  have nonnegative : 0 ≤ coefficient := mul_nonneg (Real.sqrt_nonneg _)
    (lowCurrentErrorConstant_nonnegative parameters length compact lengthPositive)
  apply (lowNormalizedCurrentError_bound parameters length compact lower lengthPositive positive bounded state).trans
  change coefficient * _ ≤ _
  apply (mul_le_mul_of_nonneg_left small nonnegative).trans
  change coefficient * (2 * (1 + coefficient))⁻¹ ≤ 1 / 2
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (show 0 < 2 * (1 + coefficient) by positivity)).mpr
  linarith

end Grad.AnnularCurrentLow
