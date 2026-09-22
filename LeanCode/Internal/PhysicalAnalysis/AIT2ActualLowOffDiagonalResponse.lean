import AIT1OriginalCompleteCoupledSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularLowVolterra Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularReconstruction Grad.ActualBoundaryPrimitives

/-- Actual lower off-diagonal BF20 entry, using the accepted current inverse
and the literal BF18 source with its zero incoming coordinate. -/
def actualLowOffDiagonal (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] lowEnergyGraph lower length positive :=
  lowCurrentInverse parameters length compact lower lengthPositive positive bounded state ∘L
    highToLowCross parameters lower length compact lengthPositive positive bounded.le state

def lowOffDiagonalConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  2 * Real.sqrt (lowReferenceGraphConstant parameters length) * highToLowErrorConstant parameters length compact

theorem lowOffDiagonalConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) :
    0 ≤ lowOffDiagonalConstant parameters length compact := by
  unfold lowOffDiagonalConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (highToLowErrorConstant_nonnegative parameters length compact)

theorem actualLowOffDiagonal_bound (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ‖actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field‖ ≤
      lowOffDiagonalConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  let input := highToLowCross parameters lower length compact lengthPositive positive bounded.le state field
  have first := (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state).le_opNorm input
  have second := lowCurrentInverse_bound parameters length compact lower lengthPositive positive bounded state small
  have third := highToLowCross_B8 parameters lower length compact lengthPositive positive bounded.le state field
  change ‖lowCurrentInverse parameters length compact lower lengthPositive positive bounded state input‖ ≤ _
  apply first.trans
  apply (mul_le_mul_of_nonneg_right second (norm_nonneg input)).trans
  apply (mul_le_mul_of_nonneg_left third (by positivity : 0 ≤ 2 * Real.sqrt (lowReferenceGraphConstant parameters length))).trans_eq
  unfold lowOffDiagonalConstant
  ring

theorem actualLowOffDiagonal_equation (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) :
    lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state
      (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field) =
        highToLowCross parameters lower length compact lengthPositive positive bounded.le state field :=
  lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small _

theorem actualLowOffDiagonal_storedEquation (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) :
    (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field).val 1 =
      lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state
        ((actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field).val 0) +
      highToLowBulkCross parameters lower length compact lengthPositive positive bounded.le state field :=
  lowCurrentInverse_storedEquation parameters length compact lower lengthPositive positive bounded state small _

theorem actualLowOffDiagonal_incoming (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) :
    lowIncomingTrace lower length positive bounded
      (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field) = 0 :=
  lowCurrentInverse_incoming parameters length compact lower lengthPositive positive bounded state small _

end Grad.AnnularCoupledInverse
