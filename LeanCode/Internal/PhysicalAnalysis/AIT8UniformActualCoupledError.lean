import AIT7ActualPhysicalOffDiagonalOperator
import AIQ15UniformPhysicalHighInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def highOffDiagonalConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  actualHighCrossResponseConstant parameters length compact * lowToHighErrorConstant parameters length compact

def actualCoupledConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  max (highOffDiagonalConstant parameters length compact) (lowOffDiagonalConstant parameters length compact)

theorem highOffDiagonalConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) : 0 ≤ highOffDiagonalConstant parameters length compact :=
  mul_nonneg (actualHighCrossResponseConstant_nonnegative parameters length compact)
    (lowToHighErrorConstant_nonnegative parameters length compact lengthPositive)

theorem actualCoupledConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) :
    0 ≤ actualCoupledConstant parameters length compact :=
  (lowOffDiagonalConstant_nonnegative parameters length compact).trans (le_max_right _ _)

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (highSmall : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters length compact)

theorem actualHighOffDiagonal_bound (field : lowEnergyGraph lower length positive) :
    ‖actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field‖ ≤
      highOffDiagonalConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  have high := actualHighCrossResponse_bound parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
    (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field)
  have cross := lowToHighCross_B8 parameters lower length compact lengthPositive positive lowerHalf state field
  change ‖actualHighCrossResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
    (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field)‖ ≤ _
  apply high.trans
  apply (mul_le_mul_of_nonneg_left cross (actualHighCrossResponseConstant_nonnegative parameters length compact)).trans_eq
  unfold highOffDiagonalConstant
  ring

/-- The exact Hilbert direct sum gives the maximum of the two actual
response constants, uniformly in the collar and on the original B8 budget. -/
theorem actualCoupledOffDiagonal_bound
    (lowSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact) :
    ‖actualCoupledOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall‖ ≤
      actualCoupledConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 :=
  hilbertOffDiagonal_norm _ _ _ _ _
    (highOffDiagonalConstant_nonnegative parameters length compact lengthPositive)
    (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8)
    (actualHighOffDiagonal_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall)
    (actualLowOffDiagonal_bound parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state lowSmall)

end Grad.AnnularCoupledInverse
