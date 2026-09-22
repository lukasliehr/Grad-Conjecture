import AIT8UniformActualCoupledError
import AEL7OneOriginalHighLowBall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularCurrentInverse
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- One primitive B8 radius, fixed before the inner radius, state or data.
It retains every actual diagonal/reconstruction margin and bounds BF20 by 1/2. -/
def coupledPrimitiveRadius (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  min (currentAnnularPrimitiveRadius parameters length compact)
    (min 1 (2 * (1 + actualCoupledConstant parameters length compact))⁻¹)

theorem coupledPrimitiveRadius_positive (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) : 0 < coupledPrimitiveRadius parameters length compact := by
  have coefficient := actualCoupledConstant_nonnegative parameters length compact
  exact lt_min (currentAnnularPrimitiveRadius_positive parameters length compact lengthPositive)
    (lt_min (by norm_num) (by positivity))

variable (parameters : PhaseParameters) (length compact : ℝ)
  (state : RetainedInverseState parameters length compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include small

theorem coupledPrimitive_highSmall :
    state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters length compact :=
  small.trans ((min_le_left _ _).trans (min_le_left _ _))

theorem coupledPrimitive_lowSmall :
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact :=
  small.trans ((min_le_left _ _).trans (min_le_right _ _))

theorem coupledPrimitive_budget_one :
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1 :=
  small.trans ((min_le_right _ _).trans (min_le_left _ _))

theorem coupledPrimitive_error_half :
    actualCoupledConstant parameters length compact *
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1 / 2 := by
  have coefficient := actualCoupledConstant_nonnegative parameters length compact
  have margin := small.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply (mul_le_mul_of_nonneg_left margin coefficient).trans
  change actualCoupledConstant parameters length compact * (2 * (1 + actualCoupledConstant parameters length compact))⁻¹ ≤ 1 / 2
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (show 0 < 2 * (1 + actualCoupledConstant parameters length compact) by positivity)).mpr
  linarith

theorem actualCoupledOffDiagonal_half (lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    ‖actualCoupledOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state
      (coupledPrimitive_highSmall parameters length compact state small)‖ ≤ 1 / 2 :=
  (actualCoupledOffDiagonal_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state
    (coupledPrimitive_highSmall parameters length compact state small)
    (coupledPrimitive_lowSmall parameters length compact state small)).trans
      (coupledPrimitive_error_half parameters length compact state small)

end Grad.AnnularCoupledInverse
