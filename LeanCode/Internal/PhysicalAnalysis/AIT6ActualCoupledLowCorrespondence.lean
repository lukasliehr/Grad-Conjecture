import AIT5OriginalLowCrossWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)

include small

/-- The low fixed-point coordinate is equivalent to the actual current
Cauchy equation with known and cross sources added exactly once. -/
theorem coupledLow_fixedPoint_iff (known : LowEnergyData lower)
    (field : CoupledSpace lower length positive lengthPositive) :
    field.ofLp.2 = lowCurrentInverse parameters length compact lower lengthPositive positive bounded state known +
      actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field.ofLp.1 ↔
    lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state field.ofLp.2 =
      known + highToLowCross parameters lower length compact lengthPositive positive bounded.le state field.ofLp.1 := by
  constructor
  · intro fixed
    rw [fixed, map_add, lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small,
      actualLowOffDiagonal_equation parameters lower length compact lengthPositive positive bounded state small]
  · intro equation
    have inverted := congrArg (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state) equation
    rw [lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive bounded state small, map_add] at inverted
    exact inverted

/-- The low incoming value is unchanged by the actual cross response. -/
theorem coupledLow_fixedPoint_incoming (known : LowEnergyData lower)
    (field : CoupledSpace lower length positive lengthPositive)
    (fixed : field.ofLp.2 = lowCurrentInverse parameters length compact lower lengthPositive positive bounded state known +
      actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field.ofLp.1) :
    lowIncomingTrace lower length positive bounded field.ofLp.2 = known.ofLp.2 := by
  rw [fixed, map_add, lowCurrentInverse_incoming parameters length compact lower lengthPositive positive bounded state small,
    actualLowOffDiagonal_incoming parameters lower length compact lengthPositive positive bounded state small, add_zero]

/-- The original complete graph slope contains one current low row and one
physical high-to-low forcing, in addition to the prescribed known source. -/
theorem coupledLow_fixedPoint_storedEquation (known : LowEnergyData lower)
    (field : CoupledSpace lower length positive lengthPositive)
    (fixed : field.ofLp.2 = lowCurrentInverse parameters length compact lower lengthPositive positive bounded state known +
      actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field.ofLp.1) :
    field.ofLp.2.val 1 =
      lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state (field.ofLp.2.val 0) +
      known.ofLp.1 + highToLowBulkCross parameters lower length compact lengthPositive positive bounded.le state field.ofLp.1 := by
  have equation := (coupledLow_fixedPoint_iff parameters lower length compact lengthPositive positive bounded state small known field).mp fixed
  have bulk := congrArg (fun data : LowEnergyData lower => data.ofLp.1) equation
  change field.ofLp.2.val 1 -
    lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state (field.ofLp.2.val 0) =
    known.ofLp.1 + highToLowBulkCross parameters lower length compact lengthPositive positive bounded.le state field.ofLp.1 at bulk
  have added := sub_eq_iff_eq_add.mp bulk
  exact added.trans (by abel)

end Grad.AnnularCoupledInverse
