import AKDS37OriginalUnitRowsBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.CartesianStartup.StartupRankOperator
variable {parameters : PhaseParameters} {length radius : ℝ}

theorem embeddedRow_bound (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius)
    (rank : ℕ) (row : Fin 3) :
    (embeddedRow (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) row).bound ≤
      (embeddingBudget * rowsBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length)) * physicalBudget parameters state.field state.rho state.epsilon 10 := by
  have rows := state.row_bounds radiusNonnegative rank
  have rowPositive := rowBudgets_nonnegative 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length)
  have forceCap : forceBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) ≤ rowsBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) := by
    unfold rowsBudget
    linarith [rowPositive.2.1, rowPositive.2.2.2]
  have thirdCap : thirdBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) ≤ rowsBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) := by
    unfold rowsBudget
    linarith [rowPositive.1, rowPositive.2.2.2]
  have fluxCap : principalFluxBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) ≤ rowsBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) := by
    unfold rowsBudget
    linarith [rowPositive.1, rowPositive.2.1]
  have budgetPositive := physicalBudget_nonnegative parameters state.field state.rho state.epsilon 10
  have planarCap : (value rank planarInclusionMap).bound ≤ embeddingBudget := by
    change (value 0 planarInclusionMap).bound ≤ _
    unfold embeddingBudget
    linarith [(value 0 toroidalInclusionMap).nonnegative]
  have toroidalCap : (value rank toroidalInclusionMap).bound ≤ embeddingBudget := by
    change (value 0 toroidalInclusionMap).bound ≤ _
    unfold embeddingBudget
    linarith [(value 0 planarInclusionMap).nonnegative]
  fin_cases row
  · change (value rank planarInclusionMap).bound * (force (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).bound ≤ _
    exact (mul_le_mul planarCap (rows.1.trans (mul_le_mul_of_nonneg_right forceCap budgetPositive))
      (force (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)
  · change (value rank toroidalInclusionMap).bound * (third (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).bound ≤ _
    exact (mul_le_mul toroidalCap (rows.2.1.trans (mul_le_mul_of_nonneg_right thirdCap budgetPositive))
      (third (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)
  · change (value rank planarInclusionMap).bound * (principalFlux (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).bound ≤ _
    exact (mul_le_mul planarCap (rows.2.2.2.trans (mul_le_mul_of_nonneg_right fluxCap budgetPositive))
      (principalFlux (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative)).nonnegative embeddingBudget_nonnegative).trans_eq (by ring)

theorem principal_bound (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius)
    (rank : ℕ) (outer inner : Fin 2) :
    (principalTensor (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) outer inner).bound ≤
      principalBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) (originalUnitFive parameters length) * physicalBudget parameters state.field state.rho state.epsilon 10 := by
  have entryBound (row : Fin 3) := mul_le_mul (principalFixed_le rank outer inner row)
    (state.embeddedRow_bound radiusNonnegative rank row)
    (embeddedRow (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) row).nonnegative fixedTensorBudget_nonnegative
  change ((principalFixed rank outer inner 0).bound * (embeddedRow (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) 0).bound +
    (principalFixed rank outer inner 1).bound * (embeddedRow (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) 1).bound) +
    (principalFixed rank outer inner 2).bound * (embeddedRow (unitDiskAdmissible parameters) rank state.data (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) 2).bound ≤ _
  exact (add_le_add (add_le_add (entryBound 0) (entryBound 1)) (entryBound 2)).trans_eq (by unfold principalBudget; ring)

end Grad.OriginalCoreRealization.OriginalUnitRankState
