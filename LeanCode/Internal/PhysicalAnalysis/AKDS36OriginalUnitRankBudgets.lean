import AKDS35OriginalUnitLowGraphBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.CartesianStartup.StartupRankOperator
variable {parameters : PhaseParameters} {length radius : ℝ}

theorem current_bound (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) (rank : ℕ) :
    (current (unitDiskAdmissible parameters) rank state.data.gaugeDeviation
      (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative)).bound≤
      currentBudget 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) := by
  let admissible := unitDiskAdmissible parameters
  let four := originalUnitFour parameters length radius
  let inverse := state.inverseCoherent radiusNonnegative
  have coherent := (state.coherent radiusNonnegative).2.2.2.1
  have boundsBoth := state.gauge_extension_bounds radiusNonnegative
  have gauge := matrix_bound_of_pair admissible rank (fullGaugeFamily state.data.gaugeDeviation)
    (fullGaugeFamily_coherent _ coherent) (startupGaugeMatrixConstant 1 parameters.sigma0 parameters.gamma four) boundsBoth.1
  have extension := matrix_bound_of_pair admissible rank (complementExtensionFamily admissible state.data.gaugeDeviation)
    (complementExtensionFamily_coherent _ _ coherent inverse)
    (startupExtensionMatrixConstant 1 parameters.sigma0 parameters.gamma four) boundsBoth.2
  change 1 + (matrix admissible rank (complementExtensionFamily admissible state.data.gaugeDeviation)
    (complementExtensionFamily_coherent _ _ coherent inverse)).bound *
    ((complement rank).bound * (matrix admissible rank (fullGaugeFamily state.data.gaugeDeviation)
      (fullGaugeFamily_coherent _ coherent)).bound) ≤ _
  unfold currentBudget
  rw [complement_bound_independent]
  exact add_le_add_right (mul_le_mul extension
    (mul_le_mul_of_nonneg_left gauge (complement 0).nonnegative)
    (mul_nonneg (complement 0).nonnegative (matrix admissible rank (fullGaugeFamily state.data.gaugeDeviation)
      (fullGaugeFamily_coherent _ coherent)).nonnegative)
    (mul_nonneg (by norm_num) (abs_nonneg _))) 1

theorem rowLowBounds (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius)
    (grade : ℕ) (smallGrade : grade≤1) :
    ‖state.data.fluxDeviation grade‖≤originalUnitFour parameters length radius grade*physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    ‖state.data.rotatedPlanarProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    ‖state.data.rotatedThirdProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters state.field state.rho state.epsilon 10 := by
  have rows := state.rowBounds radiusNonnegative grade
  have four := mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : grade+4≤10))
    (originalUnitFour_nonnegative parameters length radius grade)
  have five := mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : grade+5≤10))
    (originalUnitFive_nonnegative parameters length grade)
  exact ⟨rows.2.1.trans four,rows.2.2.1.trans five,rows.2.2.2.trans five⟩

theorem deviation_bounds (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) (rank : ℕ) :
    (matrix (unitDiskAdmissible parameters) rank state.data.rotatedPlanarProduct
      (state.coherent radiusNonnegative).2.2.2.2.2.2.2.1).bound≤
      (2*|startupDeviationMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFive parameters length)|)*
        physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    (matrix (unitDiskAdmissible parameters) rank state.data.rotatedThirdProduct
      (state.coherent radiusNonnegative).2.2.2.2.2.2.2.2).bound≤
      (2*|startupDeviationMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFive parameters length)|)*
        physicalBudget parameters state.field state.rho state.epsilon 10 ∧
    (matrix (unitDiskAdmissible parameters) rank state.data.fluxDeviation
      (state.coherent radiusNonnegative).2.2.2.2.1).bound≤
      (2*|startupDeviationMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius)|)*
        physicalBudget parameters state.field state.rho state.epsilon 10 := by
  have d0 := state.rowLowBounds radiusNonnegative 0 (by norm_num)
  have d1 := state.rowLowBounds radiusNonnegative 1 le_rfl
  have positive := physicalBudget_nonnegative parameters state.field state.rho state.epsilon 10
  exact ⟨matrix_bound_of_scaled_pair (unitDiskAdmissible parameters) rank _ _ _ _ positive
      (startupDeviationMatrix_bounds (unitDiskAdmissible parameters) _ _ (originalUnitFive parameters length) _ d0.2.1 d1.2.1),
    matrix_bound_of_scaled_pair (unitDiskAdmissible parameters) rank _ _ _ _ positive
      (startupDeviationMatrix_bounds (unitDiskAdmissible parameters) _ _ (originalUnitFive parameters length) _ d0.2.2 d1.2.2),
    matrix_bound_of_scaled_pair (unitDiskAdmissible parameters) rank _ _ _ _ positive
      (startupDeviationMatrix_bounds (unitDiskAdmissible parameters) _ _ (originalUnitFour parameters length radius) _ d0.1 d1.1)⟩

end Grad.OriginalCoreRealization.OriginalUnitRankState
