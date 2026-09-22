import AKDS31OriginalUnitRankState
import AKDP56ActualPrincipalEndpointControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients
open Grad.CartesianStartup Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
variable {parameters : PhaseParameters} {length radius : ℝ}

def budget (grade : ℕ) (state : OriginalUnitRankState parameters length radius) : ℝ :=
  1+physicalBudget parameters state.field state.rho state.epsilon (12+grade)

theorem budget_nonnegative (grade : ℕ) (state : OriginalUnitRankState parameters length radius) :
    0≤budget grade state := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)

theorem currentProfiles (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    FamilyEstimate parameters state.field state.rho state.epsilon 12 (unitProfile (originalUnitFour parameters length radius))
      (fullGaugeFamily state.data.gaugeDeviation) (identityFamily 1 parameters.sigma0 parameters.gamma 1 3) ∧
    FamilyEstimate parameters state.field state.rho state.epsilon 12
      (unitProfile (complementExtensionConstant (originalUnitFour parameters length radius)))
      (complementExtensionFamily (unitDiskAdmissible parameters) state.data.gaugeDeviation)
      (identityFamily 1 parameters.sigma0 parameters.gamma 1 3) :=
  startupCurrent_actualProfiles parameters (unitDiskAdmissible parameters) state.field state.data.gaugeDeviation
    (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative)
    (originalUnitFour parameters length radius) (originalUnitFour_nonnegative parameters length radius)
    ((physicalBudget_monotone parameters state.field state.rho state.epsilon (by norm_num : 6≤12)).trans state.unit)
    (fun grade => (state.rowBounds radiusNonnegative grade).1) state.determinantLow

theorem deviationProfiles (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    FamilyEstimate parameters state.field state.rho state.epsilon 12 (startupDeviationProfile (originalUnitFour parameters length radius))
      state.data.fluxDeviation (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3) ∧
    FamilyEstimate parameters state.field state.rho state.epsilon 12 (startupDeviationProfile (originalUnitFive parameters length))
      state.data.rotatedPlanarProduct (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 2) ∧
    FamilyEstimate parameters state.field state.rho state.epsilon 12 (startupDeviationProfile (originalUnitFive parameters length))
      state.data.rotatedThirdProduct (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 1) := by
  have coherence := state.coherent radiusNonnegative
  constructor
  · apply startupDeviationFamily_estimate parameters state.field state.rho state.epsilon 12 _ coherence.2.2.2.2.1
      (originalUnitFour parameters length radius) (originalUnitFour_nonnegative parameters length radius)
    intro grade
    exact (state.rowBounds radiusNonnegative grade).2.1.trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : grade+4≤12+grade))
        (originalUnitFour_nonnegative parameters length radius grade))
  constructor
  · apply startupDeviationFamily_estimate parameters state.field state.rho state.epsilon 12 _ coherence.2.2.2.2.2.2.2.1
      (originalUnitFive parameters length) (originalUnitFive_nonnegative parameters length)
    intro grade
    exact (state.rowBounds radiusNonnegative grade).2.2.1.trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : grade+5≤12+grade))
        (originalUnitFive_nonnegative parameters length grade))
  · apply startupDeviationFamily_estimate parameters state.field state.rho state.epsilon 12 _ coherence.2.2.2.2.2.2.2.2
      (originalUnitFive parameters length) (originalUnitFive_nonnegative parameters length)
    intro grade
    exact (state.rowBounds radiusNonnegative grade).2.2.2.trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : grade+5≤12+grade))
        (originalUnitFive_nonnegative parameters length grade))

end Grad.OriginalCoreRealization.OriginalUnitRankState
