import AKDS30OriginalUnitLedgerProfiles
import AKDP32ActualLedgerRankState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives Grad.CartesianStartup
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.RadialLedger

def originalUnitRankRadius (parameters : PhaseParameters) (length radius : ℝ) : ℝ :=
  min (originalCoefficientLowRadius parameters length)
    (min (ledgerLowRadius parameters 1 radius 1) (determinantLowRadius (originalUnitFour parameters length radius)))

theorem originalUnitRankRadius_positive (parameters : PhaseParameters) (length radius : ℝ) :
    0<originalUnitRankRadius parameters length radius :=
  lt_min (originalCoefficientLowRadius_positive parameters length)
    (lt_min (ledgerLowRadius_positive parameters zero_lt_one radius zero_lt_one) (determinantLowRadius_positive _))

def OriginalUnitRankData (parameters : PhaseParameters) := ℝ×ℝ×ℝ×ℝ×ℝ×ACore parameters 3
namespace OriginalUnitRankData
abbrev rho {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.1
abbrev alpha {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.2.1
abbrev delta {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.2.2.1
abbrev parameter {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.2.2.2.1
abbrev epsilon {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.2.2.2.2.1
abbrev field {parameters : PhaseParameters} (state : OriginalUnitRankData parameters) := state.2.2.2.2.2
end OriginalUnitRankData

/-- A faithful physical state on one original-disk coefficient ball. The
physical length is independent of the algebra's unit-disk parameters. -/
def OriginalUnitRankState (parameters : PhaseParameters) (length radius : ℝ) :=
  { state : OriginalUnitRankData parameters //
    |state.alpha|≤radius ∧ |state.delta|≤radius ∧ |state.parameter|≤radius ∧
    physicalBudget parameters state.field state.rho state.epsilon 12≤1 ∧
    physicalBudget parameters state.field state.rho state.epsilon 6≤originalUnitRankRadius parameters length radius }

namespace OriginalUnitRankState
variable {parameters : PhaseParameters} {length radius : ℝ}
abbrev rho (state : OriginalUnitRankState parameters length radius) := state.val.rho
abbrev epsilon (state : OriginalUnitRankState parameters length radius) := state.val.epsilon
abbrev field (state : OriginalUnitRankState parameters length radius) := state.val.field
abbrev data (state : OriginalUnitRankState parameters length radius) :=
  originalUnitLedgerData parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon state.val.field
abbrev unit (state : OriginalUnitRankState parameters length radius) := state.property.2.2.2.1
abbrev small (state : OriginalUnitRankState parameters length radius) := state.property.2.2.2.2

theorem coefficientLow (state : OriginalUnitRankState parameters length radius) :
    physicalBudget parameters state.field state.rho state.epsilon 6≤originalCoefficientLowRadius parameters length :=
  state.small.trans (min_le_left _ _)

theorem determinantLow (state : OriginalUnitRankState parameters length radius) :
    physicalBudget parameters state.field state.rho state.epsilon 6≤determinantLowRadius (originalUnitFour parameters length radius) :=
  state.small.trans ((min_le_right _ _).trans (min_le_right _ _))

theorem seedBase (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    ‖seedInverseInput (unitDiskAdmissible parameters) state.val.rho state.val.alpha state.val.delta state.val.parameter 0‖≤1/4 := by
  have lowSix : physicalBudget parameters state.field state.rho state.epsilon 6≤1 :=
    (physicalBudget_monotone parameters state.field state.rho state.epsilon (by norm_num : 6≤12)).trans state.unit
  have rhoSmall : |state.rho|≤1 := by
    unfold physicalBudget at lowSix
    linarith [originalGradeNorm_nonnegative 6 state.field,abs_nonneg state.epsilon]
  have epsilonSmall : |state.epsilon|≤1 := by
    unfold physicalBudget at lowSix
    linarith [originalGradeNorm_nonnegative 6 state.field,abs_nonneg state.rho]
  have margin := actualInverseInput_margins parameters (unitDiskAdmissible parameters) radiusNonnegative zero_lt_one
    state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon rhoSmall state.property.1
    state.property.2.1 state.property.2.2.1 epsilonSmall state.field
    (state.small.trans ((min_le_right _ _).trans (min_le_left _ _)))
  exact margin.2.2

theorem coherent (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    LedgerCoherent state.data :=
  originalUnitLedgerData_coherent parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon state.field state.coefficientLow (state.seedBase radiusNonnegative)

theorem rowBounds (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) (grade : ℕ) :
    ‖state.data.gaugeDeviation grade‖≤originalUnitFour parameters length radius grade*physicalBudget parameters state.field state.rho state.epsilon (grade+4) ∧
    ‖state.data.fluxDeviation grade‖≤originalUnitFour parameters length radius grade*physicalBudget parameters state.field state.rho state.epsilon (grade+4) ∧
    ‖state.data.rotatedPlanarProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters state.field state.rho state.epsilon (grade+5) ∧
    ‖state.data.rotatedThirdProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters state.field state.rho state.epsilon (grade+5) :=
  originalUnitLedgerData_row_bounds parameters length radius radiusNonnegative state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.val.epsilon state.field state.property.1 state.property.2.1 state.property.2.2.1 state.coefficientLow grade

theorem inverseCoherent (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    FamilyCoherent (determinantInverseFamily (unitDiskAdmissible parameters) state.data.gaugeDeviation) := by
  have bounds (grade : ℕ) := (state.rowBounds radiusNonnegative grade).1
  have gauge := (state.coherent radiusNonnegative).2.2.2.1
  exact (determinantInverse_estimate parameters (unitDiskAdmissible parameters) state.field state.rho state.epsilon
    state.data.gaugeDeviation gauge (originalUnitFour parameters length radius) (originalUnitFour_nonnegative parameters length radius)
    ((physicalBudget_monotone parameters state.field state.rho state.epsilon (by norm_num : 6≤12)).trans state.unit)
    bounds state.determinantLow).actualCoherent

end OriginalUnitRankState
end Grad.OriginalCoreRealization
