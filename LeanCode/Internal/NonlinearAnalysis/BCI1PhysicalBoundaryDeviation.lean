import BCT25PhysicalBoundaryConsumer
import ASG47ActualInsertedTraceConsumer

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Grad.ActualBoundaryInverse

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

def boundaryDeviationScalar (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) : ℤ × ℤ → ℂ :=
  polarEntryScalar parameters (boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field)
    (boundaryPolarDeviation_coherent parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low) 2 component 0 1

def boundaryDeviationConstant (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) (moment : ℕ) : ℝ :=
  polarEntryConstant 2 component moment 0 *
    |(paddedBoundaryProfile parameters L compact).deviation (moment + 1)|

theorem boundaryDeviationConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) (moment : ℕ) : 0 ≤ boundaryDeviationConstant parameters L compact component moment :=
  mul_nonneg (polarEntryConstant_pos 2 component moment 0).le (abs_nonneg _)

theorem boundaryDeviationScalar_summable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component)) :=
  polarEntryScalarMoment_summable parameters _
    (boundaryPolarDeviation_coherent parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low) 2 component moment 0 1 zero_le_one le_rfl

/-- The true reference deviation has no constant term. This vanishing
estimate, rather than a 1+B estimate, will justify the boundary inverse. -/
theorem boundaryDeviationScalar_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    (∑' mode, productMoment parameters moment 1
      (boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component) mode) ≤
      boundaryDeviationConstant parameters L compact component moment *
        physicalBudget parameters field rho epsilon (moment + 5) := by
  have coherent := boundaryPolarDeviation_coherent parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low
  have raw := polarEntryScalarMoment_bound parameters
    (boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field) coherent
    2 component moment 0 1 zero_le_one le_rfl
  apply raw.trans
  have deviation := boundaryPolarDeviation_bound parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low (moment + 1)
  have larger := mul_le_mul_of_nonneg_right
    (le_abs_self ((paddedBoundaryProfile parameters L compact).deviation (moment + 1)))
    (physicalBudget_nonnegative parameters field rho epsilon (4 + (moment + 1)))
  have estimate := mul_le_mul_of_nonneg_left (deviation.trans larger)
    (polarEntryConstant_pos 2 component moment 0).le
  simpa only [Nat.add_zero, show 4 + (moment + 1) = moment + 5 by omega,
    boundaryDeviationConstant, mul_assoc] using estimate

theorem boundaryRotatedDeviationScalar_moment (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    let coefficient := boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component
    Summable (productMoment parameters moment 1 (angularCoefficientSequence coefficient)) ∧
      (∑' mode, productMoment parameters moment 1 (angularCoefficientSequence coefficient) mode) ≤
        boundaryDeviationConstant parameters L compact component (moment + 1) *
          physicalBudget parameters field rho epsilon (moment + 6) := by
  dsimp only
  have summable := boundaryDeviationScalar_summable parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low component (moment + 1)
  refine ⟨angularCoefficientSequence_moment_summable parameters moment 1 _ summable, ?_⟩
  apply (angularCoefficientSequence_moment_bound parameters moment 1 _ summable).trans
  simpa only [show moment + 1 + 5 = moment + 6 by omega] using
    boundaryDeviationScalar_moment parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component (moment + 1)

end Grad.ActualBoundaryInverse
