import BCT4ExactPolarBoundary

noncomputable section

set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- Fixed numerical profile for the full original boundary coefficient. -/
def boundaryScalarConstant (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) (moment : ℕ) : ℝ :=
  polarEntryConstant 2 component moment 0 *
    (|(paddedBoundaryProfile parameters L compact).fixed (moment + 1)| +
      |(paddedBoundaryProfile parameters L compact).deviation (moment + 1)|)

theorem boundaryScalarConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (component : Fin 3) (moment : ℕ) :
    0 ≤ boundaryScalarConstant parameters L compact component moment :=
  mul_nonneg (polarEntryConstant_pos 2 component moment 0).le
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

def boundaryScalar (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) : ℤ × ℤ → ℂ :=
  polarEntryScalar parameters (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
    (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent 2 component 0 1

theorem boundaryScalar_doubleCoefficient (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      originalBoundaryRow parameters L rho alpha delta parameter epsilon field axialAngle angle
        (polarClosedPoint 1 angle zero_le_one le_rfl) component) mode.2) mode.1 =
      boundaryScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component mode := by
  have coefficient := polarEntry_doubleCoefficient parameters
    (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
    (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent
    2 component 1 zero_le_one le_rfl mode
  simp_rw [paddedBoundaryFamily_polarEntry parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low] at coefficient
  exact coefficient

theorem boundaryScalarMoment_summable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (boundaryScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component)) :=
  polarEntryScalarMoment_summable parameters _
    (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent
    2 component moment 0 1 zero_le_one le_rfl

/-- Full two-frequency envelope on the original radius-one phase, with
one high physical factor and no high-grade smallness. -/
theorem boundaryScalarMoment_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    (∑' mode, productMoment parameters moment 1
      (boundaryScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component) mode) ≤
      boundaryScalarConstant parameters L compact component moment *
        (1 + physicalBudget parameters field rho epsilon (moment + 5)) := by
  have estimate := paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  have fullNorm : ‖paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field (moment + 1)‖ ≤
      (|(paddedBoundaryProfile parameters L compact).fixed (moment + 1)| +
        |(paddedBoundaryProfile parameters L compact).deviation (moment + 1)|) *
          (1 + physicalBudget parameters field rho epsilon (moment + 5)) := by
    have triangle := norm_add_le
      (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field (moment + 1) -
        paddedBoundaryReference parameters (moment + 1))
      (paddedBoundaryReference parameters (moment + 1))
    rw [sub_add_cancel] at triangle
    have bound := triangle.trans (add_le_add (estimate.deviationBound (moment + 1))
      (estimate.referenceBound (moment + 1)))
    have budget := physicalBudget_nonnegative parameters field rho epsilon (moment + 5)
    rw [show 4 + (moment + 1) = moment + 5 by omega] at bound
    have fixedAbs := le_abs_self ((paddedBoundaryProfile parameters L compact).fixed (moment + 1))
    have devAbs := le_abs_self ((paddedBoundaryProfile parameters L compact).deviation (moment + 1))
    nlinarith [abs_nonneg ((paddedBoundaryProfile parameters L compact).fixed (moment + 1)),
      abs_nonneg ((paddedBoundaryProfile parameters L compact).deviation (moment + 1))]
  have raw := polarEntryScalarMoment_bound parameters
    (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
    estimate.actualCoherent 2 component moment 0 1 zero_le_one le_rfl
  apply raw.trans
  have bound := mul_le_mul_of_nonneg_left fullNorm (polarEntryConstant_pos 2 component moment 0).le
  simpa only [Nat.add_zero, boundaryScalarConstant, mul_assoc] using bound

end Grad.ActualBoundaryPrimitives
