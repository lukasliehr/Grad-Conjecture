import BCT6PolarAngularCalculus

noncomputable section
open scoped BigOperators

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

/-- The im Fourier row is the genuine ordinary angular derivative of AD19's
actual physical boundary covector on the original unit circle. -/
theorem boundaryScalar_genuine_rotation (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) :
    let physical := fun axialAngle angle =>
      originalBoundaryRow parameters L rho alpha delta parameter epsilon field axialAngle angle
        (polarClosedPoint 1 angle zero_le_one le_rfl) component
    (∀ axialAngle, Differentiable ℝ (physical axialAngle)) ∧
    ∀ mode : ℤ × ℤ,
      angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        deriv (physical axialAngle) angle) mode.2) mode.1 =
          angularCoefficientSequence (boundaryScalar parameters L rho alpha delta parameter epsilon compact
            field compactNonnegative alphaSmall deltaSmall parameterSmall low component) mode := by
  have correspondence := polarFamily_classicalAngular parameters
    (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
    (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent
    2 component 1 zero_le_one le_rfl
  dsimp only at correspondence ⊢
  simp_rw [paddedBoundaryFamily_polarEntry parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low] at correspondence
  exact correspondence

/-- Exactly one additional envelope moment pays the genuine angular row. -/
theorem boundaryRotatedScalarMoment_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (moment : ℕ) :
    let coefficient := boundaryScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component
    Summable (productMoment parameters moment 1 (angularCoefficientSequence coefficient)) ∧
      (∑' mode, productMoment parameters moment 1 (angularCoefficientSequence coefficient) mode) ≤
        boundaryScalarConstant parameters L compact component (moment + 1) *
          (1 + physicalBudget parameters field rho epsilon (moment + 6)) := by
  dsimp only
  have summable := boundaryScalarMoment_summable parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low component (moment + 1)
  refine ⟨angularCoefficientSequence_moment_summable parameters moment 1 _ summable, ?_⟩
  apply (angularCoefficientSequence_moment_bound parameters moment 1 _ summable).trans
  simpa only [show moment + 1 + 5 = moment + 6 by omega] using
    boundaryScalarMoment_bound parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component (moment + 1)

end Grad.ActualBoundaryPrimitives
