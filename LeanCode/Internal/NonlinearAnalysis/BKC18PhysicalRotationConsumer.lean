import BKC17ActualUnknownSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.RealFixedRanges

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

/-- The actual physical angular row is the genuine weak derivative on the
original full prescribed-source domain. -/
theorem actualPhysicalCovariantTrace_derivative
    (large : 3 ≤ angular + cell + 2)
    (x : NegativeTrace parameters angular cell 1)
    (xMeanFree : IsAngularMeanFree parameters angular cell x)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    IsAngularDerivative parameters angular cell
      (actualPhysicalCovariantTrace parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell x xi source.val)
      (actualPhysicalRotatedCovariantTrace parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell x xi source.val) := by
  apply actualCovariantKernel_derivative parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
    angular cell (actualSevenSlotTrace parameters L angular cell x xi source.val)
  · exact xMeanFree
  · exact positiveToNegative_derivative parameters angular cell xi

/-- Literal coefficient consumer for the genuine rotation, with no supplied R
row assumption and no replacement of the prescribed source range. -/
theorem actualPhysicalRotatedCovariantTrace_coefficient
    (large : 3 ≤ angular + cell + 2)
    (x : NegativeTrace parameters angular cell 1)
    (xMeanFree : IsAngularMeanFree parameters angular cell x)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (actualPhysicalRotatedCovariantTrace parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell x xi source.val) mode =
      (Complex.I * (mode.1 : ℂ)) • negativeTraceCoefficient parameters angular cell
        (actualPhysicalCovariantTrace parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell x xi source.val) mode :=
  actualPhysicalCovariantTrace_derivative parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell large x xMeanFree xi source mode

/-- Both actual encoded W terms have AE14 support on the original constrained
seven-slot datum. The xi mean condition is exactly the retained-field domain. -/
theorem actualPhysicalEncodedW_support
    (large : 3 ≤ angular + cell + 2)
    (x : NegativeTrace parameters angular cell 1)
    (xMeanFree : IsAngularMeanFree parameters angular cell x)
    (xi : PositiveTrace parameters angular cell 1)
    (xiMeanFree : ∀ axial, positiveTraceCoefficient parameters angular cell xi (0, axial) = 0)
    (source : sourceRange parameters (angular + cell + 2) large) :
    let input := actualSevenSlotTrace parameters L angular cell x xi source.val
    let smallFirst := small.trans (actualMassInverseLowRadius_le_first parameters L compactRadius)
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedWKernel parameters L rho alpha delta parameter epsilon
          compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) ∧
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownWKernel parameters L rho alpha delta parameter epsilon
          compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)
        (fullNegativeKernelAction parameters angular cell
          (actualRecoveredMassKernel parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
          (sevenSlotFlatten parameters angular cell input))) := by
  dsimp only
  constructor
  · apply actualKnownEncodedWKernel_action_support
    exact actualSevenSlotTrace_known_support parameters L angular cell large x xi xiMeanFree source
  · apply actualUnknownWKernel_action_support
    exact actualRecoveredMassKernel_action_meanFree parameters L rho alpha delta parameter epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell
      (actualSevenSlotTrace parameters L angular cell x xi source.val) xMeanFree

end Grad.BoundaryKernelAction
