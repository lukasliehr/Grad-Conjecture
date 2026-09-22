import BKB52ActualFirstInverse

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation Grad.AxisCore
open Grad.SourceBoundaryTrace

def sevenSlotCoefficientVector (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) (mode : ℤ × ℤ) :
    ComplexEuclidean 7 :=
  WithLp.toLp 2 (fun slot =>
    negativeTraceCoefficient parameters angular cell (input slot) mode 0)

theorem fullSevenSlotKernelAction_coefficient_hasSum {targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters 7 targetDimension)
    (input : SevenSlotTrace parameters angular cell) (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ × ℤ =>
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (sevenSlotCoefficientVector parameters angular cell input
          (twoFrequencyTranslation shift mode)))
      (negativeTraceCoefficient parameters angular cell
        (fullSevenSlotKernelAction parameters angular cell kernel input) mode) := by
  apply (fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel
    (sevenSlotFlatten parameters angular cell input) mode).congr
  intro shift
  congr 1

/-- Exact ambient full-kernel consumer for the source-dependent AH20 seven
inputs, with literal coefficient convolution and the original AH18 trace
bounds.  This prerequisite does not assert AE14 support preservation, the
genuine physical `R` identity, or the final evaluated `B(t+7/8)` bounds. -/
theorem actualAF16_covariant_consumer (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (positive : 0 < L)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    let input := actualSevenSlotTrace parameters L angular cell x xi source
    let covariantKernel := actualCovariantKernel parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall
    let rotatedKernel := actualRotatedCovariantKernel parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall
    ‖actualPhysicalCovariantTrace parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
        angular cell x xi source‖ ≤
        fullKernelMoment parameters (angular + cell + 1) covariantKernel * ‖input‖ ∧
      ‖actualPhysicalRotatedCovariantTrace parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
        angular cell x xi source‖ ≤
        fullKernelMoment parameters (angular + cell + 1) rotatedKernel * ‖input‖ ∧
      ‖input‖ ^ 2 ≤ ‖x‖ ^ 2 + 3 * ‖xi‖ ^ 2 +
        sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source‖ ^ 2 := by
  dsimp only
  exact ⟨actualCovariantReconstruction_bound parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall angular cell _,
    actualRotatedCovariantReconstruction_bound parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall angular cell _,
    actualSevenSlotTrace_bound_sq parameters L positive angular cell x xi source⟩

end Grad.BoundaryKernelAction
