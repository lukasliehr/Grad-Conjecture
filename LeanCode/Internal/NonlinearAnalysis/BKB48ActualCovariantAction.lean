import BKB47SevenSlotAction

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.QuotientProjection

/-- The bounded ambient full-kernel reconstruction formula for `a_c` on the
seven AH20 inputs.  Its restriction to the encoded physical supports is not
asserted here. -/
def actualCovariantReconstruction (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ) :
    SevenSlotTrace parameters angular cell →L[ℂ]
      NegativeTrace parameters angular cell 3 :=
  fullSevenSlotKernelAction parameters angular cell
    (actualCovariantKernel parameters L rho alpha delta parameter epsilon compactRadius
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- The bounded ambient formula for the angular row conventionally denoted
`Ra_c`.  This does not assert the still-open genuine-rotation identity. -/
def actualRotatedCovariantReconstruction (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ) :
    SevenSlotTrace parameters angular cell →L[ℂ]
      NegativeTrace parameters angular cell 3 :=
  fullSevenSlotKernelAction parameters angular cell
    (actualRotatedCovariantKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)

theorem actualCovariantReconstruction_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ) (input : SevenSlotTrace parameters angular cell) :
    ‖actualCovariantReconstruction parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
        angular cell input‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
          (actualCovariantKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) *
        ‖input‖ :=
  fullSevenSlotKernelAction_bound parameters angular cell _ input

theorem actualRotatedCovariantReconstruction_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ) (input : SevenSlotTrace parameters angular cell) :
    ‖actualRotatedCovariantReconstruction parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
        angular cell input‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
          (actualRotatedCovariantKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) *
        ‖input‖ :=
  fullSevenSlotKernelAction_bound parameters angular cell _ input

/-- The ambient seven-slot covariant formula, with the three known slots
supplied by the accepted original outer-source trace. -/
def actualPhysicalCovariantTrace (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
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
    NegativeTrace parameters angular cell 3 :=
  actualCovariantReconstruction parameters L rho alpha delta parameter epsilon
    compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
    angular cell (actualSevenSlotTrace parameters L angular cell x xi source)

/-- The corresponding ambient angular-row formula.  Equality with the
physical rotation of `actualPhysicalCovariantTrace` is not claimed here. -/
def actualPhysicalRotatedCovariantTrace (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
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
    NegativeTrace parameters angular cell 3 :=
  actualRotatedCovariantReconstruction parameters L rho alpha delta parameter epsilon
    compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall
    angular cell (actualSevenSlotTrace parameters L angular cell x xi source)

end Grad.BoundaryKernelAction
