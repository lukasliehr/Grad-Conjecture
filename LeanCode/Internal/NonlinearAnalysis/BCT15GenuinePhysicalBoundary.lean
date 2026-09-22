import BCT14PrimitiveUniqueness
import BKC16ActualCovariantRotation

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters)
  (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
  (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
  (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
  (angular cell : ℕ)

/-- The literal high physical covector applied to the reconstructed current. -/
def actualHighPhysicalBoundary :
    SevenSlotTrace parameters angular cell →L[ℂ] NegativeTrace parameters angular cell 1 :=
  fullSevenSlotKernelAction parameters angular cell
    (actualHighPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

theorem actualHighPhysicalBoundary_high (input : SevenSlotTrace parameters angular cell) :
    IsHighAngularTrace parameters angular cell
      (actualHighPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) := by
  unfold actualHighPhysicalBoundary fullSevenSlotKernelAction
  simp only [ContinuousLinearMap.comp_apply]
  rw [actualHighPhysicalBoundaryKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply]
  exact highAngularKernel_high parameters angular cell _

/-- AH21 with its genuine angular derivative established from the actual
physical coefficient and actual reconstruction. The only input relation
is the literal AH20 scalar derivative and mean-free Rp. -/
theorem actualHighPhysicalBoundary_derivative (input : SevenSlotTrace parameters angular cell)
    (supported : IsAngularMeanFree parameters angular cell (input 0))
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    IsAngularDerivative parameters angular cell
      (actualHighPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input)
      (actualDifferentiatedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) := by
  unfold actualHighPhysicalBoundary actualDifferentiatedPhysicalBoundary fullSevenSlotKernelAction
    actualHighPhysicalBoundaryKernel actualDifferentiatedPhysicalBoundaryKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add]
  apply highAngularKernel_derivative
  unfold actualBoundaryMultiplier actualRotatedBoundaryMultiplier
  apply boundaryRowMultiplicationKernel_derivative
  exact actualCovariantKernel_derivative parameters L rho alpha delta parameter epsilon compact field
    (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
    compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input supported scalarDerivative

/-- The complete P_R extension is the original high physical boundary on
every admissible seven-slot trace, not a replacement boundary condition. -/
theorem actualPhysicalBoundaryPR_eq_high (input : SevenSlotTrace parameters angular cell)
    (supported : IsAngularMeanFree parameters angular cell (input 0))
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    highBoundaryPrimitiveTrace parameters angular cell
      (actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) =
      actualHighPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input := by
  apply angularInverse_recovers_of_derivative
  · exact (actualHighPhysicalBoundary_high parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input).meanFree
  · exact actualHighPhysicalBoundary_derivative parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input supported scalarDerivative

end Grad.ActualBoundaryPrimitives
