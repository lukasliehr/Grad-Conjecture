import BCT12ExactHighPrimitive

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

theorem actualDifferentiatedPhysicalBoundary_high
    (input : SevenSlotTrace parameters angular cell) :
    IsHighAngularTrace parameters angular cell
      (actualDifferentiatedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) := by
  unfold actualDifferentiatedPhysicalBoundary fullSevenSlotKernelAction
  simp only [ContinuousLinearMap.comp_apply]
  rw [actualDifferentiatedPhysicalBoundaryKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply]
  exact highAngularKernel_high parameters angular cell _

/-- The exact AH8 nonsmooth extension into the complete high P_R carrier.
Its derivative coordinates are the genuine AH21 kernel expression. -/
def actualPhysicalBoundaryPR :
    SevenSlotTrace parameters angular cell →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  (actualDifferentiatedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
    field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell).codRestrict
      (highAngularSubmodule parameters angular cell 1)
      (actualDifferentiatedPhysicalBoundary_high parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell)

theorem actualPhysicalBoundaryPR_derivative
    (input : SevenSlotTrace parameters angular cell) :
    IsAngularDerivative parameters angular cell
      (highBoundaryPrimitiveTrace parameters angular cell
        (actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input))
      (actualDifferentiatedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) :=
  highBoundaryPrimitive_derivative parameters angular cell _

theorem actualPhysicalBoundaryPR_trace
    (input : SevenSlotTrace parameters angular cell) :
    highBoundaryPrimitiveTrace parameters angular cell
      (actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input) =
      actualExtendedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input := by
  unfold highBoundaryPrimitiveTrace actualPhysicalBoundaryPR actualExtendedPhysicalBoundary
    actualDifferentiatedPhysicalBoundary fullSevenSlotKernelAction
  rw [actualExtendedPhysicalBoundaryKernel, fullNegativeKernelAction_comp]
  rfl

/-- AH22 in the actual P_R norm on the seven trace inputs. The later
one-high evaluation bounds this concrete kernel moment uniformly. -/
theorem actualPhysicalBoundaryPR_bound
    (input : SevenSlotTrace parameters angular cell) :
    ‖actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
        (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall) * ‖input‖ :=
  actualDifferentiatedPhysicalBoundary_bound parameters L rho alpha delta parameter epsilon compact
    field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input

end Grad.ActualBoundaryPrimitives
