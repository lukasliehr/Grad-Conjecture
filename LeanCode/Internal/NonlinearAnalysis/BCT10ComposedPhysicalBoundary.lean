import BCT9HighBoundaryProjection
import BKB48ActualCovariantAction

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- One fixed original B7 ball for reconstruction and the actual physical
boundary covector. It does not depend on any running trace grade. -/
def physicalBoundaryLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (actualMassInverseLowRadius parameters L compact)
    (boundaryCoefficientLowRadius parameters L compact)

theorem physicalBoundaryLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < physicalBoundaryLowRadius parameters L compact :=
  lt_min (actualMassInverseLowRadius_positive parameters L compact)
    (boundaryCoefficientLowRadius_positive parameters L compact)

section ActualState

variable (parameters : PhaseParameters)
  (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
  (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
  (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)

include small in
theorem physicalBoundary_reconstruction_small :
    physicalBudget parameters field rho epsilon 7 ≤ actualMassInverseLowRadius parameters L compact :=
  small.trans (min_le_left _ _)

include small in
theorem physicalBoundary_coefficient_small :
    physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact :=
  (physicalBudget_monotone parameters field rho epsilon (by omega : 6 ≤ 7)).trans
    (small.trans (min_le_right _ _))

/-- AH21's undifferentiated high physical row on the complete seven-slot
trace input. Its agreement with the genuine derivative is proved after the
physical reconstruction support and product-rule bridge. -/
def actualHighPhysicalBoundaryKernel : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelComposition
      (actualBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall
        (physicalBoundary_coefficient_small parameters L rho epsilon compact field small))
      (actualCovariantKernel parameters L rho alpha delta parameter epsilon compact field
        (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
        compactNonnegative alphaSmall deltaSmall parameterSmall))

/-- The differentiated AH21 row, built from the actual physical covector
and the exact reconstruction kernels. All its moments are finite at the
original analytic width. -/
def actualDifferentiatedPhysicalBoundaryKernel : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelAdd
      (fullKernelComposition
        (actualRotatedBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
          compactNonnegative alphaSmall deltaSmall parameterSmall
          (physicalBoundary_coefficient_small parameters L rho epsilon compact field small))
        (actualCovariantKernel parameters L rho alpha delta parameter epsilon compact field
          (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
          compactNonnegative alphaSmall deltaSmall parameterSmall))
      (fullKernelComposition
        (actualBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
          compactNonnegative alphaSmall deltaSmall parameterSmall
          (physicalBoundary_coefficient_small parameters L rho epsilon compact field small))
        (actualRotatedCovariantKernel parameters L rho alpha delta parameter epsilon compact field
          (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
          compactNonnegative alphaSmall deltaSmall parameterSmall)))

/-- AH8's canonical nonsmooth extension: apply K to the bounded
differentiated high output. -/
def actualExtendedPhysicalBoundaryKernel : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (angularInverseKernel parameters 1)
    (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

def actualDifferentiatedPhysicalBoundary (angular cell : ℕ) :
    SevenSlotTrace parameters angular cell →L[ℂ] NegativeTrace parameters angular cell 1 :=
  fullSevenSlotKernelAction parameters angular cell
    (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

def actualExtendedPhysicalBoundary (angular cell : ℕ) :
    SevenSlotTrace parameters angular cell →L[ℂ] NegativeTrace parameters angular cell 1 :=
  fullSevenSlotKernelAction parameters angular cell
    (actualExtendedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

theorem actualDifferentiatedPhysicalBoundary_bound (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) :
    ‖actualDifferentiatedPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
        (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall) * ‖input‖ :=
  fullSevenSlotKernelAction_bound parameters angular cell _ input

end ActualState
end Grad.ActualBoundaryPrimitives
