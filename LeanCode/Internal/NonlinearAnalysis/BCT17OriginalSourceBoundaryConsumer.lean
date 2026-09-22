import BCT16MeanFreePrimitiveInput

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.RealFixedRanges

variable (parameters : PhaseParameters)
  (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
  (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
  (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
  (angular cell : ℕ) (large : 3 ≤ angular + cell + 2)

/-- The physical high boundary on the original prescribed source space,
the whole mean-free P_R input, and the literal positive-half retained trace. -/
def physicalBoundaryFromPrescribedSource
    (p : MeanFreeBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    HighBoundaryPrimitive parameters angular cell :=
  actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact
    field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell
    (actualSevenSlotTrace parameters L angular cell p.val xi source.val)

theorem physicalBoundaryFromPrescribedSource_eq_high
    (p : MeanFreeBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    highBoundaryPrimitiveTrace parameters angular cell
      (physicalBoundaryFromPrescribedSource parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell large p xi source) =
      actualHighPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell
        (actualSevenSlotTrace parameters L angular cell p.val xi source.val) := by
  apply actualPhysicalBoundaryPR_eq_high
  · exact p.property
  · exact positiveToNegative_derivative parameters angular cell xi

/-- Literal AH21 consumer: the actual original AD19 covector acts on the
actual reconstructed current, followed by the unchanged high-mode projector. -/
theorem physicalBoundaryFromPrescribedSource_eq_covector
    (p : MeanFreeBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    highBoundaryPrimitiveTrace parameters angular cell
      (physicalBoundaryFromPrescribedSource parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell large p xi source) =
      fullNegativeKernelAction parameters angular cell (highAngularKernel parameters 1)
        (fullNegativeKernelAction parameters angular cell
          (actualBoundaryMultiplier parameters L rho alpha delta parameter epsilon compact field
            compactNonnegative alphaSmall deltaSmall parameterSmall
            (physicalBoundary_coefficient_small parameters L rho epsilon compact field small))
          (actualPhysicalCovariantTrace parameters L rho alpha delta parameter epsilon compact field
            (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
            compactNonnegative alphaSmall deltaSmall parameterSmall angular cell p.val xi source.val)) := by
  rw [physicalBoundaryFromPrescribedSource_eq_high]
  unfold actualHighPhysicalBoundary actualHighPhysicalBoundaryKernel
    actualPhysicalCovariantTrace actualCovariantReconstruction fullSevenSlotKernelAction
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]

/-- The completed physical boundary satisfies the source-trace estimate
with its concrete kernel moment and the exact original source norm. -/
theorem physicalBoundaryFromPrescribedSource_bound_sq (positive : 0 < L)
    (p : MeanFreeBoundaryPrimitive parameters angular cell)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    ‖physicalBoundaryFromPrescribedSource parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell large p xi source‖ ^ 2 ≤
      fullKernelMoment parameters (angular + cell + 1)
        (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall) ^ 2 *
        (‖p‖ ^ 2 + 3 * ‖xi‖ ^ 2 +
          sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source.val‖ ^ 2) := by
  have boundaryBound := pow_le_pow_left₀ (norm_nonneg _)
    (actualPhysicalBoundaryPR_bound parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell
      (actualSevenSlotTrace parameters L angular cell p.val xi source.val)) 2
  rw [mul_pow] at boundaryBound
  exact boundaryBound.trans (mul_le_mul_of_nonneg_left
    (actualSevenSlotTrace_bound_sq parameters L positive angular cell p.val xi source.val) (sq_nonneg _))

end Grad.ActualBoundaryPrimitives
