import AJC10CompletedHighPacketAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.AnnularReconstruction
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

theorem completedProjectedFirstRow :
    regularRadialBulkAction parameters 0 lower positive bounded
      (radialNormalizedRetainedFirstRowKernel parameters L compact state.val)
      (radialNormalizedRetainedFirstRowKernel_regular parameters L compact state.val) =
      (highRowProjection lower).comp (lowPhysicalRowAction parameters L compact lower positive bounded state 0) := by
  have composed : regularRadialBulkAction parameters 0 lower positive bounded
      (radialNormalizedRetainedFirstRowKernel parameters L compact state.val)
      (radialNormalizedRetainedFirstRowKernel_regular parameters L compact state.val) =
      (highBulkProjection parameters 0 lower positive bounded 1).comp
        (lowPhysicalRowAction parameters L compact lower positive bounded state 0) :=
    regularRadialBulkAction_comp parameters 0 lower positive bounded
      (fun radius => highAngularKernel (radialKernelParameters parameters radius) 1)
      (radialNormalizedUnprojectedFirstRowKernel parameters L compact state)
      (scalarModeRadialKernel_regular parameters 1 highAngularMultiplier 1 highAngularMultiplier_norm_le)
      (radialNormalizedUnprojectedFirstRowKernel_regular parameters L compact state)
  exact composed.trans (congrArg (fun projection : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower =>
    projection.comp (lowPhysicalRowAction parameters L compact lower positive bounded state 0))
      (completedHighProjection_same parameters 0 lower positive bounded))

/-- The exact retained first-row identity holds on the actual completed L2
inputs, including the independent f slot. -/
theorem completedEliminatedSeven_firstRow (input : DivisionRow 8 lower) :
    highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive bounded state 0
      (eliminatedSevenBulkAction parameters L compact lower positive bounded state 0 input)) +
      highRowProjection lower (bulkMatrixUnit lower (0 : Fin 1) (7 : Fin 8) input) =
    highRowProjection lower (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 8) input) := by
  let high : RegularKernelFamily (fun radius => highAngularKernel (radialKernelParameters parameters radius) 1) := scalarModeRadialKernel_regular parameters 1 highAngularMultiplier 1 highAngularMultiplier_norm_le
  let row := radialNormalizedRetainedFirstRowKernel_regular parameters L compact state.val
  let seven := radialEliminatedSevenKernel_regular parameters L compact state
  let slot0 : RegularKernelFamily (fun radius => eightInputSlotKernel (radialKernelParameters parameters radius) 0) := constantMatrixRadialKernel_regular parameters 8 1 (matrixUnit 0 0)
  let slot7 : RegularKernelFamily (fun radius => eightInputSlotKernel (radialKernelParameters parameters radius) 7) := constantMatrixRadialKernel_regular parameters 8 1 (matrixUnit 0 7)
  have kernelLaw := regularRadialBulkAction_congr parameters 0 lower positive bounded
    (fun radius => fullKernelAdd
      (fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val radius)
        (radialEliminatedSevenKernel parameters L compact state radius))
      (fullKernelComposition (highAngularKernel (radialKernelParameters parameters radius) 1)
        (eightInputSlotKernel (radialKernelParameters parameters radius) 7)))
    ((row.comp seven).add (high.comp slot7))
    (fun radius => fullKernelComposition (highAngularKernel (radialKernelParameters parameters radius) 1)
      (eightInputSlotKernel (radialKernelParameters parameters radius) 0))
    (high.comp slot0) (radialEliminatedSevenKernel_firstRow parameters L compact state)
  rw [regularRadialBulkAction_add parameters 0 lower positive bounded _ _ (row.comp seven) (high.comp slot7),
    regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ row seven,
    regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ high slot7,
    regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ high slot0] at kernelLaw
  have firstRow := completedProjectedFirstRow parameters L compact lower positive bounded state
  have highSame := completedHighProjection_same parameters 0 lower positive bounded
  change regularRadialBulkAction parameters 0 lower positive bounded
    (radialNormalizedRetainedFirstRowKernel parameters L compact state.val) row = _ at firstRow
  rw [firstRow] at kernelLaw
  change (highBulkProjection parameters 0 lower positive bounded 1) = _ at highSame
  change ((highRowProjection lower).comp (lowPhysicalRowAction parameters L compact lower positive bounded state 0)).comp
      (eliminatedSevenBulkAction parameters L compact lower positive bounded state 0) +
      (highBulkProjection parameters 0 lower positive bounded 1).comp
        (regularRadialBulkAction parameters 0 lower positive bounded
          (fun radius => constantMatrixKernel (radialKernelParameters parameters radius) 8 1 (matrixUnit 0 7)) slot7) =
      (highBulkProjection parameters 0 lower positive bounded 1).comp
        (regularRadialBulkAction parameters 0 lower positive bounded
          (fun radius => constantMatrixKernel (radialKernelParameters parameters radius) 8 1 (matrixUnit 0 0)) slot0) at kernelLaw
  rw [highSame, regularMatrixUnit_eq_bulk, regularMatrixUnit_eq_bulk] at kernelLaw
  exact congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower => action input) kernelLaw

end Grad.AnnularStrongSolution
