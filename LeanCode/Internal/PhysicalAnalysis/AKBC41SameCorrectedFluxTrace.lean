import AKBC40SameLiteralCofactorFlux
import AKAO32LiteralSameCorrectedP

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularPhysicalReconstruction
open Grad.ActualPolarFlux Grad.OriginalKernelGraphRestriction Grad.ActualPolarEquations

theorem originalCurveNegativeTrace_inverseRadius {parameters : PhaseParameters} (lower : ℝ) (positive : 0<lower)
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalInverseRadiusCurves lower positive curves) radius=
      (radius.val : ℂ)⁻¹ • originalCurveNegativeTrace curves radius := by
  exact map_smul (bulkNegativeLift parameters (tupleRadius lower positive radius) 1) (radius.val : ℂ)⁻¹ _

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (state : RetainedInverseState parameters length compact)
    {vectorRow : DivisionRow 3 lower} (vector : SmoothLowPhysicalRow parameters lower positive vectorRow)
    {xiRow : DivisionRow 1 lower} (xi : SmoothLowPhysicalRow parameters lower positive xiRow)

def originalSignedFluxCurves :=
  ((vector.signedCofactorRow parameters length compact lower positive bounded state 0).add
    ((originalInverseRadiusCurves lower positive xi).signedCofactorComponent parameters length compact lower positive bounded state 0 1)).meanFree

theorem originalSignedFluxCurves_negative (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalSignedFluxCurves parameters length compact lower positive bounded state vector xi) radius=
      radialCorrectedFluxTrace parameters length compact state.val.val (tupleRadius lower positive radius) 0 0
        (originalCurveNegativeTrace vector radius) ((radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius) := by
  rw [originalSignedFluxCurves,originalCurveNegativeTrace_meanFree,originalCurveNegativeTrace_add]
  unfold SmoothLowPhysicalRow.signedCofactorRow SmoothLowPhysicalRow.signedCofactorComponent
  rw [originalCurveNegativeTrace_action,originalCurveNegativeTrace_action,
    originalCurveNegativeTrace_inverseRadius lower positive xi radius]
  rw [radialCorrectedFluxTrace,originalSigma_cofactorRow parameters length compact state,
    originalSigma_cofactorComponent parameters length compact state]
  simp only [radialSignedCofactorRowKernel,fullNegativeKernelAction_add,fullNegativeKernelAction_neg,forceMeanFreeTrace]

end Grad.OriginalKernelCovariantRecovery
