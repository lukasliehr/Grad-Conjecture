import AKBR4SameFullOuterSevenCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource

open Grad.ActualPolarFlux Grad.ActualSmoothPhysicalField Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarFullSource Grad.ActualGaugeSigmaPrimitives Grad.OriginalKernelCovariantRecovery
variable (parameters : PhaseParameters) (length compact : ℝ) (state : PhysicalBoundaryState parameters length compact)

def originalBoundaryProduct (source : ℝ×ℝ→ComplexEuclidean 3) : ℝ×ℝ→ComplexEuclidean 1 :=
  polarFamilyRowProduct parameters
    (paddedBoundaryFamily parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon state.val.field)
    2 1 zero_le_one le_rfl source

/-- The actual BCT boundary multiplier acts on the SAME original physical
Fourier field, with all axial cells and the original boundary weights. -/
theorem originalBoundaryMultiplier_coefficient (input : NegativeTrace parameters 0 0 3)
    (source : ℝ×ℝ→ComplexEuclidean 3) (continuousSource : Continuous source)
    (represented : ∀ mode,negativeTraceCoefficient parameters 0 0 input mode=doubleCoefficient source mode) (mode : ℤ×ℤ) :
    negativeTraceCoefficient parameters 0 0
      (fullNegativeKernelAction parameters 0 0
        (actualBoundaryMultiplier parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon compact state.val.field
          state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall) input) mode=
      doubleCoefficient (originalBoundaryProduct parameters length compact state source) mode := by
  have action := fullNegativeKernelAction_coefficient_hasSum parameters 0 0
    (actualBoundaryMultiplier parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon compact state.val.field
      state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall) input mode
  have product := polarFamilyRowProduct_hasSum parameters
    (paddedBoundaryFamily parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon state.val.field)
    (paddedBoundaryFamily_estimate parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon compact state.val.field
      state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall).actualCoherent
    2 1 zero_le_one le_rfl source continuousSource mode
  apply action.unique
  apply product.congr_fun
  intro shift
  rw [represented]
  rfl

/-- Literal AD19 boundary covector, with its physical seed inverse and
algebraic transpose, before the outer high-angular projection. -/
theorem originalBoundaryProduct_value (source : ℝ×ℝ→ComplexEuclidean 3) (angles : ℝ×ℝ) :
    originalBoundaryProduct parameters length compact state source angles 0=
      ∑ component : Fin 3, originalBoundaryRow parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter
        state.val.epsilon state.val.field angles.2 angles.1
        (Grad.SourceCollarDivision.polarClosedPoint 1 angles.1 zero_le_one le_rfl) component*source angles component := by
  simp only [originalBoundaryProduct,polarFamilyRowProduct,polarFamilyAngleEntry,
    paddedBoundaryFamily_polarEntry parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter state.val.epsilon compact
      state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall]
  simp [matrixUnit_apply,operatorBasis]

end Grad.OriginalKernelOuterUniqueness
