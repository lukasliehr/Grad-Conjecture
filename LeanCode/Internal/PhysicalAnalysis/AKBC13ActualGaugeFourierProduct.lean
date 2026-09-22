import AKBC12OriginalDomainGaugeMeans
import AKAO4LiteralPolarMatrixProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularSmoothCore Grad.AnnularPhysicalReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualGaugeSigmaPrimitives Grad.ActualPolarFlux

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (lower : ℝ) (positive : 0<lower)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ))

/-- Original-width multiplication by each literal gauge row, on the same
physical Fourier trace; all integer axial cells are retained. -/
theorem originalGaugeNegative_product (kind : Fin 2) (mode : ℤ × ℤ) :
    negativeTraceCoefficient _ 0 0
      (fullNegativeKernelAction (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (radialGaugeKernel parameters L compact state (tupleRadius lower positive radius) kind 0)
        (originalCurveNegativeTrace curves radius)) mode =
      doubleCoefficient
        (polarFamilyRowProduct parameters
          (originalGaugeDeviation parameters L state.data.rho state.data.alpha state.data.delta
            state.data.parameter state.data.epsilon state.data.field)
          (if kind=0 then 1 else 2) radius.val (positive.le.trans radius.property.1) radius.property.2
          (fun angles => curves.fullField bounded (radius.val,angles))) mode := by
  have action := fullNegativeKernelAction_coefficient_hasSum
    (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
    (radialGaugeKernel parameters L compact state (tupleRadius lower positive radius) kind 0)
    (originalCurveNegativeTrace curves radius) mode
  have product := polarFamilyRowProduct_hasSum parameters
    (originalGaugeDeviation parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field)
    (originalGaugeDeviation_coherent parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low)
    (if kind=0 then 1 else 2) radius.val (positive.le.trans radius.property.1) radius.property.2
    (fun angles => curves.fullField bounded (radius.val,angles))
    (curves.fullField_continuous_angles bounded radius.val radius.property) mode
  apply action.unique
  apply product.congr_fun
  intro shift
  rw [originalCurveNegativeTrace_coefficient curves bounded radius]
  rfl

end Grad.OriginalKernelCovariantRecovery
