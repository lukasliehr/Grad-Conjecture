import AKBC27SameActualCartesianCircle
import AKAJ4ExactCartesianPhysicalForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualForceMatrixFidelity

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RadialCoefficientState parameters length compact) (lower : ℝ) (positive : 0<lower)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ))

/-- The literal full force convolution acts on the exact original negative
trace. No finite-cell truncation or changed analytic width is introduced. -/
theorem originalForceNegative_product (kind : Fin 2) (mode : ℤ×ℤ) :
    negativeTraceCoefficient _ 0 0
      (fullNegativeKernelAction (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (radialForceKernel parameters length compact state (tupleRadius lower positive radius) kind 0)
        (originalCurveNegativeTrace curves radius)) mode=
      doubleCoefficient
        (forceMatrixProduct parameters length state.data.epsilon state.data.field kind radius.val
          (positive.le.trans radius.property.1) radius.property.2
          (fun angles => curves.fullField bounded (radius.val,angles))) mode := by
  have action := fullNegativeKernelAction_coefficient_hasSum
    (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
    (radialForceKernel parameters length compact state (tupleRadius lower positive radius) kind 0)
    (originalCurveNegativeTrace curves radius) mode
  have product := forceMatrixProduct_hasSum parameters length state.data.rho state.data.epsilon state.data.field state.low kind
    radius.val (positive.le.trans radius.property.1) radius.property.2
    (fun angles => curves.fullField bounded (radius.val,angles))
    (curves.fullField_continuous_angles bounded radius.val radius.property) mode
  apply action.unique
  apply product.congr_fun
  intro shift
  rw [originalCurveNegativeTrace_coefficient curves bounded radius]
  rfl

end Grad.OriginalKernelCovariantRecovery
