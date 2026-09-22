import AKBC3ActualSmoothNegativeTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction

variable {dimension : ℕ} {parameters : PhaseParameters} {angular cell : ℕ}

/-- Exact primitive of a genuine derivative, retaining its original mean. -/
theorem originalTracePrimitive_rotation {field rotated : NegativeTrace parameters angular cell dimension}
    (rotation : IsAngularDerivative parameters angular cell field rotated) :
    fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters dimension) rotated =
      fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters dimension) field :=
  rotation.meanFreeProjection.primitive (angularMeanFreeKernel_action_meanFree parameters angular cell field)

theorem originalTraceDoublePrimitive_twice (field : NegativeTrace parameters angular cell dimension) :
    fullNegativeKernelAction parameters angular cell (angularDoubleInverseKernel parameters dimension) field =
      fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters dimension)
        (fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters dimension) field) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularDoubleInverseKernel,angularInverseKernel,scalarModeDiagonalKernel_action_coefficient,
    angularDoubleInverseMultiplier,mul_smul]

theorem originalTraceDoublePrimitive_second {field rotated twice : NegativeTrace parameters angular cell dimension}
    (rotation : IsAngularDerivative parameters angular cell field rotated)
    (second : IsAngularDerivative parameters angular cell rotated twice) :
    fullNegativeKernelAction parameters angular cell (angularDoubleInverseKernel parameters dimension) twice =
      fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters dimension) field := by
  rw [originalTraceDoublePrimitive_twice,second.primitive rotation.meanFree]
  exact originalTracePrimitive_rotation rotation

theorem originalTrace_meanFree_add_mean (field : NegativeTrace parameters angular cell dimension) :
    fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters dimension) field+
      fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters dimension) field=field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [negativeTraceCoefficient_add,angularMeanFreeKernel,angularMeanKernel,scalarModeDiagonalKernel_action_coefficient]
  by_cases zero : mode.1=0 <;> simp [angularMeanFreeMultiplier,angularMeanMultiplier,zero]

end Grad.OriginalKernelCovariantRecovery
