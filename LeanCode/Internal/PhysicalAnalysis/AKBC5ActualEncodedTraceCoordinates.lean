import AKBC4ExactAngularPrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (angular cell : ℕ)

def originalTraceVector (first second third : NegativeTrace parameters angular cell 1) :
    NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell (firstCoordinateInjectionKernel parameters) first+
    fullNegativeKernelAction parameters angular cell (secondCoordinateInjectionKernel parameters) second+
    fullNegativeKernelAction parameters angular cell (thirdCoordinateInjectionKernel parameters) third

theorem originalTraceVector_coefficient (first second third : NegativeTrace parameters angular cell 1)
    (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (originalTraceVector parameters angular cell first second third) mode =
      WithLp.toLp 2 ![negativeTraceCoefficient parameters angular cell first mode 0,
        negativeTraceCoefficient parameters angular cell second mode 0,
        negativeTraceCoefficient parameters angular cell third mode 0] := by
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [originalTraceVector,negativeTraceCoefficient_add,
    firstCoordinateInjectionKernel,secondCoordinateInjectionKernel,thirdCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient]

theorem originalTraceVector_coordinate (first second third : NegativeTrace parameters angular cell 1) (coordinate : Fin 3) :
    forceCoordinateTrace parameters angular cell coordinate (originalTraceVector parameters angular cell first second third) =
      ![first,second,third] coordinate := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have only := Fin.eq_zero component
  subst component
  simp only [forceCoordinateTrace,coordinateProjectionKernel_action_coefficient,originalTraceVector_coefficient]
  fin_cases coordinate <;> rfl

theorem originalTraceVector_reconstruct (field : NegativeTrace parameters angular cell 3) :
    originalTraceVector parameters angular cell (forceCoordinateTrace parameters angular cell 0 field)
      (forceCoordinateTrace parameters angular cell 1 field) (forceCoordinateTrace parameters angular cell 2 field) = field := by
  apply (forceVector_eq_iff parameters angular cell _ _).mpr
  constructor
  · exact originalTraceVector_coordinate parameters angular cell _ _ _ 0
  constructor
  · exact originalTraceVector_coordinate parameters angular cell _ _ _ 1
  · exact originalTraceVector_coordinate parameters angular cell _ _ _ 2

theorem originalEncodedJ_coordinates (field : NegativeTrace parameters angular cell 3) (coordinate : Fin 3) :
    forceCoordinateTrace parameters angular cell coordinate
      (fullNegativeKernelAction parameters angular cell (encodedJKernel parameters) field) =
      ![forceMeanTrace parameters angular cell (forceCoordinateTrace parameters angular cell 0 field),
        fullNegativeKernelAction parameters angular cell (angularDoubleInverseKernel parameters 1)
          (forceCoordinateTrace parameters angular cell 1 field),
        fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1)
          (forceCoordinateTrace parameters angular cell 2 field)] coordinate := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro component
  have only := Fin.eq_zero component
  subst component
  fin_cases coordinate <;>
    simp [forceCoordinateTrace,forceMeanTrace,coordinateProjectionKernel_action_coefficient,
      encodedJKernel,fullNegativeKernelAction_add,negativeTraceCoefficient_add,
      angularMeanComponentKernel,angularDoubleInverseComponentKernel,angularInverseComponentKernel,
      componentModeKernel_action_coefficient,angularMeanKernel,angularDoubleInverseKernel,angularInverseKernel,
      scalarModeDiagonalKernel_action_coefficient]

end Grad.OriginalKernelCovariantRecovery
