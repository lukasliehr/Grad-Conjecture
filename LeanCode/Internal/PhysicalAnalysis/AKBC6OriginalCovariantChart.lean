import AKBC5ActualEncodedTraceCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (angular cell : ℕ)

def originalCovariantEncoded (field rotated twice : NegativeTrace parameters angular cell 3)
    (scalarTwice : NegativeTrace parameters angular cell 1) : NegativeTrace parameters angular cell 3 :=
  originalTraceVector parameters angular cell
    (forceMeanTrace parameters angular cell (forceCoordinateTrace parameters angular cell 0 field))
    (forceCoordinateTrace parameters angular cell 1 twice-scalarTwice)
    (forceCoordinateTrace parameters angular cell 2 rotated)

def originalCovariantFreeChart (rotated : NegativeTrace parameters angular cell 3)
    (scalar : NegativeTrace parameters angular cell 1) : NegativeTrace parameters angular cell 3 :=
  originalTraceVector parameters angular cell
    (fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1)
      (forceCoordinateTrace parameters angular cell 0 rotated)) scalar 0

def originalCovariantUngauged (field : NegativeTrace parameters angular cell 3) : NegativeTrace parameters angular cell 3 :=
  originalTraceVector parameters angular cell (forceCoordinateTrace parameters angular cell 0 field)
    (forceMeanFreeTrace parameters angular cell (forceCoordinateTrace parameters angular cell 1 field))
    (forceMeanFreeTrace parameters angular cell (forceCoordinateTrace parameters angular cell 2 field))

theorem originalCovariantEncoded_support (field rotated twice : NegativeTrace parameters angular cell 3)
    (scalarRotated scalarTwice : NegativeTrace parameters angular cell 1)
    (rotation : IsAngularDerivative parameters angular cell field rotated)
    (second : IsAngularDerivative parameters angular cell rotated twice)
    (scalarSecond : IsAngularDerivative parameters angular cell scalarRotated scalarTwice) :
    EncodedSupport parameters angular cell (originalCovariantEncoded parameters angular cell field rotated twice scalarTwice) := by
  constructor
  · intro mode nonzero
    rw [originalCovariantEncoded,originalTraceVector_coefficient]
    change negativeTraceCoefficient parameters angular cell
      (forceMeanTrace parameters angular cell (forceCoordinateTrace parameters angular cell 0 field)) mode 0=0
    exact congrArg (fun value : ComplexEuclidean 1 => value 0)
      (angularMeanKernel_action_constant parameters angular cell (forceCoordinateTrace parameters angular cell 0 field) mode nonzero)
  constructor
  · intro axial
    rw [originalCovariantEncoded,originalTraceVector_coefficient]
    change negativeTraceCoefficient parameters angular cell
      (forceCoordinateTrace parameters angular cell 1 twice-scalarTwice) (0,axial) 0=0
    have zero := ((second.constantMatrix (matrixUnit 0 (1 : Fin 3))).sub scalarSecond).meanFree axial
    exact congrArg (fun value : ComplexEuclidean 1 => value 0) zero
  · intro axial
    rw [originalCovariantEncoded,originalTraceVector_coefficient]
    change negativeTraceCoefficient parameters angular cell
      (forceCoordinateTrace parameters angular cell 2 rotated) (0,axial) 0=0
    exact congrArg (fun value : ComplexEuclidean 1 => value 0)
      ((rotation.constantMatrix (matrixUnit 0 (2 : Fin 3))).meanFree axial)

/-- The actual smooth covariant's encoded coordinates decode to its literal
three components, with precisely the two angular tail means removed. -/
theorem originalCovariantEncoded_decodes (field rotated twice : NegativeTrace parameters angular cell 3)
    (scalar scalarRotated scalarTwice : NegativeTrace parameters angular cell 1)
    (rotation : IsAngularDerivative parameters angular cell field rotated)
    (second : IsAngularDerivative parameters angular cell rotated twice)
    (scalarRotation : IsAngularDerivative parameters angular cell scalar scalarRotated)
    (scalarSecond : IsAngularDerivative parameters angular cell scalarRotated scalarTwice)
    (scalarMean : IsAngularMeanFree parameters angular cell scalar) :
    fullNegativeKernelAction parameters angular cell (encodedJKernel parameters)
      (originalCovariantEncoded parameters angular cell field rotated twice scalarTwice)+
      originalCovariantFreeChart parameters angular cell rotated scalar =
        originalCovariantUngauged parameters angular cell field := by
  apply (forceVector_eq_iff parameters angular cell _ _).mpr
  have coordinate (index : Fin 3) : IsAngularDerivative parameters angular cell
      (forceCoordinateTrace parameters angular cell index field)
      (forceCoordinateTrace parameters angular cell index rotated) :=
    rotation.constantMatrix (matrixUnit (0 : Fin 1) index)
  have coordinateSecond (index : Fin 3) : IsAngularDerivative parameters angular cell
      (forceCoordinateTrace parameters angular cell index rotated)
      (forceCoordinateTrace parameters angular cell index twice) :=
    second.constantMatrix (matrixUnit (0 : Fin 1) index)
  constructor
  · simp only [map_add,originalEncodedJ_coordinates,originalCovariantEncoded,originalTraceVector_coordinate,
      originalCovariantFreeChart,originalCovariantUngauged,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change forceMeanTrace parameters angular cell (forceMeanTrace parameters angular cell (forceCoordinateTrace parameters angular cell 0 field))+
      fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1) (forceCoordinateTrace parameters angular cell 0 rotated)=_
    rw [angularMean_action_constant_eq parameters angular cell _ (angularMeanKernel_action_constant _ _ _ _),
      originalTracePrimitive_rotation (coordinate 0),add_comm]
    exact originalTrace_meanFree_add_mean _
  constructor
  · simp only [map_add,originalEncodedJ_coordinates,originalCovariantEncoded,originalTraceVector_coordinate,
      originalCovariantFreeChart,originalCovariantUngauged,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change fullNegativeKernelAction parameters angular cell (angularDoubleInverseKernel parameters 1)
      (forceCoordinateTrace parameters angular cell 1 twice-scalarTwice)+scalar=_
    rw [map_sub,originalTraceDoublePrimitive_second (coordinate 1) (coordinateSecond 1),
      originalTraceDoublePrimitive_second scalarRotation scalarSecond,
      angularMeanFreeKernel_action_eq parameters angular cell scalar scalarMean,sub_add_cancel]
  · simp only [map_add,originalEncodedJ_coordinates,originalCovariantEncoded,originalTraceVector_coordinate,
      originalCovariantFreeChart,originalCovariantUngauged,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1)
      (forceCoordinateTrace parameters angular cell 2 rotated)+0=_
    rw [add_zero]
    exact originalTracePrimitive_rotation (coordinate 2)

end Grad.OriginalKernelCovariantRecovery
