import AKBC24OriginalAxialFrameColumn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularSmoothCore Grad.AnnularPhysicalReconstruction Grad.BoundaryKernelAction
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelGraphRestriction Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Ledger

def OriginalNegativeCircle {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (negative : NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension)
    (circle : CellL2 dimension) : Prop :=
  ∀ mode,negativeTraceCoefficient _ 0 0 negative mode=lambdaCircleCoefficient parameters radius.val circle mode

theorem OriginalNegativeCircle.unique {dimension : ℕ} {parameters : PhaseParameters} {radius : RadialPoint}
    {first second : NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension}
    {circle : CellL2 dimension} (one : OriginalNegativeCircle parameters radius first circle)
    (two : OriginalNegativeCircle parameters radius second circle) : first=second := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  exact (one mode).trans (two mode).symm

theorem OriginalNegativeCircle.derivative {dimension : ℕ} {parameters : PhaseParameters} {radius : RadialPoint}
    {field rotated : NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension}
    {circle circleR : CellL2 dimension} (one : OriginalNegativeCircle parameters radius field circle)
    (two : OriginalNegativeCircle parameters radius rotated circleR)
    (rotation : OriginalCircleRotation circle circleR) : IsAngularDerivative _ 0 0 field rotated := by
  intro mode
  rw [one mode,two mode]
  change (_ : ℂ) • circleR mode=(_ : ℂ) • ((_ : ℂ) • circle mode)
  rw [rotation,smul_comm]

theorem OriginalNegativeCircle.rotation {dimension : ℕ} {parameters : PhaseParameters} {radius : RadialPoint}
    {field rotated : NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension}
    {circle circleR : CellL2 dimension} (one : OriginalNegativeCircle parameters radius field circle)
    (derivative : IsAngularDerivative _ 0 0 field rotated)
    (rotation : OriginalCircleRotation circle circleR) : OriginalNegativeCircle parameters radius rotated circleR := by
  intro mode
  rw [derivative mode,one mode]
  change (_ : ℂ) • ((_ : ℂ) • circle mode)=(_ : ℂ) • circleR mode
  rw [rotation,smul_comm]

theorem originalCurveNegative_circle {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ)) (circle : CellL2 dimension)
    (represented : OriginalCircleRepresents parameters (tupleRadius lower positive radius) circle
      (fun angles => curves.fullField bounded (radius.val,angles))) :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius) (originalCurveNegativeTrace curves radius) circle := by
  intro mode
  exact (originalCurveNegativeTrace_coefficient curves bounded radius mode).trans (represented mode).symm

theorem originalCoreNegative_circle {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (field : ACore parameters dimension)
    (radius : Icc lower (1 : ℝ))
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (same : ∀ angles,curves.fullField bounded (radius.val,angles)=
      originalCoreCircle parameters field (tupleRadius lower positive radius) angles) :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (originalCurveNegativeTrace curves radius) (originalCoreCircleTrace parameters field (tupleRadius lower positive radius)) := by
  apply originalCurveNegative_circle curves bounded radius
  have equality := funext same
  rw [equality]
  exact originalCoreCircleTrace_represents parameters field _

theorem originalCurveNegative_coordinate_coefficient {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ)) (coordinate : Fin 3) (mode : ℤ×ℤ) :
    negativeTraceCoefficient _ 0 0
      (forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 coordinate
        (originalCurveNegativeTrace curves radius)) mode=
      doubleCoefficient (fun angles => matrixUnit (0 : Fin 1) coordinate (curves.fullField bounded (radius.val,angles))) mode := by
  rw [doubleCoefficient_valueMap _ _ (curves.fullField_continuous_angles bounded radius.val radius.property)]
  change negativeTraceCoefficient _ 0 0
    (fullNegativeKernelAction _ 0 0 (coordinateProjectionKernel _ 3 coordinate) (originalCurveNegativeTrace curves radius)) mode=_
  rw [coordinateProjectionKernel,constantMatrixKernel_action_coefficient,originalCurveNegativeTrace_coefficient curves bounded radius]

end Grad.OriginalKernelCovariantRecovery
