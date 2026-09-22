import AKBL12NativeGaugePhysicalCellMeans
import AKBF14SameNativeXiMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualSmoothPhysicalField Grad.AnnularOriginalSmoothCore Grad.ActualPhysicalField
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness
open Grad.AnnularCurrentEnergy

 theorem startupNative_coordinate_trace {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (radius : Icc lower (1 : ℝ)) (coordinate : Fin dimension) :
    fullNegativeKernelAction (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (coordinateProjectionKernel _ dimension coordinate) (originalCurveNegativeTrace curves radius) =
        originalCurveNegativeTrace (curves.bulkUnit (0 : Fin 1) coordinate) radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [coordinateProjectionKernel,constantMatrixKernel_action_coefficient,
    originalCurveNegativeTrace_coefficient curves bounded radius,
    originalCurveNegativeTrace_coefficient (curves.bulkUnit (0 : Fin 1) coordinate) bounded radius]
  simp_rw [curves.fullField_bulkUnit bounded (0 : Fin 1) coordinate radius.val radius.property]
  exact (doubleCoefficient_valueMap (matrixUnit (0 : Fin 1) coordinate)
    (fun angles => curves.fullField bounded (radius.val,angles))
    (curves.fullField_continuous_angles bounded radius.val radius.property) mode).symm

 theorem startupNative_zeroMean_of_row {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (zero : ∀ cell : ℤ, row (0,cell) = 0) (radius : Icc lower (1 : ℝ)) :
    IsAngularMeanFree (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (originalCurveNegativeTrace curves radius) := by
  intro cell
  rw [originalCurveNegativeTrace_coefficient curves bounded radius,doubleCoefficient,
    doubleCoefficient_swap _ (curves.fullField_continuous_angles bounded radius.val radius.property)]
  simp_rw [fullField_mean_of_zeroAngular curves bounded zero radius.val radius.property]
  exact angularCoefficient_zero cell

 def startupNativeSevenSlots (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 7) : SevenSlotTrace parameters angular cell :=
  WithLp.toLp 2 (fun coordinate : Fin 7 => fullNegativeKernelAction parameters angular cell
    (coordinateProjectionKernel parameters 7 coordinate) field)

 theorem startupNativeSevenSlots_flatten (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 7) :
    sevenSlotFlatten parameters angular cell (startupNativeSevenSlots parameters angular cell field) = field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  rw [sevenSlotFlatten_coefficient]
  change negativeTraceCoefficient parameters angular cell
    (fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 7 coordinate) field) mode 0 = _
  rw [coordinateProjectionKernel_action_coefficient]

/-- Both actual native gauge means of the SAME covariant curves follow
from the stored original Xi/r row, using only its genuine zero angular mode.
The original Gamma kernel, radius and seven-row input are unchanged. -/
 theorem startupNative_covariantCurve_gauged (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : AnnularReconstructionState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (zero : ∀ cell : ℤ, bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7) row (0,cell) = 0)
    (radius : Icc lower (1 : ℝ)) :
    radialPhysicalGaugeMeans parameters length compact state.val (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace (curves.covariant parameters length compact lower positive bounded state) radius) = 0 := by
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (fun current => radialNormalizedCovariantKernel parameters length compact state.val current state.property)
    (radialNormalizedCovariantKernel_regular parameters length compact state)
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded) curves radius
  change originalCurveNegativeTrace (curves.covariant parameters length compact lower positive bounded state) radius = _ at action
  rw [action]
  let field := originalCurveNegativeTrace curves radius
  let input := startupNativeSevenSlots (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 field
  have flattened := startupNativeSevenSlots_flatten (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 field
  have supported : IsAngularMeanFree (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 (input 3) := by
    change IsAngularMeanFree _ 0 0 (fullNegativeKernelAction _ 0 0
      (coordinateProjectionKernel _ 7 (3 : Fin 7)) (originalCurveNegativeTrace curves radius))
    rw [startupNative_coordinate_trace curves bounded radius]
    exact startupNative_zeroMean_of_row (curves.bulkUnit (0 : Fin 1) (3 : Fin 7)) bounded zero radius
  have gauged := startupNative_normalizedCovariant_gauged parameters length compact state.val
    (tupleRadius lower positive radius) state.property 0 0 input supported
  rw [flattened] at gauged
  exact gauged

end Grad.CartesianStartup
