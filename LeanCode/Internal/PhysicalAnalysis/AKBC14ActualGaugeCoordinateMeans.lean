import AKBC13ActualGaugeFourierProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

theorem originalGaugeRows_coordinate (field : NegativeTrace (rp parameters r) angular cell 3)
    (kind : Fin 2) :
    fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 2 kind)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeRowsKernel parameters L compact state r 0) field)=
    fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeKernel parameters L compact state r kind 0) field := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  rw [coordinateProjectionKernel,constantMatrixKernel_action_coefficient]
  have rows := (matrixUnit (0 : Fin 1) kind).hasSum
    (fullNegativeKernelAction_coefficient_hasSum (rp parameters r) angular cell
      (radialGaugeRowsKernel parameters L compact state r 0) field mode)
  have single := fullNegativeKernelAction_coefficient_hasSum (rp parameters r) angular cell
    (radialGaugeKernel parameters L compact state r kind 0) field mode
  apply rows.unique
  apply single.congr_fun
  intro shift
  simp only [radialGaugeRowsKernel,radialMatrixKernel,boundaryMatrixMultiplicationKernel_entry_apply,
    radialGaugeKernel,radialRowKernel,boundaryRowMultiplicationKernel_entry_apply]
  apply PiLp.ext
  intro index
  fin_cases index
  fin_cases kind <;> simp [matrixUnit_apply,operatorBasis]

theorem originalGaugeMeans_coordinate (field : NegativeTrace (rp parameters r) angular cell 3)
    (kind : Fin 2) :
    fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 2 kind)
      (radialPhysicalGaugeMeans parameters L compact state r angular cell field)=
    forceMeanTrace (rp parameters r) angular cell
      (forceCoordinateTrace (rp parameters r) angular cell (if kind=0 then 1 else 2) field+
       fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeKernel parameters L compact state r kind 0) field) := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  simp only [radialPhysicalGaugeMeans,radialGaugeMeanRowsKernel,fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply,map_add,negativeTraceCoefficient_add,
    coordinateProjectionKernel,constantMatrixKernel_action_coefficient,angularMeanKernel,forceMeanTrace,
    scalarModeDiagonalKernel_action_coefficient,map_smul]
  have row := congrArg (fun trace => negativeTraceCoefficient (rp parameters r) angular cell trace mode)
    (originalGaugeRows_coordinate parameters L compact state r angular cell field kind)
  rw [coordinateProjectionKernel,constantMatrixKernel_action_coefficient] at row
  rw [row]
  simp only [gaugeTailProjectionKernel,constantMatrixKernel_action_coefficient]
  congr 1
  apply PiLp.ext
  intro index
  fin_cases index
  fin_cases kind <;>
    simp [gaugeTailProjectionMap,matrixUnit_apply,operatorBasis,forceCoordinateTrace,
      coordinateProjectionKernel_action_coefficient]

end Grad.OriginalKernelCovariantRecovery
