import AKBM11SameOriginalForceTraceCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.ActualCartesianEquations
open Grad.OriginalKernelCovariantRecovery Grad.AnnularCurrentLow Grad.AnnularOriginalSmoothCore Grad.ActualDeterminantEquations
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

theorem originalCurveNegativeTrace_sub {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {firstRow secondRow : DivisionRow dimension lower}
    (first : SmoothLowPhysicalRow parameters lower positive firstRow)
    (second : SmoothLowPhysicalRow parameters lower positive secondRow) (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace (first.sub second) radius=originalCurveNegativeTrace first radius-originalCurveNegativeTrace second radius :=
  map_sub (Grad.AnnularPhysicalReconstruction.bulkNegativeLift parameters (tupleRadius lower positive radius) dimension) _ _

theorem originalCurveFullField_zero_of_negative {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : Icc lower (1:ℝ)) (zero : originalCurveNegativeTrace curves radius=0) (angles : ℝ×ℝ) :
    curves.fullField bounded (radius.val,angles)=0 := by
  apply congrFun (curves.fullField_eq_of_doubleCoefficient bounded radius.val radius.property (fun _ => 0)
    continuous_const (fun _ _ => rfl) (fun _ _ => rfl) _) angles
  intro mode
  have coefficient := congrArg (fun trace => negativeTraceCoefficient _ 0 0 trace mode) zero
  rw [originalCurveNegativeTrace_coefficient curves bounded radius,
    curves.fullField_doubleCoefficient bounded radius.val radius.property mode] at coefficient
  rw [coefficient]
  simp [doubleCoefficient,negativeTraceCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]

theorem originalCurveNegativeTrace_force {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (length compact : ℝ) (state : AnnularReconstructionState parameters length compact) (kind : Fin 2)
    (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace (physicalForceCurves parameters length compact lower positive bounded state kind curves) radius=
      fullNegativeKernelAction _ 0 0 (radialForceKernel parameters length compact state.val (tupleRadius lower positive radius) kind 0)
        (originalCurveNegativeTrace curves radius) := by
  exact originalCurveNegativeTrace_action parameters lower positive bounded
    (fun radius => radialForceKernel parameters length compact state.val radius kind 0)
    (radialForceKernel_regular parameters length compact state.val kind 0)
    (radialForceKernel_conjugated_smooth parameters length compact state.val lower positive bounded kind 0) curves radius

end Grad.OriginalKernelHomogeneousGraph
