import AKBL4SameNativeCovariantGauge
import AKBC39SameNegativeCurveActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualSmoothPhysicalField Grad.AnnularOriginalSmoothCore

/-- The actual native gauge means imply the literal physical gauge row's
zero polar coefficient in every axial cell. This is the needed converse of
the original-domain adapter, without an ACore or H1 premise. -/
theorem startupNative_gaugePhysicalCell_mean (parameters : PhaseParameters) (length compact : ℝ)
    (state : RadialCoefficientState parameters length compact) (lower : ℝ) (positive : 0 < lower)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : Icc lower (1 : ℝ))
    (gauged : radialPhysicalGaugeMeans parameters length compact state (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace curves radius) = 0) (kind : Fin 2) (cell : ℤ) :
    doubleCoefficient (originalTotalGaugeProduct parameters length compact state (tupleRadius lower positive radius) kind
      (fun angles => curves.fullField bounded (radius.val,angles))) (0,cell) = 0 := by
  have coordinate := originalGaugeMeans_coordinate parameters length compact state (tupleRadius lower positive radius) 0 0
    (originalCurveNegativeTrace curves radius) kind
  rw [gauged,map_zero] at coordinate
  have value := congrArg (fun trace : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 1 =>
    negativeTraceCoefficient _ 0 0 trace (0,cell)) coordinate
  simp only [forceMeanTrace,angularMeanKernel,scalarModeDiagonalKernel_action_coefficient,
    angularMeanMultiplier,ite_true,one_smul] at value
  rw [originalTotalGaugeTrace_coefficient parameters length compact state kind lower positive curves bounded radius] at value
  exact value.symm.trans ((negativeTraceCoefficientCLM _ 0 0 (0,cell)).map_zero)

/-- The same assertion in the literal nested Fourier form consumed by the
Cartesian rough gauge projector; no axial coefficient leaves a product. -/
theorem startupNative_gaugePhysicalCell_angularMean (parameters : PhaseParameters) (length compact : ℝ)
    (state : RadialCoefficientState parameters length compact) (lower : ℝ) (positive : 0 < lower)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : Icc lower (1 : ℝ))
    (gauged : radialPhysicalGaugeMeans parameters length compact state (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace curves radius) = 0) (kind : Fin 2) (cell : ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial =>
      originalTotalGaugeProduct parameters length compact state (tupleRadius lower positive radius) kind
        (fun angles => curves.fullField bounded (radius.val,angles)) (polar,axial)) cell) 0 = 0 :=
  startupNative_gaugePhysicalCell_mean parameters length compact state lower positive curves bounded radius gauged kind cell

end Grad.CartesianStartup
