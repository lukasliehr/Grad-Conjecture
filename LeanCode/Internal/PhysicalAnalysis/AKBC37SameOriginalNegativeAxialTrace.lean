import AKBC36ActualAxialCovariantCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.SourceCollarFullSource
open Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.PhaseAlgebra
open Grad.AnnularWeightedSmoothness
open Grad.AnnularPhysicalReconstruction Grad.AnnularSmoothCore

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ))

def originalCurveNegativeAxial : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 dimension :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) dimension
    (hilbertFrequencyOperator parameters dimension (some true) (curves.curve 1 radius.val))

include bounded

theorem originalCurveNegativeAxial_coefficient (mode : ℤ×ℤ) :
    negativeTraceCoefficient _ 0 0 (originalCurveNegativeAxial curves radius) mode=
      (Complex.I*(mode.2 : ℂ)) • negativeTraceCoefficient _ 0 0 (originalCurveNegativeTrace curves radius) mode := by
  rw [originalCurveNegativeAxial,originalCurveNegativeTrace,bulkNegativeLift_coefficient,bulkNegativeLift_coefficient,
    hilbertFrequencyOperator_apply]
  have shift := curves.shift bounded 0 1 radius.val radius.property mode
  norm_num only [zero_add,pow_one] at shift
  rw [shift,originalFrequencyRatio_cancel]
  exact smul_comm _ _ _

theorem originalCoreNegative_axial (field : ACore parameters dimension)
    (represented : OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (originalCurveNegativeTrace curves radius) (originalCoreCircleTrace parameters field (tupleRadius lower positive radius))) :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (originalCurveNegativeAxial curves radius)
      (originalCoreCircleTrace parameters (timeDerivativeCore parameters field) (tupleRadius lower positive radius)) := by
  intro mode
  rw [originalCurveNegativeAxial_coefficient curves bounded radius,represented mode,
    originalCoreCircleTrace_time_coefficient]

end Grad.OriginalKernelCovariantRecovery
