import AKZ3OriginalMatrixRadialKernel
import AKAQ12LiteralOriginalKernelConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra

def lambdaShiftRatio (shift mode : ℤ × ℤ) : ℝ :=
  cellFrequency mode.2 / cellFrequency (twoFrequencyTranslation shift mode).2

theorem lambdaShiftRatio_positive (shift mode : ℤ × ℤ) : 0 < lambdaShiftRatio shift mode :=
  div_pos (cellFrequency_pos _) (cellFrequency_pos _)

theorem lambdaShiftRatio_bound (shift mode : ℤ × ℤ) :
    lambdaShiftRatio shift mode ≤ 2 * annularFrequency shift.1 shift.2 := by
  rw [lambdaShiftRatio,div_le_iff₀ (cellFrequency_pos _)]
  have subadd := cellFrequency_subadditive shift.2 (mode.2-shift.2)
  have same : shift.2 + (mode.2-shift.2) = mode.2 := by omega
  rw [same] at subadd
  have shiftBound := cellFrequency_le_abs_add_one shift.2
  have frequencyOne := cellFrequency_one_le (mode.2-shift.2)
  have extra : 0 ≤ |(shift.1 : ℝ)| := abs_nonneg _
  have multiplication := mul_nonneg (by positivity : 0 ≤ 1 + |(shift.2 : ℝ)|)
    (sub_nonneg.mpr frequencyOne)
  simp only [twoFrequencyTranslation_apply]
  unfold annularFrequency
  nlinarith [mul_nonneg extra (cellFrequency_pos (mode.2-shift.2)).le,
    mul_nonneg (abs_nonneg (shift.2 : ℝ)) (cellFrequency_pos (mode.2-shift.2)).le]

def lambdaPhaseRatio (parameters : PhaseParameters) (radius : ℝ) (shift mode : ℤ × ℤ) : ℝ :=
  bulkWeightRatio parameters 0 radius shift mode * lambdaShiftRatio shift mode

theorem lambdaPhaseRatio_positive (parameters : PhaseParameters) (radius : ℝ) (shift mode : ℤ × ℤ) :
    0 < lambdaPhaseRatio parameters radius shift mode :=
  mul_pos (bulkWeightRatio_pos parameters 0 radius shift mode) (lambdaShiftRatio_positive shift mode)

/-- Exact original W and lambda ratio; no half-order or angular input norm. -/
theorem lambdaPhaseRatio_bound (parameters : PhaseParameters) (radius : RadialPoint) (shift mode : ℤ × ℤ) :
    lambdaPhaseRatio parameters radius.val shift mode ≤
      2 * (boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift * annularFrequency shift.1 shift.2) := by
  have phase : bulkWeightRatio parameters 0 radius.val shift mode ≤
      boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift := by
    simpa only [pow_zero,mul_one] using bulkWeightRatio_le parameters 0 radius shift mode
  have combined := mul_le_mul phase (lambdaShiftRatio_bound shift mode)
    (lambdaShiftRatio_positive shift mode).le (boundaryCoefficientPhaseCost_nonnegative _ _)
  unfold lambdaPhaseRatio
  nlinarith only [combined]

end Grad.OriginalKernelRetainedDecay
