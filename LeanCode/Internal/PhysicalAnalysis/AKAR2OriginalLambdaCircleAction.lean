import AKAR1OriginalLambdaPhaseRatio

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients

variable {input output : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernel : RadialKernel parameters radius input output)

def lambdaCircleShiftEntry (shift mode : ℤ × ℤ) : ComplexEuclidean input →L[ℂ] ComplexEuclidean output :=
  (lambdaPhaseRatio parameters radius.val shift mode : ℂ) • kernel.entry shift (twoFrequencyTranslation shift mode)

def lambdaCircleMajorant (shift : ℤ × ℤ) : ℝ :=
  2 * (boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift *
    annularFrequency shift.1 shift.2 * kernel.entryNorm shift)

theorem lambdaCircleMajorant_nonnegative (shift : ℤ × ℤ) :
    0 ≤ lambdaCircleMajorant parameters radius kernel shift :=
  mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _)
    (annularFrequency_pos shift).le) (fullKernelEntryNorm_nonnegative kernel shift))

theorem lambdaCircleShiftEntry_bound (shift mode : ℤ × ℤ) :
    ‖lambdaCircleShiftEntry parameters radius kernel shift mode‖ ≤ lambdaCircleMajorant parameters radius kernel shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real,Real.norm_of_nonneg (lambdaPhaseRatio_positive parameters radius.val shift mode).le]
  have combined := mul_le_mul (lambdaPhaseRatio_bound parameters radius shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode)) (norm_nonneg _)
    (by positivity [boundaryCoefficientPhaseCost_nonnegative (radialKernelParameters parameters radius) shift,
      (annularFrequency_pos shift).le])
  exact combined.trans_eq (by unfold lambdaCircleMajorant; ring)

def lambdaCircleShiftAction (shift : ℤ × ℤ) : CellL2 input →L[ℂ] CellL2 output :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (lambdaCircleShiftEntry parameters radius kernel shift)
    (lambdaCircleMajorant_nonnegative parameters radius kernel shift)
    (lambdaCircleShiftEntry_bound parameters radius kernel shift)

theorem lambdaCircleShiftAction_norm (shift : ℤ × ℤ) :
    ‖lambdaCircleShiftAction parameters radius kernel shift‖ ≤ lambdaCircleMajorant parameters radius kernel shift :=
  coefficientOperator_norm_le _ _ _ _ _ _

theorem lambdaCircleMajorant_summable : Summable (lambdaCircleMajorant parameters radius kernel) := by
  unfold lambdaCircleMajorant
  simpa only [pow_one] using (kernel.moments 1).mul_left 2

theorem lambdaCircleShiftAction_summable : Summable (lambdaCircleShiftAction parameters radius kernel) :=
  (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lambdaCircleShiftAction_norm parameters radius kernel)
    (lambdaCircleMajorant_summable parameters radius kernel)).of_norm

/-- Original W lambda weighted circle coordinates, with the same literal
full-cell convolution and no angular Sobolev assumption on the input. -/
def lambdaCircleAction : CellL2 input →L[ℂ] CellL2 output :=
  ∑' shift, lambdaCircleShiftAction parameters radius kernel shift

theorem lambdaCircleAction_norm : ‖lambdaCircleAction parameters radius kernel‖ ≤
    2 * fullKernelMoment (radialKernelParameters parameters radius) 1 kernel := by
  have normSummable := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lambdaCircleShiftAction_norm parameters radius kernel) (lambdaCircleMajorant_summable parameters radius kernel)
  apply (norm_tsum_le_tsum_norm normSummable).trans
  apply (normSummable.tsum_le_tsum (lambdaCircleShiftAction_norm parameters radius kernel)
    (lambdaCircleMajorant_summable parameters radius kernel)).trans_eq
  simp only [lambdaCircleMajorant,fullKernelMoment,pow_one,tsum_mul_left]

theorem lambdaCircleAction_bound (field : CellL2 input) :
    ‖lambdaCircleAction parameters radius kernel field‖ ≤
      (2 * fullKernelMoment (radialKernelParameters parameters radius) 1 kernel) * ‖field‖ :=
  (lambdaCircleAction parameters radius kernel).le_of_opNorm_le (lambdaCircleAction_norm parameters radius kernel) field

theorem lambdaCircleAction_coefficient (field : CellL2 input) (mode : ℤ × ℤ) :
    HasSum (fun shift => (lambdaPhaseRatio parameters radius.val shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)))
      (lambdaCircleAction parameters radius kernel field mode) := by
  have applied := (operatorEvaluation parameters 0 field).hasSum
    (lambdaCircleShiftAction_summable parameters radius kernel).hasSum
  exact (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean output) 2 mode).hasSum applied

end Grad.OriginalKernelRetainedDecay
