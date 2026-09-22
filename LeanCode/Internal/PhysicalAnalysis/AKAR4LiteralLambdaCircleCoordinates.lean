import AKAR2OriginalLambdaCircleAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients

def lambdaCircleWeight (parameters : PhaseParameters) (radius : ℝ) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (radialPhase parameters radius mode.2) * cellFrequency mode.2

theorem lambdaCircleWeight_positive (parameters : PhaseParameters) (radius : ℝ) (mode : ℤ × ℤ) :
    0 < lambdaCircleWeight parameters radius mode := mul_pos (Real.exp_pos _) (cellFrequency_pos _)

theorem lambdaPhaseRatio_original (parameters : PhaseParameters) (radius : ℝ) (shift mode : ℤ × ℤ) :
    lambdaPhaseRatio parameters radius shift mode = lambdaCircleWeight parameters radius mode /
      lambdaCircleWeight parameters radius (twoFrequencyTranslation shift mode) := by
  simp only [lambdaPhaseRatio,lambdaShiftRatio,bulkWeightRatio,pow_zero,mul_one,div_one,lambdaCircleWeight,Real.exp_sub]
  ring

def lambdaCircleCoefficient {dimension : ℕ} (parameters : PhaseParameters) (radius : ℝ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((lambdaCircleWeight parameters radius mode : ℂ)⁻¹) • field mode

theorem lambdaCircle_weighted {dimension : ℕ} (parameters : PhaseParameters) (radius : ℝ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    (lambdaCircleWeight parameters radius mode : ℂ) • lambdaCircleCoefficient parameters radius field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (lambdaCircleWeight_positive parameters radius mode).ne') _

/-- Exact norm is the double Fourier realization of L2(theta;ell2_lambda),
with the original W at the same radius. -/
theorem lambdaCircle_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (radius : ℝ) (field : CellL2 dimension) :
    ‖field‖^2 = ∑' mode : ℤ × ℤ,
      Real.exp (2 * radialPhase parameters radius mode.2) * cellFrequency mode.2^2 *
        ‖lambdaCircleCoefficient parameters radius field mode‖^2 := by
  have law := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at law
  rw [law]
  apply tsum_congr
  intro mode
  rw [← lambdaCircle_weighted parameters radius field mode,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (lambdaCircleWeight_positive parameters radius mode).le,mul_pow]
  rw [lambdaCircleWeight,mul_pow,← Real.exp_nat_mul]
  congr 2

theorem lambdaCircleAction_original_coefficient {input output : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernel : RadialKernel parameters radius input output) (field : CellL2 input) (mode : ℤ × ℤ) :
    HasSum (fun shift => kernel.entry shift (twoFrequencyTranslation shift mode)
      (lambdaCircleCoefficient parameters radius.val field (twoFrequencyTranslation shift mode)))
      (lambdaCircleCoefficient parameters radius.val (lambdaCircleAction parameters radius kernel field) mode) := by
  let scale : ComplexEuclidean output →L[ℂ] ComplexEuclidean output :=
    ((lambdaCircleWeight parameters radius.val mode : ℂ)⁻¹) • ContinuousLinearMap.id ℂ _
  have law := scale.hasSum (lambdaCircleAction_coefficient parameters radius kernel field mode)
  convert law using 1
  · funext shift
    change kernel.entry shift (twoFrequencyTranslation shift mode) (_ • _) =
      ((lambdaCircleWeight parameters radius.val mode : ℂ)⁻¹) •
        ((lambdaPhaseRatio parameters radius.val shift mode : ℂ) • _)
    rw [map_smul,smul_smul]
    congr 1
    rw [lambdaPhaseRatio_original]
    push_cast
    field_simp [(lambdaCircleWeight_positive parameters radius.val mode).ne',
      (lambdaCircleWeight_positive parameters radius.val (twoFrequencyTranslation shift mode)).ne']
  · rfl

end Grad.OriginalKernelRetainedDecay
