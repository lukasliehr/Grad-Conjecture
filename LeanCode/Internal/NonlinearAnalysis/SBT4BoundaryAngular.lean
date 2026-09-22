import SBT3TangentialCore

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem boundaryInverseFrequency_bound (mode : ℤ × ℤ) :
    ‖(annularFrequency mode.1 mode.2 : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (annularFrequency_pos mode).le]
  apply inv_le_one_of_one_le₀
  unfold annularFrequency
  linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]

theorem boundaryAngularRatio_bound (mode : ℤ × ℤ) :
    ‖(Complex.I * (mode.1 : ℂ)) / (annularFrequency mode.1 mode.2 : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (annularFrequency_pos mode).le]
  have castNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by norm_cast
  rw [castNorm, div_le_one (annularFrequency_pos mode)]
  unfold annularFrequency
  linarith [abs_nonneg (mode.2 : ℝ)]

def boundaryLower {dimension : ℕ} : SourceBoundary dimension →L[ℂ] SourceBoundary dimension :=
  sequenceMultiplier (fun mode => (annularFrequency mode.1 mode.2 : ℂ)⁻¹) 1 zero_le_one boundaryInverseFrequency_bound

def boundaryAngular {dimension : ℕ} : SourceBoundary dimension →L[ℂ] SourceBoundary dimension :=
  sequenceMultiplier (fun mode => (Complex.I * (mode.1 : ℂ)) / (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one boundaryAngularRatio_bound

theorem boundaryLower_bound {dimension : ℕ} (field : SourceBoundary dimension) :
    ‖boundaryLower field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one boundaryInverseFrequency_bound field‖ ≤ _
  exact (sequenceMultiplierValue_bound _ 1 zero_le_one boundaryInverseFrequency_bound field).trans_eq (one_mul _)

theorem boundaryAngular_bound {dimension : ℕ} (field : SourceBoundary dimension) :
    ‖boundaryAngular field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one boundaryAngularRatio_bound field‖ ≤ _
  exact (sequenceMultiplierValue_bound _ 1 zero_le_one boundaryAngularRatio_bound field).trans_eq (one_mul _)

theorem boundaryLower_coefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundary dimension) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power (boundaryLower field) mode =
      sourceBoundaryCoefficient parameters (power + 1) field mode := by
  change (sourceBoundaryWeight parameters power mode : ℂ)⁻¹ •
    ((annularFrequency mode.1 mode.2 : ℂ)⁻¹ • field mode) =
      (sourceBoundaryWeight parameters (power + 1) mode : ℂ)⁻¹ • field mode
  rw [smul_smul]
  congr 1
  simp only [sourceBoundaryWeight, pow_succ, Complex.ofReal_mul, mul_inv]
  ring

theorem boundaryAngular_coefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundary dimension) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power (boundaryAngular field) mode =
      (Complex.I * (mode.1 : ℂ)) • sourceBoundaryCoefficient parameters (power + 1) field mode := by
  change (sourceBoundaryWeight parameters power mode : ℂ)⁻¹ •
    (((Complex.I * (mode.1 : ℂ)) / (annularFrequency mode.1 mode.2 : ℂ)) • field mode) =
      (Complex.I * (mode.1 : ℂ)) • ((sourceBoundaryWeight parameters (power + 1) mode : ℂ)⁻¹ • field mode)
  rw [smul_smul, smul_smul]
  congr 1
  simp only [sourceBoundaryWeight, pow_succ, Complex.ofReal_mul, mul_inv, div_eq_mul_inv]
  ring

theorem sourceBoundaryCoefficient_smul {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (scalar : ℂ) (field : SourceBoundary dimension) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power (scalar • field) mode =
      scalar • sourceBoundaryCoefficient parameters power field mode := by
  change (sourceBoundaryWeight parameters power mode : ℂ)⁻¹ • (scalar • field mode) =
    scalar • ((sourceBoundaryWeight parameters power mode : ℂ)⁻¹ • field mode)
  exact smul_comm _ _ _

end Grad.SourceBoundaryTrace
