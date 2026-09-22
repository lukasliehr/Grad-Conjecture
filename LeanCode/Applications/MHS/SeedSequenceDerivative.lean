import SeedWeightedCoordinates

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.Constraints.Seed

open Grad.CartesianState Grad.GaugeCoefficients.Algebra

def derivativeRatio (cell : ℤ) : ℂ := Complex.I * (cell : ℂ) / (cellPolynomialWeight cell : ℂ)

theorem derivativeRatio_norm_le (cell : ℤ) : ‖derivativeRatio cell‖ ≤ 1 := by
  have positive : 0 < cellPolynomialWeight cell := by rw [cellPolynomialWeight_formula]; positivity
  unfold derivativeRatio
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Complex.norm_real,
    Real.norm_of_nonneg positive.le]
  apply (div_le_one positive).mpr
  rw [cellPolynomialWeight_formula]
  linarith

def sequenceDerivative (sequence : WeightedSequence) : WeightedSequence := by
  refine ⟨fun cell => derivativeRatio cell • sequence cell, ?_⟩
  apply memℓp_gen
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  have original : Summable (fun cell => ‖sequence cell‖) := by
    simpa only [oneToReal, Real.rpow_one] using
      (lp.memℓp sequence).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have summable : Summable (fun cell => ‖derivativeRatio cell • sequence cell‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun cell => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (derivativeRatio_norm_le cell) (norm_nonneg _)).trans_eq (one_mul _)) original
  simpa only [oneToReal, Real.rpow_one] using summable

def sequenceDerivativeLinear : WeightedSequence →ₗ[ℂ] WeightedSequence where
  toFun := sequenceDerivative
  map_add' first second := by
    apply lp.ext
    funext cell
    exact smul_add (derivativeRatio cell) (first cell) (second cell)
  map_smul' scalar value := by
    apply lp.ext
    funext cell
    exact smul_comm (derivativeRatio cell) scalar (value cell)

def sequenceDerivativeCLM : WeightedSequence →L[ℂ] WeightedSequence :=
  sequenceDerivativeLinear.mkContinuous 1 (fun sequence => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num)
    intro cell
    change ‖derivativeRatio cell • sequence cell‖ ≤ ‖sequence cell‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (derivativeRatio_norm_le cell) (norm_nonneg _)).trans_eq (one_mul _))

theorem sequenceDerivativeCLM_apply (sequence : WeightedSequence) (cell : ℤ) :
    sequenceDerivativeCLM sequence cell = derivativeRatio cell • sequence cell := rfl

theorem sequenceDerivative_weight (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) (value : OperatorValue 2 2) :
    derivativeRatio cell • ((sequenceWeight phase (grade + 1) cell : ℂ) • value) =
      (sequenceWeight phase grade cell : ℂ) • ((Complex.I * (cell : ℂ)) • value) := by
  rw [smul_smul, smul_smul]
  congr 1
  have nonzero : (cellPolynomialWeight cell : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have positive : 0 < cellPolynomialWeight cell := by rw [cellPolynomialWeight_formula]; positivity
    exact positive.ne'
  unfold derivativeRatio sequenceWeight
  push_cast
  rw [pow_succ]
  field_simp

end Grad.Constraints.Seed
