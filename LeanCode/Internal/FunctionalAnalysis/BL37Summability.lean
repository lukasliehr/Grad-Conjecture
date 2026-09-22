import BL36KernelSymmetry
import Mathlib.Analysis.PSeries

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem boundaryPhase_nonneg (parameters : PhaseParameters) (cell : ℤ) :
    0 ≤ boundaryPhase parameters cell := by
  have frequencyPos := cellFrequency_pos cell
  have rootUpper : Real.sqrt (1 + cellFrequency cell ^ 2) ≤ 1 + cellFrequency cell := by
    rw [show (1 + cellFrequency cell) = Real.sqrt ((1 + cellFrequency cell) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have gammaBound : parameters.gamma * (Real.sqrt (1 + cellFrequency cell ^ 2) - 1) ≤
      parameters.gamma * cellFrequency cell :=
    mul_le_mul_of_nonneg_left (by linarith) parameters.gamma_pos.le
  have sigmaBound : parameters.gamma * cellFrequency cell ≤
      parameters.sigma0 * cellFrequency cell :=
    mul_le_mul_of_nonneg_right (parameters_gamma_lt_sigma0 parameters).le frequencyPos.le
  unfold boundaryPhase
  linarith

theorem boundaryPhase_exp_one_le (parameters : PhaseParameters) (cell : ℤ) :
    1 ≤ Real.exp (boundaryPhase parameters cell) := by
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (boundaryPhase parameters cell) :=
      Real.exp_le_exp.mpr (boundaryPhase_nonneg parameters cell)

/-- The grade-three boundary weight dominates the literal factorized
inverse-square majorant. -/
theorem boundaryWeight_grade_three_lower (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    (1 + (mode.1 : ℝ) ^ 2) * (1 + (mode.2 : ℝ) ^ 2) ≤ boundaryWeight parameters 3 mode ^ 2 := by
  have frequencyOne := boundaryFrequency_one_le mode
  have exponentOne := boundaryPhase_exp_one_le parameters mode.2
  have quarticFormula : boundaryFrequency mode ^ 4 = (1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, boundaryFrequency_sq]
  have productLower : (1 + (mode.1 : ℝ) ^ 2) * (1 + (mode.2 : ℝ) ^ 2) ≤ boundaryFrequency mode ^ 4 := by
    rw [quarticFormula]
    nlinarith [sq_nonneg (mode.1 : ℝ), sq_nonneg (mode.2 : ℝ),
      sq_nonneg ((mode.1 : ℝ) * (mode.2 : ℝ)), sq_nonneg ((mode.1 : ℝ) ^ 2 - (mode.2 : ℝ) ^ 2)]
  have powerLower : boundaryFrequency mode ^ 4 ≤ boundaryFrequency mode ^ (2 * 3 - 1) :=
    pow_le_pow_right₀ frequencyOne (by norm_num)
  have exponentSquareOne : 1 ≤ Real.exp (boundaryPhase parameters mode.2) ^ 2 := by
    nlinarith
  unfold boundaryWeight
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (boundaryFrequency_pos mode).le _)]
  calc (1 + (mode.1 : ℝ) ^ 2) * (1 + (mode.2 : ℝ) ^ 2)
      ≤ boundaryFrequency mode ^ (2 * 3 - 1) := productLower.trans powerLower
    _ ≤ Real.exp (boundaryPhase parameters mode.2) ^ 2 * boundaryFrequency mode ^ (2 * 3 - 1) :=
      le_mul_of_one_le_left (by positivity) exponentSquareOne

theorem oneDimensionInverse_summable : Summable (fun cell : ℤ => (1 + (cell : ℝ) ^ 2)⁻¹) := by
  have indicator : Summable (fun cell : ℤ => if cell = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 1).summable
  have power : Summable (fun cell : ℤ => 1 / (cell : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun cell => by positivity) _ (power.add indicator)
  intro cell
  by_cases zero : cell = 0
  · subst zero
    norm_num
  · have castNonzero : (cell : ℝ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have squarePos : (0 : ℝ) < (cell : ℝ) ^ 2 := by positivity
    rw [if_neg zero, add_zero, ← one_div]
    exact one_div_le_one_div_of_le squarePos (by linarith)

theorem boundaryWeight_inverse_sq_summable (parameters : PhaseParameters) :
    Summable (fun mode : ℤ × ℤ => (boundaryWeight parameters 3 mode ^ 2)⁻¹) := by
  have product : Summable (fun mode : ℤ × ℤ =>
      (1 + (mode.1 : ℝ) ^ 2)⁻¹ * (1 + (mode.2 : ℝ) ^ 2)⁻¹) :=
    Summable.mul_of_nonneg oneDimensionInverse_summable oneDimensionInverse_summable
      (fun cell => by positivity) (fun cell => by positivity)
  apply Summable.of_nonneg_of_le (fun mode => by positivity) _ product
  intro mode
  rw [← mul_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (boundaryWeight_grade_three_lower parameters mode)

theorem boundaryCore_weighted_sq_summable {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    Summable (fun mode : ℤ × ℤ =>
      boundaryWeight parameters grade mode ^ 2 * ‖values.1 mode‖ ^ 2) := by
  have member := values.property grade gradePositive
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at member
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at member
  apply member.congr
  intro mode
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (boundaryWeight_pos parameters grade mode), mul_pow]

/-- Literal absolute summability of the original boundary coefficients. -/
theorem boundaryCore_norm_summable {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) :
    Summable (fun mode : ℤ × ℤ => ‖values.1 mode‖) := by
  have majorant : Summable (fun mode : ℤ × ℤ =>
      ((boundaryWeight parameters 3 mode ^ 2)⁻¹ +
        boundaryWeight parameters 3 mode ^ 2 * ‖values.1 mode‖ ^ 2) / 2) :=
    ((boundaryWeight_inverse_sq_summable parameters).add
      (boundaryCore_weighted_sq_summable parameters values 3 (by omega))).div_const 2
  apply Summable.of_nonneg_of_le (fun mode => norm_nonneg _) _ majorant
  intro mode
  have weightPos := boundaryWeight_pos parameters 3 mode
  have identity : (boundaryWeight parameters 3 mode)⁻¹ *
      (boundaryWeight parameters 3 mode * ‖values.1 mode‖) = ‖values.1 mode‖ := by
    rw [← mul_assoc, inv_mul_cancel₀ weightPos.ne', one_mul]
  have inverseSquare : (boundaryWeight parameters 3 mode)⁻¹ ^ 2 =
      (boundaryWeight parameters 3 mode ^ 2)⁻¹ := inv_pow _ _
  have squareExpand : (boundaryWeight parameters 3 mode * ‖values.1 mode‖) ^ 2 =
      boundaryWeight parameters 3 mode ^ 2 * ‖values.1 mode‖ ^ 2 := mul_pow _ _ _
  nlinarith [sq_nonneg ((boundaryWeight parameters 3 mode)⁻¹ -
    boundaryWeight parameters 3 mode * ‖values.1 mode‖), identity, inverseSquare, squareExpand]

theorem boundaryLiftSummand_norm {dimension : ℕ} (values : ℤ × ℤ → ComplexEuclidean dimension)
    (time : ℝ) (angle cellPoint : CellCircle) (mode : ℤ × ℤ) :
    ‖boundaryLiftSummand values time angle cellPoint mode‖ =
      Real.exp (-boundaryFrequency mode * time) * ‖values mode‖ := by
  unfold boundaryLiftSummand
  rw [norm_smul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), boundaryFourier_norm, boundaryFourier_norm, mul_one, mul_one]

/-- The literal N24 double series is absolutely summable at every
nonnegative collar time. -/
theorem boundaryLiftSummand_summable {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (time : ℝ) (timeNonneg : 0 ≤ time)
    (angle cellPoint : CellCircle) :
    Summable (fun mode : ℤ × ℤ => boundaryLiftSummand values.1 time angle cellPoint mode) := by
  apply Summable.of_norm_bounded (boundaryCore_norm_summable parameters values)
  intro mode
  rw [boundaryLiftSummand_norm]
  apply mul_le_of_le_one_left (norm_nonneg _)
  calc Real.exp (-boundaryFrequency mode * time) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        have frequencyPos := boundaryFrequency_pos mode
        nlinarith
    _ = 1 := Real.exp_zero

end Grad.BoundaryLift
