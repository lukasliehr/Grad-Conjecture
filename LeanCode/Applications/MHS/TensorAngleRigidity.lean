import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace Grad.MainAssembly.TensorAngleRigidity

open Matrix

/-- The literal normalized inverse pressure Hessian tensor from G20. -/
def normalizedShape (rho angle : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column =>
    if row = 0 then
      if column = 0 then
        1 / 2 + rho / 2 * Real.cos (2 * angle)
      else rho / 2 * Real.sin (2 * angle)
    else if column = 0 then
      rho / 2 * Real.sin (2 * angle)
    else 1 / 2 - rho / 2 * Real.cos (2 * angle)

/-- The moving-normal-frame action induced by the normal sign. -/
def normalSignMatrix (normalSign : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column =>
    if row = 0 then
      if column = 0 then 1 else 0
    else if column = 0 then 0 else normalSign

private theorem two_angle_period {first second : ℝ} (integer : ℤ)
    (difference : second - first = (integer : ℝ) * Real.pi) :
    2 * second = 2 * first + (integer : ℝ) * (2 * Real.pi) := by
  nlinarith

/-- Exact first half of `NG_R06`: equality of the literal positive-eccentricity
tensors is equivalent to angle difference in `pi * Z`. -/
theorem normalizedShape_eq_iff_piLattice (rho first second : ℝ)
    (rhoPositive : 0 < rho) :
    normalizedShape rho second = normalizedShape rho first ↔
      ∃ integer : ℤ, second - first = (integer : ℝ) * Real.pi := by
  constructor
  · intro tensorEquality
    have cosineEquality := congrFun (congrFun tensorEquality 0) 0
    have sineEquality := congrFun (congrFun tensorEquality 0) 1
    norm_num [normalizedShape] at cosineEquality sineEquality
    have cosEq : Real.cos (2 * second) = Real.cos (2 * first) := by
      exact cosineEquality.resolve_right rhoPositive.ne'
    have sinEq : Real.sin (2 * second) = Real.sin (2 * first) := by
      exact sineEquality.resolve_right rhoPositive.ne'
    have cosineDifference : Real.cos (2 * (second - first)) = 1 := by
      rw [show 2 * (second - first) = 2 * second - 2 * first by ring,
        Real.cos_sub, cosEq, sinEq]
      simpa only [pow_two] using Real.cos_sq_add_sin_sq (2 * first)
    rcases (Real.cos_eq_one_iff (2 * (second - first))).mp
        cosineDifference with ⟨integer, periodEquality⟩
    refine ⟨integer, ?_⟩
    nlinarith
  · rintro ⟨integer, difference⟩
    have period := two_angle_period integer difference
    have cosinePeriod : Real.cos (2 * second) = Real.cos (2 * first) := by
      rw [period, Real.cos_add_int_mul_two_pi]
    have sinePeriod : Real.sin (2 * second) = Real.sin (2 * first) := by
      rw [period, Real.sin_add_int_mul_two_pi]
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [normalizedShape, cosinePeriod, sinePeriod]

/-- Exact signed normal-frame covariance in `NG_R06`. -/
theorem normalSign_conjugation (rho angle normalSign : ℝ)
    (normalSignValue : normalSign = 1 ∨ normalSign = -1) :
    normalSignMatrix normalSign * normalizedShape rho angle *
        (normalSignMatrix normalSign)ᵀ =
      normalizedShape rho (normalSign * angle) := by
  rcases normalSignValue with rfl | rfl
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalSignMatrix, normalizedShape, Matrix.mul_apply,
        Fin.sum_univ_succ]
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalSignMatrix, normalizedShape, Matrix.mul_apply,
        Fin.sum_univ_succ, Real.cos_neg, Real.sin_neg]

end Grad.MainAssembly.TensorAngleRigidity
