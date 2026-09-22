import TRM4GraphShift

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

/-- Multiplication by `cos θ`, expressed by the two literal unit character shifts. -/
def annularCosine {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((2 : ℂ)⁻¹) •
    ((annularGraphShift lower positive power (1 : ℤ) :
        annularDerivativeGraph dimension lower positive radial →L[ℂ]
          annularDerivativeGraph dimension lower positive radial) +
      annularGraphShift lower positive power (-1 : ℤ))

/-- Multiplication by `sin θ`, expressed by the two literal unit character shifts. -/
def annularSine {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((2 * Complex.I : ℂ)⁻¹) •
    ((annularGraphShift lower positive power (1 : ℤ) :
        annularDerivativeGraph dimension lower positive radial →L[ℂ]
          annularDerivativeGraph dimension lower positive radial) -
      annularGraphShift lower positive power (-1 : ℤ))

theorem annularCosine_value {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularCosine lower positive power field =
      (2 : ℂ)⁻¹ • (annularGraphShift lower positive power (1 : ℤ) field +
        annularGraphShift lower positive power (-1 : ℤ) field) := rfl

theorem annularSine_value {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularSine lower positive power field =
      (2 * Complex.I : ℂ)⁻¹ •
        (annularGraphShift lower positive power (1 : ℤ) field -
          annularGraphShift lower positive power (-1 : ℤ) field) := rfl

@[simp] theorem annularCosine_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularCosine lower positive power field).val index mode =
      (2 : ℂ)⁻¹ •
        (annularShiftScalar power 1 mode • field.val index (mode.1 - 1, mode.2) +
          annularShiftScalar power (-1) mode • field.val index (mode.1 - (-1), mode.2)) := by
  rfl

@[simp] theorem annularSine_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularSine lower positive power field).val index mode =
      (2 * Complex.I : ℂ)⁻¹ •
        (annularShiftScalar power 1 mode • field.val index (mode.1 - 1, mode.2) -
          annularShiftScalar power (-1) mode • field.val index (mode.1 + 1, mode.2)) := by
  rfl

theorem annularCosine_apply_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularCosine lower positive power field‖ ≤ (2 : ℝ) ^ power * ‖field‖ := by
  have plus : ‖annularGraphShift lower positive power (1 : ℤ) field‖ ≤
      (2 : ℝ) ^ power * ‖field‖ := by
    simpa only [Int.cast_one, abs_one, one_add_one_eq_two] using
      annularGraphShift_apply_norm_le lower positive power (1 : ℤ) field
  have minus : ‖annularGraphShift lower positive power (-1 : ℤ) field‖ ≤
      (2 : ℝ) ^ power * ‖field‖ := by
    simpa only [Int.cast_neg, Int.cast_one, abs_neg, abs_one, one_add_one_eq_two] using
      annularGraphShift_apply_norm_le lower positive power (-1 : ℤ) field
  rw [annularCosine_value, norm_smul]
  have scalarNorm : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [scalarNorm]
  calc
    (2 : ℝ)⁻¹ * ‖annularGraphShift lower positive power (1 : ℤ) field +
        annularGraphShift lower positive power (-1 : ℤ) field‖
      ≤ (2 : ℝ)⁻¹ *
          (‖annularGraphShift lower positive power (1 : ℤ) field‖ +
            ‖annularGraphShift lower positive power (-1 : ℤ) field‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ *
          (2 * ((2 : ℝ) ^ power * ‖field‖)) := by
        gcongr
        linarith
    _ = (2 : ℝ) ^ power * ‖field‖ := by ring

theorem annularSine_apply_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularSine lower positive power field‖ ≤ (2 : ℝ) ^ power * ‖field‖ := by
  have plus : ‖annularGraphShift lower positive power (1 : ℤ) field‖ ≤
      (2 : ℝ) ^ power * ‖field‖ := by
    simpa only [Int.cast_one, abs_one, one_add_one_eq_two] using
      annularGraphShift_apply_norm_le lower positive power (1 : ℤ) field
  have minus : ‖annularGraphShift lower positive power (-1 : ℤ) field‖ ≤
      (2 : ℝ) ^ power * ‖field‖ := by
    simpa only [Int.cast_neg, Int.cast_one, abs_neg, abs_one, one_add_one_eq_two] using
      annularGraphShift_apply_norm_le lower positive power (-1 : ℤ) field
  rw [annularSine_value, norm_smul]
  have scalarNorm : ‖(2 * Complex.I : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_two, Complex.norm_I]
    norm_num
  rw [scalarNorm]
  calc
    (2 : ℝ)⁻¹ * ‖annularGraphShift lower positive power (1 : ℤ) field -
        annularGraphShift lower positive power (-1 : ℤ) field‖
      ≤ (2 : ℝ)⁻¹ *
          (‖annularGraphShift lower positive power (1 : ℤ) field‖ +
            ‖annularGraphShift lower positive power (-1 : ℤ) field‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ *
          (2 * ((2 : ℝ) ^ power * ‖field‖)) := by
        gcongr
        linarith
    _ = (2 : ℝ) ^ power * ‖field‖ := by ring

theorem annularCosine_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) :
    ‖annularCosine (dimension := dimension) (radial := radial) lower positive power‖ ≤
      (2 : ℝ) ^ power := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact annularCosine_apply_norm_le lower positive power

theorem annularSine_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) :
    ‖annularSine (dimension := dimension) (radial := radial) lower positive power‖ ≤
      (2 : ℝ) ^ power := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact annularSine_apply_norm_le lower positive power

end Grad.SourceCollarAngular
