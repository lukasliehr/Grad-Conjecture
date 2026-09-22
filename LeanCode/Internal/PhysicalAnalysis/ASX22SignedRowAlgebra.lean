import ASX19OriginalSmoothModes

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse

private theorem positive_force {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficient : ℂ) (nonzero : coefficient ≠ 0) (derivative : E →ₗ[ℂ] E) (potential source : E) :
    (-coefficient) • derivative (coefficient⁻¹ • potential) -
      (2 * coefficient) • ((2 * coefficient)⁻¹ • (derivative potential - source) - derivative (coefficient⁻¹ • potential)) = source := by
  rw [map_smul]
  have first : coefficient • (coefficient⁻¹ • derivative potential) = derivative potential := by
    rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  have second : (2 * coefficient) • ((2 * coefficient)⁻¹ • (derivative potential - source)) = derivative potential - source := by
    rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero (by norm_num) nonzero), one_smul]
  calc
    _ = coefficient • (coefficient⁻¹ • derivative potential) -
        (2 * coefficient) • ((2 * coefficient)⁻¹ • (derivative potential - source)) := by module
    _ = source := by rw [first, second]; abel

theorem exceptionalPositiveForce_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (derivative : E →ₗ[ℂ] E) (potential source : E) :
    (-2 * Complex.I * (sign : ℂ)) • derivative ((2 * Complex.I * (sign : ℂ))⁻¹ • potential) -
      (Complex.I * ((2 * sign + 2 * sign : ℤ) : ℂ)) •
        ((4 * Complex.I * (sign : ℂ))⁻¹ • (derivative potential - source) -
          derivative ((2 * Complex.I * (sign : ℂ))⁻¹ • potential)) = source := by
  have first : -2 * Complex.I * (sign : ℂ) = -(2 * Complex.I * (sign : ℂ)) := by ring
  have second : Complex.I * ((2 * sign + 2 * sign : ℤ) : ℂ) = 2 * (2 * Complex.I * (sign : ℂ)) := by push_cast; ring
  have third : 4 * Complex.I * (sign : ℂ) = 2 * (2 * Complex.I * (sign : ℂ)) := by ring
  rw [first, second, third]
  exact positive_force _ (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (signedCast_nonzero sign signed)) derivative potential source

theorem exceptionalNegativeForce_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (derivative : E →ₗ[ℂ] E) (potential field : E) :
    (-2 * Complex.I * ((-sign : ℤ) : ℂ)) • derivative ((2 * Complex.I * (sign : ℂ))⁻¹ • potential) -
      (Complex.I * ((2 * sign + 2 * -sign : ℤ) : ℂ)) • field = derivative potential := by
  have first : -2 * Complex.I * ((-sign : ℤ) : ℂ) = 2 * Complex.I * (sign : ℂ) := by push_cast; ring
  have second : Complex.I * ((2 * sign + 2 * -sign : ℤ) : ℂ) = 0 := by push_cast; ring
  rw [first, second, zero_smul, sub_zero, map_smul, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (signedCast_nonzero sign signed)), one_smul]

theorem exceptionalThird_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (rotation : E →ₗ[ℂ] E) (source : E)
    (equation : rotation source = (Complex.I * ((2 * sign : ℤ) : ℂ)) • source) :
    rotation ((2 * Complex.I * (sign : ℂ))⁻¹ • source) = source := by
  have coefficient : Complex.I * ((2 * sign : ℤ) : ℂ) = 2 * Complex.I * (sign : ℂ) := by push_cast; ring
  rw [map_smul, equation, coefficient, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (signedCast_nonzero sign signed)), one_smul]

end Grad.ActualExceptionalInverse
