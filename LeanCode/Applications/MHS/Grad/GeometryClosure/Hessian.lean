import Grad.GeometryClosure.Seed

/-! Algebra for G18, conditional on an explicitly given invertible matrix and positive scale.
Nothing here identifies this matrix with the differential-geometric pressure Hessian. -/
noncomputable section
namespace Grad.GeometryClosure
open Matrix

/-- The algebraic formula in (27); use its theorems only with a > 0 and det M a unit. -/
def algebraicNormalHessian (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (-2 / a ^ 2) • ((M⁻¹)ᵀ * M⁻¹)

/-- Trace-normalized inverse of the negative algebraic Hessian.
The domain and positive trace are established in the theorems below. -/
def algebraicNormalizedShape (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((-algebraicNormalHessian a M)⁻¹).trace⁻¹ • (-algebraicNormalHessian a M)⁻¹

theorem neg_algebraicNormalHessian (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    -algebraicNormalHessian a M = (2 / a ^ 2) • ((M⁻¹)ᵀ * M⁻¹) := by
  unfold algebraicNormalHessian
  rw [← neg_smul]
  congr 1
  ring

/-- Both algebraic Gram inverse products, using actual nonsingular matrix inverses. -/
theorem inverse_gram_products (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) :
    ((M⁻¹)ᵀ * M⁻¹) * (M * Mᵀ) = 1 ∧
    (M * Mᵀ) * ((M⁻¹)ᵀ * M⁻¹) = 1 := by
  have hleft := Matrix.nonsing_inv_mul M hM
  have hright := Matrix.mul_nonsing_inv M hM
  constructor
  · calc
      _ = (M⁻¹)ᵀ * (M⁻¹ * M) * Mᵀ := by simp only [Matrix.mul_assoc]
      _ = (M⁻¹)ᵀ * Mᵀ := by rw [hleft, Matrix.mul_one]
      _ = (M * M⁻¹)ᵀ := (Matrix.transpose_mul _ _).symm
      _ = 1 := by rw [hright, Matrix.transpose_one]
  · calc
      _ = M * (Mᵀ * (M⁻¹)ᵀ) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M * (M⁻¹ * M)ᵀ * M⁻¹ := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hleft, Matrix.transpose_one, Matrix.mul_one, hright]

/-- G18 algebra: both inverse products, with positivity supplying the nonzero scale. -/
theorem algebraic_negative_hessian_inverse_products (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) :
    (-algebraicNormalHessian a M) * ((a ^ 2 / 2) • (M * Mᵀ)) = 1 ∧
    ((a ^ 2 / 2) • (M * Mᵀ)) * (-algebraicNormalHessian a M) = 1 := by
  have hs : (2 / a ^ 2) * (a ^ 2 / 2) = 1 := by field_simp
  have hs' : (a ^ 2 / 2) * (2 / a ^ 2) = 1 := by rw [mul_comm]; exact hs
  rw [neg_algebraicNormalHessian]
  constructor
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
      (inverse_gram_products M hM).1, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs',
      (inverse_gram_products M hM).2, one_smul]

/-- G18 algebra: the actual inverse of the negative algebraic Hessian. -/
theorem algebraic_negative_hessian_inverse (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) :
    (-algebraicNormalHessian a M)⁻¹ = (a ^ 2 / 2) • (M * Mᵀ) := by
  exact Matrix.inv_eq_right_inv (algebraic_negative_hessian_inverse_products a ha M hM).1

/-- G18 algebra: exact and positive inverse trace when tr(MMᵀ) = 2. -/
theorem algebraic_negative_hessian_inverse_trace (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) (htrace : (M * Mᵀ).trace = 2) :
    ((-algebraicNormalHessian a M)⁻¹).trace = a ^ 2 ∧
    0 < ((-algebraicNormalHessian a M)⁻¹).trace := by
  rw [algebraic_negative_hessian_inverse a ha M hM, Matrix.trace_smul, htrace]
  constructor
  · simp [smul_eq_mul]
  · simpa [smul_eq_mul] using sq_pos_of_pos ha

/-- G18 algebra: cancellation of the positive scale in the normalized shape. -/
theorem algebraic_axis_shape_exact (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) (htrace : (M * Mᵀ).trace = 2) :
    algebraicNormalizedShape a M = (1 / 2 : ℝ) • (M * Mᵀ) := by
  unfold algebraicNormalizedShape
  rw [(algebraic_negative_hessian_inverse_trace a ha M hM htrace).1,
    algebraic_negative_hessian_inverse a ha M hM, smul_smul]
  congr 1
  field_simp

/-- The quadratic form is exactly a negative multiple of a sum of Euclidean squares. -/
theorem algebraic_hessian_quadratic (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (q : Fin 2 → ℝ) :
    q ⬝ᵥ (algebraicNormalHessian a M *ᵥ q) =
      (-2 / a ^ 2) * ((M⁻¹ *ᵥ q) 0 ^ 2 + (M⁻¹ *ᵥ q) 1 ^ 2) := by
  rw [algebraicNormalHessian, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp [dotProduct, Fin.sum_univ_two, smul_eq_mul, pow_two]

/-- Strict negativity for nonzero vectors; the matrix inverse is used to exclude a zero square sum. -/
theorem algebraic_hessian_negative (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det)
    (q : Fin 2 → ℝ) (hq : q ≠ 0) : q ⬝ᵥ (algebraicNormalHessian a M *ᵥ q) < 0 := by
  have hnonzero : M⁻¹ *ᵥ q ≠ 0 := by
    intro hz
    apply hq
    have he := congrArg (fun v => M *ᵥ v) hz
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM] using he
  have hsq : 0 < (M⁻¹ *ᵥ q) 0 ^ 2 + (M⁻¹ *ᵥ q) 1 ^ 2 := by
    by_contra hn
    have h0 : (M⁻¹ *ᵥ q) 0 = 0 := by nlinarith [sq_nonneg ((M⁻¹ *ᵥ q) 1)]
    have h1 : (M⁻¹ *ᵥ q) 1 = 0 := by nlinarith [sq_nonneg ((M⁻¹ *ᵥ q) 0)]
    apply hnonzero
    ext i
    fin_cases i <;> assumption
  rw [algebraic_hessian_quadratic]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos ha)) hsq

/-- Applying the algebra to the explicit seed supplies determinant invertibility and trace two. -/
theorem algebraic_seed_shape (a : ℝ) (ha : 0 < a) {rho : ℝ}
    (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    algebraicNormalizedShape a (seedMatrix rho alpha) = angleShape rho alpha := by
  rw [algebraic_axis_shape_exact a ha _ (isUnit_iff_ne_zero.mpr (ne_of_gt (seed_det hrl hru alpha).2))
    (seed_trace hrl hru alpha).2]
  exact angle_shape_entries hrl hru alpha

end Grad.GeometryClosure
