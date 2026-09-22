import SCD29GraphNorm

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

/-- Translation of the angular Fourier index.  Multiplication by the
character of index `shift` sends the coefficient at `m - shift` to `m`. -/
def angularModeTranslation (shift : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mode := (mode.1 - shift, mode.2)
  invFun mode := (mode.1 + shift, mode.2)
  left_inv mode := by simp
  right_inv mode := by simp

@[simp] theorem angularModeTranslation_apply (shift : ℤ) (mode : ℤ × ℤ) :
    angularModeTranslation shift mode = (mode.1 - shift, mode.2) := rfl

theorem annularFrequency_pos (mode cell : ℤ) :
    0 < annularFrequency mode cell := by
  unfold annularFrequency
  positivity

/-- The exact weight comparison under an arbitrary angular translation. -/
theorem annularFrequency_shift_le (mode cell shift : ℤ) :
    annularFrequency mode cell ≤
      (1 + |(shift : ℝ)|) * annularFrequency (mode - shift) cell := by
  have triangle : |(mode : ℝ)| ≤ |((mode - shift : ℤ) : ℝ)| + |(shift : ℝ)| := by
    calc
      |(mode : ℝ)| = |(((mode - shift : ℤ) : ℝ) + (shift : ℝ))| := by
        congr 1
        push_cast
        ring
      _ ≤ |((mode - shift : ℤ) : ℝ)| + |(shift : ℝ)| := abs_add_le _ _
  have sourceOne : 1 ≤ annularFrequency (mode - shift) cell := by
    unfold annularFrequency
    linarith [abs_nonneg (((mode - shift : ℤ) : ℝ)), abs_nonneg (cell : ℝ)]
  unfold annularFrequency at *
  nlinarith [abs_nonneg (shift : ℝ), abs_nonneg (cell : ℝ)]

theorem annularFrequency_ratio_nonnegative (mode cell shift : ℤ) :
    0 ≤ annularFrequency mode cell / annularFrequency (mode - shift) cell :=
  div_nonneg (annularFrequency_nonnegative _ _) (annularFrequency_nonnegative _ _)

theorem annularFrequency_ratio_le (mode cell shift : ℤ) :
    annularFrequency mode cell / annularFrequency (mode - shift) cell ≤
      1 + |(shift : ℝ)| := by
  exact (div_le_iff₀ (annularFrequency_pos (mode - shift) cell)).mpr
    (annularFrequency_shift_le mode cell shift)

theorem annularFrequency_ratio_pow_le (power : ℕ) (mode cell shift : ℤ) :
    (annularFrequency mode cell / annularFrequency (mode - shift) cell) ^ power ≤
      (1 + |(shift : ℝ)|) ^ power :=
  pow_le_pow_left₀ (annularFrequency_ratio_nonnegative mode cell shift)
    (annularFrequency_ratio_le mode cell shift) power

theorem annularFrequency_unit_shift_pow_le (power : ℕ) (mode cell shift : ℤ)
    (unit : |shift| = 1) :
    (annularFrequency mode cell / annularFrequency (mode - shift) cell) ^ power ≤
      (2 : ℝ) ^ power := by
  have castUnit : |(shift : ℝ)| = 1 := by
    simpa only [Int.cast_abs, Int.cast_one] using congrArg (fun value : ℤ => (value : ℝ)) unit
  simpa only [castUnit, add_comm, one_add_one_eq_two] using
    annularFrequency_ratio_pow_le power mode cell shift

end Grad.SourceCollarAngular
