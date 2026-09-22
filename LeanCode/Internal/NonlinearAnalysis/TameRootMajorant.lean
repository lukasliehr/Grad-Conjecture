import TameRootRemainder

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The quadratic envelope majorant of the root Taylor remainder: padded
power bounds, the decorated monomial estimate, the double binomial collapse
to the strict ratio, and the final quadratic-in-`t` remainder bound. -/

variable {parameters : PhaseParameters}

/-- The graded envelope scale of the curve data. -/
def rootEnvelopeScale (x u w : TameCoefficient parameters) (grade : ℕ) : ℝ :=
  Real.exp parameters.sigma0 *
    (coefficientEnvelope grade x + coefficientEnvelope grade u +
      coefficientEnvelope grade w + 1)

theorem rootEnvelopeScale_one_le (x u w : TameCoefficient parameters) (grade : ℕ) :
    1 ≤ rootEnvelopeScale x u w grade := by
  have exp_one_le : 1 ≤ Real.exp parameters.sigma0 :=
    Real.one_le_exp parameters.sigma0_pos.le
  have sum_one_le : 1 ≤ coefficientEnvelope grade x + coefficientEnvelope grade u +
      coefficientEnvelope grade w + 1 := by
    have := coefficientEnvelope_nonneg grade x
    have := coefficientEnvelope_nonneg grade u
    have := coefficientEnvelope_nonneg grade w
    linarith
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
  _ ≤ _ := mul_le_mul exp_one_le sum_one_le zero_le_one (Real.exp_pos _).le

theorem rootEnvelopeScale_nonneg (x u w : TameCoefficient parameters) (grade : ℕ) :
    0 ≤ rootEnvelopeScale x u w grade :=
  zero_le_one.trans (rootEnvelopeScale_one_le x u w grade)

theorem exp_le_rootEnvelopeScale (x u w : TameCoefficient parameters) (grade : ℕ) :
    Real.exp parameters.sigma0 ≤ rootEnvelopeScale x u w grade := by
  have sum_one_le : 1 ≤ coefficientEnvelope grade x + coefficientEnvelope grade u +
      coefficientEnvelope grade w + 1 := by
    have := coefficientEnvelope_nonneg grade x
    have := coefficientEnvelope_nonneg grade u
    have := coefficientEnvelope_nonneg grade w
    linarith
  calc Real.exp parameters.sigma0 = Real.exp parameters.sigma0 * 1 := (mul_one _).symm
  _ ≤ _ := mul_le_mul_of_nonneg_left sum_one_le (Real.exp_pos _).le

theorem envelope_x_le_rootEnvelopeScale (x u w : TameCoefficient parameters) (grade : ℕ) :
    coefficientEnvelope grade x ≤ rootEnvelopeScale x u w grade := by
  have exp_one_le : 1 ≤ Real.exp parameters.sigma0 :=
    Real.one_le_exp parameters.sigma0_pos.le
  have := coefficientEnvelope_nonneg grade u
  have := coefficientEnvelope_nonneg grade w
  have := coefficientEnvelope_nonneg grade x
  calc coefficientEnvelope grade x
      ≤ coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1 := by linarith
    _ = 1 * (coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_one_le (by linarith)

theorem envelope_u_le_rootEnvelopeScale (x u w : TameCoefficient parameters) (grade : ℕ) :
    coefficientEnvelope grade u ≤ rootEnvelopeScale x u w grade := by
  have exp_one_le : 1 ≤ Real.exp parameters.sigma0 :=
    Real.one_le_exp parameters.sigma0_pos.le
  have := coefficientEnvelope_nonneg grade x
  have := coefficientEnvelope_nonneg grade w
  have := coefficientEnvelope_nonneg grade u
  calc coefficientEnvelope grade u
      ≤ coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1 := by linarith
    _ = 1 * (coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_one_le (by linarith)

theorem envelope_w_le_rootEnvelopeScale (x u w : TameCoefficient parameters) (grade : ℕ) :
    coefficientEnvelope grade w ≤ rootEnvelopeScale x u w grade := by
  have exp_one_le : 1 ≤ Real.exp parameters.sigma0 :=
    Real.one_le_exp parameters.sigma0_pos.le
  have := coefficientEnvelope_nonneg grade x
  have := coefficientEnvelope_nonneg grade u
  have := coefficientEnvelope_nonneg grade w
  calc coefficientEnvelope grade w
      ≤ coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1 := by linarith
    _ = 1 * (coefficientEnvelope grade x + coefficientEnvelope grade u +
          coefficientEnvelope grade w + 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_one_le (by linarith)

/-! ### Padded power bounds -/

/-- Envelope of the unit as an exponential. -/
theorem coefficientEnvelope_one_eq (grade : ℕ) :
    coefficientEnvelope grade (1 : TameCoefficient parameters) =
      Real.exp parameters.sigma0 := coefficientEnvelope_one grade

/-- Padded graded bound for base powers. -/
theorem base_pow_envelope_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    (grade exponent : ℕ) :
    coefficientEnvelope grade (x ^ exponent) ≤
      2 * ((exponent + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ exponent *
        rootEnvelopeScale x u w grade := by
  match exponent with
  | 0 =>
    rw [pow_zero, coefficientEnvelope_one_eq, pow_zero]
    have := exp_le_rootEnvelopeScale x u w grade
    have scale_nonneg := rootEnvelopeScale_nonneg x u w grade
    have power_one_le : (1 : ℝ) ≤ ((0 + 1 : ℕ) : ℝ) ^ (grade + 1) := by
      norm_num
    nlinarith
  | smaller + 1 =>
    have power_le := tamePow_envelope_le (parameters := parameters) grade smaller x
    have base_le : coefficientEnvelope 0 x ^ smaller ≤ rootSmallRadius x ^ smaller :=
      pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 x) (envelope_le_rootSmallRadius small) _
    have halves : rootSmallRadius x ^ smaller ≤ 2 * rootSmallRadius x ^ (smaller + 1) := by
      have half_le := rootSmallRadius_half_le x
      have radius_nonneg := (rootSmallRadius_pos x).le
      calc rootSmallRadius x ^ smaller
          = 2 * ((1 / 2) * rootSmallRadius x ^ smaller) := by ring
        _ ≤ 2 * (rootSmallRadius x * rootSmallRadius x ^ smaller) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right half_le (pow_nonneg radius_nonneg _)
        _ = 2 * rootSmallRadius x ^ (smaller + 1) := by
            rw [← pow_succ']
    have envelope_le := envelope_x_le_rootEnvelopeScale x u w grade
    have cast_le : (((smaller + 1 : ℕ) : ℝ)) ^ (grade + 1) ≤
        (((smaller + 1 + 1 : ℕ) : ℝ)) ^ (grade + 1) := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_succ (smaller + 1)
    calc coefficientEnvelope grade (x ^ (smaller + 1))
        ≤ ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
            coefficientEnvelope 0 x ^ smaller * coefficientEnvelope grade x := power_le
      _ ≤ ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ smaller *
            rootEnvelopeScale x u w grade := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left base_le (pow_nonneg (Nat.cast_nonneg _) _)
          · exact envelope_le
          · exact coefficientEnvelope_nonneg grade x
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
              (pow_nonneg (rootSmallRadius_pos x).le _)
      _ ≤ ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
            (2 * rootSmallRadius x ^ (smaller + 1)) * rootEnvelopeScale x u w grade := by
          apply mul_le_mul_of_nonneg_right _ (rootEnvelopeScale_nonneg x u w grade)
          exact mul_le_mul_of_nonneg_left halves (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := by
          have rearrange : ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
              (2 * rootSmallRadius x ^ (smaller + 1)) * rootEnvelopeScale x u w grade =
              2 * ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
                rootSmallRadius x ^ (smaller + 1) * rootEnvelopeScale x u w grade := by
            ring
          rw [rearrange]
          apply mul_le_mul_of_nonneg_right _ (rootEnvelopeScale_nonneg x u w grade)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rootSmallRadius_pos x).le _)
          exact mul_le_mul_of_nonneg_left cast_le (by norm_num)

/-- Padded zero-grade bound for base powers. -/
theorem base_pow_envelope_zero_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) (exponent : ℕ) :
    coefficientEnvelope 0 (x ^ exponent) ≤
      rootEnvelopeScale x u w 0 * rootSmallRadius x ^ exponent := by
  match exponent with
  | 0 =>
    rw [pow_zero, coefficientEnvelope_one_eq, pow_zero, mul_one]
    exact exp_le_rootEnvelopeScale x u w 0
  | smaller + 1 =>
    have power_le := tamePow_envelope_zero_le (parameters := parameters) smaller x
    have base_le : coefficientEnvelope 0 x ^ (smaller + 1) ≤
        rootSmallRadius x ^ (smaller + 1) :=
      pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 x) (envelope_le_rootSmallRadius small) _
    have scale_one_le := rootEnvelopeScale_one_le x u w 0
    calc coefficientEnvelope 0 (x ^ (smaller + 1))
        ≤ rootSmallRadius x ^ (smaller + 1) := power_le.trans base_le
      _ = 1 * rootSmallRadius x ^ (smaller + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right scale_one_le
          (pow_nonneg (rootSmallRadius_pos x).le _)

/-- Padded graded bound for direction powers. -/
theorem direction_pow_envelope_le (x u w direction : TameCoefficient parameters)
    (scale_le : ∀ grade, coefficientEnvelope grade direction ≤ rootEnvelopeScale x u w grade)
    (grade exponent : ℕ) :
    coefficientEnvelope grade (direction ^ exponent) ≤
      2 * ((exponent + 1 : ℕ) : ℝ) ^ (grade + 1) *
        rootDirectionSize direction ^ exponent * rootEnvelopeScale x u w grade := by
  match exponent with
  | 0 =>
    rw [pow_zero, coefficientEnvelope_one_eq, pow_zero]
    have := exp_le_rootEnvelopeScale x u w grade
    have scale_nonneg := rootEnvelopeScale_nonneg x u w grade
    have power_one_le : (1 : ℝ) ≤ ((0 + 1 : ℕ) : ℝ) ^ (grade + 1) := by norm_num
    nlinarith
  | smaller + 1 =>
    have power_le := tamePow_envelope_le (parameters := parameters) grade smaller direction
    have base_le : coefficientEnvelope 0 direction ^ smaller ≤
        rootDirectionSize direction ^ smaller :=
      pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 direction)
        (envelope_le_rootDirectionSize direction) _
    have pad_le : rootDirectionSize direction ^ smaller ≤
        rootDirectionSize direction ^ (smaller + 1) :=
      pow_le_pow_right₀ (rootDirectionSize_one_le direction) (Nat.le_succ smaller)
    have cast_le : (((smaller + 1 : ℕ) : ℝ)) ^ (grade + 1) ≤
        (((smaller + 1 + 1 : ℕ) : ℝ)) ^ (grade + 1) := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_succ (smaller + 1)
    have direction_nonneg : 0 ≤ rootDirectionSize direction ^ (smaller + 1) :=
      pow_nonneg (rootDirectionSize_pos direction).le _
    calc coefficientEnvelope grade (direction ^ (smaller + 1))
        ≤ ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
            coefficientEnvelope 0 direction ^ smaller *
            coefficientEnvelope grade direction := power_le
      _ ≤ ((smaller + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
            rootDirectionSize direction ^ (smaller + 1) *
            rootEnvelopeScale x u w grade := by
          apply mul_le_mul
          · exact mul_le_mul cast_le (base_le.trans pad_le)
              (pow_nonneg (coefficientEnvelope_nonneg 0 direction) _)
              (pow_nonneg (Nat.cast_nonneg _) _)
          · exact scale_le grade
          · exact coefficientEnvelope_nonneg grade direction
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) direction_nonneg
      _ ≤ _ := by
          have two_le : ((smaller + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
              rootDirectionSize direction ^ (smaller + 1) ≤
              2 * ((smaller + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
                rootDirectionSize direction ^ (smaller + 1) := by
            nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) (smaller + 1 + 1)) (grade + 1),
              direction_nonneg]
          exact mul_le_mul_of_nonneg_right two_le (rootEnvelopeScale_nonneg x u w grade)

/-- Padded zero-grade bound for direction powers. -/
theorem direction_pow_envelope_zero_le (x u w direction : TameCoefficient parameters)
    (exponent : ℕ) :
    coefficientEnvelope 0 (direction ^ exponent) ≤
      rootEnvelopeScale x u w 0 * rootDirectionSize direction ^ exponent := by
  match exponent with
  | 0 =>
    rw [pow_zero, coefficientEnvelope_one_eq, pow_zero, mul_one]
    exact exp_le_rootEnvelopeScale x u w 0
  | smaller + 1 =>
    have power_le := tamePow_envelope_zero_le (parameters := parameters) smaller direction
    have base_le : coefficientEnvelope 0 direction ^ (smaller + 1) ≤
        rootDirectionSize direction ^ (smaller + 1) :=
      pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 direction)
        (envelope_le_rootDirectionSize direction) _
    have scale_one_le := rootEnvelopeScale_one_le x u w 0
    calc coefficientEnvelope 0 (direction ^ (smaller + 1))
        ≤ rootDirectionSize direction ^ (smaller + 1) := power_le.trans base_le
      _ = 1 * rootDirectionSize direction ^ (smaller + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right scale_one_le
          (pow_nonneg (rootDirectionSize_pos direction).le _)

end Grad.NonlinearQuotientBounds
