import BKA3FiniteKernel

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

/-- The literal total tangential-grade negative-half weight in AH19. -/
def negativeTotalWeight (parameters : PhaseParameters) (grade : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ grade *
    negativeTraceWeight parameters 0 0 mode

theorem negativeTotalWeight_pos (parameters : PhaseParameters) (grade : ℕ)
    (mode : ℤ × ℤ) : 0 < negativeTotalWeight parameters grade mode :=
  mul_pos (pow_pos (Grad.SourceBoundaryTrace.annularFrequency_pos mode) _)
    (negativeTraceWeight_pos parameters 0 0 mode)

abbrev NegativeTotalTrace (_parameters : PhaseParameters) (_grade dimension : ℕ) :=
  lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

def negativeTotalCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : NegativeTotalTrace parameters grade dimension)
    (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((negativeTotalWeight parameters grade mode : ℂ)⁻¹) • field mode

theorem negativeTotal_weighted {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : NegativeTotalTrace parameters grade dimension)
    (mode : ℤ × ℤ) :
    (negativeTotalWeight parameters grade mode : ℂ) •
        negativeTotalCoefficient parameters grade field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr
    (negativeTotalWeight_pos parameters grade mode).ne') _

theorem annularFrequency_additive_shift_le (mode shift : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ≤
      annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) +
        annularFrequency shift.1 shift.2 := by
  have first : |(mode.1 : ℝ)| ≤
      |((mode.1 - shift.1 : ℤ) : ℝ)| + |(shift.1 : ℝ)| := by
    calc
      |(mode.1 : ℝ)| = |(((mode.1 - shift.1 : ℤ) : ℝ) + (shift.1 : ℝ))| := by
        congr 1
        push_cast
        ring
      _ ≤ _ := abs_add_le _ _
  have second : |(mode.2 : ℝ)| ≤
      |((mode.2 - shift.2 : ℤ) : ℝ)| + |(shift.2 : ℝ)| := by
    calc
      |(mode.2 : ℝ)| = |(((mode.2 - shift.2 : ℤ) : ℝ) + (shift.2 : ℝ))| := by
        congr 1
        push_cast
        ring
      _ ≤ _ := abs_add_le _ _
  unfold annularFrequency
  linarith

theorem annularFrequency_pow_shift_le (grade : ℕ) (mode shift : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ^ grade ≤
      (2 : ℝ) ^ grade *
        (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) ^ grade +
          annularFrequency shift.1 shift.2 ^ grade) := by
  let inputFrequency :=
    annularFrequency (mode.1 - shift.1) (mode.2 - shift.2)
  let shiftFrequency := annularFrequency shift.1 shift.2
  have powerMono := pow_le_pow_left₀
    (Grad.SourceBoundaryTrace.annularFrequency_pos mode).le
    (annularFrequency_additive_shift_le mode shift) grade
  have addPower := add_pow_le
    (Grad.SourceBoundaryTrace.annularFrequency_pos
      (mode.1 - shift.1, mode.2 - shift.2)).le
    (Grad.SourceBoundaryTrace.annularFrequency_pos shift).le grade
  have constantMono : (2 : ℝ) ^ (grade - 1) ≤ 2 ^ grade :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le grade 1)
  calc
    annularFrequency mode.1 mode.2 ^ grade
        ≤ (inputFrequency + shiftFrequency) ^ grade := powerMono
    _ ≤ 2 ^ (grade - 1) *
          (inputFrequency ^ grade + shiftFrequency ^ grade) := addPower
    _ ≤ 2 ^ grade *
          (inputFrequency ^ grade + shiftFrequency ^ grade) :=
        mul_le_mul_of_nonneg_right constantMono
          (add_nonneg (pow_nonneg
            (Grad.SourceBoundaryTrace.annularFrequency_pos
              (mode.1 - shift.1, mode.2 - shift.2)).le _)
            (pow_nonneg
              (Grad.SourceBoundaryTrace.annularFrequency_pos shift).le _))

def totalShareDenominator (grade : ℕ) (mode shift : ℤ × ℤ) : ℝ :=
  annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) ^ grade +
    annularFrequency shift.1 shift.2 ^ grade

theorem totalShareDenominator_pos (grade : ℕ) (mode shift : ℤ × ℤ) :
    0 < totalShareDenominator grade mode shift := by
  unfold totalShareDenominator
  exact add_pos_of_pos_of_nonneg
    (pow_pos (Grad.SourceBoundaryTrace.annularFrequency_pos
      (mode.1 - shift.1, mode.2 - shift.2)) _)
    (pow_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos shift).le _)

def highInputShare (grade : ℕ) (mode shift : ℤ × ℤ) : ℝ :=
  annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) ^ grade /
    totalShareDenominator grade mode shift

def lowInputShare (grade : ℕ) (mode shift : ℤ × ℤ) : ℝ :=
  annularFrequency shift.1 shift.2 ^ grade /
    totalShareDenominator grade mode shift

theorem highInputShare_add_lowInputShare (grade : ℕ) (mode shift : ℤ × ℤ) :
    highInputShare grade mode shift + lowInputShare grade mode shift = 1 := by
  unfold highInputShare lowInputShare totalShareDenominator
  rw [← add_div]
  exact div_self (totalShareDenominator_pos grade mode shift).ne'

def totalTameShiftCost (parameters : PhaseParameters) (grade moment : ℕ)
    (shift : ℤ × ℤ) : ℝ :=
  2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
    annularFrequency shift.1 shift.2 ^ moment

theorem totalTameShiftCost_nonnegative (parameters : PhaseParameters) (grade moment : ℕ)
    (shift : ℤ × ℤ) : 0 ≤ totalTameShiftCost parameters grade moment shift := by
  unfold totalTameShiftCost
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (by norm_num) _)
      (boundaryCoefficientPhaseCost_nonnegative parameters shift))
    (pow_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos shift).le _)

/-- The common pointwise weight estimate behind both AH19 terms. -/
theorem negativeTotalWeight_shift_split_le (parameters : PhaseParameters) (grade : ℕ)
    (mode shift : ℤ × ℤ) :
    negativeTotalWeight parameters grade mode ≤
      2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 *
          totalShareDenominator grade mode shift *
            negativeTraceWeight parameters 0 0
              (twoFrequencyTranslation shift mode) := by
  have base := negativeTraceWeight_shift_le parameters 0 0 mode shift
  unfold negativeShiftCost at base
  simp only [zero_add, pow_one] at base
  have frequencyPower := annularFrequency_pow_shift_le grade mode shift
  unfold negativeTotalWeight
  apply (mul_le_mul frequencyPower base
    (negativeTraceWeight_pos parameters 0 0 mode).le
    (mul_nonneg (pow_nonneg (by norm_num) _)
      (add_nonneg
        (pow_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos
          (mode.1 - shift.1, mode.2 - shift.2)).le _)
        (pow_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos shift).le _)))).trans_eq
  unfold totalShareDenominator
  ring

end Grad.BoundaryKernelAction
