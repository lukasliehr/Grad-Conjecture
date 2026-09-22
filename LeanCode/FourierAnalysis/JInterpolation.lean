import FTP1315Proof
import Mathlib.Analysis.MeanInequalities

noncomputable section

open scoped BigOperators ENNReal

universe valueUniverse

namespace Grad.FourierInterpolation

open Grad.FourierGrade

/-- The literal nonnegative square summand in the integer Fourier grade. -/
def gradeSquareTerm {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value) (mode : FourierMode) : ℝ :=
  frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2

theorem gradeSquareTerm_nonneg {Value : Type valueUniverse}
    [NormedAddCommGroup Value] (grade : ℕ) (values : FourierMode → Value)
    (mode : FourierMode) : 0 ≤ gradeSquareTerm grade values mode := by
  exact mul_nonneg (pow_nonneg (frequencyWeight_pos mode).le _)
    (sq_nonneg _)

theorem gradeSquareTerm_summable {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value] (grade : ℕ)
    (values : JCore Value) : Summable (gradeSquareTerm grade values.1) := by
  change Summable (fun mode : FourierMode =>
    frequencyWeight mode ^ (2 * grade) * ‖values.1 mode‖ ^ 2)
  simpa only [coreToGrade_coefficient] using
    gradeCoefficientEnergy_summable grade (coreToGrade grade values)

/-- The exact real interpolation fraction between three strict integer grades. -/
def interpolationTheta (low middle high : ℕ) : ℝ :=
  ((middle - low : ℕ) : ℝ) / ((high - low : ℕ) : ℝ)

theorem interpolationTheta_pos {low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    0 < interpolationTheta low middle high := by
  unfold interpolationTheta
  exact div_pos (by exact_mod_cast Nat.sub_pos_of_lt lowMiddle)
    (by exact_mod_cast Nat.sub_pos_of_lt (lowMiddle.trans middleHigh))

theorem interpolationTheta_lt_one {low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    interpolationTheta low middle high < 1 := by
  unfold interpolationTheta
  rw [div_lt_one]
  · exact_mod_cast (by omega : middle - low < high - low)
  · exact_mod_cast Nat.sub_pos_of_lt (lowMiddle.trans middleHigh)

theorem interpolation_grade_affine {low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    (middle : ℝ) =
      (low : ℝ) * (1 - interpolationTheta low middle high) +
        (high : ℝ) * interpolationTheta low middle high := by
  have lowHigh : low ≤ high := (lowMiddle.trans middleHigh).le
  have lowMiddleLe : low ≤ middle := lowMiddle.le
  rw [interpolationTheta]
  push_cast [Nat.cast_sub lowHigh, Nat.cast_sub lowMiddleLe]
  have denominator : (high : ℝ) - low ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (lowMiddle.trans middleHigh).ne')
  field_simp
  ring

private theorem positive_product_interpolation
    (weight coefficient low middle high theta : ℝ)
    (weightPositive : 0 < weight) (coefficientPositive : 0 < coefficient)
    (affine : middle = low * (1 - theta) + high * theta) :
    weight ^ (2 * middle) * coefficient ^ (2 : ℝ) =
      (weight ^ (2 * low) * coefficient ^ (2 : ℝ)) ^ (1 - theta) *
        (weight ^ (2 * high) * coefficient ^ (2 : ℝ)) ^ theta := by
  rw [Real.mul_rpow (Real.rpow_nonneg weightPositive.le _)
      (Real.rpow_nonneg coefficientPositive.le _),
    Real.mul_rpow (Real.rpow_nonneg weightPositive.le _)
      (Real.rpow_nonneg coefficientPositive.le _)]
  rw [← Real.rpow_mul weightPositive.le, ← Real.rpow_mul coefficientPositive.le,
    ← Real.rpow_mul weightPositive.le, ← Real.rpow_mul coefficientPositive.le]
  rw [mul_mul_mul_comm]
  rw [← Real.rpow_add weightPositive, ← Real.rpow_add coefficientPositive]
  congr 1
  · rw [affine]
    ring
  · ring

private theorem weight_nat_pow_as_rpow (weight : ℝ) (grade : ℕ) :
    weight ^ (2 * grade) = weight ^ (2 * (grade : ℝ)) := by
  rw [show (2 : ℝ) * grade = ((2 * grade : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

private theorem norm_sq_as_rpow_two {Value : Type valueUniverse}
    [NormedAddCommGroup Value] (value : Value) :
    ‖value‖ ^ 2 = ‖value‖ ^ (2 : ℝ) := by
  exact (Real.rpow_two ‖value‖).symm

/-- The conjugate exponents used in the literal weighted-series Hölder step. -/
theorem interpolation_holder_conjugate {low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high) :
    (1 / (1 - interpolationTheta low middle high) : ℝ).HolderConjugate
      (1 / interpolationTheta low middle high) := by
  have thetaPositive := interpolationTheta_pos lowMiddle middleHigh
  have thetaLessOne := interpolationTheta_lt_one lowMiddle middleHigh
  simpa only [one_div] using
    (Real.HolderConjugate.one_sub_inv_inv thetaPositive thetaLessOne)

theorem gradeSquareTerm_interpolation {Value : Type valueUniverse}
    [NormedAddCommGroup Value] {low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high)
    (values : FourierMode → Value) (mode : FourierMode) :
    gradeSquareTerm middle values mode =
      gradeSquareTerm low values mode ^
          (1 - interpolationTheta low middle high) *
        gradeSquareTerm high values mode ^
          interpolationTheta low middle high := by
  have thetaPositive := interpolationTheta_pos lowMiddle middleHigh
  have thetaLessOne := interpolationTheta_lt_one lowMiddle middleHigh
  by_cases coefficientZero : values mode = 0
  · have lowZero : gradeSquareTerm low values mode = 0 := by
      simp [gradeSquareTerm, coefficientZero]
    have middleZero : gradeSquareTerm middle values mode = 0 := by
      simp [gradeSquareTerm, coefficientZero]
    have highZero : gradeSquareTerm high values mode = 0 := by
      simp [gradeSquareTerm, coefficientZero]
    rw [middleZero, lowZero, highZero,
      Real.zero_rpow (sub_pos.mpr thetaLessOne).ne',
      Real.zero_rpow thetaPositive.ne', zero_mul]
  · have coefficientPositive : 0 < ‖values mode‖ := norm_pos_iff.mpr coefficientZero
    have identity := positive_product_interpolation
      (frequencyWeight mode) ‖values mode‖ (low : ℝ) (middle : ℝ)
      (high : ℝ) (interpolationTheta low middle high)
      (frequencyWeight_pos mode) coefficientPositive
      (interpolation_grade_affine lowMiddle middleHigh)
    simpa only [gradeSquareTerm, weight_nat_pow_as_rpow,
      norm_sq_as_rpow_two] using identity

private theorem one_div_one_div_one_sub_theta {theta : ℝ}
    (_thetaLessOne : theta < 1) :
    1 / (1 / (1 - theta)) = 1 - theta := by
  field_simp

private theorem one_div_one_div_theta {theta : ℝ} (thetaPositive : 0 < theta) :
    1 / (1 / theta) = theta := by
  field_simp

theorem gradeSquareEnergy_interpolation {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    {low middle high : ℕ} (lowMiddle : low < middle)
    (middleHigh : middle < high) (values : JCore Value) :
    ∑' mode : FourierMode, gradeSquareTerm middle values.1 mode ≤
      (∑' mode : FourierMode, gradeSquareTerm low values.1 mode) ^
          (1 - interpolationTheta low middle high) *
        (∑' mode : FourierMode, gradeSquareTerm high values.1 mode) ^
          interpolationTheta low middle high := by
  let theta := interpolationTheta low middle high
  have thetaPositive : 0 < theta := interpolationTheta_pos lowMiddle middleHigh
  have thetaLessOne : theta < 1 := interpolationTheta_lt_one lowMiddle middleHigh
  have oneMinusThetaNe : 1 - theta ≠ 0 := (sub_pos.mpr thetaLessOne).ne'
  have thetaNe : theta ≠ 0 := thetaPositive.ne'
  have lowExponentIdentity : (1 - theta) * (1 / (1 - theta)) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ oneMinusThetaNe
  have highExponentIdentity : theta * (1 / theta) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ thetaNe
  let holderLow : ℝ := 1 / (1 - theta)
  let holderHigh : ℝ := 1 / theta
  let lowFactor : FourierMode → ℝ := fun mode =>
    gradeSquareTerm low values.1 mode ^ (1 - theta)
  let highFactor : FourierMode → ℝ := fun mode =>
    gradeSquareTerm high values.1 mode ^ theta
  have lowPoweredSummable :
      Summable (fun mode : FourierMode => lowFactor mode ^ holderLow) := by
    apply (gradeSquareTerm_summable low values).congr
    intro mode
    unfold lowFactor holderLow
    calc
      gradeSquareTerm low values.1 mode =
          gradeSquareTerm low values.1 mode ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
      _ = gradeSquareTerm low values.1 mode ^
          ((1 - theta) * (1 / (1 - theta))) := by
        congr 1
        exact lowExponentIdentity.symm
      _ = (gradeSquareTerm low values.1 mode ^ (1 - theta)) ^
          (1 / (1 - theta)) :=
        Real.rpow_mul (gradeSquareTerm_nonneg low values.1 mode) _ _
  have highPoweredSummable :
      Summable (fun mode : FourierMode => highFactor mode ^ holderHigh) := by
    apply (gradeSquareTerm_summable high values).congr
    intro mode
    unfold highFactor holderHigh
    calc
      gradeSquareTerm high values.1 mode =
          gradeSquareTerm high values.1 mode ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
      _ = gradeSquareTerm high values.1 mode ^ (theta * (1 / theta)) := by
        congr 1
        exact highExponentIdentity.symm
      _ = (gradeSquareTerm high values.1 mode ^ theta) ^ (1 / theta) :=
        Real.rpow_mul (gradeSquareTerm_nonneg high values.1 mode) _ _
  have holder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (show holderLow.HolderConjugate holderHigh by
      simpa only [holderLow, holderHigh, theta] using
        interpolation_holder_conjugate lowMiddle middleHigh)
    (fun mode => Real.rpow_nonneg (gradeSquareTerm_nonneg low values.1 mode) _)
    (fun mode => Real.rpow_nonneg (gradeSquareTerm_nonneg high values.1 mode) _)
    lowPoweredSummable highPoweredSummable
  have lowTsumIdentity :
      (∑' mode : FourierMode, lowFactor mode ^ holderLow) =
        ∑' mode : FourierMode, gradeSquareTerm low values.1 mode := by
    apply tsum_congr
    intro mode
    unfold lowFactor holderLow
    rw [← Real.rpow_mul (gradeSquareTerm_nonneg low values.1 mode)]
    rw [lowExponentIdentity, Real.rpow_one]
  have highTsumIdentity :
      (∑' mode : FourierMode, highFactor mode ^ holderHigh) =
        ∑' mode : FourierMode, gradeSquareTerm high values.1 mode := by
    apply tsum_congr
    intro mode
    unfold highFactor holderHigh
    rw [← Real.rpow_mul (gradeSquareTerm_nonneg high values.1 mode)]
    rw [highExponentIdentity, Real.rpow_one]
  calc
    ∑' mode : FourierMode, gradeSquareTerm middle values.1 mode =
        ∑' mode : FourierMode, lowFactor mode * highFactor mode := by
      apply tsum_congr
      intro mode
      simpa only [lowFactor, highFactor, theta] using
        gradeSquareTerm_interpolation lowMiddle middleHigh values.1 mode
    _ ≤ (∑' mode : FourierMode, lowFactor mode ^ holderLow) ^
          (1 / holderLow) *
        (∑' mode : FourierMode, highFactor mode ^ holderHigh) ^
          (1 / holderHigh) := holder
    _ = (∑' mode : FourierMode, gradeSquareTerm low values.1 mode) ^
          (1 - interpolationTheta low middle high) *
        (∑' mode : FourierMode, gradeSquareTerm high values.1 mode) ^
          interpolationTheta low middle high := by
      rw [lowTsumIdentity, highTsumIdentity]
      rw [one_div_one_div_one_sub_theta thetaLessOne,
        one_div_one_div_theta thetaPositive]

theorem jCore_grade_norm_sq_interpolation {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    {low middle high : ℕ} (lowMiddle : low < middle)
    (middleHigh : middle < high) (values : JCore Value) :
    ‖coreToGrade middle values‖ ^ 2 ≤
      (‖coreToGrade low values‖ ^ 2) ^
          (1 - interpolationTheta low middle high) *
        (‖coreToGrade high values‖ ^ 2) ^
          interpolationTheta low middle high := by
  rw [norm_sq_eq_weighted_tsum middle (coreToGrade middle values),
    norm_sq_eq_weighted_tsum low (coreToGrade low values),
    norm_sq_eq_weighted_tsum high (coreToGrade high values)]
  simpa only [coreToGrade_coefficient, gradeSquareTerm] using
    gradeSquareEnergy_interpolation lowMiddle middleHigh values

private theorem square_rpow_product (first second firstExponent secondExponent : ℝ)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    (first ^ 2) ^ firstExponent * (second ^ 2) ^ secondExponent =
      (first ^ firstExponent * second ^ secondExponent) ^ 2 := by
  rw [← Real.rpow_two first, ← Real.rpow_two second,
    ← Real.rpow_two (first ^ firstExponent * second ^ secondExponent)]
  rw [← Real.rpow_mul firstNonnegative, ← Real.rpow_mul secondNonnegative,
    Real.mul_rpow (Real.rpow_nonneg firstNonnegative _)
      (Real.rpow_nonneg secondNonnegative _),
    ← Real.rpow_mul firstNonnegative, ← Real.rpow_mul secondNonnegative]
  congr 1 <;> ring

/-- P16 on the literal all-grade Fourier core, with constant one and the exact
integer interpolation fraction. -/
theorem jCore_grade_norm_interpolation {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    {low middle high : ℕ} (lowMiddle : low < middle)
    (middleHigh : middle < high) (values : JCore Value) :
    ‖coreToGrade middle values‖ ≤
      ‖coreToGrade low values‖ ^
          (1 - interpolationTheta low middle high) *
        ‖coreToGrade high values‖ ^
          interpolationTheta low middle high := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [← square_rpow_product ‖coreToGrade low values‖
    ‖coreToGrade high values‖
    (1 - interpolationTheta low middle high)
    (interpolationTheta low middle high) (norm_nonneg _) (norm_nonneg _)]
  exact jCore_grade_norm_sq_interpolation lowMiddle middleHigh values

end Grad.FourierInterpolation
