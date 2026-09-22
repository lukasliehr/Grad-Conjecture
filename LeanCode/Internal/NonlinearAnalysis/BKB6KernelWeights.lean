import BKB5FullKernelConstructor

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.PhaseAlgebra

theorem boundaryCoefficientPhaseCost_one_le (parameters : PhaseParameters)
    (shift : ℤ × ℤ) : 1 ≤ boundaryCoefficientPhaseCost parameters shift := by
  unfold boundaryCoefficientPhaseCost phaseWeight phaseWidth
  have widthNonnegative :
      0 ≤ (parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)| := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (parameters_gamma_lt_sigma0 parameters).le
    · exact abs_nonneg _
  have first : 1 ≤ Real.exp (parameters.sigma0 + parameters.gamma) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (add_nonneg parameters.sigma0_pos.le parameters.gamma_pos.le)
  have second : 1 ≤ Real.exp
      ((parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)|) :=
    by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr widthNonnegative
  simpa only [mul_one] using one_le_mul_of_one_le_of_one_le first second

theorem boundaryCoefficientPhaseCost_add_le (parameters : PhaseParameters)
    (first second : ℤ × ℤ) :
    boundaryCoefficientPhaseCost parameters (first + second) ≤
      boundaryCoefficientPhaseCost parameters first *
        boundaryCoefficientPhaseCost parameters second := by
  let constant := Real.exp (parameters.sigma0 + parameters.gamma)
  have constantOne : 1 ≤ constant := by
    dsimp only [constant]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (add_nonneg parameters.sigma0_pos.le parameters.gamma_pos.le)
  have phase := phaseWeight_submultiplicative parameters 1 zero_le_one le_rfl
    first.2 second.2
  have constantSquare : constant ≤ constant * constant := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left constantOne (Real.exp_pos _).le
  unfold boundaryCoefficientPhaseCost
  change constant * phaseWeight parameters 1 (first.2 + second.2) ≤
    (constant * phaseWeight parameters 1 first.2) *
      (constant * phaseWeight parameters 1 second.2)
  calc
    constant * phaseWeight parameters 1 (first.2 + second.2) ≤
        constant * (phaseWeight parameters 1 first.2 *
          phaseWeight parameters 1 second.2) :=
      mul_le_mul_of_nonneg_left phase (Real.exp_pos _).le
    _ ≤ (constant * constant) *
        (phaseWeight parameters 1 first.2 * phaseWeight parameters 1 second.2) :=
      mul_le_mul_of_nonneg_right constantSquare
        (mul_nonneg (phaseWeight_pos parameters 1 first.2).le
          (phaseWeight_pos parameters 1 second.2).le)
    _ = _ := by ring

theorem annularFrequency_add_le (first second : ℤ × ℤ) :
    annularFrequency (first + second).1 (first + second).2 ≤
      annularFrequency first.1 first.2 + annularFrequency second.1 second.2 := by
  have firstCoordinate : |((first.1 + second.1 : ℤ) : ℝ)| ≤
      |(first.1 : ℝ)| + |(second.1 : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  have secondCoordinate : |((first.2 + second.2 : ℤ) : ℝ)| ≤
      |(first.2 : ℝ)| + |(second.2 : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  change annularFrequency (first.1 + second.1) (first.2 + second.2) ≤ _
  unfold annularFrequency
  linarith

theorem annularFrequency_add_pow_le (moment : ℕ) (first second : ℤ × ℤ) :
    annularFrequency (first + second).1 (first + second).2 ^ moment ≤
      2 ^ moment *
        (annularFrequency first.1 first.2 ^ moment +
          annularFrequency second.1 second.2 ^ moment) := by
  have powerMono := pow_le_pow_left₀
    (annularFrequency_pos (first + second)).le
    (annularFrequency_add_le first second) moment
  have addPower := add_pow_le
    (annularFrequency_pos first).le (annularFrequency_pos second).le moment
  have constantMono : (2 : ℝ) ^ (moment - 1) ≤ 2 ^ moment :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le moment 1)
  calc
    annularFrequency (first + second).1 (first + second).2 ^ moment ≤
        (annularFrequency first.1 first.2 +
          annularFrequency second.1 second.2) ^ moment := powerMono
    _ ≤ 2 ^ (moment - 1) *
        (annularFrequency first.1 first.2 ^ moment +
          annularFrequency second.1 second.2 ^ moment) := addPower
    _ ≤ 2 ^ moment *
        (annularFrequency first.1 first.2 ^ moment +
          annularFrequency second.1 second.2 ^ moment) :=
      mul_le_mul_of_nonneg_right constantMono
        (add_nonneg (pow_nonneg (annularFrequency_pos first).le _)
          (pow_nonneg (annularFrequency_pos second).le _))

def fullKernelWeightedEnvelope {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) : ℝ :=
  boundaryCoefficientPhaseCost parameters shift *
    annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift

theorem fullKernelWeightedEnvelope_nonnegative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    0 ≤ fullKernelWeightedEnvelope parameters moment kernel shift := by
  exact mul_nonneg
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
      (pow_nonneg (annularFrequency_pos shift).le _))
    (fullKernelEntryNorm_nonnegative kernel shift)

theorem fullKernelWeightedEnvelope_summable {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    Summable (fullKernelWeightedEnvelope parameters moment kernel) :=
  kernel.moments moment

theorem fullKernelEntryNorm_summable {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    Summable kernel.entryNorm := by
  apply Summable.of_nonneg_of_le
    (fullKernelEntryNorm_nonnegative kernel)
    (fun shift => ?_)
    (kernel.moments 0)
  simpa only [pow_zero, mul_one, one_mul] using
    mul_le_mul_of_nonneg_right (boundaryCoefficientPhaseCost_one_le parameters shift)
      (fullKernelEntryNorm_nonnegative kernel shift)

/-- The shear `(total, second) -> (total-second, second)` used in every
two-frequency kernel product. -/
def twoFrequencyConvolutionEquiv :
    ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun pair := (pair.1 - pair.2, pair.2)
  invFun pair := (pair.1 + pair.2, pair.2)
  left_inv pair := by ext <;> simp
  right_inv pair := by ext <;> simp

end Grad.BoundaryKernelAction
