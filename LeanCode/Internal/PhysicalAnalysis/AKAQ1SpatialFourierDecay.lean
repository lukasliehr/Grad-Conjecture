import COR13Consumer
import SCD22CompletedCellValues

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets

abbrev SpatialMode := ℤ × ℤ

def spatialSquare (mode : SpatialMode) : ℝ := 1 + (mode.1 : ℝ)^2 + (mode.2 : ℝ)^2

def spatialDecay (mode : SpatialMode) : ℝ := spatialSquare mode ^ (-3 / 2 : ℝ)

def integerDecay (index : ℤ) : ℝ := (1 + (index : ℝ)^2) ^ (-3 / 4 : ℝ)

theorem spatialSquare_positive (mode : SpatialMode) : 0 < spatialSquare mode := by
  unfold spatialSquare
  positivity

theorem integerDecay_nonnegative (index : ℤ) : 0 ≤ integerDecay index := Real.rpow_nonneg (by positivity) _

theorem integerDecay_summable : Summable integerDecay := by
  have original := Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)
  have patched : Summable (fun index : ℤ => if index = 0 then (1 : ℝ) else |(index : ℝ)| ^ (-3 / 2 : ℝ)) := by
    apply original.congr_cofinite
    filter_upwards [show ∀ᶠ index : ℤ in Filter.cofinite, index ≠ 0 from by
      apply Filter.eventually_cofinite.mpr
      simp] with index nonzero
    simp only [if_neg nonzero]
    norm_num
  apply Summable.of_nonneg_of_le integerDecay_nonnegative _ patched
  intro index
  by_cases zero : index = 0
  · subst index
    simp [integerDecay]
  · have positive : 0 < |(index : ℝ)| := abs_pos.mpr (by exact_mod_cast zero)
    rw [if_neg zero]
    calc
      integerDecay index ≤ ((index : ℝ)^2) ^ (-3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (by exact_mod_cast zero)) (by linarith) (by norm_num)
      _ = |(index : ℝ)| ^ (-3 / 2 : ℝ) := by
        rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul positive.le]
        norm_num

theorem spatialDecay_nonnegative (mode : SpatialMode) : 0 ≤ spatialDecay mode :=
  Real.rpow_nonneg (spatialSquare_positive mode).le _

theorem spatialDecay_le_product (mode : SpatialMode) :
    spatialDecay mode ≤ integerDecay mode.1 * integerDecay mode.2 := by
  have productPositive : 0 < (1 + (mode.1 : ℝ)^2) * (1 + (mode.2 : ℝ)^2) := by positivity
  have squareBound : (1 + (mode.1 : ℝ)^2) * (1 + (mode.2 : ℝ)^2) ≤ spatialSquare mode ^ 2 := by
    unfold spatialSquare
    nlinarith [sq_nonneg (mode.1 : ℝ),sq_nonneg (mode.2 : ℝ),sq_nonneg ((mode.1 : ℝ)^2),sq_nonneg ((mode.2 : ℝ)^2)]
  calc
    spatialDecay mode = (spatialSquare mode ^ 2) ^ (-3 / 4 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (spatialSquare_positive mode).le]
      norm_num [spatialDecay]
    _ ≤ ((1 + (mode.1 : ℝ)^2) * (1 + (mode.2 : ℝ)^2)) ^ (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos productPositive squareBound (by norm_num)
    _ = integerDecay mode.1 * integerDecay mode.2 := Real.mul_rpow (by positivity) (by positivity)

/-- The precise two-dimensional cubic decay in GK03. No summation over the
cell frequency is spent in this estimate. -/
theorem spatialDecay_summable : Summable spatialDecay :=
  Summable.of_nonneg_of_le spatialDecay_nonnegative spatialDecay_le_product
    (integerDecay_summable.mul_of_nonneg integerDecay_summable integerDecay_nonnegative integerDecay_nonnegative)

def spatialDecayConstant : ℝ := ∑' mode, spatialDecay mode

theorem spatialDecayConstant_nonnegative : 0 ≤ spatialDecayConstant :=
  tsum_nonneg spatialDecay_nonnegative

theorem spatialDecay_sum_le (support : Finset SpatialMode) :
    ∑ mode ∈ support, spatialDecay mode ≤ spatialDecayConstant :=
  spatialDecay_summable.sum_le_tsum support (fun mode _ => spatialDecay_nonnegative mode)

private theorem imaginary_norm (angle : ℝ) : ‖Complex.I * (angle : ℂ)‖ = |angle| := by
  simp

private theorem imaginary_exp_norm (angle : ℝ) : ‖Complex.exp (Complex.I * (angle : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Squared half-Hölder bound for the actual imaginary exponential. -/
theorem imaginary_exp_difference_sq (angle : ℝ) :
    ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖^2 ≤ 4 * |angle| := by
  have smallNorm := imaginary_norm angle
  by_cases small : |angle| ≤ 1
  · have bound := Complex.norm_exp_sub_one_le (smallNorm.trans_le small)
    rw [smallNorm] at bound
    have squared := pow_le_pow_left₀ (norm_nonneg _) bound 2
    nlinarith [abs_nonneg angle, mul_nonneg (abs_nonneg angle) (sub_nonneg.mpr small)]
  · have bound : ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖ ≤ 2 := by
      simpa only [imaginary_exp_norm,norm_one,one_add_one_eq_two] using norm_sub_le (Complex.exp (Complex.I * (angle : ℂ))) 1
    nlinarith [norm_nonneg (Complex.exp (Complex.I * (angle : ℂ)) - 1)]

/-- Squared three-halves Taylor remainder, used directly before summing
spatial Fourier coefficients. This avoids any assumed Hölder representative. -/
theorem imaginary_exp_taylor_sq (angle : ℝ) :
    ‖Complex.exp (Complex.I * (angle : ℂ)) - 1 - Complex.I * (angle : ℂ)‖^2 ≤ 9 * |angle|^3 := by
  have smallNorm := imaginary_norm angle
  by_cases small : |angle| ≤ 1
  · have bound := Complex.norm_exp_sub_one_sub_id_le (smallNorm.trans_le small)
    rw [smallNorm] at bound
    have squared := pow_le_pow_left₀ (norm_nonneg _) bound 2
    have fourth : |angle|^4 ≤ |angle|^3 := by
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg angle) 3) (sub_nonneg.mpr small)]
    nlinarith [pow_nonneg (abs_nonneg angle) 3]
  · have first : ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖ ≤ 2 := by
      simpa only [imaginary_exp_norm,norm_one,one_add_one_eq_two] using norm_sub_le (Complex.exp (Complex.I * (angle : ℂ))) 1
    have bound := (norm_sub_le (Complex.exp (Complex.I * (angle : ℂ)) - 1) (Complex.I * (angle : ℂ))).trans
      (add_le_add first (le_refl ‖Complex.I * (angle : ℂ)‖))
    rw [smallNorm] at bound
    have simple : ‖Complex.exp (Complex.I * (angle : ℂ)) - 1 - Complex.I * (angle : ℂ)‖ ≤ 3 * |angle| := by linarith
    have squared := pow_le_pow_left₀ (norm_nonneg _) simple 2
    have cube : |angle|^2 ≤ |angle|^3 := by
      nlinarith [mul_nonneg (sq_nonneg |angle|) (sub_nonneg.mpr (le_of_not_ge small))]
    nlinarith

end Grad.OriginalFlatAxisDecay
