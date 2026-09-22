import TRM1AngularWeight

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

def annularShiftScalar (power : ℕ) (shift : ℤ) (mode : ℤ × ℤ) : ℂ :=
  ((annularFrequency mode.1 mode.2 /
    annularFrequency (mode.1 - shift) mode.2) ^ power : ℝ)

theorem annularShiftScalar_norm (power : ℕ) (shift : ℤ) (mode : ℤ × ℤ) :
    ‖annularShiftScalar power shift mode‖ =
      (annularFrequency mode.1 mode.2 /
        annularFrequency (mode.1 - shift) mode.2) ^ power := by
  rw [annularShiftScalar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (annularFrequency_ratio_nonnegative _ _ _) _)]

theorem annularShiftScalar_norm_le (power : ℕ) (shift : ℤ) (mode : ℤ × ℤ) :
    ‖annularShiftScalar power shift mode‖ ≤ (1 + |(shift : ℝ)|) ^ power := by
  rw [annularShiftScalar_norm]
  exact annularFrequency_ratio_pow_le power mode.1 mode.2 shift

def annularRowShiftFun {dimension : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ) : RadialL2 dimension lower :=
  annularShiftScalar power shift mode • field (angularModeTranslation shift mode)

theorem divisionRow_norm_sq_raw {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at formula
  exact formula

theorem divisionRow_sq_summable {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
  have member := lp.memℓp field
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at member
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using member

theorem annularRowShiftFun_sq_bound {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (shift : ℤ) (field : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    ‖annularRowShiftFun lower power shift field mode‖ ^ 2 ≤
      ((1 + |(shift : ℝ)|) ^ power) ^ 2 *
        ‖field (angularModeTranslation shift mode)‖ ^ 2 := by
  have termBound : ‖annularRowShiftFun lower power shift field mode‖ ≤
      (1 + |(shift : ℝ)|) ^ power *
        ‖field (angularModeTranslation shift mode)‖ := by
    rw [annularRowShiftFun, norm_smul]
    exact mul_le_mul_of_nonneg_right (annularShiftScalar_norm_le power shift mode)
      (norm_nonneg _)
  calc
    _ ≤ (((1 + |(shift : ℝ)|) ^ power) *
        ‖field (angularModeTranslation shift mode)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) termBound 2
    _ = _ := mul_pow _ _ _

theorem annularRowShiftFun_memlp {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (shift : ℤ) (field : DivisionRow dimension lower) :
    Memℓp (annularRowShiftFun lower power shift field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  have reindexed : Summable (fun mode : ℤ × ℤ =>
      ‖field (angularModeTranslation shift mode)‖ ^ 2) :=
    (angularModeTranslation shift).summable_iff.mpr (divisionRow_sq_summable lower field)
  exact Summable.of_nonneg_of_le (fun mode => sq_nonneg _)
    (annularRowShiftFun_sq_bound lower power shift field)
    (reindexed.mul_left (((1 + |(shift : ℝ)|) ^ power) ^ 2))

def annularRowShiftLinear {dimension : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ) :
    DivisionRow dimension lower →ₗ[ℂ] DivisionRow dimension lower where
  toFun field := ⟨annularRowShiftFun lower power shift field,
    annularRowShiftFun_memlp lower power shift field⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change annularShiftScalar power shift mode •
        (scalar • field (angularModeTranslation shift mode)) =
      scalar • (annularShiftScalar power shift mode •
        field (angularModeTranslation shift mode))
    exact smul_comm (annularShiftScalar power shift mode) scalar _

theorem annularRowShiftLinear_norm_le {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (shift : ℤ) (field : DivisionRow dimension lower) :
    ‖annularRowShiftLinear lower power shift field‖ ≤
      (1 + |(shift : ℝ)|) ^ power * ‖field‖ := by
  have boundNonneg : 0 ≤ (1 + |(shift : ℝ)|) ^ power := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg boundNonneg (norm_nonneg _))).mp
  rw [divisionRow_norm_sq_raw, mul_pow, divisionRow_norm_sq_raw]
  have reindexed : Summable (fun mode : ℤ × ℤ =>
      ‖field (angularModeTranslation shift mode)‖ ^ 2) :=
    (angularModeTranslation shift).summable_iff.mpr (divisionRow_sq_summable lower field)
  have targetSummable := divisionRow_sq_summable lower
    (annularRowShiftLinear lower power shift field)
  calc
    ∑' mode : ℤ × ℤ, ‖annularRowShiftLinear lower power shift field mode‖ ^ 2
        ≤ ∑' mode : ℤ × ℤ, ((1 + |(shift : ℝ)|) ^ power) ^ 2 *
          ‖field (angularModeTranslation shift mode)‖ ^ 2 :=
      targetSummable.tsum_le_tsum
        (annularRowShiftFun_sq_bound lower power shift field)
        (reindexed.mul_left (((1 + |(shift : ℝ)|) ^ power) ^ 2))
    _ = ((1 + |(shift : ℝ)|) ^ power) ^ 2 *
        ∑' mode : ℤ × ℤ, ‖field (angularModeTranslation shift mode)‖ ^ 2 :=
      tsum_mul_left
    _ = ((1 + |(shift : ℝ)|) ^ power) ^ 2 *
        ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := by
      rw [(angularModeTranslation shift).tsum_eq (fun mode => ‖field mode‖ ^ 2)]

/-- Bounded multiplication by a fixed angular character on one weighted row. -/
def annularRowShift {dimension : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ) :
    DivisionRow dimension lower →L[ℂ] DivisionRow dimension lower :=
  LinearMap.mkContinuous (annularRowShiftLinear lower power shift)
    ((1 + |(shift : ℝ)|) ^ power)
    (annularRowShiftLinear_norm_le lower power shift)

@[simp] theorem annularRowShift_apply {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (shift : ℤ) (field : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    annularRowShift lower power shift field mode =
      annularShiftScalar power shift mode • field (mode.1 - shift, mode.2) := rfl

theorem annularRowShift_norm_le {dimension : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ) :
    ‖annularRowShift (dimension := dimension) lower power shift‖ ≤
      (1 + |(shift : ℝ)|) ^ power :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem annularRowUnitShift_norm_le {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (shift : ℤ) (unit : |shift| = 1) :
    ‖annularRowShift (dimension := dimension) lower power shift‖ ≤ (2 : ℝ) ^ power := by
  have castUnit : |(shift : ℝ)| = 1 := by
    simpa only [Int.cast_abs, Int.cast_one] using congrArg (fun value : ℤ => (value : ℝ)) unit
  simpa only [castUnit, one_add_one_eq_two] using
    annularRowShift_norm_le (dimension := dimension) lower power shift

end Grad.SourceCollarAngular
