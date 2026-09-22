import AEF3ExponentialMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph

/-- Scaled inner profile. Its decay width is `lower/nu`, while the affine
factor preserves the inner value and makes the outer value exactly zero. -/
def uniformInnerLiftProfile (lower : ℝ) (mode : HighAnnularMode) (radius : ℝ) : ℝ :=
  ((1 - radius) / (1 - lower)) *
    Real.exp (-(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
      (radius - lower)) /
    Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)

theorem uniformInnerLiftProfile_smooth (lower : ℝ) (mode : HighAnnularMode) :
    ContDiff ℝ ∞ (uniformInnerLiftProfile lower mode) := by
  unfold uniformInnerLiftProfile
  fun_prop

theorem uniformInnerLiftProfile_inner (lower : ℝ) (_positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) :
    uniformInnerLiftProfile lower mode lower =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ := by
  have collar : lower < 1 := lowerHalf.trans_lt (by norm_num)
  unfold uniformInnerLiftProfile
  rw [sub_self, mul_zero, Real.exp_zero, mul_one, div_eq_mul_inv]
  have ratio : (1 - lower) * (1 - lower)⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_ne_zero.mpr collar.ne')
  change ((1 - lower) * (1 - lower)⁻¹) *
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ = _
  rw [ratio, one_mul]

@[simp] theorem uniformInnerLiftProfile_outer (lower : ℝ) (mode : HighAnnularMode) :
    uniformInnerLiftProfile lower mode 1 = 0 := by
  unfold uniformInnerLiftProfile
  rw [sub_self, zero_div, zero_mul, zero_div]

theorem uniformInnerLiftProfile_deriv (lower : ℝ) (mode : HighAnnularMode) (radius : ℝ) :
    deriv (uniformInnerLiftProfile lower mode) radius =
      -(1 / (1 - lower) + ((1 - radius) / (1 - lower)) *
          (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower)) *
        Real.exp (-(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
          (radius - lower)) /
        Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have affine := ((hasDerivAt_const radius 1).sub (hasDerivAt_id radius)).div_const (1 - lower)
  have exponent := (((hasDerivAt_id radius).sub_const lower).const_mul (-(frequency / lower))).exp
  have product := (affine.mul exponent).div_const (Real.sqrt frequency)
  have literal := product.deriv
  change deriv (uniformInnerLiftProfile lower mode) radius = _ at literal
  rw [literal]
  dsimp only [frequency]
  simp only [Pi.sub_apply, id_eq]
  ring

private theorem uniformInnerAffine_range (lower radius : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (inside : radius ∈ Icc lower 1) :
    0 ≤ (1 - radius) / (1 - lower) ∧ (1 - radius) / (1 - lower) ≤ 1 := by
  have denominator : 0 < 1 - lower := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr inside.2) denominator.le
  · exact (div_le_one denominator).2 (by linarith [inside.1])

theorem uniformInnerLiftProfile_abs_bound (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    |uniformInnerLiftProfile lower mode radius| ≤
      Real.exp (-(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
        (radius - lower)) /
      Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) := by
  have affine := uniformInnerAffine_range lower radius positive lowerHalf inside
  have frequencyPositive : 0 < Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 :=
    zero_lt_one.trans_le (Grad.AnnularVariational.annularFrequency_one_le _ _)
  unfold uniformInnerLiftProfile
  rw [abs_div, abs_mul, abs_of_nonneg affine.1, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (Real.exp_pos _).le affine.2) (Real.sqrt_nonneg _)

theorem uniformInnerLiftProfile_deriv_bound (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    |deriv (uniformInnerLiftProfile lower mode) radius| ≤
      (2 * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
        Real.exp (-(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / lower) *
          (radius - lower)) /
        Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have frequencyOne : 1 ≤ frequency := Grad.AnnularVariational.annularFrequency_one_le _ _
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have affine := uniformInnerAffine_range lower radius positive lowerHalf inside
  have denominator : 0 < 1 - lower := by linarith
  have reciprocalBound : 1 / (1 - lower) ≤ 2 := by
    apply (div_le_iff₀ denominator).2
    linarith
  have ratioPositive : 0 ≤ frequency / lower := (div_pos frequencyPositive positive).le
  have ratioTwo : 2 ≤ frequency / lower := by
    apply (le_div_iff₀ positive).2
    nlinarith
  have coefficientNonnegative : 0 ≤
      1 / (1 - lower) + (1 - radius) / (1 - lower) * (frequency / lower) :=
    add_nonneg (div_pos (by norm_num) denominator |>.le) (mul_nonneg affine.1 ratioPositive)
  have coefficientBound :
      1 / (1 - lower) + (1 - radius) / (1 - lower) * (frequency / lower) ≤
        2 * frequency / lower := by
    have productBound := mul_le_of_le_one_left ratioPositive affine.2
    calc
      _ ≤ 2 + frequency / lower := add_le_add reciprocalBound productBound
      _ ≤ frequency / lower + frequency / lower := by nlinarith
      _ = 2 * frequency / lower := by ring
  rw [uniformInnerLiftProfile_deriv, abs_div, abs_mul, abs_neg,
    abs_of_nonneg coefficientNonnegative, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientBound (Real.exp_pos _).le)
    (Real.sqrt_nonneg _)

/-- Actual smooth AAG core generated by the scaled profile. -/
def uniformInnerLiftMode (lower : ℝ) (mode : HighAnnularMode) :
    ComplexEuclidean 1 →ₗ[ℂ] complexSmoothRadialCore 1 :=
  smoothScalarRadialCore (uniformInnerLiftProfile lower mode)
    (uniformInnerLiftProfile_smooth lower mode)

@[simp] theorem uniformInnerLiftMode_inner (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
      (uniformInnerLiftMode lower mode vector).val.1 lower = vector := by
  rw [show (uniformInnerLiftMode lower mode vector).val.1 lower =
    uniformInnerLiftProfile lower mode lower • vector from rfl,
    uniformInnerLiftProfile_inner lower positive lowerHalf]
  change Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) •
    ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ • vector) = vector
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr
    (zero_lt_one.trans_le (Grad.AnnularVariational.annularFrequency_one_le _ _))).ne', one_smul]

@[simp] theorem uniformInnerLiftMode_outer (lower : ℝ) (mode : HighAnnularMode)
    (vector : ComplexEuclidean 1) :
    (uniformInnerLiftMode lower mode vector).val.1 1 = 0 := by
  change uniformInnerLiftProfile lower mode 1 • vector = 0
  rw [uniformInnerLiftProfile_outer, zero_smul]

end Grad.AnnularUniformBoundary
