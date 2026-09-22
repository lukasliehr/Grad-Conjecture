import AQR2LiteralRadialEnergy

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

def secondRadialCurve (lower : ℝ) (positive : 0 < lower) (mode : ℤ) (parameter : ℝ)
    (value slope forcing : C(ℝ, ComplexEuclidean 1)) : C(ℝ, ComplexEuclidean 1) :=
  ⟨fun radius => -(radialInverseRadiusCurve lower positive radius • slope radius) +
      ((mode : ℝ) ^ 2 * (radialInverseRadiusCurve lower positive radius) ^ 2) • value radius +
      (parameter ^ 2 * highMultiplier mode) • value radius - forcing radius,
    by fun_prop⟩

def actualRadialSecond (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) : C(ℝ, ComplexEuclidean 1) :=
  secondRadialCurve lower positive mode parameter (actualRadialValue lower positive bounded mode parameter source)
    (actualRadialSlope lower positive bounded mode parameter source) (diskCoreRadialCurve mode core)

theorem actualRadialSecond_eq_deriv (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) (high : mode ∉ lowAngularModes)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
        (Icc lower 1) radius = actualRadialSecond lower positive bounded mode parameter source core radius := by
  rw [actualRadial_second_eq lower positive bounded parameter source mode high core same radius inside,
    actualRadialSlope_eq_deriv lower positive bounded mode parameter source radius inside]
  simp only [actualRadialSecond, secondRadialCurve, radialInverseRadiusCurve, max_eq_right inside.1,
    ContinuousMap.coe_mk, highMultiplier_high mode high, Complex.coe_smul, div_eq_mul_inv, inv_pow]

theorem radialInverseRadiusCurve_bound (lower : ℝ) (positive : 0 < lower) (radius : ℝ) :
    0 ≤ radialInverseRadiusCurve lower positive radius ∧
      radialInverseRadiusCurve lower positive radius ≤ lower⁻¹ := by
  change 0 ≤ (max lower radius)⁻¹ ∧ (max lower radius)⁻¹ ≤ lower⁻¹
  constructor
  · exact inv_nonneg.mpr (positive.le.trans (le_max_left _ _))
  · simpa only [one_div] using one_div_le_one_div_of_le positive (le_max_left lower radius)

/-- The four coefficients are bounded independently of the angular cutoff;
the only angular growth is the displayed fourth power of the mode. -/
theorem secondRadialCurve_pointwise (lower : ℝ) (positive : 0 < lower) (mode : ℤ) (parameter : ℝ)
    (value slope forcing : C(ℝ, ComplexEuclidean 1)) (radius : ℝ) :
    ‖secondRadialCurve lower positive mode parameter value slope forcing radius‖ ^ 2 ≤
      4 * ((lower⁻¹) ^ 2 * ‖slope radius‖ ^ 2 +
        (mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 * ‖value radius‖ ^ 2 +
        parameter ^ 4 * ‖value radius‖ ^ 2 + ‖forcing radius‖ ^ 2) := by
  have raw := norm_four_sq
    (-(radialInverseRadiusCurve lower positive radius • slope radius))
    (((mode : ℝ) ^ 2 * (radialInverseRadiusCurve lower positive radius) ^ 2) • value radius)
    ((parameter ^ 2 * highMultiplier mode) • value radius) (-forcing radius)
  have square := pow_le_pow_left₀ (radialInverseRadiusCurve_bound lower positive radius).1
    (radialInverseRadiusCurve_bound lower positive radius).2 2
  have fourth := pow_le_pow_left₀ (radialInverseRadiusCurve_bound lower positive radius).1
    (radialInverseRadiusCurve_bound lower positive radius).2 4
  have multiplier := pow_le_pow_left₀ (highMultiplier_nonnegative mode) (highMultiplier_one_le mode) 2
  norm_num only [one_pow] at multiplier
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at raw
  have first := mul_le_mul_of_nonneg_right square (sq_nonneg ‖slope radius‖)
  have second := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left fourth (by positivity : 0 ≤ (mode : ℝ) ^ 4)) (sq_nonneg ‖value radius‖)
  have third := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left multiplier (by positivity : 0 ≤ parameter ^ 4)) (sq_nonneg ‖value radius‖)
  simp only [secondRadialCurve, ContinuousMap.coe_mk]
  norm_num only [← pow_mul] at raw
  rw [sub_eq_add_neg]
  exact raw.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add first second) (by simpa only [mul_one] using third)) le_rfl)
    (by norm_num : (0 : ℝ) ≤ 4))

end Grad.CircularHighRegularity
