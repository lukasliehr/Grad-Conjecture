import AAG6ActualCoerciveForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational Grad.CircularHighWeak
open Grad.ActualReferenceAssembly

/-- The manuscript's fixed high radial exponent. -/
def annularTiltExponent : ℝ := 9 / 4

theorem phase_radius_square_bound (parameters : PhaseParameters) (length radius : ℝ)
    (mode cell : ℤ) (lengthPositive : 0 < length) (radiusPositive : 0 < radius)
    (radiusUpper : radius ≤ 1) (high : 3 ≤ |mode|)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    (radius * annularPhaseSlope parameters cell radius) ^ 2 ≤
      (1 / 4 : ℝ) * (1 + highMultiplier mode * ((cell : ℝ) * radius / length) ^ 2) := by
  have gammaNonnegative := parameters.gamma_pos.le
  have gammaSq : parameters.gamma ^ 2 ≤ 1 / 4 := by nlinarith
  have width := (le_div_iff₀ (by positivity : 0 < 6 * length)).mp widthLength
  have sqrtFive : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have gammaLength : parameters.gamma ^ 2 * length ^ 2 ≤ 5 / 36 := by
    have squared := mul_self_le_mul_self (by positivity : 0 ≤ parameters.gamma * (6 * length)) width
    nlinarith only [squared, sqrtFive]
  have multiplier := (highMultiplier_bounds mode (highMode_not_low mode high)).1
  have gammaMultiplier : parameters.gamma ^ 2 * length ^ 2 ≤ (1 / 4 : ℝ) * highMultiplier mode := by
    linarith
  have cellPart : parameters.gamma ^ 2 * ((cell : ℝ) * radius) ^ 2 ≤
      (1 / 4 : ℝ) * highMultiplier mode * ((cell : ℝ) * radius / length) ^ 2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right gammaMultiplier (sq_nonneg ((cell : ℝ) * radius))]
  have radialPart : parameters.gamma ^ 2 * radius ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg parameters.gamma, mul_nonneg (sq_nonneg parameters.gamma)
      (show 0 ≤ 1 - radius ^ 2 by nlinarith)]
  have slope := mul_le_mul_of_nonneg_left (annularPhaseSlope_sq_le parameters cell radius) (sq_nonneg radius)
  nlinarith only [slope, radialPart, cellPart]

/-- Exact BF9 arithmetic. The positive 105/176 margin retains both low
high-sector angular modes and zero cell frequency without narrowing width. -/
theorem tilted_potential_arithmetic (modeSquare transverse damping : ℝ)
    (high : 9 ≤ modeSquare) (phase : damping ^ 2 ≤ (1 + transverse) / 4) :
    (9 / 4 + damping) ^ 2 + (105 / 176 : ℝ) ≤
      (15 / 16 : ℝ) * (modeSquare + transverse) := by
  nlinarith [sq_nonneg (damping - 9 / 11)]

/-- The actual tilted phase loses at most 15/16 of the original potential. -/
theorem annularTiltSlope_dominated (parameters : PhaseParameters) (length radius : ℝ)
    (mode cell : ℤ) (lengthPositive : 0 < length) (radiusPositive : 0 < radius)
    (radiusUpper : radius ≤ 1) (high : 3 ≤ |mode|)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    (annularTiltExponent / radius - annularPhaseSlope parameters cell radius) ^ 2 ≤
      (15 / 16 : ℝ) * annularPotential length radius mode cell := by
  have modeBound : (3 : ℝ) ≤ |(mode : ℝ)| := by exact_mod_cast high
  have modeSquare : (9 : ℝ) ≤ (mode : ℝ) ^ 2 := by nlinarith [sq_abs (mode : ℝ)]
  have phase := phase_radius_square_bound parameters length radius mode cell lengthPositive
    radiusPositive radiusUpper high widthHalf widthLength
  have estimate := tilted_potential_arithmetic ((mode : ℝ) ^ 2)
    (highMultiplier mode * ((cell : ℝ) * radius / length) ^ 2)
    (-radius * annularPhaseSlope parameters cell radius) modeSquare (by nlinarith only [phase])
  have scaled : (annularTiltExponent / radius - annularPhaseSlope parameters cell radius) ^ 2 * radius ^ 2 =
      (9 / 4 - radius * annularPhaseSlope parameters cell radius) ^ 2 := by
    unfold annularTiltExponent
    field_simp
  have potential : annularPotential length radius mode cell * radius ^ 2 =
      (mode : ℝ) ^ 2 + highMultiplier mode * ((cell : ℝ) * radius / length) ^ 2 := by
    unfold annularPotential
    field_simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos radiusPositive)).mp
  rw [scaled, mul_assoc, potential]
  nlinarith only [estimate]

end Grad.AnnularTiltedReference
