import AFI2ActualBoundaryMultiplier
import ASG8OriginalPhaseNormalization

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.AnnularVariational

open Grad.CartesianState Grad.PhaseAlgebra Grad.CircularHighWeak
open Grad.ActualReferenceAssembly

/-- The exact potential in AG7, with every cell retained. -/
def annularPotential (length radius : ℝ) (mode cell : ℤ) : ℝ :=
  (mode : ℝ) ^ 2 / radius ^ 2 + highMultiplier mode * (cell : ℝ) ^ 2 / length ^ 2

def annularFrequency (mode cell : ℤ) : ℝ := 1 + |(mode : ℝ)| + |(cell : ℝ)|

/-- The derivative of the original curved phase, not its linear envelope. -/
def annularPhaseSlope (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) : ℝ :=
  -parameters.gamma * (cellFrequency cell ^ 2 * radius /
    Real.sqrt (1 + cellFrequency cell ^ 2 * radius ^ 2))

theorem radialPhase_hasDerivAt (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) :
    HasDerivAt (fun point => radialPhase parameters point cell)
      (annularPhaseSlope parameters cell radius) radius := by
  have polynomial : HasDerivAt (fun point : ℝ => 1 + cellFrequency cell ^ 2 * point ^ 2)
      (cellFrequency cell ^ 2 * (2 * radius)) radius := by
    simpa only [Function.comp_def, Pi.pow_apply, id_eq, show 2 - 1 = 1 from rfl, pow_one, mul_one, Nat.cast_ofNat] using
      (((hasDerivAt_id radius).pow 2).const_mul (cellFrequency cell ^ 2)).const_add 1
  have positive : 0 < 1 + cellFrequency cell ^ 2 * radius ^ 2 := by positivity
  have root := polynomial.sqrt positive.ne'
  have slopeEquality : annularPhaseSlope parameters cell radius =
      -(parameters.gamma * (cellFrequency cell ^ 2 * (2 * radius) /
        (2 * Real.sqrt (1 + cellFrequency cell ^ 2 * radius ^ 2)))) := by
    unfold annularPhaseSlope
    field_simp
  rw [slopeEquality]
  exact ((root.sub_const 1).const_mul parameters.gamma).const_sub
    (parameters.sigma0 * cellFrequency cell)

theorem annularPhaseSlope_sq_le (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) :
    annularPhaseSlope parameters cell radius ^ 2 ≤
      parameters.gamma ^ 2 * (1 + (cell : ℝ) ^ 2) := by
  have frequencySq : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  have denominator : 0 < 1 + cellFrequency cell ^ 2 * radius ^ 2 := by positivity
  unfold annularPhaseSlope
  rw [mul_pow, neg_sq, div_pow, Real.sq_sqrt denominator.le, mul_pow, ← mul_div_assoc]
  apply (div_le_iff₀ denominator).2
  rw [frequencySq]
  nlinarith [sq_nonneg parameters.gamma, sq_nonneg (cell : ℝ), sq_nonneg radius]

theorem annularPotential_nine_le (length radius : ℝ) (mode cell : ℤ)
    (high : 3 ≤ |mode|) (positive : 0 < radius) (upper : radius ≤ 1) :
    9 ≤ annularPotential length radius mode cell := by
  have modeBound : (3 : ℝ) ≤ |(mode : ℝ)| := by exact_mod_cast high
  have modeSq : 9 ≤ (mode : ℝ) ^ 2 := by nlinarith [sq_abs (mode : ℝ)]
  have radiusSq : radius ^ 2 ≤ 1 := by nlinarith
  have first : 9 ≤ (mode : ℝ) ^ 2 / radius ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos positive)).2 (by nlinarith)
  have second : 0 ≤ highMultiplier mode * (cell : ℝ) ^ 2 / length ^ 2 := by
    exact div_nonneg (mul_nonneg (highMultiplier_nonnegative mode) (sq_nonneg _)) (sq_nonneg _)
  unfold annularPotential
  linarith

/-- AG11, from exactly the two numerical width restrictions in AG10. -/
theorem annularPhaseSlope_dominated (parameters : PhaseParameters) (length radius : ℝ)
    (mode cell : ℤ) (lengthPositive : 0 < length) (radiusPositive : 0 < radius)
    (radiusUpper : radius ≤ 1) (high : 3 ≤ |mode|)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    annularPhaseSlope parameters cell radius ^ 2 ≤
      (1 / 4 : ℝ) * annularPotential length radius mode cell := by
  have gammaNonneg := parameters_gamma_nonnegative parameters
  have gammaSq : parameters.gamma ^ 2 ≤ 1 / 4 := by nlinarith
  have width := (le_div_iff₀ (by positivity : 0 < 6 * length)).1 widthLength
  have sqrtFive : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have gammaLength : parameters.gamma ^ 2 * length ^ 2 ≤ 5 / 36 := by
    have squared := mul_self_le_mul_self (by positivity : 0 ≤ parameters.gamma * (6 * length)) width
    nlinarith only [squared, sqrtFive]
  have multiplier := (highMultiplier_bounds mode (highMode_not_low mode high)).1
  have cellPart : parameters.gamma ^ 2 * (cell : ℝ) ^ 2 ≤
      (1 / 4 : ℝ) * (highMultiplier mode * (cell : ℝ) ^ 2 / length ^ 2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos lengthPositive)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr multiplier) (sq_nonneg (cell : ℝ)),
      mul_nonneg (sub_nonneg.mpr gammaLength) (sq_nonneg (cell : ℝ))]
  have modeBound : (3 : ℝ) ≤ |(mode : ℝ)| := by exact_mod_cast high
  have first : (1 : ℝ) ≤ (mode : ℝ) ^ 2 / radius ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos radiusPositive)).2
    nlinarith [sq_abs (mode : ℝ)]
  have slope := annularPhaseSlope_sq_le parameters cell radius
  unfold annularPotential
  nlinarith

end Grad.AnnularVariational
