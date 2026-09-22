import SCC23RadialSeparation
import PA5PhaseConsumer

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular
open Grad.PhaseAlgebra

def productTranslation (shift : ℤ × ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mode := mode - shift
  invFun mode := mode + shift
  left_inv mode := sub_add_cancel mode shift
  right_inv mode := add_sub_cancel_right mode shift

theorem productFrequency_additive (mode shift : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ≤
      annularFrequency (mode - shift).1 (mode - shift).2 + annularFrequency shift.1 shift.2 := by
  have first : |(mode.1 : ℝ)| ≤ |((mode.1 - shift.1 : ℤ) : ℝ)| + |(shift.1 : ℝ)| := by
    simpa only [Int.cast_sub, sub_add_cancel] using
      abs_add_le ((mode.1 : ℝ) - (shift.1 : ℝ)) (shift.1 : ℝ)
  have second : |(mode.2 : ℝ)| ≤ |((mode.2 - shift.2 : ℤ) : ℝ)| + |(shift.2 : ℝ)| := by
    simpa only [Int.cast_sub, sub_add_cancel] using
      abs_add_le ((mode.2 : ℝ) - (shift.2 : ℝ)) (shift.2 : ℝ)
  change 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)| ≤
    (1 + |((mode.1 - shift.1 : ℤ) : ℝ)| + |((mode.2 - shift.2 : ℤ) : ℝ)|) +
      (1 + |(shift.1 : ℝ)| + |(shift.2 : ℝ)|)
  linarith

theorem productFrequency_power (power : ℕ) (mode shift : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ^ power ≤ (2 : ℝ) ^ power *
      (annularFrequency (mode - shift).1 (mode - shift).2 ^ power +
        annularFrequency shift.1 shift.2 ^ power) := by
  let first := annularFrequency (mode - shift).1 (mode - shift).2
  let second := annularFrequency shift.1 shift.2
  have firstNonnegative : 0 ≤ first := annularFrequency_nonnegative _ _
  have secondNonnegative : 0 ≤ second := annularFrequency_nonnegative _ _
  have maximum : annularFrequency mode.1 mode.2 ≤ 2 * max first second := by
    have := productFrequency_additive mode shift
    have := le_max_left first second
    have := le_max_right first second
    dsimp [first, second] at *
    linarith
  calc
    _ ≤ (2 * max first second) ^ power :=
      pow_le_pow_left₀ (annularFrequency_nonnegative _ _) maximum power
    _ = (2 : ℝ) ^ power * (max first second) ^ power := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ power * (first ^ power + second ^ power) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total first second with inequality | inequality
      · rw [max_eq_right inequality]
        linarith [pow_nonneg firstNonnegative power]
      · rw [max_eq_left inequality]
        linarith [pow_nonneg secondNonnegative power]

def balancedProductRatio (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) : ℝ :=
  Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) *
    annularFrequency mode.1 mode.2 ^ power /
      (annularFrequency (mode - shift).1 (mode - shift).2 ^ power + annularFrequency shift.1 shift.2 ^ power)

def productPhaseConstant (parameters : PhaseParameters) (power : ℕ) : ℝ :=
  (2 : ℝ) ^ power * Real.exp (parameters.sigma0 + parameters.gamma)

theorem productPhaseConstant_pos (parameters : PhaseParameters) (power : ℕ) :
    0 < productPhaseConstant parameters power := by unfold productPhaseConstant; positivity

theorem balancedProductRatio_nonnegative (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) : 0 ≤ balancedProductRatio parameters power radius shift mode := by
  unfold balancedProductRatio
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (annularFrequency_nonnegative _ _) _))
    (add_nonneg (pow_nonneg (annularFrequency_nonnegative _ _) _) (pow_nonneg (annularFrequency_nonnegative _ _) _))

theorem balancedProductRatio_bound (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (shift mode : ℤ × ℤ) :
    balancedProductRatio parameters power radius shift mode ≤
      productPhaseConstant parameters power * coefficientRadialEnvelope parameters shift.2 radius := by
  have phase := (exp_radialPhase_ratio parameters radius nonnegative bounded mode.2 (mode - shift).2).trans
    (exp_radialPhase_le parameters radius nonnegative bounded (mode.2 - (mode - shift).2))
  have difference : mode.2 - (mode - shift).2 = shift.2 := by simp
  rw [difference] at phase
  have frequency := productFrequency_power power mode shift
  have positiveDenominator : 0 <
      annularFrequency (mode - shift).1 (mode - shift).2 ^ power + annularFrequency shift.1 shift.2 ^ power :=
    add_pos (pow_pos (annularFrequency_pos _ _) _) (pow_pos (annularFrequency_pos _ _) _)
  rw [balancedProductRatio, div_le_iff₀ positiveDenominator]
  exact (mul_le_mul phase frequency (pow_nonneg (annularFrequency_nonnegative _ _) _)
    (mul_nonneg (Real.exp_pos _).le (phaseWeight_pos _ _ _).le)).trans_eq (by
      dsimp [productPhaseConstant, coefficientRadialEnvelope, phaseWeight, phaseWidth]
      ring)

theorem balancedProductRatio_continuous (parameters : PhaseParameters) (power : ℕ)
    (shift mode : ℤ × ℤ) : Continuous (fun radius => balancedProductRatio parameters power radius shift mode) := by
  unfold balancedProductRatio radialPhase
  fun_prop

end Grad.SourceCollarCoefficients
