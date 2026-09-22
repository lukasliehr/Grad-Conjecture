import AEN6ActualRadialBounds

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterBounds Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.CollarCartesian Grad.ActualRadialWords Grad.BoundaryLift
open Grad.GaugeCoefficients.Algebra

theorem smallMode_word_integral (mode : ℤ) (small : |(mode : ℝ)| ≤ 2)
    (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order target : ℕ) (paid : order ≤ target) (word : CartesianWord order) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖centerWordRows profile order word mode time‖ ^ 2) ≤
      (2 * (2 : ℝ) ^ (2 * target)) * radialWithinEnergy (1 / 2) (wordCount word 0) profile := by
  have continuousDensity := (smooth.continuousOn_iteratedDerivWithin
    (m := wordCount word 0) (by exact_mod_cast (le_top : (wordCount word 0 : ℕ∞) ≤ ⊤))
    (uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1))).norm.pow 2
  have radial := reflected_integral_le_radial _ continuousDensity (fun _ _ => sq_nonneg _)
  have counts := wordCount_total word
  have coefficient : |(mode : ℝ)| ^ (2 * wordCount word 1) ≤ (2 : ℝ) ^ (2 * target) :=
    (pow_le_pow_left₀ (abs_nonneg _) small _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  simp only [centerWordRows, wordAmplitude_norm_sq]
  rw [intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left radial (pow_nonneg (abs_nonneg _) _)).trans
    ((mul_le_mul_of_nonneg_right coefficient (mul_nonneg (by norm_num)
      (radialWithinEnergy_nonnegative (1 / 2) (by norm_num) (by norm_num) _ _))).trans_eq (by ring))

theorem signedProfile_mixedRows (grade : ℕ) (datum : SignedEquationDatum)
    (target : ℕ) (paid : target ≤ grade + 1) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowsDensity {datum.mode}
      (centerWordRows (pureProfile datum.mode datum.field)) target time) ≤
        (2 * centerMixedRowFactor target * (2 : ℝ) ^ (2 * target) * signedProfileConstant grade) *
          signedNativeSize grade datum ^ 2 := by
  have estimate := centerMixedRows_integral_bound datum.mode _ (pureProfile_smooth datum.mode datum.field).contDiffOn target
    ((2 * (2 : ℝ) ^ (2 * target)) * (signedProfileConstant grade * signedNativeSize grade datum ^ 2)) (by
      intro current currentBound word
      have counts := wordCount_total word
      exact (smallMode_word_integral datum.mode datum.small _ (pureProfile_smooth datum.mode datum.field).contDiffOn
        current target currentBound word).trans (mul_le_mul_of_nonneg_left
          (signedProfile_allRadial grade datum (wordCount word 0) (by omega)) (by positivity)))
  exact estimate.trans_eq (by ring)

def signedOuterSquaredConstant (grade target : ℕ) : ℝ :=
  centerOuterNativeFactor target * (2 : ℝ) ^ (2 * target) * signedProfileConstant grade

theorem signedOuterSquaredConstant_nonnegative (grade target : ℕ) : 0 ≤ signedOuterSquaredConstant grade target :=
  mul_nonneg (mul_nonneg (centerOuterNativeFactor_nonnegative target) (by positivity)) (signedProfileConstant_nonnegative grade)

theorem signedProfile_outer_squared (grade : ℕ) (datum : SignedEquationDatum) (target : ℕ) (paid : target ≤ grade + 1) :
    ‖unitDiskCoreInto target (centerOuterJet datum.mode datum.field)‖ ^ 2 ≤
      signedOuterSquaredConstant grade target * signedNativeSize grade datum ^ 2 := by
  rw [unitDiskSobolev_norm_sq]
  simp only [unitDiskDerivative_core]
  unfold signedOuterSquaredConstant centerOuterNativeFactor
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  have row := (centerOuterJet_mixedRows_bound (derivativeMultiIndex index)).choose_spec.2 datum.mode datum.field
  have mixed := signedProfile_mixedRows grade datum (cartesianOrder (derivativeMultiIndex index)) (le_trans index.property paid)
  have coefficient : (2 : ℝ) ^ (2 * cartesianOrder (derivativeMultiIndex index)) ≤ (2 : ℝ) ^ (2 * target) :=
    pow_le_pow_right₀ (by norm_num) (by have orderBound : cartesianOrder (derivativeMultiIndex index) ≤ target := index.property; omega)
  have mixedBound := mixed.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficient
      (mul_nonneg (by norm_num) (centerMixedRowFactor_nonnegative _))) (signedProfileConstant_nonnegative grade))
    (sq_nonneg _))
  exact (row.trans (mul_le_mul_of_nonneg_left mixedBound (centerOuterRowConstant_nonnegative _))).trans_eq
    (by unfold centerOuterRowConstant; ring)

def signedOuterConstant (grade target : ℕ) : ℝ := Real.sqrt (signedOuterSquaredConstant grade target)

theorem signedOuterConstant_nonnegative (grade target : ℕ) : 0 ≤ signedOuterConstant grade target := Real.sqrt_nonneg _

theorem signedProfile_outer_native (grade : ℕ) (datum : SignedEquationDatum) (target : ℕ) (paid : target ≤ grade + 1) :
    ‖unitDiskCoreInto target (centerOuterJet datum.mode datum.field)‖ ≤
      signedOuterConstant grade target * signedNativeSize grade datum := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (signedOuterConstant_nonnegative grade target)
    (signedNativeSize_nonnegative grade datum))).mp
  rw [mul_pow, signedOuterConstant, Real.sq_sqrt (signedOuterSquaredConstant_nonnegative grade target)]
  exact signedProfile_outer_squared grade datum target paid

end Grad.ExceptionalNative
