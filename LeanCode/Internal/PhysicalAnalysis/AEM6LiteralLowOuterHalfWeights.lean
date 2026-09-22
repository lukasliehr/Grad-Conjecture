import AEM5ActualOuterFrequencyComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowOuterNegativeFactor (length : ℝ) (mode : LowAnnularMode) : ℝ :=
  Real.sqrt (lowMu length (1 / 2) mode.val.2) / Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)

def lowOuterPositiveFactor (parameters : PhaseParameters) (length : ℝ) (mode : LowAnnularMode) : ℝ :=
  (lowAmplitude length parameters.gamma mode)⁻¹ *
    (Real.sqrt (lowMu length (1 / 2) mode.val.2) * Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) /
      lowMu length 1 mode.val.2)

theorem lowOuterNegativeFactor_bound (length : ℝ) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    |lowOuterNegativeFactor length mode| ≤ lowOuterFrequencyConstant length := by
  have frequencyPositive : 0 < Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 :=
    zero_lt_one.trans_le (Grad.AnnularVariational.annularFrequency_one_le _ _)
  have constant := lowOuterFrequencyConstant_two_le length lengthPositive
  have bound := lowMu_half_le_frequency length lengthPositive mode
  unfold lowOuterNegativeFactor
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr frequencyPositive)).mpr
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (lowMu_nonneg _ _ _), Real.sq_sqrt frequencyPositive.le]
  have square : lowOuterFrequencyConstant length ≤ lowOuterFrequencyConstant length ^ 2 := by nlinarith
  exact bound.trans (mul_le_mul_of_nonneg_right square frequencyPositive.le)

theorem lowOuterPositiveFactor_bound (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    |lowOuterPositiveFactor parameters length mode| ≤ 2 * lowOuterFrequencyConstant length := by
  let nu := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  let mu := lowMu length 1 mode.val.2
  let half := lowMu length (1 / 2) mode.val.2
  let constant := lowOuterFrequencyConstant length
  have nuPositive : 0 < nu := zero_lt_one.trans_le (Grad.AnnularVariational.annularFrequency_one_le _ _)
  have muPositive : 0 < mu := lowMu_pos length 1 mode.val.2 zero_lt_one
  have halfNonnegative : 0 ≤ half := lowMu_nonneg _ _ _
  have constantTwo : 2 ≤ constant := lowOuterFrequencyConstant_two_le length lengthPositive
  have product : half * nu ≤ (constant * mu) ^ 2 := by
    have first : half ≤ 2 * mu := lowMu_half_le_two_outer length mode.val.2
    have second : nu ≤ constant * mu := lowFrequency_le_outerMu length lengthPositive mode
    have multiplied := mul_le_mul first second nuPositive.le (by positivity : 0 ≤ 2 * mu)
    have extra := mul_nonneg (show 0 ≤ constant ^ 2 - 2 * constant by nlinarith) (sq_nonneg mu)
    nlinarith
  have root : Real.sqrt half * Real.sqrt nu ≤ constant * mu := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg (by linarith) muPositive.le)).mp
    rw [mul_pow, Real.sq_sqrt halfNonnegative, Real.sq_sqrt nuPositive.le]
    exact product
  have quotient : Real.sqrt half * Real.sqrt nu / mu ≤ constant := (div_le_iff₀ muPositive).mpr root
  have quotientNonnegative : 0 ≤ Real.sqrt half * Real.sqrt nu / mu := by positivity
  change |(lowAmplitude length parameters.gamma mode)⁻¹ * (Real.sqrt half * Real.sqrt nu / mu)| ≤ _
  rw [abs_mul, abs_of_nonneg quotientNonnegative]
  exact mul_le_mul (lowAmplitude_inverse_bound length parameters.gamma mode) quotient quotientNonnegative (by norm_num)

end Grad.AnnularCrossMaps
