import AKB3ConjugatedLowSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.GaugeCoefficients.Physical.WeightedTrace

theorem conjugatedLowSection_decay (parameters : PhaseParameters)
    (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (grade : ℕ) (field weighted : lowEnergyGraph lower length positive)
    (same : ∀ (component : Fin 2) (index : LowAnnularIndex), weighted.val component index =
      ((Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ (grade + 5) : ℝ) : ℂ) •
        field.val component index)
    (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    ‖((Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ grade : ℝ) : ℂ) •
      conjugatedLowSection parameters lower length positive bounded field index radius‖ ≤
      ((2 * sourceEndpointConstant lower) *
        (‖weighted.val 0‖ + (length⁻¹ + lower⁻¹) * ‖weighted.val 1‖)) *
          (Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ 4)⁻¹ := by
  let frequency := Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2
  have frequencyOne : 1 ≤ frequency := annularFrequency_one_le _ _
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have high (component : Fin 2) : frequency ^ (grade + 5) * ‖field.val component index‖ ≤ ‖weighted.val component‖ := by
    have point := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (weighted.val component) index
    rw [same, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)] at point
    exact point
  have lowerValue : frequency ^ (grade + 4) * ‖field.val 0 index‖ ≤ ‖weighted.val 0‖ :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ frequencyOne (by omega : grade + 4 ≤ grade + 5)) (norm_nonneg _)).trans (high 0)
  have value := frequency_rescale frequency frequencyPositive grade 4 _ _ lowerValue
  have slope := frequency_rescale frequency frequencyPositive (grade + 1) 4 _ _
    (by simpa only [Nat.add_assoc] using high 1)
  have factorNonnegative : 0 ≤ length⁻¹ + lower⁻¹ := add_nonneg (inv_nonneg.mpr lengthPositive.le) (inv_nonneg.mpr positive.le)
  have scaledSlope := mul_le_mul_of_nonneg_left slope factorNonnegative
  rw [pow_succ] at scaledSlope
  have sum := add_le_add value scaledSlope
  have scaled := mul_le_mul_of_nonneg_left sum (show 0 ≤ 2 * sourceEndpointConstant lower from mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have raw := conjugatedLowSection_bound parameters lower length positive bounded field index radius
  have mu := mul_le_mul_of_nonneg_right (actualLowMu_frequency_bound lower length positive lengthPositive index) (norm_nonneg (field.val 1 index))
  have rawFrequency := raw.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl mu)
    (show 0 ≤ 2 * sourceEndpointConstant lower from mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  dsimp only [frequency] at scaled
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)]
  exact (mul_le_mul_of_nonneg_left rawFrequency (pow_nonneg frequencyPositive.le grade)).trans
    (by simpa only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using scaled)

end Grad.AnnularWeightedSmoothCore
