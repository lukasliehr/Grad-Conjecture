import AKB1ConjugatedHighSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularFluxTrace Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem conjugatedFluxSection_bound (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    ‖annularFluxSection lower positive bounded field mode radius‖ ≤
      sourceEndpointConstant lower *
        (‖field.val.1 mode‖ + Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 * ‖field.val.2 mode‖) := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (annularFluxRadialGraph lower positive bounded field mode)
  exact ((annularFluxSection lower positive bounded field mode).norm_coe_le_norm radius).trans
    (representative.trans (mul_le_mul_of_nonneg_left
      (actualFluxMode_H1_bound lower positive bounded field mode) (Real.sqrt_nonneg _)))

theorem conjugatedFluxSection_physical (parameters : PhaseParameters)
    (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    Real.exp (radialPhase parameters radius.val mode.val.2) •
      actualFluxPhysicalSection lower positive bounded parameters field mode radius =
      annularFluxSection lower positive bounded field mode radius := by
  change Real.exp (radialPhase parameters radius.val mode.val.2) •
    (Real.exp (-radialPhase parameters radius.val mode.val.2) •
      annularFluxSection lower positive bounded field mode radius) = _
  rw [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

theorem conjugatedFluxSection_decay (grade : ℕ)
    (field weighted : annularFluxWeakGraph lower positive)
    (sameValue : ∀ mode : HighAnnularMode, weighted.val.1 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.1 mode)
    (sameSlope : ∀ mode : HighAnnularMode, weighted.val.2 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.2 mode)
    (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      annularFluxSection lower positive bounded field mode radius‖ ≤
      (sourceEndpointConstant lower * (‖weighted.val.1‖ + ‖weighted.val.2‖)) *
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹ := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have frequencyOne : 1 ≤ frequency := annularFrequency_one_le _ _
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have highValue : frequency ^ (grade + 5) * ‖field.val.1 mode‖ ≤ ‖weighted.val.1‖ := by
    have point := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) weighted.val.1 mode
    rw [sameValue, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)] at point
    exact point
  have highSlope : frequency ^ (grade + 5) * ‖field.val.2 mode‖ ≤ ‖weighted.val.2‖ := by
    have point := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) weighted.val.2 mode
    rw [sameSlope, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)] at point
    exact point
  have lowerValue : frequency ^ (grade + 4) * ‖field.val.1 mode‖ ≤ ‖weighted.val.1‖ := by
    apply le_trans _ highValue
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ frequencyOne (by omega : grade + 4 ≤ grade + 5)) (norm_nonneg _)
  have value := frequency_rescale frequency frequencyPositive grade 4 _ _ lowerValue
  have slope := frequency_rescale frequency frequencyPositive (grade + 1) 4 _ _
    (by simpa only [Nat.add_assoc] using highSlope)
  have sum := add_le_add value slope
  rw [pow_succ] at sum
  have scaled := mul_le_mul_of_nonneg_left sum (show 0 ≤ sourceEndpointConstant lower from Real.sqrt_nonneg _)
  dsimp only [frequency] at scaled
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)]
  exact (mul_le_mul_of_nonneg_left
    (conjugatedFluxSection_bound lower positive bounded field mode radius)
    (pow_nonneg frequencyPositive.le grade)).trans
    (by simpa only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using scaled)

end Grad.AnnularWeightedSmoothCore
