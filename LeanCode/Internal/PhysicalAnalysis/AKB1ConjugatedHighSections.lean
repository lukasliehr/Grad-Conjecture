import AJU12ExactSameRawPhysicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- The genuine high H1 section before removal of the original analytic
phase. This is already an accepted graph representative. -/
def conjugatedHighSection (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    RadialContinuousSection 1 lower :=
  weightedRadialSection 1 lower positive bounded (annularModeRadialH1 lower length positive mode field)

theorem conjugatedHighSection_bound (field : annularEnergySpace lower length positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    ‖conjugatedHighSection lower length positive bounded field mode radius‖ ≤
      (2 * sourceEndpointConstant lower) * ‖field.val mode‖ := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (annularModeRadialH1 lower length positive mode field)
  exact ((conjugatedHighSection lower length positive bounded field mode).norm_coe_le_norm radius).trans
    ((representative.trans (mul_le_mul_of_nonneg_left
      (actualEnergyMode_H1_bound lower length positive field mode) (Real.sqrt_nonneg _))).trans_eq (by ring))

/-- Literal equality to exp(Phi) times the SAME physical high section. -/
theorem conjugatedHighSection_physical (parameters : PhaseParameters)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    Real.exp (radialPhase parameters radius.val mode.val.2) •
      annularPhysicalValueSection parameters lower length positive bounded mode field radius =
      conjugatedHighSection lower length positive bounded field mode radius := by
  change Real.exp (radialPhase parameters radius.val mode.val.2) •
    (Real.exp (-radialPhase parameters radius.val mode.val.2) •
      conjugatedHighSection lower length positive bounded field mode radius) = _
  rw [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

/-- An existing higher-grade energy element supplies a uniform summable
majorant for each lower-grade physical section, on both endpoints as well. -/
theorem conjugatedHighSection_decay (grade : ℕ)
    (field weighted : annularEnergySpace lower length positive)
    (same : ∀ mode : HighAnnularMode, weighted.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 4) : ℝ) : ℂ) • field.val mode)
    (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      conjugatedHighSection lower length positive bounded field mode radius‖ ≤
      ((2 * sourceEndpointConstant lower) * ‖weighted‖) *
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹ := by
  let frequency := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have frequencyPositive : 0 < frequency := lt_of_lt_of_le (by norm_num) (annularFrequency_one_le _ _)
  have weightedBound : frequency ^ (grade + 4) * ‖field.val mode‖ ≤ ‖weighted‖ := by
    have point := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) weighted.val mode
    rw [same, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)] at point
    exact point
  have rescale : frequency ^ grade * ‖field.val mode‖ ≤ ‖weighted‖ * (frequency ^ 4)⁻¹ := by
    apply (le_div_iff₀ (pow_pos frequencyPositive 4)).mpr
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using weightedBound
  have constantNonnegative : 0 ≤ 2 * sourceEndpointConstant lower :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have scaled := mul_le_mul_of_nonneg_left rescale constantNonnegative
  dsimp only [frequency] at scaled
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg frequencyPositive.le _)]
  exact (mul_le_mul_of_nonneg_left
    (conjugatedHighSection_bound lower length positive bounded field mode radius)
    (pow_nonneg frequencyPositive.le grade)).trans
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using scaled)

end Grad.AnnularWeightedSmoothCore
