import AJI2ContinuousHilbertFourierSections
import AAZJ1OriginalPhaseDomination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualEnergyMode_H1_bound (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ‖annularModeRadialH1 lower length positive mode field‖ ≤ 2 * ‖field.val mode‖ := by
  have square := weightedRadialH1_norm_sq 1 lower (annularModeRadialH1 lower length positive mode field)
  rw [annularModeRadialH1_value, annularModeRadialH1_derivative] at square
  have value : ‖annularEnergyValue lower length positive field mode‖ ≤ (1 / 3 : ℝ) * ‖field.val mode‖ := by
    exact (annularValueMassMap_bound lower length positive mode (annularModeMass lower (field.val mode))).trans
      (mul_le_mul_of_nonneg_left ((annularModeMass_bound lower (field.val mode)).trans_eq (one_mul _)) (by norm_num))
  have slope : ‖annularEnergyDerivative lower length positive field mode‖ ≤ ‖field.val mode‖ :=
    (annularModeDerivative_bound lower (field.val mode)).trans_eq (one_mul _)
  nlinarith [norm_nonneg (annularModeRadialH1 lower length positive mode field),
    norm_nonneg (field.val mode), norm_nonneg (annularEnergyValue lower length positive field mode),
    norm_nonneg (annularEnergyDerivative lower length positive field mode)]

theorem actualHighPhysicalSection_bound (parameters : PhaseParameters)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    ‖annularPhysicalValueSection parameters lower length positive bounded mode field radius‖ ≤
      (2 * sourceEndpointConstant lower) * ‖field.val mode‖ := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (annularModeRadialH1 lower length positive mode field)
  have point := (weightedRadialSection 1 lower positive bounded
    (annularModeRadialH1 lower length positive mode field)).norm_coe_le_norm radius
  have bound := point.trans (representative.trans (mul_le_mul_of_nonneg_left
    (actualEnergyMode_H1_bound lower length positive field mode) (Real.sqrt_nonneg _)))
  change ‖annularInversePhase parameters mode.val.2 radius.val •
    weightedRadialSection 1 lower positive bounded (annularModeRadialH1 lower length positive mode field) radius‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right
    (annularInversePhase_le_one parameters lower positive mode radius.val radius.property) (norm_nonneg _)).trans_eq (one_mul _)).trans
      (bound.trans_eq (by ring))

/-- An existing higher-grade energy element supplies a uniform summable
majorant for each lower-grade physical section, on both endpoints as well. -/
theorem actualHighPhysicalSection_decay (parameters : PhaseParameters) (grade : ℕ)
    (field weighted : annularEnergySpace lower length positive)
    (same : ∀ mode : HighAnnularMode, weighted.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 4) : ℝ) : ℂ) • field.val mode)
    (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      annularPhysicalValueSection parameters lower length positive bounded mode field radius‖ ≤
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
    (actualHighPhysicalSection_bound lower length positive bounded parameters field mode radius)
    (pow_nonneg frequencyPositive.le grade)).trans
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using scaled)

end Grad.AnnularSmoothCore
