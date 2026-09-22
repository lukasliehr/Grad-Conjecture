import AJI4ActualHighHilbertSections
import AAQ8CanonicalFluxSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

theorem frequency_rescale (frequency : ℝ) (positive : 0 < frequency) (grade reserve : ℕ)
    (quantity bound : ℝ) (estimate : frequency ^ (grade + reserve) * quantity ≤ bound) :
    frequency ^ grade * quantity ≤ bound * (frequency ^ reserve)⁻¹ := by
  apply (le_div_iff₀ (pow_pos positive reserve)).mpr
  simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using estimate

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualFluxMode_H1_bound (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    ‖annularFluxRadialGraph lower positive bounded field mode‖ ≤
      ‖field.val.1 mode‖ + Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 * ‖field.val.2 mode‖ := by
  have square := weightedRadialH1_norm_sq 1 lower (annularFluxRadialGraph lower positive bounded field mode)
  rw [annularFluxRadialGraph_value, annularFluxRadialGraph_slope, norm_smul,
    Real.norm_of_nonneg (Grad.AnnularFluxTrace.annularFrequency_pos mode).le] at square
  have product := mul_nonneg (Grad.AnnularFluxTrace.annularFrequency_pos mode).le (norm_nonneg (field.val.2 mode))
  nlinarith [norm_nonneg (annularFluxRadialGraph lower positive bounded field mode),
    norm_nonneg (field.val.1 mode), mul_nonneg (norm_nonneg (field.val.1 mode)) product]

def actualFluxPhysicalSection (parameters : PhaseParameters)
    (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (annularInversePhase parameters mode.val.2)
    (annularFluxSection lower positive bounded field mode)

theorem actualFluxPhysicalSection_bound (parameters : PhaseParameters)
    (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    ‖actualFluxPhysicalSection lower positive bounded parameters field mode radius‖ ≤
      sourceEndpointConstant lower *
        (‖field.val.1 mode‖ + Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 * ‖field.val.2 mode‖) := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (annularFluxRadialGraph lower positive bounded field mode)
  have point := (annularFluxSection lower positive bounded field mode).norm_coe_le_norm radius
  have bound := point.trans (representative.trans (mul_le_mul_of_nonneg_left
    (actualFluxMode_H1_bound lower positive bounded field mode) (Real.sqrt_nonneg _)))
  change ‖annularInversePhase parameters mode.val.2 radius.val •
    annularFluxSection lower positive bounded field mode radius‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right
    (annularInversePhase_le_one parameters lower positive mode radius.val radius.property) (norm_nonneg _)).trans_eq (one_mul _)).trans bound

theorem actualFluxPhysicalSection_decay (parameters : PhaseParameters) (grade : ℕ)
    (field weighted : annularFluxWeakGraph lower positive)
    (sameValue : ∀ mode : HighAnnularMode, weighted.val.1 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.1 mode)
    (sameSlope : ∀ mode : HighAnnularMode, weighted.val.2 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.2 mode)
    (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      actualFluxPhysicalSection lower positive bounded parameters field mode radius‖ ≤
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
    (actualFluxPhysicalSection_bound lower positive bounded parameters field mode radius)
    (pow_nonneg frequencyPositive.le grade)).trans
    (by simpa only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using scaled)

end Grad.AnnularSmoothCore
