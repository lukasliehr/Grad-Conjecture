import AJI5ActualFluxContinuousBounds
import AIW6UniformOriginalLowFactors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularOriginalLow
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualLowMode_H1_bound (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖lowEnergyRadialGraph lower length positive bounded field index‖ ≤
      ‖field.val 0 index‖ + lowMu length lower index.2.val.2 * ‖field.val 1 index‖ := by
  have square := weightedRadialH1_norm_sq 1 lower (lowEnergyRadialGraph lower length positive bounded field index)
  have value := pow_le_pow_left₀ (norm_nonneg _)
    (lowEnergyRadialGraph_value_bound lower length positive bounded field index) 2
  have slope := pow_le_pow_left₀ (norm_nonneg _)
    (lowEnergyRadialGraph_slope_bound lower length positive bounded field index) 2
  have product := mul_nonneg (lowMu_nonneg length lower index.2.val.2) (norm_nonneg (field.val 1 index))
  nlinarith [norm_nonneg (lowEnergyRadialGraph lower length positive bounded field index),
    norm_nonneg (field.val 0 index), mul_nonneg (norm_nonneg (field.val 0 index)) product]

theorem actualLowInversePhysical_bound (parameters : PhaseParameters)
    (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |lowPhysicalInverseCurve parameters lower length positive index radius| ≤ 2 := by
  have phase : |annularInversePhase parameters index.2.val.2 radius| ≤ 1 := by
    change |Real.exp (-Grad.PhaseAlgebra.radialPhase parameters radius index.2.val.2)| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (annularPhase_positive parameters radius (positive.trans_le inside.1).le inside.2 index.2.val.2).le)
  have mu : |(lowMuCurve lower length positive index.2.val.2 radius)⁻¹| ≤ 1 := by
    change |(lowMu length (max lower radius) index.2.val.2)⁻¹| ≤ 1
    rw [max_eq_right inside.1, abs_of_pos (inv_pos.mpr (lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)))]
    exact inv_le_one_of_one_le₀ (lowMu_inner_one_le radius length (positive.trans_le inside.1) inside.2 index.2.val.2)
  unfold lowPhysicalInverseCurve
  split_ifs
  · change |(lowAmplitude length parameters.gamma index.2)⁻¹ *
      (annularInversePhase parameters index.2.val.2 radius * (lowMuCurve lower length positive index.2.val.2 radius)⁻¹)| ≤ 2
    rw [abs_mul, abs_mul]
    have estimate := mul_le_mul (lowAmplitude_inverse_bound length parameters.gamma index.2)
      (mul_le_mul phase mu (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [one_mul, mul_one] using estimate
  · exact phase.trans (by norm_num)

include positive in
theorem actualLowMu_frequency_bound (lengthPositive : 0 < length) (index : LowAnnularIndex) :
    lowMu length lower index.2.val.2 ≤ (length⁻¹ + lower⁻¹) *
      Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 := by
  have cell : |(index.2.val.2 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (index.2.val.1 : ℝ)]
  have one := annularFrequency_one_le index.2.val.1 index.2.val.2
  have first := mul_le_mul_of_nonneg_right cell (inv_nonneg.mpr lengthPositive.le)
  have second := mul_le_mul_of_nonneg_right one (inv_nonneg.mpr positive.le)
  have upper := originalLow_mu_upper length lower lengthPositive positive index.2.val.2
  rw [div_eq_mul_inv] at upper
  exact upper.trans ((add_le_add first (by simpa only [one_mul] using second)).trans_eq (by ring))

theorem actualLowPhysicalSection_bound (parameters : PhaseParameters)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    ‖lowPhysicalSection parameters lower length positive bounded field index radius‖ ≤
      (2 * sourceEndpointConstant lower) *
        (‖field.val 0 index‖ + lowMu length lower index.2.val.2 * ‖field.val 1 index‖) := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (lowEnergyRadialGraph lower length positive bounded field index)
  have point := (lowEnergySection lower length positive bounded field index).norm_coe_le_norm radius
  have bound := point.trans (representative.trans (mul_le_mul_of_nonneg_left
    (actualLowMode_H1_bound lower length positive bounded field index) (Real.sqrt_nonneg _)))
  change ‖lowPhysicalInverseCurve parameters lower length positive index radius.val •
    lowEnergySection lower length positive bounded field index radius‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right
    (actualLowInversePhysical_bound lower length positive parameters index radius.val radius.property) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left bound (by norm_num))).trans_eq (by ring)

end Grad.AnnularSmoothCore
