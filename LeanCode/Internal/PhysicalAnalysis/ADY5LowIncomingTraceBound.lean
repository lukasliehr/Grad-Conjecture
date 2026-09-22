import ADY4ActualLowFiniteSmoothDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem lowMu_collar_bound (lower length : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    lowMu length radius cell ≤ lowMu length lower cell := by
  have inverse : radius⁻¹ ≤ lower⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le positive inside.1
  apply Real.sqrt_le_sqrt
  exact add_le_add_right (pow_le_pow_left₀ (inv_nonneg.mpr (positive.trans_le inside.1).le) inverse 2) _

theorem lowMu_inner_one_le (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (cell : ℤ) :
    1 ≤ lowMu length lower cell :=
  ((one_le_inv₀ positive).mpr bounded).trans (lowMu_radial length lower cell positive)

theorem lowStorageInverse_bound (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) : |lowStorageInverse lower positive radius| ≤ 1 := by
  change |(max lower radius) ^ (7 / 4 : ℝ)| ≤ 1
  rw [max_eq_right inside.1, abs_of_pos (Real.rpow_pos_of_pos (positive.trans_le inside.1) _)]
  have estimate := Real.rpow_le_rpow (positive.trans_le inside.1).le inside.2 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  simpa only [Real.one_rpow] using estimate

theorem lowScalar_norm_bound (lower : ℝ) (coefficient : C(ℝ, ℝ)) (constant : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ constant)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    ‖collarScalar 1 lower coefficient field‖ ≤ constant * ‖field‖ := by
  rw [← scalarRadialMap_eq_collarScalar lower coefficient constant bounded]
  exact scalarRadialMap_bound lower coefficient constant bounded field

theorem lowRadialSqrt_norm_bound (lower : ℝ) (field : CollarL2 (ComplexEuclidean 1) lower) :
    ‖radialSqrtMap 1 lower field‖ ≤ ‖field‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [radialSqrtMap_ae 1 lower field, ae_restrict_mem measurableSet_Icc] with radius literal inside
  rw [literal, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt inside.2)

theorem lowEnergyRadialGraph_value_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖weightedRadialCoordinate 1 lower 0 (lowEnergyRadialGraph lower length positive bounded field index)‖ ≤
      ‖field.val 0 index‖ := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, lowEnergyRadialGraph_value]
  change ‖radialSqrtMap 1 lower (collarScalar 1 lower (lowStorageInverse lower positive) (field.val 0 index))‖ ≤ _
  exact (lowRadialSqrt_norm_bound lower _).trans
    (by simpa only [one_mul] using (lowScalar_norm_bound lower (lowStorageInverse lower positive) 1
      (lowStorageInverse_bound lower positive) (field.val 0 index)))

theorem lowEnergyRadialGraph_slope_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖weightedRadialCoordinate 1 lower 1 (lowEnergyRadialGraph lower length positive bounded field index)‖ ≤
      lowMu length lower index.2.val.2 * ‖field.val 1 index‖ := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, lowEnergyRadialGraph_slope]
  change ‖radialSqrtMap 1 lower (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
    (collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index)))‖ ≤ _
  apply (lowRadialSqrt_norm_bound lower _).trans
  have muBound : ∀ radius ∈ Icc lower 1,
      |lowMuCurve lower length positive index.2.val.2 radius| ≤ lowMu length lower index.2.val.2 := by
    intro radius inside
    change |lowMu length (max lower radius) index.2.val.2| ≤ _
    rw [max_eq_right inside.1, abs_of_nonneg (lowMu_nonneg _ _ _)]
    exact lowMu_collar_bound lower length positive index.2.val.2 radius inside
  exact (lowScalar_norm_bound lower (lowMuCurve lower length positive index.2.val.2)
    (lowMu length lower index.2.val.2) muBound _).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using (lowScalar_norm_bound lower (lowStorageInverse lower positive) 1
        (lowStorageInverse_bound lower positive) (field.val 1 index))) (lowMu_nonneg _ _ _))

/-- Fixed-ell trace bound. No uniform-in-ell assertion is used here. -/
theorem lowEndpoint_mu_bound_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    (lowMu length lower index.2.val.2)⁻¹ * ‖lowEnergyEndpoint lower length positive bounded endpoint field index‖ ^ 2 ≤
      (collarTraceConstant lower / lower) * (‖field.val 0 index‖ ^ 2 + ‖field.val 1 index‖ ^ 2) := by
  rw [lowEnergyEndpoint_radialTrace]
  have estimate := weightedRadialTrace_frequency_bound_sq 1 lower (lowMu length lower index.2.val.2)
    positive bounded (lowMu_inner_one_le lower length positive bounded.le index.2.val.2) endpoint
      (lowEnergyRadialGraph lower length positive bounded field index)
  have value := pow_le_pow_left₀ (norm_nonneg _)
    (lowEnergyRadialGraph_value_bound lower length positive bounded field index) 2
  have slope := pow_le_pow_left₀ (norm_nonneg _)
    (lowEnergyRadialGraph_slope_bound lower length positive bounded field index) 2
  have normalized : (lowMu length lower index.2.val.2)⁻¹ ^ 2 *
      ‖weightedRadialCoordinate 1 lower 1 (lowEnergyRadialGraph lower length positive bounded field index)‖ ^ 2 ≤
      ‖field.val 1 index‖ ^ 2 := by
    have scaled := mul_le_mul_of_nonneg_left slope (sq_nonneg (lowMu length lower index.2.val.2)⁻¹)
    rw [mul_pow] at scaled
    have cancellation : (lowMu length lower index.2.val.2)⁻¹ ^ 2 *
        (lowMu length lower index.2.val.2 ^ 2 * ‖field.val 1 index‖ ^ 2) = ‖field.val 1 index‖ ^ 2 := by
      field_simp [(lowMu_pos length lower index.2.val.2 positive).ne']
    rwa [cancellation] at scaled
  exact estimate.trans (mul_le_mul_of_nonneg_left (add_le_add value normalized)
    (div_nonneg (zero_le_one.trans (collarTraceConstant_one_le bounded)) positive.le))

def lowIncomingConstant (lower : ℝ) : ℝ :=
  lower ^ (-(7 / 4 : ℝ)) * Real.sqrt (collarTraceConstant lower / lower)

theorem lowIncomingConstant_nonneg (lower : ℝ) (positive : 0 < lower) : 0 ≤ lowIncomingConstant lower :=
  mul_nonneg (Real.rpow_pos_of_pos positive _).le (Real.sqrt_nonneg _)

theorem lowIncomingCoefficient_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖lowIncomingCoefficient lower length positive bounded field index‖ ≤
      lowIncomingConstant lower * (‖field.val 0 index‖ + ‖field.val 1 index‖) := by
  have normalized := lowEndpoint_mu_bound_sq lower length positive bounded 0 field index
  have traceNonnegative : 0 ≤ collarTraceConstant lower / lower :=
    div_nonneg (zero_le_one.trans (collarTraceConstant_one_le bounded)) positive.le
  have estimate := mul_le_mul_of_nonneg_left normalized
    (Real.rpow_pos_of_pos positive (-(7 / 2 : ℝ))).le
  rw [← mul_assoc, ← lowIncomingCoefficient_norm_sq] at estimate
  rw [← mul_assoc] at estimate
  have constantSq : lowIncomingConstant lower ^ 2 = lower ^ (-(7 / 2 : ℝ)) * (collarTraceConstant lower / lower) := by
    unfold lowIncomingConstant
    rw [mul_pow, Real.sq_sqrt traceNonnegative, pow_two, ← Real.rpow_add positive]
    norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (lowIncomingConstant_nonneg lower positive)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
  rw [mul_pow, constantSq]
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [norm_nonneg (field.val 0 index), norm_nonneg (field.val 1 index)])
    (mul_nonneg (Real.rpow_pos_of_pos positive _).le traceNonnegative))

end Grad.AnnularLowEnergy
