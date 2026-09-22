import AAG7SharpEndpointCore

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularPotential_continuousOn (lower length : ℝ) (positive : 0 < lower) (mode cell : ℤ) :
    ContinuousOn (fun radius => annularPotential length radius mode cell) (Icc lower 1) := by
  exact (continuousOn_const.div (continuousOn_id.pow 2)
    (fun radius inside => (sq_pos_of_pos (positive.trans_le inside.1)).ne')).add continuousOn_const

theorem annularModeEnergyCore_endpoint_sq (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1) (endpoint : Fin 2) :
    lower * (annularFrequency mode.val.1 mode.val.2 * ‖core.val.1 (radialEndpointRadius lower endpoint)‖ ^ 2) ≤
      (collarTraceConstant lower * annularPotentialComparison length) *
        ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ ^ 2 := by
  let frequency := annularFrequency mode.val.1 mode.val.2
  let comparison := annularPotentialComparison length
  let potential := fun radius => annularPotential length radius mode.val.1 mode.val.2
  have frequencyPositive : 0 < frequency := lt_of_lt_of_le zero_lt_one (annularFrequency_one_le _ _)
  have comparisonOne : 1 ≤ comparison := annularPotentialComparison_one_le length
  have traceConstant : 0 ≤ collarTraceConstant lower := zero_le_one.trans (collarTraceConstant_one_le bounded)
  have trace : ‖core.val.1 (radialEndpointRadius lower endpoint)‖ ^ 2 ≤ collarTraceConstant lower *
      (frequency * (∫ radius in lower..1, ‖core.val.1 radius‖ ^ 2) +
        frequency⁻¹ * (∫ radius in lower..1, ‖core.val.2 radius‖ ^ 2)) := by
    fin_cases endpoint
    · exact scalar_inner_collar_trace core.val.1 core.val.2 lower frequency bounded
        (annularFrequency_one_le _ _) core.val.1.continuous core.val.2.continuous
        (fun radius _ => core.property.2 radius)
    · exact scalar_collar_trace core.val.1 core.val.2 lower frequency bounded
        (annularFrequency_one_le _ _) core.val.1.continuous core.val.2.continuous
        (fun radius _ => core.property.2 radius)
  have potentialContinuous := annularPotential_continuousOn lower length positive mode.val.1 mode.val.2
  have energyIntegrable : IntervalIntegrable
      (fun radius => radius * (‖core.val.2 radius‖ ^ 2 + potential radius * ‖core.val.1 radius‖ ^ 2)) volume lower 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le bounded.le]
    exact continuousOn_id.mul ((core.val.2.continuous.norm.pow 2).continuousOn.add
      (potentialContinuous.mul (core.val.1.continuous.norm.pow 2).continuousOn))
  have comparisonIntegral : lower *
      (frequency ^ 2 * (∫ radius in lower..1, ‖core.val.1 radius‖ ^ 2) +
        (∫ radius in lower..1, ‖core.val.2 radius‖ ^ 2)) ≤
      comparison * ∫ radius in lower..1, radius *
        (‖core.val.2 radius‖ ^ 2 + potential radius * ‖core.val.1 radius‖ ^ 2) := by
    have valueIntegrable : IntervalIntegrable (fun radius => frequency ^ 2 * ‖core.val.1 radius‖ ^ 2) volume lower 1 :=
      (continuous_const.mul (core.val.1.continuous.norm.pow 2)).intervalIntegrable lower 1
    have slopeIntegrable : IntervalIntegrable (fun radius => ‖core.val.2 radius‖ ^ 2) volume lower 1 :=
      (core.val.2.continuous.norm.pow 2).intervalIntegrable lower 1
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add valueIntegrable slopeIntegrable,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on bounded.le
      ((continuous_const.mul ((continuous_const.mul (core.val.1.continuous.norm.pow 2)).add
        (core.val.2.continuous.norm.pow 2))).intervalIntegrable lower 1)
      (energyIntegrable.const_mul comparison)
    intro radius inside
    have radiusPositive := positive.trans_le inside.1
    have potentialPositive := annularPotential_pos length radius mode.val.1 mode.val.2 mode.property radiusPositive
    have frequencyBound := annularFrequency_sq_le_potential length radius mode.val.1 mode.val.2
      lengthPositive radiusPositive inside.2 mode.property
    have massCoefficient : lower * frequency ^ 2 ≤ comparison * radius * potential radius := by
      have first := mul_le_mul_of_nonneg_left frequencyBound positive.le
      have second := mul_le_mul_of_nonneg_right inside.1
        (mul_nonneg (zero_le_one.trans comparisonOne) potentialPositive.le)
      dsimp [frequency, comparison, potential] at *
      nlinarith only [first, second]
    have slopeCoefficient : lower ≤ comparison * radius :=
      inside.1.trans (le_mul_of_one_le_left radiusPositive.le comparisonOne)
    have mass := mul_le_mul_of_nonneg_right massCoefficient (sq_nonneg ‖core.val.1 radius‖)
    have slope := mul_le_mul_of_nonneg_right slopeCoefficient (sq_nonneg ‖core.val.2 radius‖)
    change lower * (frequency ^ 2 * ‖core.val.1 radius‖ ^ 2 + ‖core.val.2 radius‖ ^ 2) ≤
      comparison * (radius * (‖core.val.2 radius‖ ^ 2 + potential radius * ‖core.val.1 radius‖ ^ 2))
    nlinarith only [mass, slope]
  have scaled := mul_le_mul_of_nonneg_left trace (mul_nonneg positive.le frequencyPositive.le)
  have identity : lower * frequency * (collarTraceConstant lower *
      (frequency * (∫ radius in lower..1, ‖core.val.1 radius‖ ^ 2) +
        frequency⁻¹ * (∫ radius in lower..1, ‖core.val.2 radius‖ ^ 2))) =
      collarTraceConstant lower * (lower *
        (frequency ^ 2 * (∫ radius in lower..1, ‖core.val.1 radius‖ ^ 2) +
          (∫ radius in lower..1, ‖core.val.2 radius‖ ^ 2))) := by
    field_simp
  rw [identity] at scaled
  have estimated := scaled.trans (mul_le_mul_of_nonneg_left comparisonIntegral traceConstant)
  rw [annularModeEnergyCore_norm_sq lower length positive bounded.le]
  change lower * (frequency * ‖core.val.1 (radialEndpointRadius lower endpoint)‖ ^ 2) ≤ _
  dsimp [comparison, potential] at estimated
  nlinarith [mul_nonneg (mul_nonneg traceConstant (zero_le_one.trans comparisonOne))
    (sq_nonneg ‖core.val.1 1‖)]

def annularTraceConstant (lower length : ℝ) : ℝ :=
  Real.sqrt (collarTraceConstant lower * annularPotentialComparison length / lower)

theorem annularModeEnergyCore_endpoint_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1) (endpoint : Fin 2) :
    ‖(Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
      core.val.1 (radialEndpointRadius lower endpoint)‖ ≤
      annularTraceConstant lower length * ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ := by
  have estimate := annularModeEnergyCore_endpoint_sq lower length positive bounded lengthPositive mode core endpoint
  have constantNonnegative : 0 ≤ collarTraceConstant lower * annularPotentialComparison length / lower :=
    div_nonneg (mul_nonneg (zero_le_one.trans (collarTraceConstant_one_le bounded))
      (zero_le_one.trans (annularPotentialComparison_one_le length))) positive.le
  have frequencyNonnegative := zero_le_one.trans (annularFrequency_one_le mode.val.1 mode.val.2)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold annularTraceConstant
  have divided : annularFrequency mode.val.1 mode.val.2 *
      ‖core.val.1 (radialEndpointRadius lower endpoint)‖ ^ 2 ≤
      (collarTraceConstant lower * annularPotentialComparison length *
        ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ ^ 2) / lower :=
    (le_div_iff₀ positive).2 (by nlinarith only [estimate])
  rw [mul_div_right_comm] at divided
  have rooted := Real.sqrt_le_sqrt divided
  simpa only [Real.sqrt_mul frequencyNonnegative, Real.sqrt_mul constantNonnegative,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using rooted

end Grad.AnnularVariational
