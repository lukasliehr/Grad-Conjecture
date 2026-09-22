import ASG17SmoothRadialPrimitives

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Anchored Poincare bound on a subinterval of(0,1). It follows directly
from the accepted FTC energy estimate, so no derivative is postulated. -/
theorem anchoredCore_energy (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : SmoothRadialCore dimension) (anchored : core.val.val.1 lower = 0) :
    (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) ≤
      4 * (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2) := by
  let base := ∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2
  let slope := ∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2
  have baseNonnegative : 0 ≤ base := intervalIntegral.integral_nonneg bounded.le (fun _ _ => sq_nonneg _)
  have slopeNonnegative : 0 ≤ slope := intervalIntegral.integral_nonneg bounded.le (fun _ _ => sq_nonneg _)
  have pointwise (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      ‖core.val.val.1 radius‖ ^ 2 ≤ (1 / 2 : ℝ) * base + 2 * slope := by
    have energy := endpoint_energy_bound core.val.val.1 core.val.val.2 lower radius (1 / 2)
      inside.1 (by norm_num) core.val.val.1.continuous core.val.val.2.continuous
      (fun point _ => core.val.property point)
    rw [anchored, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at energy
    norm_num at energy
    have valueLe := squareIntegral_mono core.val.val.1 core.val.val.1.continuous le_rfl inside.1 inside.2
    have slopeLe := squareIntegral_mono core.val.val.2 core.val.val.2.continuous le_rfl inside.1 inside.2
    dsimp [base, slope]
    linarith
  have integrated := intervalIntegral.integral_mono_on (μ := volume) bounded.le
    ((core.val.val.1.continuous.norm.pow 2).intervalIntegrable lower 1)
    (continuous_const.intervalIntegrable lower 1) pointwise
  rw [intervalIntegral.integral_const] at integrated
  change base ≤ (1 - lower) * ((1 / 2 : ℝ) * base + 2 * slope) at integrated
  have shortened : (1 - lower) * ((1 / 2 : ℝ) * base + 2 * slope) ≤
      1 * ((1 / 2 : ℝ) * base + 2 * slope) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  change base ≤ 4 * slope
  linarith

theorem weightedRadialCore_energy_upper (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (core : SmoothRadialCore dimension) :
    ‖weightedRadialCoreInto dimension lower core‖ ^ 2 ≤
      (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
      (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2) := by
  rw [weightedRadialCore_norm_sq dimension lower positive bounded, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on (μ := volume) bounded
      ((continuous_id.mul ((core.val.val.1.continuous.norm.pow 2).add
        (core.val.val.2.continuous.norm.pow 2))).intervalIntegrable lower 1)
      (((core.val.val.1.continuous.norm.pow 2).add (core.val.val.2.continuous.norm.pow 2)).intervalIntegrable lower 1)
    intro radius inside
    exact mul_le_of_le_one_left (add_nonneg (sq_nonneg _) (sq_nonneg _)) inside.2
  · exact (core.val.val.1.continuous.norm.pow 2).intervalIntegrable lower 1
  · exact (core.val.val.2.continuous.norm.pow 2).intervalIntegrable lower 1

def anchoredPrimitiveInto (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] WeightedRadialH1 dimension lower :=
  (weightedRadialCoreInto dimension lower).comp (anchoredPrimitiveCore dimension lower)

theorem anchoredPrimitiveInto_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (core : SmoothRadialCore dimension) :
    ‖anchoredPrimitiveInto dimension lower core‖ ≤ Real.sqrt 5 * ‖smoothRadialValueL2 dimension lower core‖ := by
  have energy := anchoredCore_energy dimension lower positive bounded
    (anchoredPrimitiveCore dimension lower core) (anchoredPrimitiveCore_lower dimension lower core)
  have upper := weightedRadialCore_energy_upper dimension lower positive bounded.le
    (anchoredPrimitiveCore dimension lower core)
  rw [anchoredPrimitiveCore_slope] at energy upper
  have inputNorm : ‖smoothRadialValueL2 dimension lower core‖ ^ 2 =
      ∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2 :=
    collarContinuousL2_norm_sq (ComplexEuclidean dimension) lower bounded.le core.val.val.1
  have squared : ‖anchoredPrimitiveInto dimension lower core‖ ^ 2 ≤
      5 * ‖smoothRadialValueL2 dimension lower core‖ ^ 2 := by
    change ‖weightedRadialCoreInto dimension lower (anchoredPrimitiveCore dimension lower core)‖ ^ 2 ≤ _
    rw [inputNorm]
    linarith
  have rooted := Real.sqrt_le_sqrt squared
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using rooted

end Grad.AnnularSourceGraph
