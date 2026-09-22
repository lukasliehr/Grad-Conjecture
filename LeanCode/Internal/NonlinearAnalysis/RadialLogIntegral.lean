import RadialIntegralBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Set Filter MeasureTheory
open scoped Interval Topology

namespace Grad.NonlinearRadial

def logarithmicMass (lower upper : ℝ) : ℝ :=
  ∫ scale in Icc lower upper, -Real.log scale

theorem negativeLog_integrable (lower upper : ℝ) :
    IntegrableOn (fun scale => -Real.log scale) (Icc lower upper) := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (le_max_left lower upper)).mp
    (intervalIntegral.intervalIntegrable_log').neg |>.mono_set (Icc_subset_Icc le_rfl (le_max_right lower upper))

theorem logarithmicMass_nonnegative {lower upper : ℝ} (nonnegative : 0 ≤ lower) (bounded : upper ≤ 1) :
    0 ≤ logarithmicMass lower upper := by
  apply setIntegral_nonneg measurableSet_Icc
  intro scale scaleIn
  exact neg_nonneg.mpr (Real.log_nonpos (nonnegative.trans scaleIn.1) (scaleIn.2.trans bounded))

theorem negMulLog_mul_inverse (scale : ℝ) : Real.negMulLog scale * scale⁻¹ = -Real.log scale := by
  by_cases nonzero : scale = 0
  · simp [nonzero, Real.negMulLog]
  · unfold Real.negMulLog
    field_simp

theorem logarithmicMass_zero {upper : ℝ} (nonnegative : 0 ≤ upper) :
    logarithmicMass 0 upper = upper + Real.negMulLog upper := by
  rw [logarithmicMass, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le nonnegative, intervalIntegral.integral_neg, integral_log_from_zero]
  unfold Real.negMulLog
  ring

theorem logarithmicMass_unit : logarithmicMass 0 1 = 1 := by
  rw [logarithmicMass_zero zero_le_one]
  simp [Real.negMulLog]

theorem logarithmicMass_tendsto_zero :
    Tendsto (fun upper => logarithmicMass 0 upper) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  have continuousFunction : Continuous (fun upper : ℝ => upper + Real.negMulLog upper) :=
    continuous_id.add Real.continuous_negMulLog
  have limit := continuousFunction.continuousAt (x := (0 : ℝ)) |>.tendsto
  have limitZero : Tendsto (fun upper : ℝ => upper + Real.negMulLog upper) (𝓝[≥] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa only [Real.negMulLog_zero, zero_add] using limit
  apply limitZero.congr'
  filter_upwards [self_mem_nhdsWithin] with upper upperIn
  exact (logarithmicMass_zero upperIn).symm

end Grad.NonlinearRadial
