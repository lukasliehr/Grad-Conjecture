import AKAB2OriginalWeightedPointwiseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval

/-- The polar Jacobian r and the cutoff derivative epsilon^-1 combine
with the original r^(7/4) unweighting. The remaining shell L2 factor
gives exactly the manuscript's epsilon^(9/4). -/
theorem weightedAxisShellError_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F]
    (epsilon : ℝ) (positive : 0 < epsilon) (weighted : ℝ → F) (error : ℝ → E)
    (squareIntegrable : MemLp weighted 2 (volume.restrict (Ioc epsilon (2 * epsilon))))
    (measurable : AEStronglyMeasurable error (volume.restrict (Ioc epsilon (2 * epsilon))))
    (pointwise : ∀ᵐ radius ∂volume.restrict (Ioc epsilon (2 * epsilon)),
      ‖error radius‖ ≤ (epsilon⁻¹ * radius) * radius ^ (7 / 4 : ℝ) * ‖weighted radius‖) :
    ‖∫ radius in Ioc epsilon (2 * epsilon), error radius‖ ≤
      (2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * epsilon ^ (9 / 4 : ℝ) *
        Real.sqrt (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2) := by
  let factor : ℝ := 2 * (2 * epsilon) ^ (7 / 4 : ℝ)
  have factorNonnegative : 0 ≤ factor := by dsimp [factor]; positivity
  have dominated : ∀ᵐ radius ∂volume.restrict (Ioc epsilon (2 * epsilon)),
      ‖error radius‖ ≤ factor * ‖weighted radius‖ := by
    filter_upwards [pointwise, ae_restrict_mem measurableSet_Ioc] with radius bound inside
    have radiusNonnegative : 0 ≤ radius := (positive.trans inside.1).le
    have cutoffBound : epsilon⁻¹ * radius ≤ 2 := by
      calc
        _ ≤ epsilon⁻¹ * (2 * epsilon) := mul_le_mul_of_nonneg_left inside.2 (inv_nonneg.mpr positive.le)
        _ = 2 := by field_simp
    have powerBound : radius ^ (7 / 4 : ℝ) ≤ (2 * epsilon) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow radiusNonnegative inside.2 (by norm_num)
    exact bound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul cutoffBound powerBound (Real.rpow_nonneg radiusNonnegative _) (by norm_num)) (norm_nonneg _))
  have majorant : Integrable (fun radius => factor * ‖weighted radius‖)
      (volume.restrict (Ioc epsilon (2 * epsilon))) :=
    (squareIntegrable.integrable (by norm_num)).norm.const_mul factor
  have integrableError : Integrable error (volume.restrict (Ioc epsilon (2 * epsilon))) :=
    majorant.mono' measurable dominated
  have scalarIdentity : factor * Real.sqrt epsilon =
      (2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * epsilon ^ (9 / 4 : ℝ) := by
    dsimp [factor]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) positive.le, Real.sqrt_eq_rpow]
    rw [show (9 / 4 : ℝ) = 7 / 4 + 1 / 2 by norm_num, Real.rpow_add positive]
    ring
  calc
    _ ≤ ∫ radius in Ioc epsilon (2 * epsilon), ‖error radius‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ radius in Ioc epsilon (2 * epsilon), factor * ‖weighted radius‖ :=
      integral_mono_ae integrableError.norm majorant dominated
    _ = factor * (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖) := integral_const_mul _ _
    _ ≤ factor * (Real.sqrt epsilon * Real.sqrt (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (radialShell_integral_norm_le epsilon positive weighted squareIntegrable) factorNonnegative
    _ = _ := by rw [← mul_assoc, scalarIdentity]

end Grad.WeightedAxisRemoval
