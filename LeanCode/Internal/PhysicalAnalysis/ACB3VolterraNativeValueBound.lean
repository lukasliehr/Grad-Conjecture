import ACB1OriginalCenterSourceBound

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra

theorem radiusPower_value_norm {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    ‖(radiusPowerJet power field).value‖ ≤ ‖field.value‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro point
  rw [radiusPowerJet_value, norm_smul, Real.norm_eq_abs, radiusSquare_eq,
    abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
  have small : ‖point.val‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) point.property
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (sq_nonneg _) small)).trans
    (ContinuousMap.norm_coe_le_norm field.value point)

theorem volterraPower_value_norm {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    ‖(volterraPower count field).value‖ ≤ kernelMass count * ‖field.value‖ := by
  rw [volterraPower_kernel]
  apply (radiusPower_value_norm count _).trans
  simpa only [closedDerivative_zero_order] using positiveKernel_derivative_norm count field emptyCartesianWord

def centerValueConstant (radius : ℝ) : ℝ := ∑' count : ℕ, (3 * radius ^ 2) ^ count / (count.factorial : ℝ)

theorem centerValueConstant_nonnegative (radius : ℝ) : 0 ≤ centerValueConstant radius :=
  tsum_nonneg (fun _ => by positivity)

theorem centerValueConstant_summable (radius : ℝ) :
    Summable (fun count : ℕ => (3 * radius ^ 2) ^ count / (count.factorial : ℝ)) :=
  Real.summable_pow_div_factorial (3 * radius ^ 2)

theorem volterra_value_term_bound {dimension : ℕ} (radius parameter : ℝ)
    (bounded : |parameter| ≤ 3 * radius ^ 2) (field : ClosedJet dimension) (count : ℕ) :
    ‖(((parameter ^ count : ℝ) : ℂ) • volterraPower (count + 1) field).value‖ ≤
      ((3 * radius ^ 2) ^ count / (count.factorial : ℝ)) * ‖field.value‖ := by
  rw [closedJet_value_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have mass := (kernelMass_succ_le count).trans (kernelMass_le_inverse_factorial count)
  calc
    _ ≤ |parameter| ^ count * (kernelMass (count + 1) * ‖field.value‖) :=
      mul_le_mul_of_nonneg_left (volterraPower_value_norm (count + 1) field) (pow_nonneg (abs_nonneg _) _)
    _ ≤ (3 * radius ^ 2) ^ count * ((1 / (count.factorial : ℝ)) * ‖field.value‖) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) bounded count)
        (mul_le_mul_of_nonneg_right mass (norm_nonneg _))
        (mul_nonneg (kernelMass_positive _).le (norm_nonneg _)) (by positivity)
    _ = _ := by ring

/-- A value-only bound for the actual all-order smooth resolvent. The
constant is chosen before the parameter and the source. -/
theorem volterraResolvent_value_norm {dimension : ℕ} (radius parameter : ℝ)
    (bounded : |parameter| ≤ 3 * radius ^ 2) (field : ClosedJet dimension) :
    ‖(volterraResolventJet parameter field).value‖ ≤ centerValueConstant radius * ‖field.value‖ := by
  exact (volterraResolventJet_value_hasSum parameter field).norm_le_of_bounded
    ((centerValueConstant_summable radius).hasSum.mul_right ‖field.value‖)
    (volterra_value_term_bound radius parameter bounded field)

end Grad.ActualCenterBounds
