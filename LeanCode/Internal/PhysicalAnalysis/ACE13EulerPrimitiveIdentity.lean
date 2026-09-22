import ACE12ActualSmoothVolterraSeries

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds

def shiftedEulerJet {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  eulerJet field + ((power + 1 : ℝ) : ℂ) • field

theorem shiftedEulerJet_extension_value {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (shiftedEulerJet power field).value point =
      fderiv ℝ (smoothClosedExtension field) point.val point.val +
        (power + 1 : ℝ) • smoothClosedExtension field point.val := by
  rw [shiftedEulerJet, closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul,
    ContinuousMap.smul_apply, eulerJet_extension_value, smoothClosedExtension_value, Complex.coe_smul]

theorem eulerPrimitive_derivative {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (point : ClosedDisk) (scale : ℝ) (inside : scale ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun current : ℝ => current ^ (power + 1) • smoothClosedExtension field (current • point.val))
      (scale ^ power • smoothClosedExtension (shiftedEulerJet power field) (scale • point.val)) scale := by
  have path : HasDerivAt (fun current : ℝ => current • point.val) point.val scale := by
    have derivative : HasDerivAt (fun current : ℝ => current • point.val) ((1 : ℝ) • point.val) scale :=
      (hasDerivAt_id scale).smul_const point.val
    simpa only [one_smul] using derivative
  have derivative := ((hasDerivAt_id scale).pow (power + 1)).smul
    (((smoothClosedExtension_smooth field).differentiable (by simp) (scale • point.val)).hasFDerivAt.comp_hasDerivAt scale path)
  have identity := (smoothClosedExtension_value (shiftedEulerJet power field)
    (dilationPoint scale inside.1 inside.2 point)).trans (shiftedEulerJet_extension_value power field _)
  change smoothClosedExtension (shiftedEulerJet power field) (scale • point.val) =
    fderiv ℝ (smoothClosedExtension field) (scale • point.val) (scale • point.val) +
      (power + 1 : ℝ) • smoothClosedExtension field (scale • point.val) at identity
  rw [map_smul] at identity
  apply derivative.congr_deriv
  rw [identity]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one, Pi.pow_apply, id_eq, Function.comp_apply, pow_succ]
  module

/-- Compact FTC supplies the true inverse of the shifted Euler operator;
the vanishing endpoint is automatic at scale zero. -/
theorem powerDilation_shiftedEuler {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    powerDilationJet power (shiftedEulerJet power field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [powerDilationJet_value, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have integrable : IntervalIntegrable (fun scale : ℝ => scale ^ power •
      smoothClosedExtension (shiftedEulerJet power field) (scale • point.val)) volume 0 1 := by
    have path : Continuous (fun scale : ℝ => scale • point.val) := by fun_prop
    have composed : Continuous (fun scale : ℝ =>
        smoothClosedExtension (shiftedEulerJet power field) (scale • point.val)) :=
      (smoothClosedExtension_smooth (shiftedEulerJet power field)).continuous.comp path
    exact ((continuous_id.pow power).smul composed).intervalIntegrable 0 1
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun scale inside => eulerPrimitive_derivative power field point scale
      (by simpa only [uIcc_of_le zero_le_one] using inside)) integrable
  simpa only [one_pow, one_smul, zero_pow (by omega : power + 1 ≠ 0), zero_smul,
    sub_zero, smoothClosedExtension_value] using integral

end Grad.ActualCenterVolterra
