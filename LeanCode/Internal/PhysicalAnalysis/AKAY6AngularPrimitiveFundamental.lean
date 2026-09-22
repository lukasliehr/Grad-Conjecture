import AKAY5AngularRotationCommutes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial

theorem startupAngularTest_interval (weight : ℝ → ℝ) (test : Spatial → ℝ) (point : Spatial) :
    startupAngularTest weight test point =
      (2 * Real.pi)⁻¹ * ∫ angle in (0 : ℝ)..(2 * Real.pi),
        weight angle * test (planeRotationEquiv (-angle) point) := by
  rw [startupAngularTest, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]

theorem startupInverseOrbit_continuous (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (point : Spatial) : Continuous (fun angle : ℝ => test (planeRotationEquiv (-angle) point)) := by
  have insertion : ContDiff ℝ ∞ (fun angle : ℝ => (point, angle)) := contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using (smooth.comp (startupInverseTestRotation_smooth.comp insertion)).continuous

theorem startupInverseRotation_period_endpoint (point : Spatial) :
    planeRotationEquiv (-(2 * Real.pi)) point = point := by
  ext coordinate
  fin_cases coordinate <;> simp [planeRotation]

theorem startupInverseRotation_zero (point : Spatial) : planeRotationEquiv (-(0 : ℝ)) point = point := by
  ext coordinate
  fin_cases coordinate <;> simp [planeRotation]

/-- The actual angular mean annihilates R, by the full-period fundamental theorem. -/
theorem startupMeanTest_rotation_zero (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (point : Spatial) :
    startupAngularTest (fun _ : ℝ => 1) (startupRotationDerivative test) point = 0 := by
  have continuousDerivative := (startupInverseOrbit_continuous (startupRotationDerivative test)
    (startupRotationDerivative_smooth test smooth) point).neg
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun angle _ => startupInverseOrbit_hasDerivAt test smooth point angle)
    (continuousDerivative.intervalIntegrable 0 (2 * Real.pi))
  rw [startupInverseRotation_period_endpoint, startupInverseRotation_zero, sub_self,
    intervalIntegral.integral_neg] at fundamental
  rw [startupAngularTest_interval]
  simp only [one_mul]
  have zeroIntegral := neg_eq_zero.mp fundamental
  rw [zeroIntegral, mul_zero]

/-- The unshifted primitive has the exact mean-minus-identity transpose law. -/
theorem startupPrimitiveTest_rotation (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (point : Spatial) :
    startupAngularTest (fun angle : ℝ => angle) (startupRotationDerivative test) point =
      startupAngularTest (fun _ : ℝ => 1) test point - test point := by
  have continuousDerivative := (startupInverseOrbit_continuous (startupRotationDerivative test)
    (startupRotationDerivative_smooth test smooth) point).neg
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun angle _ => hasDerivAt_id angle)
    (fun angle _ => startupInverseOrbit_hasDerivAt test smooth point angle)
    (continuous_const.intervalIntegrable 0 (2 * Real.pi))
    (continuousDerivative.intervalIntegrable 0 (2 * Real.pi))
  simp only [id_eq, mul_neg, intervalIntegral.integral_neg, startupInverseRotation_period_endpoint,
    startupInverseRotation_zero, zero_mul, sub_zero, one_mul] at parts
  have equality : (∫ angle in (0 : ℝ)..(2 * Real.pi),
      angle * startupRotationDerivative test (planeRotationEquiv (-angle) point)) =
        (∫ angle in (0 : ℝ)..(2 * Real.pi), test (planeRotationEquiv (-angle) point)) -
          (2 * Real.pi) * test point := by linarith [parts]
  rw [startupAngularTest_interval, startupAngularTest_interval]
  simp only [one_mul]
  rw [equality, mul_sub, ← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]

end Grad.CartesianStartup
