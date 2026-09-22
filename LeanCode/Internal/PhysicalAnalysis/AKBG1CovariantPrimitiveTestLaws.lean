import AKAY40WeightedAngularFundamental

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Interval
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial

theorem startupAngularTest_weight_add (first second : ℝ → ℝ) (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest (fun angle => first angle + second angle) test point =
      startupAngularTest first test point + startupAngularTest second test point := by
  unfold startupAngularTest
  simp_rw [add_mul]
  have firstIntegrable : IntegrableOn (fun angle => first angle * test (planeRotationEquiv (-angle) point))
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (firstContinuous.mul (startupInverseOrbit_continuous test smooth point)).integrableOn_Icc
  have secondIntegrable : IntegrableOn (fun angle => second angle * test (planeRotationEquiv (-angle) point))
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (secondContinuous.mul (startupInverseOrbit_continuous test smooth point)).integrableOn_Icc
  rw [integral_add firstIntegrable secondIntegrable]
  ring

theorem startupAngularTest_weight_neg (weight : ℝ → ℝ) (test : Spatial → ℝ) (point : Spatial) :
    startupAngularTest (fun angle => -weight angle) test point = -startupAngularTest weight test point := by
  unfold startupAngularTest
  simp only [neg_mul, integral_neg, mul_neg]

theorem startupAngularTest_weight_sub (first second : ℝ → ℝ) (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest (fun angle => first angle - second angle) test point =
      startupAngularTest first test point - startupAngularTest second test point := by
  simp only [sub_eq_add_neg]
  rw [startupAngularTest_weight_add first (fun angle => -second angle) firstContinuous secondContinuous.neg test smooth point,
    startupAngularTest_weight_neg]

theorem startupCosineTest_rotation (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest Real.cos (startupRotationDerivative test) point = -startupAngularTest Real.sin test point := by
  have actual := startupWeightedAngularTest_rotation Real.cos (fun angle => -Real.sin angle)
    Real.hasDerivAt_cos Real.continuous_sin.neg test smooth point
  simpa only [Real.cos_two_pi, Real.cos_zero, sub_self, mul_zero, zero_mul, sub_zero,
    startupAngularTest_weight_neg] using actual

theorem startupSineTest_rotation (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest Real.sin (startupRotationDerivative test) point = startupAngularTest Real.cos test point := by
  have actual := startupWeightedAngularTest_rotation Real.sin Real.cos
    Real.hasDerivAt_sin Real.continuous_cos test smooth point
  simpa only [Real.sin_two_pi, Real.sin_zero, sub_self, mul_zero, zero_mul, sub_zero] using actual

theorem startupPrimitiveCosineTest_rotation (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest (fun angle => angle * Real.cos angle) (startupRotationDerivative test) point =
      startupAngularTest Real.cos test point - startupAngularTest (fun angle => angle * Real.sin angle) test point - test point := by
  have derivative (angle : ℝ) : HasDerivAt (fun theta => theta * Real.cos theta)
      (Real.cos angle - angle * Real.sin angle) angle := by
    have product := (hasDerivAt_id angle).mul (Real.hasDerivAt_cos angle)
    change HasDerivAt (fun theta : ℝ => theta * Real.cos theta)
      (1 * Real.cos angle + angle * (-Real.sin angle)) angle at product
    simpa only [one_mul, mul_neg, sub_eq_add_neg] using product
  have actual := startupWeightedAngularTest_rotation (fun angle => angle * Real.cos angle)
    (fun angle => Real.cos angle - angle * Real.sin angle) derivative (by fun_prop) test smooth point
  rw [startupAngularTest_weight_sub Real.cos (fun angle => angle * Real.sin angle)
    Real.continuous_cos (by fun_prop) test smooth point] at actual
  simpa only [Real.cos_two_pi, Real.cos_zero, mul_one, zero_mul, sub_zero,
    inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul] using actual

theorem startupPrimitiveSineTest_rotation (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest (fun angle => angle * Real.sin angle) (startupRotationDerivative test) point =
      startupAngularTest Real.sin test point + startupAngularTest (fun angle => angle * Real.cos angle) test point := by
  have derivative (angle : ℝ) : HasDerivAt (fun theta => theta * Real.sin theta)
      (Real.sin angle + angle * Real.cos angle) angle := by
    have product := (hasDerivAt_id angle).mul (Real.hasDerivAt_sin angle)
    change HasDerivAt (fun theta : ℝ => theta * Real.sin theta)
      (1 * Real.sin angle + angle * Real.cos angle) angle at product
    simpa only [one_mul] using product
  have actual := startupWeightedAngularTest_rotation (fun angle => angle * Real.sin angle)
    (fun angle => Real.sin angle + angle * Real.cos angle) derivative (by fun_prop) test smooth point
  rw [startupAngularTest_weight_add Real.sin (fun angle => angle * Real.cos angle)
    Real.continuous_sin (by fun_prop) test smooth point] at actual
  simpa only [Real.sin_two_pi, Real.sin_zero, mul_zero, sub_self, zero_mul, sub_zero] using actual

end Grad.CartesianStartup
