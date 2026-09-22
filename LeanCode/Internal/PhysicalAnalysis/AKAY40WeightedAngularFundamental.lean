import AKAY39ExactRawQradWeakTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
open scoped ContDiff Interval
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial

/-- Compact angular integration by parts with the exact endpoint term.
This handles the covariant matrix primitive without an assumed R inverse. -/
theorem startupWeightedAngularTest_rotation (weight derivative : ℝ → ℝ)
    (weightDerivative : ∀ angle, HasDerivAt weight (derivative angle) angle)
    (derivativeContinuous : Continuous derivative)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest weight (startupRotationDerivative test) point =
      startupAngularTest derivative test point -
        ((2 * Real.pi)⁻¹ * (weight (2 * Real.pi) - weight 0)) * test point := by
  have orbitDerivative := (startupInverseOrbit_continuous (startupRotationDerivative test)
    (startupRotationDerivative_smooth test smooth) point).neg
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun angle _ => weightDerivative angle)
    (fun angle _ => startupInverseOrbit_hasDerivAt test smooth point angle)
    (derivativeContinuous.intervalIntegrable 0 (2 * Real.pi))
    (orbitDerivative.intervalIntegrable 0 (2 * Real.pi))
  simp only [mul_neg, intervalIntegral.integral_neg, startupInverseRotation_period_endpoint,
    startupInverseRotation_zero] at parts
  have equality : (∫ angle in (0 : ℝ)..(2 * Real.pi),
      weight angle * startupRotationDerivative test (planeRotationEquiv (-angle) point)) =
        (∫ angle in (0 : ℝ)..(2 * Real.pi), derivative angle * test (planeRotationEquiv (-angle) point)) -
          (weight (2 * Real.pi) - weight 0) * test point := by linarith [parts]
  rw [startupAngularTest_interval, startupAngularTest_interval, equality]
  ring

end Grad.CartesianStartup
