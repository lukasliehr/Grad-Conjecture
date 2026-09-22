import AKAX5AngularDerivativeTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ActualAngularInverse Grad.Constraints Grad.GaugeCoefficients.Physical.RadialLedger

/-- Equality of the actual parameter weights identifies the stored full-cell kernels. -/
theorem startupAngularKernel_eq_of_weights (first second : ℝ → ℂ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (same : first = second) :
    startupAngularKernel 3 first firstSmooth = startupAngularKernel 3 second secondSmooth := by
  cases same
  rfl

theorem startupZeroPrimitive_real :
    startupPrimitiveKernel 3 0 = startupRealAngularKernel (fun angle : ℝ => angle) contDiff_id := by
  apply startupAngularKernel_eq_of_weights
  funext angle
  simp only [shiftPrimitiveKernel, neg_zero, angularCharacter_zero_mode, mul_one]

theorem startupZeroMean_real :
    startupCharacterKernel 3 0 = startupRealAngularKernel (fun _ : ℝ => 1) contDiff_const := by
  apply startupAngularKernel_eq_of_weights
  funext angle
  simp only [angularCharacter_zero_mode, Complex.ofReal_one]

theorem startupCovectorAngular_eq_real (first : ℝ → ℂ) (second : ℝ → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (same : ∀ angle, first angle = (second angle : ℂ)) (input output : Fin 2) :
    startupCovectorAngularKernel first firstSmooth input output =
      startupRealAngularKernel (startupRealCovectorWeight second input output)
        (startupRealCovectorWeight_smooth second secondSmooth input output) := by
  apply startupAngularKernel_eq_of_weights
  funext angle
  change first angle * (startupInverseRotationEntry input output angle : ℂ) =
    (second angle * startupInverseRotationEntry input output angle : ℝ)
  rw [same angle, Complex.ofReal_mul]

theorem startupZeroPrimitiveCovector_real (input output : Fin 2) :
    startupCovectorAngularKernel (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output =
      startupRealAngularKernel (startupRealCovectorWeight (fun angle : ℝ => angle) input output)
        (startupRealCovectorWeight_smooth (fun angle : ℝ => angle) contDiff_id input output) := by
  refine startupCovectorAngular_eq_real (shiftPrimitiveKernel 0) (fun angle : ℝ => angle)
    (shiftPrimitiveKernel_smooth 0) contDiff_id ?_ input output
  intro angle
  simp only [shiftPrimitiveKernel, neg_zero, angularCharacter_zero_mode, mul_one]

theorem startupZeroMeanCovector_real (input output : Fin 2) :
    startupCovectorAngularKernel (angularCharacter 0) (angularCharacter_smooth 0) input output =
      startupRealAngularKernel (startupRealCovectorWeight (fun _ : ℝ => 1) input output)
        (startupRealCovectorWeight_smooth (fun _ : ℝ => 1) contDiff_const input output) := by
  refine startupCovectorAngular_eq_real (angularCharacter 0) (fun _ : ℝ => 1)
    (angularCharacter_smooth 0) contDiff_const ?_ input output
  intro angle
  simp only [angularCharacter_zero_mode, Complex.ofReal_one]

/-- The true inverse tensor is literally the primitive term minus both covectors of its mean correction. -/
theorem startupTrueInverseTensor_real (input output : Fin 2) :
    startupTrueInverseTensorKernel input output =
      startupRealAngularKernel (startupRealCovectorWeight (fun angle : ℝ => angle) input output)
        (startupRealCovectorWeight_smooth (fun angle : ℝ => angle) contDiff_id input output) -
      ∑ middle : Fin 2,
        (startupRealAngularKernel (startupRealCovectorWeight (fun angle : ℝ => angle) middle output)
          (startupRealCovectorWeight_smooth (fun angle : ℝ => angle) contDiff_id middle output)).comp
        (startupRealAngularKernel (startupRealCovectorWeight (fun _ : ℝ => 1) input middle)
          (startupRealCovectorWeight_smooth (fun _ : ℝ => 1) contDiff_const input middle)) := by
  simp only [startupTrueInverseTensorKernel, startupZeroPrimitiveCovector_real, startupZeroMeanCovector_real]

end Grad.CartesianStartup
