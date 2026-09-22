import ASP2AngularCommutation

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily Grad.FourierGrade

private theorem exponential_derivative (mode : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode angle) angle := by
  have derivative := (cellExponential_hasFDerivAt mode angle).hasDerivAt
  simpa [cellExponentialDerivative, mul_comm] using derivative

private theorem primitive_antiderivative (mode : ℤ) (nonzero : mode ≠ 0) (angle : ℝ) :
    HasDerivAt (fun current : ℝ =>
      ((current : ℂ) * (Complex.I * (mode : ℂ))⁻¹ - (Complex.I * (mode : ℂ))⁻¹ ^ 2) * cellExponential mode current)
      ((angle : ℂ) * cellExponential mode angle) angle := by
  have cast : HasDerivAt (fun current : ℝ => (current : ℂ)) 1 angle := by
    simpa using (hasDerivAt_id angle).ofReal_comp
  have derivative := ((cast.mul_const (Complex.I * (mode : ℂ))⁻¹).sub
    (hasDerivAt_const angle ((Complex.I * (mode : ℂ))⁻¹ ^ 2))).mul (exponential_derivative mode angle)
  have frequency : (Complex.I * (mode : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast nonzero)
  have algebra : (1 * (Complex.I * (mode : ℂ))⁻¹ - 0) * cellExponential mode angle +
      ((angle : ℂ) * (Complex.I * (mode : ℂ))⁻¹ - (Complex.I * (mode : ℂ))⁻¹ ^ 2) *
        ((Complex.I * (mode : ℂ)) * cellExponential mode angle) =
      (angle : ℂ) * cellExponential mode angle := by
    field_simp [frequency]
    ring
  exact algebra ▸ derivative

theorem angularPrimitive_scalar_integral (mode : ℤ) (nonzero : mode ≠ 0) :
    (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      (angle : ℂ) * cellExponential mode angle) = (Complex.I * (mode : ℂ))⁻¹ := by
  have continuousIntegrand : Continuous (fun angle : ℝ => (angle : ℂ) * cellExponential mode angle) := by
    have continuous := Complex.continuous_ofReal.mul (angularCharacter_smooth (-mode)).continuous
    change Continuous (fun angle : ℝ => (angle : ℂ) * angularCharacter (-mode) angle) at continuous
    simpa only [angularCharacter, neg_neg] using continuous
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun angle _ => primitive_antiderivative mode nonzero angle)
    (continuousIntegrand.intervalIntegrable 0 (2 * Real.pi))
  have endpoint : cellExponential mode (2 * Real.pi) = 1 := by
    have periodic := angularCharacter_periodic (-mode) 0
    simpa only [angularCharacter, neg_neg, zero_add, cellExponential, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero] using periodic
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc, endpoint] at integral
  have atZero : cellExponential mode 0 = 1 := by simp [cellExponential]
  simp only [Complex.ofReal_zero, zero_mul, atZero, mul_one] at integral
  have simplified : (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      (angle : ℂ) * cellExponential mode angle) = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (mode : ℂ))⁻¹ := by
    rw [integral]
    ring
  rw [simplified]
  change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (mode : ℂ))⁻¹) = _
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀]
  · exact one_mul _
  · exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

end Grad.ActualSmoothPDE
