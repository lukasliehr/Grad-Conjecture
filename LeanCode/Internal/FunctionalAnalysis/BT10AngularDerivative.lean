import BT9AngularParseval

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

theorem angularCoefficient_scalar_derivative (field derivative : ℝ → ℂ)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ angle : ℝ, HasDerivAt field (derivative angle) angle)
    (periodicEndpoint : field Real.pi = field (-Real.pi)) (mode : ℤ) :
    angularCoefficient derivative mode = (Complex.I * (mode : ℂ)) * angularCoefficient field mode := by
  by_cases zeroMode : mode = 0
  · subst mode
    have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun angle _ => differentiates angle) (derivativeContinuous.intervalIntegrable (-Real.pi) Real.pi)
    rw [periodicEndpoint, sub_self] at fundamental
    rw [angularCoefficient_integral]
    simp only [neg_zero, fourier_zero, one_smul, fundamental,
      smul_zero, Int.cast_zero, mul_zero, zero_mul]
  · have raw := fourierCoeffOn_of_hasDerivAt_Ioo (neg_lt_self Real.pi_pos) zeroMode
      fieldContinuous.continuousOn (fun angle _ => differentiates angle)
      (derivativeContinuous.intervalIntegrable (-Real.pi) Real.pi)
    rw [periodicEndpoint, sub_self, mul_zero, zero_sub] at raw
    have periodEquality : (Real.pi : ℂ) - ((-Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
    rw [periodEquality] at raw
    change angularCoefficient field mode = 1 / (-2 * (Real.pi : ℂ) * Complex.I * (mode : ℂ)) *
      -(2 * (Real.pi : ℂ) * angularCoefficient derivative mode) at raw
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have modeNonzero : (mode : ℂ) ≠ 0 := by exact_mod_cast zeroMode
    have cancellation : (Complex.I * (mode : ℂ)) *
        (1 / (-2 * (Real.pi : ℂ) * Complex.I * (mode : ℂ)) *
          -(2 * (Real.pi : ℂ) * angularCoefficient derivative mode)) = angularCoefficient derivative mode := by
      field_simp
    exact (congrArg (fun value : ℂ => (Complex.I * (mode : ℂ)) * value) raw).trans cancellation |>.symm

theorem angularCoefficient_derivative {dimension : ℕ} (field derivative : ℝ → ComplexEuclidean dimension)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ angle : ℝ, HasDerivAt field (derivative angle) angle)
    (periodicEndpoint : field Real.pi = field (-Real.pi)) (mode : ℤ) :
    angularCoefficient derivative mode = (Complex.I * (mode : ℂ)) • angularCoefficient field mode := by
  apply PiLp.ext
  intro coordinate
  rw [angularCoefficient_component derivative derivativeContinuous coordinate mode]
  change angularCoefficient (fun angle => derivative angle coordinate) mode =
    (Complex.I * (mode : ℂ)) * angularCoefficient field mode coordinate
  rw [angularCoefficient_component field fieldContinuous coordinate mode]
  let projection : ComplexEuclidean dimension →L[ℂ] ℂ :=
    Grad.FourierGrade.euclideanComponent dimension coordinate
  apply angularCoefficient_scalar_derivative
  · exact projection.continuous.comp fieldContinuous
  · exact projection.continuous.comp derivativeContinuous
  · intro angle
    exact (projection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt angle (differentiates angle)
  · exact congrArg projection periodicEndpoint

theorem angularCoefficient_derivative_norm {dimension : ℕ}
    (field derivative : ℝ → ComplexEuclidean dimension)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ angle : ℝ, HasDerivAt field (derivative angle) angle)
    (periodicEndpoint : field Real.pi = field (-Real.pi)) (mode : ℤ) :
    ‖angularCoefficient derivative mode‖ = |(mode : ℝ)| * ‖angularCoefficient field mode‖ := by
  rw [angularCoefficient_derivative field derivative fieldContinuous derivativeContinuous differentiates periodicEndpoint,
    norm_smul, norm_mul, Complex.norm_I, one_mul]
  norm_cast

end Grad.BoundaryTrace
