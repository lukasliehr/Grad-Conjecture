import SCS26FourierSumInterchange

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.SourceCollarAngular
open Grad.SourceCollarDivision

theorem angularCoefficient_norm_le {dimension : ℕ} (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (dominated : ∀ angle ∈ Icc (-Real.pi) Real.pi, ‖field angle‖ ≤ bound) (mode : ℤ) :
    ‖angularCoefficient field mode‖ ≤ bound := by
  have square := angular_scaled_bessel_sup field continuousField 1 bound (by norm_num)
    (fun angle inside => by simpa only [one_mul] using dominated angle inside) {mode}
  simp only [Finset.sum_singleton, one_mul] at square
  exact (sq_le_sq₀ (norm_nonneg _) boundNonnegative).mp square

/-- Multiplying an arbitrary continuous source by an absolutely summable
angular Fourier kernel gives its genuine coefficient convolution. -/
theorem angularCoefficient_series_product {Index : Type*} [Countable Index] {dimension : ℕ}
    (coefficients : Index → ℂ) (frequency : Index → ℤ)
    (norms : Summable (fun index => ‖coefficients index‖))
    (kernel : ℝ → ℂ) (source : ℝ → ComplexEuclidean dimension)
    (continuousSource : Continuous source) (bound : ℝ)
    (dominated : ∀ angle ∈ Icc (-Real.pi) Real.pi, ‖source angle‖ ≤ bound)
    (kernelSeries : ∀ angle ∈ Icc (-Real.pi) Real.pi,
      HasSum (fun index => cellExponential (frequency index) angle * coefficients index) (kernel angle))
    (mode : ℤ) :
    HasSum (fun index => coefficients index • angularCoefficient source (mode - frequency index))
      (angularCoefficient (fun angle => kernel angle • source angle) mode) := by
  let fields := fun index angle => (cellExponential (frequency index) angle * coefficients index) • source angle
  have integrated := angularCoefficient_hasSum fields (fun angle => kernel angle • source angle)
    (fun index => ((cellExponential_smooth (frequency index)).continuous.mul continuous_const).smul continuousSource)
    (fun index => ‖coefficients index‖ * bound) (norms.mul_right bound)
    (fun index angle inside => by
      simpa only [fields, norm_smul, norm_mul, cellExponential_norm, one_mul] using
        mul_le_mul_of_nonneg_left (dominated angle inside) (norm_nonneg (coefficients index)))
    (fun angle inside =>
      (ContinuousLinearMap.toSpanSingleton ℂ (source angle)).hasSum (kernelSeries angle inside)) mode
  apply integrated.congr_fun
  intro index
  have expression : fields index = coefficients index •
      (fun angle => cellExponential (frequency index) angle • source angle) := by
    funext angle
    simp only [fields, Pi.smul_apply, smul_smul]
    rw [mul_comm]
  rw [expression, angularCoefficient_smul_continuous, angularCoefficient_character_mul]

end Grad.SourceCollarFullSource
