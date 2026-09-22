import ANH4BoundaryL2

noncomputable section

open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.BoundaryTrace Grad.Constraints

theorem lowAngularModes_iff (mode : ℤ) : mode ∈ lowAngularModes ↔ |mode| < 3 := by
  simp only [lowAngularModes, Finset.mem_insert, Finset.mem_singleton]
  rw [abs_lt]
  omega

theorem highMode_sq (mode : ℤ) (high : mode ∉ lowAngularModes) :
    (9 : ℝ) ≤ |(mode : ℝ)| ^ 2 := by
  have bound : (3 : ℤ) ≤ |mode| := by
    rw [lowAngularModes_iff] at high
    omega
  have realBound : (3 : ℝ) ≤ |(mode : ℝ)| := by exact_mod_cast bound
  nlinarith

/-- Parseval and the literal derivative multiplier give the exact factor
nine on the complement of the five low angular modes. -/
theorem circle_high_poincare {dimension : ℕ}
    (field derivative : ℝ → ComplexEuclidean dimension)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ angle : ℝ, HasDerivAt field (derivative angle) angle)
    (periodicEndpoint : field Real.pi = field (-Real.pi))
    (high : ∀ mode ∈ lowAngularModes, angularCoefficient field mode = 0) :
    9 * (∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) ≤
      ∫ angle in -Real.pi..Real.pi, ‖derivative angle‖ ^ 2 := by
  have fieldSum := angular_hasSum_sq field fieldContinuous
  have derivativeSum := angular_hasSum_sq derivative derivativeContinuous
  have termBound (mode : ℤ) : 9 * ‖angularCoefficient field mode‖ ^ 2 ≤
      ‖angularCoefficient derivative mode‖ ^ 2 := by
    by_cases low : mode ∈ lowAngularModes
    · rw [high mode low, norm_zero, zero_pow (by decide), mul_zero]
      exact sq_nonneg _
    · rw [angularCoefficient_derivative_norm field derivative fieldContinuous
        derivativeContinuous differentiates periodicEndpoint, mul_pow]
      exact mul_le_mul_of_nonneg_right (highMode_sq mode low) (sq_nonneg _)
  have summed := (fieldSum.summable.mul_left 9).tsum_le_tsum termBound derivativeSum.summable
  rw [tsum_mul_left, fieldSum.tsum_eq, derivativeSum.tsum_eq] at summed
  have positive : 0 < (2 * Real.pi)⁻¹ := by positivity
  apply le_of_mul_le_mul_left (a := (2 * Real.pi)⁻¹) _ positive
  nlinarith [summed]

end Grad.CircularHighWeak
