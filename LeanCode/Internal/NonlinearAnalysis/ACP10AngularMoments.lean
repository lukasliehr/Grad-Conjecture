import ACP9ForceScalarMoments

noncomputable section
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

def angularCoefficientSequence (sequence : ℤ × ℤ → ℂ) (mode : ℤ × ℤ) : ℂ :=
  (Complex.I * (mode.1 : ℂ)) * sequence mode

theorem angularCoefficientSequence_moment_le (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (sequence : ℤ × ℤ → ℂ) (mode : ℤ × ℤ) :
    productMoment parameters power radius (angularCoefficientSequence sequence) mode ≤
      productMoment parameters (power + 1) radius sequence mode := by
  have modeNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by norm_cast
  have modeBound : |(mode.1 : ℝ)| ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.2 : ℝ)]
  unfold productMoment angularCoefficientSequence
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, modeNorm, pow_succ]
  have bound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right modeBound (norm_nonneg (sequence mode)))
    (mul_nonneg (coefficientRadialEnvelope_pos parameters mode.2 radius).le
      (pow_nonneg (annularFrequency_nonnegative mode.1 mode.2) power))
  exact bound.trans_eq (by ring)

theorem angularCoefficientSequence_moment_summable (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (sequence : ℤ × ℤ → ℂ)
    (summable : Summable (productMoment parameters (power + 1) radius sequence)) :
    Summable (productMoment parameters power radius (angularCoefficientSequence sequence)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (angularCoefficientSequence_moment_le parameters power radius sequence) summable

theorem angularCoefficientSequence_moment_bound (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (sequence : ℤ × ℤ → ℂ)
    (summable : Summable (productMoment parameters (power + 1) radius sequence)) :
    (∑' mode, productMoment parameters power radius (angularCoefficientSequence sequence) mode) ≤
      ∑' mode, productMoment parameters (power + 1) radius sequence mode :=
  (angularCoefficientSequence_moment_summable parameters power radius sequence summable).tsum_le_tsum
    (angularCoefficientSequence_moment_le parameters power radius sequence) summable

/-- Exact one-extra-moment cost of R(delta r0); no high-grade smallness. -/
theorem rotatedForceScalarMoment_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius
      (angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius
      (angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component radial radius)) mode) ≤
      forceFourierConstant parameters L kind (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 7) := by
  have summable := forceScalarMoment_summable parameters L rho epsilon field kind low component
    (tangential + 1) radial radius nonnegative bounded
  refine ⟨angularCoefficientSequence_moment_summable parameters tangential radius _ summable, ?_⟩
  apply (angularCoefficientSequence_moment_bound parameters tangential radius _ summable).trans
  simpa only [show tangential + 1 + radial + 6 = tangential + radial + 7 by omega] using
    forceScalarMoment_bound parameters L rho epsilon field kind low component
      (tangential + 1) radial radius nonnegative bounded

end Grad.ActualCurrentPrimitives
