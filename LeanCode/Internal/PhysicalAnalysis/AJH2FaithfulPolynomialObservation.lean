import AJH1PolynomialKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.BoundaryLift Grad.BoundaryTrace

/-- Strong original negative-half trace grades continuously observe every
ordinary Sobolev grade. This is an observation, not a change of analytic width. -/
theorem negativeTraceWeight_polynomial_lower (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ^ power ≤ negativeTraceWeight parameters (power + 1) (power + 1) mode := by
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  have product : annularFrequency mode.1 mode.2 ≤ (1 + |(mode.1 : ℝ)|) * (1 + |(mode.2 : ℝ)|) := by
    unfold annularFrequency
    nlinarith [mul_nonneg (abs_nonneg (mode.1 : ℝ)) (abs_nonneg (mode.2 : ℝ))]
  have exponential : 1 ≤ Real.exp (2 * boundaryPhase parameters mode.2) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (boundaryPhase_nonneg parameters mode.2))
  have square : (annularFrequency mode.1 mode.2 ^ power) ^ 2 * annularFrequency mode.1 mode.2 ≤
      Real.exp (2 * boundaryPhase parameters mode.2) *
        (1 + |(mode.1 : ℝ)|) ^ (2 * (power + 1)) * (1 + |(mode.2 : ℝ)|) ^ (2 * (power + 1)) := by
    calc
      _ = annularFrequency mode.1 mode.2 ^ (power * 2 + 1) := by rw [← pow_mul, ← pow_succ]
      _ ≤ annularFrequency mode.1 mode.2 ^ (2 * (power + 1)) := pow_le_pow_right₀ frequencyOne (by omega)
      _ ≤ ((1 + |(mode.1 : ℝ)|) * (1 + |(mode.2 : ℝ)|)) ^ (2 * (power + 1)) :=
        pow_le_pow_left₀ (annularFrequency_pos mode).le product _
      _ = (1 + |(mode.1 : ℝ)|) ^ (2 * (power + 1)) * (1 + |(mode.2 : ℝ)|) ^ (2 * (power + 1)) := mul_pow _ _ _
      _ ≤ _ := by
        have bound := mul_le_mul_of_nonneg_right exponential
          (mul_nonneg (by positivity : 0 ≤ (1 + |(mode.1 : ℝ)|) ^ (2 * (power + 1)))
            (by positivity : 0 ≤ (1 + |(mode.2 : ℝ)|) ^ (2 * (power + 1))))
        simpa only [one_mul, mul_assoc] using bound
  apply (Real.le_sqrt (pow_nonneg (annularFrequency_pos mode).le power)
    (negativeTraceWeightSq_pos parameters (power + 1) (power + 1) mode).le).2
  change _ ≤ _ * (annularFrequency mode.1 mode.2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (annularFrequency_pos mode)]
  exact square

def polynomialObservationFactor (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ power / negativeTraceWeight parameters (power + 1) (power + 1) mode

theorem polynomialObservationFactor_positive (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) :
    0 < polynomialObservationFactor parameters power mode :=
  div_pos (pow_pos (annularFrequency_pos mode) power) (negativeTraceWeight_pos parameters _ _ mode)

theorem polynomialObservationFactor_bound (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) :
    polynomialObservationFactor parameters power mode ≤ 1 := by
  rw [polynomialObservationFactor, div_le_one (negativeTraceWeight_pos parameters _ _ mode)]
  exact negativeTraceWeight_polynomial_lower parameters power mode

def polynomialObservationEntry (parameters : PhaseParameters) (power dimension : ℕ) (mode : ℤ × ℤ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  (polynomialObservationFactor parameters power mode : ℂ) • ContinuousLinearMap.id ℂ _

theorem polynomialObservationEntry_bound (parameters : PhaseParameters) (power dimension : ℕ) (mode : ℤ × ℤ) :
    ‖polynomialObservationEntry parameters power dimension mode‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro field
  change ‖(polynomialObservationFactor parameters power mode : ℂ) • field‖ ≤ 1 * ‖field‖
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (polynomialObservationFactor_positive parameters power mode).le]
  exact mul_le_mul_of_nonneg_right (polynomialObservationFactor_bound parameters power mode) (norm_nonneg _)

/-- Actual diagonal observation from the original strong trace carrier. -/
def polynomialObservation (parameters : PhaseParameters) (power dimension : ℕ) :
    NegativeTrace parameters (power + 1) (power + 1) dimension →L[ℂ] CellL2 dimension :=
  coefficientOperator parameters 0 (Equiv.refl _) (polynomialObservationEntry parameters power dimension)
    (by norm_num : (0 : ℝ) ≤ 1) (polynomialObservationEntry_bound parameters power dimension)

theorem polynomialObservation_apply (parameters : PhaseParameters) (power dimension : ℕ)
    (field : NegativeTrace parameters (power + 1) (power + 1) dimension) (mode : ℤ × ℤ) :
    polynomialObservation parameters power dimension field mode =
      (annularFrequency mode.1 mode.2 ^ power : ℂ) • negativeTraceCoefficient parameters (power + 1) (power + 1) field mode := by
  change (polynomialObservationFactor parameters power mode : ℂ) • field mode = _
  rw [negativeTraceCoefficient, smul_smul]
  congr 1
  unfold polynomialObservationFactor
  push_cast
  rfl

end Grad.AnnularRadialSmoothness
