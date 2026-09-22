import SeedQuantitative

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame

def sequenceWeight (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) : ℝ :=
  Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade

theorem sequenceWeight_nonnegative (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    0 ≤ sequenceWeight phase grade cell := by
  unfold sequenceWeight
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (by rw [cellPolynomialWeight_formula]; positivity) _)

theorem weighted_norm (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) (value : OperatorValue 2 2) :
    ‖(sequenceWeight phase grade cell : ℂ) • value‖ = sequenceWeight phase grade cell * ‖value‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (sequenceWeight_nonnegative phase grade cell)]

def coefficientSequence (phase : PhaseParameters) (grade : ℕ)
    (coefficient : Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2) : WeightedSequence := by
  refine ⟨fun cell => (sequenceWeight phase grade cell : ℂ) •
    coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin, ?_⟩
  apply memℓp_gen
  have summable := (coefficient_envelope_bound phase grade coefficient
    (fun cell => coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin)
    (fun _ => rfl)).1
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  have normSummable : Summable (fun cell => ‖(sequenceWeight phase grade cell : ℂ) •
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin‖) :=
    summable.congr (fun cell => (weighted_norm phase grade cell _).symm)
  simpa only [oneToReal, Real.rpow_one] using normSummable

theorem weightedSequence_norm (sequence : WeightedSequence) :
    ‖sequence‖ = ∑' cell, ‖sequence cell‖ := by
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [lp.norm_eq_tsum_rpow (by norm_num), oneToReal]
  simp only [Real.rpow_one, div_one]

theorem coefficientSequence_norm_le (phase : PhaseParameters) (grade : ℕ)
    (coefficient : Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2) :
    ‖coefficientSequence phase grade coefficient‖ ≤ envelopeComparison phase grade * ‖coefficient‖ := by
  rw [weightedSequence_norm]
  change (∑' cell, ‖(sequenceWeight phase grade cell : ℂ) •
    coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin‖) ≤ _
  simp only [weighted_norm]
  exact (coefficient_envelope_bound phase grade coefficient
    (fun cell => coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin)
    (fun _ => rfl)).2

def coefficientSequenceLinear (phase : PhaseParameters) (grade : ℕ) :
    Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2 →ₗ[ℂ] WeightedSequence where
  toFun := coefficientSequence phase grade
  map_add' first second := by
    apply lp.ext
    funext cell
    change (sequenceWeight phase grade cell : ℂ) •
      coefficientDerivative (first + second) cell (zeroDerivativeIndexAt grade) seedOrigin = _
    rw [coefficientDerivative_add_apply, smul_add]
    rfl
  map_smul' scalar coefficient := by
    apply lp.ext
    funext cell
    change (sequenceWeight phase grade cell : ℂ) •
      coefficientDerivative (scalar • coefficient) cell (zeroDerivativeIndexAt grade) seedOrigin = _
    rw [coefficientDerivative_smul_apply, smul_comm]
    rfl

def coefficientSequenceCLM (phase : PhaseParameters) (grade : ℕ) :
    Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2 →L[ℂ] WeightedSequence :=
  (coefficientSequenceLinear phase grade).mkContinuous (envelopeComparison phase grade)
    (coefficientSequence_norm_le phase grade)

theorem coefficientSequenceCLM_apply (phase : PhaseParameters) (grade : ℕ)
    (coefficient : Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2) (cell : ℤ) :
    coefficientSequenceCLM phase grade coefficient cell = (sequenceWeight phase grade cell : ℂ) •
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) seedOrigin := rfl

end Grad.Constraints.Seed
