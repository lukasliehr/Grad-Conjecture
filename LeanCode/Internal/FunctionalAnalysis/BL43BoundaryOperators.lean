import BL42CoefficientOperator
import MultiplierInterface

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

variable {sourceDimension targetDimension : ℕ}

theorem boundaryEnvelopeTerm_nonneg (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) : 0 ≤ Multipliers.envelopeTerm parameters grade coefficients shift :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (zero_le_one.trans (cellPolynomialWeight_one_le shift)) _)) (norm_nonneg _)

def multiplierShiftEntry (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) (mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  ((boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1, mode.2 - shift) : ℝ) : ℂ) • coefficients shift

theorem multiplierShiftEntry_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) (mode : ℤ × ℤ) :
    ‖multiplierShiftEntry parameters grade coefficients shift mode‖ ≤
      Multipliers.envelopeTerm parameters grade coefficients shift := by
  have ratioPos : 0 < boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1, mode.2 - shift) :=
    div_pos (boundaryWeight_pos parameters grade mode) (boundaryWeight_pos parameters grade _)
  have ratioBound : boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1, mode.2 - shift) ≤
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade := by
    rw [div_le_iff₀ (boundaryWeight_pos parameters grade _)]
    have shiftLaw := boundaryWeight_cell_shift_le parameters grade mode.1 mode.2 shift
    simpa only [Prod.mk.eta] using shiftLaw
  unfold multiplierShiftEntry Multipliers.envelopeTerm
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ratioPos]
  exact mul_le_mul ratioBound le_rfl (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (zero_le_one.trans (cellPolynomialWeight_one_le shift)) _))

/-- The single-shift boundary multiplier operator with the literal N6
envelope coefficient bound. -/
def multiplierShiftOperator (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) :
    BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean targetDimension) grade :=
  coefficientOperator parameters grade (cellPairTranslation shift)
    (multiplierShiftEntry parameters grade coefficients shift)
    (boundaryEnvelopeTerm_nonneg parameters grade coefficients shift)
    (multiplierShiftEntry_norm_le parameters grade coefficients shift)

theorem multiplierShiftOperator_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) :
    ‖multiplierShiftOperator parameters grade coefficients shift‖ ≤
      Multipliers.envelopeTerm parameters grade coefficients shift :=
  coefficientOperator_norm_le parameters grade _ _ _ _

theorem multiplierShiftOperator_summable (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (envelopeSummable : Summable (Multipliers.envelopeTerm parameters grade coefficients)) :
    Summable (fun shift : ℤ => multiplierShiftOperator parameters grade coefficients shift) :=
  Summable.of_norm_bounded envelopeSummable
    (fun shift => multiplierShiftOperator_norm_le parameters grade coefficients shift)

/-- The actual N28 boundary multiplication operator: the operator-norm sum
of all literal shifted multiplier rows. -/
def boundaryMultiplication (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean targetDimension) grade :=
  ∑' shift : ℤ, multiplierShiftOperator parameters grade coefficients shift

theorem boundaryMultiplication_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (envelopeSummable : Summable (Multipliers.envelopeTerm parameters grade coefficients)) :
    ‖boundaryMultiplication parameters grade coefficients‖ ≤
      Multipliers.envelope parameters grade coefficients := by
  have normSummable : Summable (fun shift : ℤ =>
      ‖multiplierShiftOperator parameters grade coefficients shift‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun shift => multiplierShiftOperator_norm_le parameters grade coefficients shift)
      envelopeSummable
  calc ‖boundaryMultiplication parameters grade coefficients‖
      ≤ ∑' shift : ℤ, ‖multiplierShiftOperator parameters grade coefficients shift‖ :=
        norm_tsum_le_tsum_norm normSummable
    _ ≤ ∑' shift : ℤ, Multipliers.envelopeTerm parameters grade coefficients shift :=
        normSummable.tsum_le_tsum
          (fun shift => multiplierShiftOperator_norm_le parameters grade coefficients shift)
          envelopeSummable
    _ = Multipliers.envelope parameters grade coefficients := rfl

/-- Evaluation of operators at one fixed field, as a continuous linear map. -/
def operatorEvaluation (parameters : PhaseParameters) (grade : ℕ)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) :
    (BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →L[ℂ]
        BoundaryGrade parameters (ComplexEuclidean targetDimension) grade) →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean targetDimension) grade :=
  LinearMap.mkContinuous
    { toFun := fun operator => operator field
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖field‖ (fun operator => by
      rw [mul_comm]
      exact operator.le_opNorm field)

theorem multiplierShiftOperator_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade)
    (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade
        (multiplierShiftOperator parameters grade coefficients shift field) mode =
      coefficients shift (boundaryCoefficient parameters grade field (mode.1, mode.2 - shift)) := by
  have applyLaw : multiplierShiftOperator parameters grade coefficients shift field mode =
      ((boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1, mode.2 - shift) : ℝ) : ℂ) •
        coefficients shift (field (mode.1, mode.2 - shift)) := rfl
  unfold boundaryCoefficient
  rw [applyLaw, smul_smul]
  have modeNe : ((boundaryWeight parameters grade mode : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne'
  have scalarLaw : ((boundaryWeight parameters grade mode : ℝ) : ℂ)⁻¹ *
      ((boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1, mode.2 - shift) : ℝ) : ℂ) =
        ((boundaryWeight parameters grade (mode.1, mode.2 - shift) : ℝ) : ℂ)⁻¹ := by
    rw [Complex.ofReal_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ modeNe, one_mul]
  rw [scalarLaw, ← map_smul]

theorem boundaryMultiplication_coefficient_hasSum (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (envelopeSummable : Summable (Multipliers.envelopeTerm parameters grade coefficients))
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ => coefficients shift
        (boundaryCoefficient parameters grade field (mode.1, mode.2 - shift)))
      (boundaryCoefficient parameters grade
        (boundaryMultiplication parameters grade coefficients field) mode) := by
  have operatorSum :=
    (multiplierShiftOperator_summable parameters grade coefficients envelopeSummable).hasSum
  have applied := (operatorEvaluation parameters grade field).hasSum operatorSum
  have coefficientSum := (boundaryCoefficientCLM parameters grade mode).hasSum applied
  have termLaw : ∀ shift : ℤ, boundaryCoefficientCLM parameters grade mode
      (operatorEvaluation parameters grade field
        (multiplierShiftOperator parameters grade coefficients shift)) =
      coefficients shift (boundaryCoefficient parameters grade field (mode.1, mode.2 - shift)) := by
    intro shift
    rw [show operatorEvaluation parameters grade field
        (multiplierShiftOperator parameters grade coefficients shift) =
          multiplierShiftOperator parameters grade coefficients shift field from rfl,
      boundaryCoefficientCLM_apply, multiplierShiftOperator_coefficient]
  have targetLaw : boundaryCoefficientCLM parameters grade mode
      (operatorEvaluation parameters grade field
        (∑' shift : ℤ, multiplierShiftOperator parameters grade coefficients shift)) =
      boundaryCoefficient parameters grade
        (boundaryMultiplication parameters grade coefficients field) mode := rfl
  rw [← targetLaw]
  simpa only [termLaw] using coefficientSum

end Grad.BoundaryLift
