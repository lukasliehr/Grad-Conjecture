import MultiplierCompletion

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState

theorem envelopeTerm_nonnegative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) : 0 ≤ envelopeTerm parameters grade coefficients shift :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _)) (norm_nonneg _)

theorem singleModeCompleted_envelope_bound {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (shift : ℤ) :
    ‖singleModeCompleted (grade := grade) parameters shift (coefficients shift)‖ ≤
      multiplierConstant grade parameters.gamma * envelopeTerm parameters grade coefficients shift := by
  simpa only [shiftBound, envelopeTerm, mul_assoc] using
    singleModeCompleted_norm_le (grade := grade) parameters shift (coefficients shift)

theorem singleModeCompleted_norm_summable {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm parameters grade coefficients)) :
    Summable (fun shift => ‖singleModeCompleted (grade := grade) parameters shift (coefficients shift)‖) :=
  Summable.of_nonneg_of_le (fun shift => norm_nonneg
    (singleModeCompleted (grade := grade) parameters shift (coefficients shift)))
    (singleModeCompleted_envelope_bound (grade := grade) parameters coefficients)
    (summable.mul_left (multiplierConstant grade parameters.gamma))

/-- Norm-convergent sum of the actual single-mode completed operators.
No assumption is made about higher c_r values. -/
def completedMultiplier {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    AGrade parameters sourceDimension grade →L[ℂ] AGrade parameters targetDimension grade :=
  ∑' shift, singleModeCompleted parameters shift (coefficients shift)

theorem completedMultiplier_norm_le {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm parameters grade coefficients)) :
    ‖completedMultiplier (grade := grade) parameters coefficients‖ ≤
      multiplierConstant grade parameters.gamma * envelope parameters grade coefficients := by
  let modes := fun shift => singleModeCompleted (grade := grade) parameters shift (coefficients shift)
  have normSummable : Summable (fun shift => ‖modes shift‖) :=
    singleModeCompleted_norm_summable (grade := grade) parameters coefficients summable
  have firstBound : ‖∑' shift, modes shift‖ ≤ ∑' shift, ‖modes shift‖ :=
    norm_tsum_le_tsum_norm (f := modes) normSummable
  have secondBound : (∑' shift, ‖modes shift‖) ≤
      ∑' shift, multiplierConstant grade parameters.gamma * envelopeTerm parameters grade coefficients shift :=
    Summable.tsum_le_tsum
      (fun shift => singleModeCompleted_envelope_bound (grade := grade) parameters coefficients shift)
      normSummable (summable.mul_left (multiplierConstant grade parameters.gamma))
  exact firstBound.trans (secondBound.trans_eq tsum_mul_left)

theorem completedMultiplier_bound {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm parameters grade coefficients))
    (field : AGrade parameters sourceDimension grade) :
    ‖completedMultiplier parameters coefficients field‖ ≤
      multiplierConstant grade parameters.gamma * envelope parameters grade coefficients * ‖field‖ :=
  ((completedMultiplier parameters coefficients).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (completedMultiplier_norm_le parameters coefficients summable) (norm_nonneg _))

theorem completedMultiplier_rows {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm parameters grade coefficients))
    (field : GradeCore parameters sourceDimension grade) (output : ℤ) :
    HasSum (multiplierRow parameters coefficients field output)
      (completedCoordinates parameters (completedMultiplier parameters coefficients (aGradeEta parameters field)) output) := by
  have normSummable := singleModeCompleted_norm_summable (grade := grade) parameters coefficients summable
  let modes := fun shift => singleModeCompleted (grade := grade) parameters shift (coefficients shift)
  have sumModes : Summable modes := Summable.of_norm (f := modes) normSummable
  have hasModes : HasSum modes (∑' shift, modes shift) := sumModes.hasSum
  have applied := (ContinuousLinearMap.apply ℂ (AGrade parameters targetDimension grade)
    (aGradeEta parameters field)).hasSum (f := modes) hasModes
  have coordinateSum := (completedCoordinates parameters).hasSum applied
  have cellSum := (lp.evalCLM ℂ (fun _ : ℤ => CartesianGradeRow targetDimension grade) 2 output).hasSum coordinateSum
  change HasSum (fun shift => completedCoordinates parameters
      (singleModeCompleted parameters shift (coefficients shift) (aGradeEta parameters field)) output)
    (completedCoordinates parameters (completedMultiplier parameters coefficients (aGradeEta parameters field)) output) at cellSum
  simpa only [singleModeCompleted_row] using cellSum

theorem sameGradeMultiplier : MultiplierGoal := by
  intro grade gamma gammaPositive _
  refine ⟨multiplierConstant grade gamma,
    multiplierConstant_nonnegative grade gamma gammaPositive.le, ?_⟩
  intro parameters gammaEquality sourceDimension targetDimension coefficients summable
  refine ⟨completedMultiplier parameters coefficients, ?_, completedMultiplier_rows parameters coefficients summable⟩
  intro field
  simpa only [gammaEquality] using completedMultiplier_bound parameters coefficients summable field

end Grad.Constraints.Multipliers
