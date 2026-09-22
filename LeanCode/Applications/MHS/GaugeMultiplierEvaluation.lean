import GaugeMultiplier

noncomputable section

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion
open Grad.Constraints.Multipliers

def derivativeEvaluationLinear {dimension : ℕ} (phase : PhaseParameters)
    (cell : ℤ) (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) :
    GradeCore phase dimension (order + 3) →ₗ[ℂ] ComplexEuclidean dimension :=
  (ContinuousMap.evalCLM ℂ point).toLinearMap.comp
    ((Grad.Constraints.closedDerivativeLinear order word).comp
      (coreCellLinear phase cell))

theorem derivativeEvaluation_bound {dimension : ℕ} (phase : PhaseParameters)
    (cell : ℤ) (order : ℕ) (word : CartesianWord order) (point : ClosedDisk)
    (field : GradeCore phase dimension (order + 3)) :
    ‖derivativeEvaluationLinear phase cell order word point field‖ ≤
      originalDerivativeSumConstant phase order * ‖field‖ := by
  have summable : Summable (fun index : ℤ => ‖closedDerivative (field.toCore.1 index) order word‖) := by
    simpa only [pow_zero, one_mul] using
      originalClosedDerivative_frequency_summable phase field.toCore word 0
  have totalBound := originalClosedDerivative_frequency_tsum_bound phase field word 0 (by omega)
  simp only [pow_zero, one_mul] at totalBound
  exact ((ContinuousMap.norm_coe_le_norm (closedDerivative (field.toCore.1 cell) order word) point).trans
    (summable.le_tsum cell (fun _ _ => norm_nonneg _))).trans totalBound

def completedDerivativeEvaluation {dimension : ℕ} (phase : PhaseParameters)
    (cell : ℤ) (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) :
    AGrade phase dimension (order + 3) →L[ℂ] ComplexEuclidean dimension :=
  denseCoreExtension phase (derivativeEvaluationLinear phase cell order word point)
    (originalDerivativeSumConstant phase order) (derivativeEvaluation_bound phase cell order word point)

theorem completedDerivativeEvaluation_eta {dimension : ℕ} (phase : PhaseParameters)
    (cell : ℤ) (order : ℕ) (word : CartesianWord order) (point : ClosedDisk)
    (field : GradeCore phase dimension (order + 3)) :
    completedDerivativeEvaluation phase cell order word point (aGradeEta phase field) =
      closedDerivative (field.toCore.1 cell) order word point :=
  denseCoreExtension_apply_eta phase _ _ _ field

theorem smoothMultiplier_derivative_hasSum {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (cell : ℤ) (order : ℕ)
    (word : CartesianWord order) (point : ClosedDisk) :
    HasSum (fun shift : ℤ => coefficients shift
      (closedDerivative (field.1 (cell - shift)) order word point))
      (closedDerivative ((smoothMultiplier phase coefficients summable field).1 cell) order word point) := by
  let modes : ℤ → AGrade phase sourceDimension (order + 3) →L[ℂ]
      AGrade phase targetDimension (order + 3) :=
    fun shift => singleModeCompleted phase shift (coefficients shift)
  have modeSeries : Summable modes := completedModes_summable phase coefficients (summable (order + 3))
  have applied := (ContinuousLinearMap.apply ℂ (AGrade phase targetDimension (order + 3))
    (aGradeEta phase (GradeCore.ofCoreLinear (grade := order + 3) field))).hasSum modeSeries.hasSum
  have evaluated := (completedDerivativeEvaluation phase cell order word point).hasSum applied
  change HasSum (fun shift => completedDerivativeEvaluation phase cell order word point
      (singleModeCompleted phase shift (coefficients shift)
        (aGradeEta phase (GradeCore.ofCoreLinear field))))
    (completedDerivativeEvaluation phase cell order word point
      (completedMultiplier phase coefficients (aGradeEta phase (GradeCore.ofCoreLinear field)))) at evaluated
  rw [← smoothMultiplier_eta phase coefficients summable field (order + 3),
    completedDerivativeEvaluation_eta] at evaluated
  simp only [singleModeCompleted_eta, completedDerivativeEvaluation_eta] at evaluated
  change HasSum (fun shift => closedDerivative
    (valueMapJet (coefficients shift) (field.1 (cell - shift))) order word point)
    (closedDerivative ((smoothMultiplier phase coefficients summable field).1 cell) order word point) at evaluated
  simp only [valueMapJet_derivative] at evaluated
  exact evaluated

theorem smoothMultiplier_preserves_zero_first_jets {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension)
    (zeroJets : ∀ cell, Grad.Constraints.ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, Grad.Constraints.ZeroCartesianFirstJets
      ((smoothMultiplier phase coefficients summable field).1 cell) := by
  intro cell order orderBound word
  have series := smoothMultiplier_derivative_hasSum phase coefficients summable field cell order word
    ⟨0, by simp [closedUnitDisk]⟩
  simp only [zeroJets _ order orderBound word, map_zero] at series
  exact series.unique hasSum_zero

end Grad.Constraints.Gauges
