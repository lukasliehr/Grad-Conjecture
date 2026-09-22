import BKA8TraceInputs

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

theorem splitTangentialWeight_le_frequency_pow (angular cell : ℕ)
    (mode : ℤ × ℤ) :
    splitTangentialWeight angular cell mode ≤
      annularFrequency mode.1 mode.2 ^ (angular + cell) := by
  have angularBase : 1 + |(mode.1 : ℝ)| ≤
      annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.2 : ℝ)]
  have cellBase : 1 + |(mode.2 : ℝ)| ≤
      annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ)]
  unfold splitTangentialWeight
  calc
    (1 + |(mode.1 : ℝ)|) ^ angular * (1 + |(mode.2 : ℝ)|) ^ cell
        ≤ annularFrequency mode.1 mode.2 ^ angular *
            annularFrequency mode.1 mode.2 ^ cell :=
          mul_le_mul
            (pow_le_pow_left₀ (by positivity) angularBase angular)
            (pow_le_pow_left₀ (by positivity) cellBase cell)
            (pow_nonneg (by positivity) _)
            (pow_nonneg (annularFrequency_pos mode).le _)
    _ = _ := by rw [pow_add]

theorem negativeTraceWeight_le_sourceBoundaryWeight (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    negativeTraceWeight parameters angular cell mode ≤
      sourceBoundaryWeight parameters (angular + cell) mode := by
  let frequency := annularFrequency mode.1 mode.2
  let power := angular + cell
  have splitBound := splitTangentialWeight_le_frequency_pow angular cell mode
  have splitSq := pow_le_pow_left₀
    (splitTangentialWeight_pos angular cell mode).le splitBound 2
  have inverseBound : frequency⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (annularFrequency_one_le mode)
  have negativeFactor :
      negativeTraceWeightSq parameters angular cell mode =
        Real.exp (2 * boundaryPhase parameters mode.2) *
          splitTangentialWeight angular cell mode ^ 2 * frequency⁻¹ := by
    unfold negativeTraceWeightSq splitTangentialWeight
    dsimp only [frequency]
    rw [mul_pow]
    rw [show 2 * angular = angular * 2 by omega,
      show 2 * cell = cell * 2 by omega, pow_mul, pow_mul]
    ring
  have sourceFactor :
      sourceBoundaryWeight parameters power mode ^ 2 =
        Real.exp (2 * boundaryPhase parameters mode.2) *
          (frequency ^ power) ^ 2 := by
    unfold sourceBoundaryWeight
    dsimp only [frequency, power]
    rw [mul_pow, two_mul, Real.exp_add]
    ring
  have squareBound :
      negativeTraceWeightSq parameters angular cell mode ≤
        sourceBoundaryWeight parameters power mode ^ 2 := by
    rw [negativeFactor, sourceFactor]
    have firstNonneg :
        0 ≤ Real.exp (2 * boundaryPhase parameters mode.2) *
          splitTangentialWeight angular cell mode ^ 2 := by positivity
    calc
      Real.exp (2 * boundaryPhase parameters mode.2) *
            splitTangentialWeight angular cell mode ^ 2 * frequency⁻¹
      _ ≤ (Real.exp (2 * boundaryPhase parameters mode.2) *
              splitTangentialWeight angular cell mode ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left inverseBound firstNonneg
      _ ≤ Real.exp (2 * boundaryPhase parameters mode.2) *
          (frequency ^ power) ^ 2 := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left splitSq (Real.exp_pos _).le
  apply (sq_le_sq₀ (negativeTraceWeight_pos parameters angular cell mode).le
    (sourceBoundaryWeight_pos parameters power mode).le).mp
  unfold negativeTraceWeight
  rw [Real.sq_sqrt
    (negativeTraceWeightSq_pos parameters angular cell mode).le]
  exact squareBound

def sourceToNegativeRatio (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  negativeTraceWeight parameters angular cell mode /
    sourceBoundaryWeight parameters (angular + cell) mode

theorem sourceToNegativeRatio_nonnegative (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    0 ≤ sourceToNegativeRatio parameters angular cell mode := by
  unfold sourceToNegativeRatio
  exact div_nonneg (negativeTraceWeight_pos parameters angular cell mode).le
    (sourceBoundaryWeight_pos parameters (angular + cell) mode).le

theorem sourceToNegativeRatio_le_one (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    sourceToNegativeRatio parameters angular cell mode ≤ 1 := by
  rw [sourceToNegativeRatio, div_le_one
    (sourceBoundaryWeight_pos parameters (angular + cell) mode)]
  exact negativeTraceWeight_le_sourceBoundaryWeight parameters angular cell mode

theorem sourceToNegativeRatio_norm_le_one (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    ‖(sourceToNegativeRatio parameters angular cell mode : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg
    (sourceToNegativeRatio_nonnegative parameters angular cell mode)]
  exact sourceToNegativeRatio_le_one parameters angular cell mode

/-- An exact source-boundary field at total power `angular+cell`, embedded
coefficientwise in the AH16 negative-half carrier. -/
def sourceBoundaryToNegative {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    SourceBoundary dimension →L[ℂ] NegativeTrace parameters angular cell dimension :=
  sequenceMultiplier
    (fun mode => (sourceToNegativeRatio parameters angular cell mode : ℂ))
    1 zero_le_one (sourceToNegativeRatio_norm_le_one parameters angular cell)

theorem sourceBoundaryToNegative_bound {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : SourceBoundary dimension) :
    ‖sourceBoundaryToNegative parameters angular cell field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one
    (sourceToNegativeRatio_norm_le_one parameters angular cell) field‖ ≤ _
  simpa only [one_mul] using sequenceMultiplierValue_bound
    (fun mode => (sourceToNegativeRatio parameters angular cell mode : ℂ))
    1 zero_le_one (sourceToNegativeRatio_norm_le_one parameters angular cell) field

private theorem sourceBoundaryToNegative_raw {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (field : SourceBoundary dimension)
    (mode : ℤ × ℤ) :
    sourceBoundaryToNegative parameters angular cell field mode =
      (sourceToNegativeRatio parameters angular cell mode : ℂ) • field mode := by
  have result := sequenceMultiplier_apply
    (fun mode => (sourceToNegativeRatio parameters angular cell mode : ℂ))
    1 zero_le_one (sourceToNegativeRatio_norm_le_one parameters angular cell) field mode
  unfold sourceBoundaryToNegative
  with_reducible exact result

theorem sourceBoundaryToNegative_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (field : SourceBoundary dimension)
    (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell field) mode =
      sourceBoundaryCoefficient parameters (angular + cell) field mode := by
  unfold negativeTraceCoefficient sourceBoundaryCoefficient
  rw [sourceBoundaryToNegative_raw]
  simp only [smul_smul]
  congr 1
  unfold sourceToNegativeRatio
  push_cast
  field_simp [
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (sourceBoundaryWeight_pos parameters (angular + cell) mode).ne']

end Grad.BoundaryKernelAction
