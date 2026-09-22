import BKB1FullKernel
import BL43BoundaryOperators

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

def fullNegativeShiftEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  ((negativeWeightRatio parameters angular cell shift mode : ℂ)) •
    kernel.entry shift (twoFrequencyTranslation shift mode)

theorem fullNegativeShiftEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ‖fullNegativeShiftEntry parameters angular cell kernel shift mode‖ ≤
      negativeShiftCost parameters angular cell shift * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (negativeWeightRatio_nonnegative parameters angular cell shift mode)]
  exact mul_le_mul
    (negativeWeightRatio_le parameters angular cell shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode))
    (norm_nonneg _) (negativeShiftCost_nonnegative parameters angular cell shift)

def fullNegativeShiftAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    NegativeTrace parameters angular cell sourceDimension →L[ℂ]
      NegativeTrace parameters angular cell targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (fullNegativeShiftEntry parameters angular cell kernel shift)
    (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
      (fullKernelEntryNorm_nonnegative kernel shift))
    (fullNegativeShiftEntry_norm_le parameters angular cell kernel shift)

theorem fullNegativeShiftAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    ‖fullNegativeShiftAction parameters angular cell kernel shift‖ ≤
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ (angular + cell + 1) *
          kernel.entryNorm shift := by
  unfold fullNegativeShiftAction
  simpa only [negativeShiftCost, mul_assoc] using
    coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
      (fullNegativeShiftEntry parameters angular cell kernel shift)
      (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullNegativeShiftEntry_norm_le parameters angular cell kernel shift)

theorem fullNegativeShiftAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ)
    (field : NegativeTrace parameters angular cell sourceDimension)
    (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeShiftAction parameters angular cell kernel shift field) mode =
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (negativeTraceCoefficient parameters angular cell field
          (twoFrequencyTranslation shift mode)) := by
  unfold negativeTraceCoefficient
  have rawApply :
      fullNegativeShiftAction parameters angular cell kernel shift field mode =
        (negativeWeightRatio parameters angular cell shift mode : ℂ) •
          kernel.entry shift (twoFrequencyTranslation shift mode)
            (field (twoFrequencyTranslation shift mode)) := by
    have result := coefficientOperator_apply parameters 0
      (twoFrequencyTranslation shift)
      (fullNegativeShiftEntry parameters angular cell kernel shift)
      (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullNegativeShiftEntry_norm_le parameters angular cell kernel shift) field mode
    unfold fullNegativeShiftAction
    with_reducible simpa only [fullNegativeShiftEntry, smul_apply] using result
  rw [rawApply, map_smul]
  simp only [smul_smul]
  congr 1
  unfold negativeWeightRatio
  push_cast
  field_simp [
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (negativeTraceWeight_pos parameters angular cell
      (twoFrequencyTranslation shift mode)).ne']

theorem fullNegativeShiftAction_summable {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    Summable (fun shift : ℤ × ℤ =>
      fullNegativeShiftAction parameters angular cell kernel shift) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun shift => norm_nonneg _)
    (fullNegativeShiftAction_norm_le parameters angular cell kernel)
    (kernel.moments (angular + cell + 1))

/-- AH18 on the full, input-mode-dependent AE7 kernel. -/
def fullNegativeKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    NegativeTrace parameters angular cell sourceDimension →L[ℂ]
      NegativeTrace parameters angular cell targetDimension :=
  ∑' shift : ℤ × ℤ, fullNegativeShiftAction parameters angular cell kernel shift

theorem fullNegativeKernelAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    ‖fullNegativeKernelAction parameters angular cell kernel‖ ≤
      fullKernelMoment parameters (angular + cell + 1) kernel := by
  have normSummable : Summable (fun shift : ℤ × ℤ =>
      ‖fullNegativeShiftAction parameters angular cell kernel shift‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fullNegativeShiftAction_norm_le parameters angular cell kernel)
      (kernel.moments (angular + cell + 1))
  exact (norm_tsum_le_tsum_norm normSummable).trans
    (normSummable.tsum_le_tsum
      (fullNegativeShiftAction_norm_le parameters angular cell kernel)
      (kernel.moments (angular + cell + 1)))

theorem fullNegativeKernelAction_bound {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension) :
    ‖fullNegativeKernelAction parameters angular cell kernel field‖ ≤
      fullKernelMoment parameters (angular + cell + 1) kernel * ‖field‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (fullNegativeKernelAction_norm_le parameters angular cell kernel)
      (norm_nonneg field))

def negativeTraceCoefficientCLM {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    NegativeTrace parameters angular cell dimension →L[ℂ] ComplexEuclidean dimension :=
  ((negativeTraceWeight parameters angular cell mode : ℂ)⁻¹) •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode

@[simp] theorem negativeTraceCoefficientCLM_apply {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) (field : NegativeTrace parameters angular cell dimension) :
    negativeTraceCoefficientCLM parameters angular cell mode field =
      negativeTraceCoefficient parameters angular cell field mode := rfl

theorem fullNegativeKernelAction_coefficient_hasSum
    {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension)
    (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ × ℤ =>
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (negativeTraceCoefficient parameters angular cell field
          (twoFrequencyTranslation shift mode)))
      (negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell kernel field) mode) := by
  have operatorSum :=
    (fullNegativeShiftAction_summable parameters angular cell kernel).hasSum
  have applied := (operatorEvaluation parameters 0 field).hasSum operatorSum
  have evaluated := (negativeTraceCoefficientCLM parameters angular cell mode).hasSum applied
  have termLaw : ∀ shift : ℤ × ℤ,
      negativeTraceCoefficientCLM parameters angular cell mode
        (operatorEvaluation parameters 0 field
          (fullNegativeShiftAction parameters angular cell kernel shift)) =
        kernel.entry shift (twoFrequencyTranslation shift mode)
          (negativeTraceCoefficient parameters angular cell field
            (twoFrequencyTranslation shift mode)) := by
    intro shift
    rw [show operatorEvaluation parameters 0 field
        (fullNegativeShiftAction parameters angular cell kernel shift) =
          fullNegativeShiftAction parameters angular cell kernel shift field from rfl,
      negativeTraceCoefficientCLM_apply,
      fullNegativeShiftAction_coefficient]
  have targetLaw :
      negativeTraceCoefficientCLM parameters angular cell mode
        (operatorEvaluation parameters 0 field
          (∑' shift : ℤ × ℤ,
            fullNegativeShiftAction parameters angular cell kernel shift)) =
        negativeTraceCoefficient parameters angular cell
          (fullNegativeKernelAction parameters angular cell kernel field) mode := rfl
  rw [← targetLaw]
  simpa only [termLaw] using evaluated

end Grad.BoundaryKernelAction
