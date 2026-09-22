import BKA2ShiftWeights
import BL42CoefficientOperator

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

abbrev FiniteTwoFrequencyKernel (sourceDimension targetDimension : ℕ) :=
  (ℤ × ℤ) →₀
    (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)

def negativeWeightRatio (parameters : PhaseParameters) (angular cell : ℕ)
    (shift mode : ℤ × ℤ) : ℝ :=
  negativeTraceWeight parameters angular cell mode /
    negativeTraceWeight parameters angular cell (twoFrequencyTranslation shift mode)

theorem negativeWeightRatio_nonnegative (parameters : PhaseParameters) (angular cell : ℕ)
    (shift mode : ℤ × ℤ) :
    0 ≤ negativeWeightRatio parameters angular cell shift mode := by
  unfold negativeWeightRatio
  exact div_nonneg
    (negativeTraceWeight_pos parameters angular cell mode).le
    (negativeTraceWeight_pos parameters angular cell
      (twoFrequencyTranslation shift mode)).le

theorem negativeWeightRatio_le (parameters : PhaseParameters) (angular cell : ℕ)
    (shift mode : ℤ × ℤ) :
    negativeWeightRatio parameters angular cell shift mode ≤
      negativeShiftCost parameters angular cell shift := by
  rw [negativeWeightRatio, div_le_iff₀
    (negativeTraceWeight_pos parameters angular cell
      (twoFrequencyTranslation shift mode))]
  exact negativeTraceWeight_shift_le parameters angular cell mode shift

def negativeKernelEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  ((negativeWeightRatio parameters angular cell shift mode : ℂ)) • entry

theorem negativeKernelEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ‖negativeKernelEntry parameters angular cell shift entry mode‖ ≤
      negativeShiftCost parameters angular cell shift * ‖entry‖ := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (negativeWeightRatio_nonnegative parameters angular cell shift mode)]
  exact mul_le_mul_of_nonneg_right
    (negativeWeightRatio_le parameters angular cell shift mode) (norm_nonneg entry)

/-- One Fourier displacement acting on the exact negative-half carrier. -/
def negativeSingleAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    NegativeTrace parameters angular cell sourceDimension →L[ℂ]
      NegativeTrace parameters angular cell targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (negativeKernelEntry parameters angular cell shift entry)
    (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
      (norm_nonneg entry))
    (negativeKernelEntry_norm_le parameters angular cell shift entry)

theorem negativeSingleAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖negativeSingleAction parameters angular cell shift entry‖ ≤
      negativeShiftCost parameters angular cell shift * ‖entry‖ :=
  coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
    (negativeKernelEntry parameters angular cell shift entry)
    (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
      (norm_nonneg entry))
    (negativeKernelEntry_norm_le parameters angular cell shift entry)

theorem negativeSingleAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (negativeSingleAction parameters angular cell shift entry field) mode =
      entry (negativeTraceCoefficient parameters angular cell field
        (twoFrequencyTranslation shift mode)) := by
  unfold negativeTraceCoefficient
  have rawApply :
      (negativeSingleAction parameters angular cell shift entry field) mode =
        (negativeWeightRatio parameters angular cell shift mode : ℂ) •
          entry (field (twoFrequencyTranslation shift mode)) := by
    have result := coefficientOperator_apply parameters 0
      (twoFrequencyTranslation shift)
      (negativeKernelEntry parameters angular cell shift entry)
      (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
        (norm_nonneg entry))
      (negativeKernelEntry_norm_le parameters angular cell shift entry) field mode
    unfold negativeSingleAction
    with_reducible simpa only [negativeKernelEntry, smul_apply] using result
  rw [rawApply, map_smul]
  simp only [smul_smul]
  congr 1
  unfold negativeWeightRatio
  push_cast
  field_simp [
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (negativeTraceWeight_pos parameters angular cell
      (twoFrequencyTranslation shift mode)).ne']

def finiteKernelMoment {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) : ℝ :=
  ∑ shift ∈ kernel.support,
    negativeShiftCost parameters angular cell shift * ‖kernel shift‖

theorem finiteKernelMoment_nonnegative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    0 ≤ finiteKernelMoment parameters angular cell kernel := by
  unfold finiteKernelMoment
  exact Finset.sum_nonneg fun shift _ =>
    mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
      (norm_nonneg (kernel shift))

/-- AH18: the literal finite two-frequency kernel action on the complete
negative-half trace carrier. -/
def finiteNegativeKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    NegativeTrace parameters angular cell sourceDimension →L[ℂ]
      NegativeTrace parameters angular cell targetDimension :=
  ∑ shift ∈ kernel.support,
    negativeSingleAction parameters angular cell shift (kernel shift)

theorem finiteNegativeKernelAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    ‖finiteNegativeKernelAction parameters angular cell kernel‖ ≤
      finiteKernelMoment parameters angular cell kernel := by
  unfold finiteNegativeKernelAction finiteKernelMoment
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun shift _ =>
      negativeSingleAction_norm_le parameters angular cell shift (kernel shift))

theorem finiteNegativeKernelAction_bound {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension) :
    ‖finiteNegativeKernelAction parameters angular cell kernel field‖ ≤
      finiteKernelMoment parameters angular cell kernel * ‖field‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (finiteNegativeKernelAction_norm_le parameters angular cell kernel)
      (norm_nonneg field))

theorem finiteNegativeKernelAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (finiteNegativeKernelAction parameters angular cell kernel field) mode =
      ∑ shift ∈ kernel.support, kernel shift
        (negativeTraceCoefficient parameters angular cell field
          (twoFrequencyTranslation shift mode)) := by
  have distribute :
      negativeTraceCoefficient parameters angular cell
          ((∑ shift ∈ kernel.support,
            negativeSingleAction parameters angular cell shift (kernel shift)) field) mode =
        ∑ shift ∈ kernel.support,
          negativeTraceCoefficient parameters angular cell
            (negativeSingleAction parameters angular cell shift (kernel shift) field) mode := by
    have actionSum :
        ((∑ shift ∈ kernel.support,
          negativeSingleAction parameters angular cell shift (kernel shift)) field) =
          ∑ shift ∈ kernel.support,
            negativeSingleAction parameters angular cell shift (kernel shift) field := by
      rw [sum_apply]
    rw [actionSum]
    unfold negativeTraceCoefficient
    have coordinateSum :
        ((∑ shift ∈ kernel.support,
          negativeSingleAction parameters angular cell shift (kernel shift) field) mode) =
          ∑ shift ∈ kernel.support,
            (negativeSingleAction parameters angular cell shift (kernel shift) field) mode := by
      simp only [lp.coeFn_sum, Finset.sum_apply]
    rw [coordinateSum, Finset.smul_sum]
  rw [finiteNegativeKernelAction, distribute]
  exact Finset.sum_congr rfl fun shift _ =>
    negativeSingleAction_coefficient parameters angular cell shift (kernel shift) field mode

end Grad.BoundaryKernelAction
