import BKA5OneHighAction

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem highSingleAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖highSingleAction parameters grade shift entry‖ ≤
      totalTameShiftCost parameters grade 1 shift * ‖entry‖ :=
  coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
    (highPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
      (norm_nonneg entry))
    (highPartEntry_norm_le parameters grade shift entry)

theorem lowSingleAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖lowSingleAction parameters grade shift entry‖ ≤
      totalTameShiftCost parameters grade (grade + 1) shift * ‖entry‖ :=
  coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
    (lowPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
      (norm_nonneg entry))
    (lowPartEntry_norm_le parameters grade shift entry)

private theorem highSingleAction_raw {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : NegativeTotalTrace parameters grade sourceDimension) (mode : ℤ × ℤ) :
    highSingleAction parameters grade shift entry field mode =
      (highPartRatio parameters grade shift mode : ℂ) •
        entry (field (twoFrequencyTranslation shift mode)) := by
  have result := coefficientOperator_apply parameters 0
    (twoFrequencyTranslation shift) (highPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
      (norm_nonneg entry))
    (highPartEntry_norm_le parameters grade shift entry) field mode
  unfold highSingleAction
  with_reducible simpa only [highPartEntry, smul_apply] using result

private theorem lowSingleAction_raw {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : NegativeTotalTrace parameters 0 sourceDimension) (mode : ℤ × ℤ) :
    lowSingleAction parameters grade shift entry field mode =
      (lowPartRatio parameters grade shift mode : ℂ) •
        entry (field (twoFrequencyTranslation shift mode)) := by
  have result := coefficientOperator_apply parameters 0
    (twoFrequencyTranslation shift) (lowPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
      (norm_nonneg entry))
    (lowPartEntry_norm_le parameters grade shift entry) field mode
  unfold lowSingleAction
  with_reducible simpa only [lowPartEntry, smul_apply] using result

theorem highSingleAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : NegativeTotalTrace parameters grade sourceDimension) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (highSingleAction parameters grade shift entry field) mode =
      (highInputShare grade mode shift : ℂ) •
        entry (negativeTotalCoefficient parameters grade field
          (twoFrequencyTranslation shift mode)) := by
  unfold negativeTotalCoefficient
  rw [highSingleAction_raw, map_smul]
  simp only [smul_smul]
  congr 1
  unfold highPartRatio
  push_cast
  field_simp [
    (negativeTotalWeight_pos parameters grade mode).ne',
    (negativeTotalWeight_pos parameters grade
      (twoFrequencyTranslation shift mode)).ne']

theorem lowSingleAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : NegativeTotalTrace parameters 0 sourceDimension) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (lowSingleAction parameters grade shift entry field) mode =
      (lowInputShare grade mode shift : ℂ) •
        entry (negativeTotalCoefficient parameters 0 field
          (twoFrequencyTranslation shift mode)) := by
  unfold negativeTotalCoefficient
  rw [lowSingleAction_raw, map_smul]
  simp only [smul_smul]
  congr 1
  unfold lowPartRatio
  push_cast
  field_simp [
    (negativeTotalWeight_pos parameters grade mode).ne',
    (negativeTotalWeight_pos parameters 0
      (twoFrequencyTranslation shift mode)).ne']

def totalKernelMoment {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) : ℝ :=
  ∑ shift ∈ kernel.support,
    boundaryCoefficientPhaseCost parameters shift *
      annularFrequency shift.1 shift.2 ^ moment * ‖kernel shift‖

theorem totalKernelMoment_nonnegative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    0 ≤ totalKernelMoment parameters moment kernel := by
  unfold totalKernelMoment
  exact Finset.sum_nonneg fun shift _ =>
    mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le _))
      (norm_nonneg (kernel shift))

def finiteHighKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    NegativeTotalTrace parameters grade sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  ∑ shift ∈ kernel.support, highSingleAction parameters grade shift (kernel shift)

def finiteLowKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    NegativeTotalTrace parameters 0 sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  ∑ shift ∈ kernel.support, lowSingleAction parameters grade shift (kernel shift)

theorem finiteHighKernelAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    ‖finiteHighKernelAction parameters grade kernel‖ ≤
      2 ^ grade * totalKernelMoment parameters 1 kernel := by
  unfold finiteHighKernelAction
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun shift _ =>
    highSingleAction_norm_le parameters grade shift (kernel shift)).trans_eq
  unfold totalTameShiftCost totalKernelMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro shift _
  ring

theorem finiteLowKernelAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    ‖finiteLowKernelAction parameters grade kernel‖ ≤
      2 ^ grade * totalKernelMoment parameters (grade + 1) kernel := by
  unfold finiteLowKernelAction
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun shift _ =>
    lowSingleAction_norm_le parameters grade shift (kernel shift)).trans_eq
  unfold totalTameShiftCost totalKernelMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro shift _
  ring

end Grad.BoundaryKernelAction
