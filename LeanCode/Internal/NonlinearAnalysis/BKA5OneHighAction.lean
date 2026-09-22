import BKA4TotalWeights

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

def highPartRatio (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) : ℝ :=
  negativeTotalWeight parameters grade mode /
      negativeTotalWeight parameters grade (twoFrequencyTranslation shift mode) *
    highInputShare grade mode shift

def lowPartRatio (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) : ℝ :=
  negativeTotalWeight parameters grade mode /
      negativeTotalWeight parameters 0 (twoFrequencyTranslation shift mode) *
    lowInputShare grade mode shift

theorem highPartRatio_nonnegative (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) : 0 ≤ highPartRatio parameters grade shift mode := by
  unfold highPartRatio highInputShare
  exact mul_nonneg
    (div_nonneg (negativeTotalWeight_pos parameters grade mode).le
      (negativeTotalWeight_pos parameters grade
        (twoFrequencyTranslation shift mode)).le)
    (div_nonneg (pow_nonneg (annularFrequency_pos
      (twoFrequencyTranslation shift mode)).le _)
      (totalShareDenominator_pos grade mode shift).le)

theorem lowPartRatio_nonnegative (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) : 0 ≤ lowPartRatio parameters grade shift mode := by
  unfold lowPartRatio lowInputShare
  exact mul_nonneg
    (div_nonneg (negativeTotalWeight_pos parameters grade mode).le
      (negativeTotalWeight_pos parameters 0
        (twoFrequencyTranslation shift mode)).le)
    (div_nonneg (pow_nonneg (annularFrequency_pos shift).le _)
      (totalShareDenominator_pos grade mode shift).le)

theorem highPartRatio_le (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) :
    highPartRatio parameters grade shift mode ≤
      totalTameShiftCost parameters grade 1 shift := by
  let input := twoFrequencyTranslation shift mode
  let inputPower := annularFrequency input.1 input.2 ^ grade
  have common := negativeTotalWeight_shift_split_le parameters grade mode shift
  have multiplied := mul_le_mul_of_nonneg_right common
    (pow_nonneg (annularFrequency_pos input).le grade)
  unfold highPartRatio highInputShare
  rw [div_mul_div_comm, div_le_iff₀
    (mul_pos (negativeTotalWeight_pos parameters grade input)
      (totalShareDenominator_pos grade mode shift))]
  calc
    negativeTotalWeight parameters grade mode * inputPower
        ≤ (2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 *
              totalShareDenominator grade mode shift *
                negativeTraceWeight parameters 0 0 input) * inputPower := multiplied
    _ = totalTameShiftCost parameters grade 1 shift *
          (negativeTotalWeight parameters grade input *
            totalShareDenominator grade mode shift) := by
        unfold totalTameShiftCost negativeTotalWeight
        dsimp only [inputPower]
        rw [pow_one]
        ring

theorem lowPartRatio_le (parameters : PhaseParameters) (grade : ℕ)
    (shift mode : ℤ × ℤ) :
    lowPartRatio parameters grade shift mode ≤
      totalTameShiftCost parameters grade (grade + 1) shift := by
  let input := twoFrequencyTranslation shift mode
  let shiftPower := annularFrequency shift.1 shift.2 ^ grade
  have common := negativeTotalWeight_shift_split_le parameters grade mode shift
  have multiplied := mul_le_mul_of_nonneg_right common
    (pow_nonneg (annularFrequency_pos shift).le grade)
  unfold lowPartRatio lowInputShare
  rw [div_mul_div_comm, div_le_iff₀
    (mul_pos (negativeTotalWeight_pos parameters 0 input)
      (totalShareDenominator_pos grade mode shift))]
  calc
    negativeTotalWeight parameters grade mode * shiftPower
        ≤ (2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 *
              totalShareDenominator grade mode shift *
                negativeTraceWeight parameters 0 0 input) * shiftPower := multiplied
    _ = totalTameShiftCost parameters grade (grade + 1) shift *
          (negativeTotalWeight parameters 0 input *
            totalShareDenominator grade mode shift) := by
        unfold totalTameShiftCost negativeTotalWeight
        dsimp only [shiftPower]
        simp only [pow_zero, one_mul]
        rw [pow_succ]
        ring

def highPartEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  (highPartRatio parameters grade shift mode : ℂ) • entry

def lowPartEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  (lowPartRatio parameters grade shift mode : ℂ) • entry

theorem highPartEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ‖highPartEntry parameters grade shift entry mode‖ ≤
      totalTameShiftCost parameters grade 1 shift * ‖entry‖ := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (highPartRatio_nonnegative parameters grade shift mode)]
  exact mul_le_mul_of_nonneg_right (highPartRatio_le parameters grade shift mode)
    (norm_nonneg entry)

theorem lowPartEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ × ℤ) :
    ‖lowPartEntry parameters grade shift entry mode‖ ≤
      totalTameShiftCost parameters grade (grade + 1) shift * ‖entry‖ := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (lowPartRatio_nonnegative parameters grade shift mode)]
  exact mul_le_mul_of_nonneg_right (lowPartRatio_le parameters grade shift mode)
    (norm_nonneg entry)

def highSingleAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    NegativeTotalTrace parameters grade sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (highPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
      (norm_nonneg entry))
    (highPartEntry_norm_le parameters grade shift entry)

def lowSingleAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ × ℤ)
    (entry : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    NegativeTotalTrace parameters 0 sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (lowPartEntry parameters grade shift entry)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
      (norm_nonneg entry))
    (lowPartEntry_norm_le parameters grade shift entry)

end Grad.BoundaryKernelAction
