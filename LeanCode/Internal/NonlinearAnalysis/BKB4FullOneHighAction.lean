import BKB3FiniteCorollary

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

def fullHighShiftEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  (highPartRatio parameters grade shift mode : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode)

def fullLowShiftEntry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension :=
  (lowPartRatio parameters grade shift mode : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode)

theorem fullHighShiftEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ‖fullHighShiftEntry parameters grade kernel shift mode‖ ≤
      totalTameShiftCost parameters grade 1 shift * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (highPartRatio_nonnegative parameters grade shift mode)]
  exact mul_le_mul (highPartRatio_le parameters grade shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode))
    (norm_nonneg _) (totalTameShiftCost_nonnegative parameters grade 1 shift)

theorem fullLowShiftEntry_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift mode : ℤ × ℤ) :
    ‖fullLowShiftEntry parameters grade kernel shift mode‖ ≤
      totalTameShiftCost parameters grade (grade + 1) shift *
        kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (lowPartRatio_nonnegative parameters grade shift mode)]
  exact mul_le_mul (lowPartRatio_le parameters grade shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode))
    (norm_nonneg _)
    (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)

def fullHighShiftAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    NegativeTotalTrace parameters grade sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (fullHighShiftEntry parameters grade kernel shift)
    (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
      (fullKernelEntryNorm_nonnegative kernel shift))
    (fullHighShiftEntry_norm_le parameters grade kernel shift)

def fullLowShiftAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    NegativeTotalTrace parameters 0 sourceDimension →L[ℂ]
      NegativeTotalTrace parameters grade targetDimension :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (fullLowShiftEntry parameters grade kernel shift)
    (mul_nonneg
      (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
      (fullKernelEntryNorm_nonnegative kernel shift))
    (fullLowShiftEntry_norm_le parameters grade kernel shift)

theorem fullHighShiftAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    ‖fullHighShiftAction parameters grade kernel shift‖ ≤
      2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 * kernel.entryNorm shift := by
  unfold fullHighShiftAction
  simpa only [totalTameShiftCost, pow_one, mul_assoc] using
    coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
      (fullHighShiftEntry parameters grade kernel shift)
      (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullHighShiftEntry_norm_le parameters grade kernel shift)

theorem fullLowShiftAction_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    ‖fullLowShiftAction parameters grade kernel shift‖ ≤
      2 ^ grade * boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ (grade + 1) *
          kernel.entryNorm shift := by
  unfold fullLowShiftAction
  simpa only [totalTameShiftCost, mul_assoc] using
    coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
      (fullLowShiftEntry parameters grade kernel shift)
      (mul_nonneg
        (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullLowShiftEntry_norm_le parameters grade kernel shift)

theorem fullHighShiftAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ)
    (field : NegativeTotalTrace parameters grade sourceDimension)
    (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (fullHighShiftAction parameters grade kernel shift field) mode =
      (highInputShare grade mode shift : ℂ) •
        kernel.entry shift (twoFrequencyTranslation shift mode)
          (negativeTotalCoefficient parameters grade field
            (twoFrequencyTranslation shift mode)) := by
  unfold negativeTotalCoefficient
  have rawApply :
      fullHighShiftAction parameters grade kernel shift field mode =
        fullHighShiftEntry parameters grade kernel shift mode
          (field (twoFrequencyTranslation shift mode)) := by
    unfold fullHighShiftAction
    exact coefficientOperator_apply parameters 0
      (twoFrequencyTranslation shift) (fullHighShiftEntry parameters grade kernel shift)
      (mul_nonneg (totalTameShiftCost_nonnegative parameters grade 1 shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullHighShiftEntry_norm_le parameters grade kernel shift) field mode
  rw [rawApply, map_smul]
  simp only [fullHighShiftEntry, smul_apply, smul_smul]
  congr 1
  unfold highPartRatio
  push_cast
  field_simp [
    (negativeTotalWeight_pos parameters grade mode).ne',
    (negativeTotalWeight_pos parameters grade
      (twoFrequencyTranslation shift mode)).ne']

theorem fullLowShiftAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ)
    (field : NegativeTotalTrace parameters 0 sourceDimension)
    (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (fullLowShiftAction parameters grade kernel shift field) mode =
      (lowInputShare grade mode shift : ℂ) •
        kernel.entry shift (twoFrequencyTranslation shift mode)
          (negativeTotalCoefficient parameters 0 field
            (twoFrequencyTranslation shift mode)) := by
  unfold negativeTotalCoefficient
  have rawApply :
      fullLowShiftAction parameters grade kernel shift field mode =
        fullLowShiftEntry parameters grade kernel shift mode
          (field (twoFrequencyTranslation shift mode)) := by
    unfold fullLowShiftAction
    exact coefficientOperator_apply parameters 0
      (twoFrequencyTranslation shift) (fullLowShiftEntry parameters grade kernel shift)
      (mul_nonneg
        (totalTameShiftCost_nonnegative parameters grade (grade + 1) shift)
        (fullKernelEntryNorm_nonnegative kernel shift))
      (fullLowShiftEntry_norm_le parameters grade kernel shift) field mode
  rw [rawApply, map_smul]
  simp only [fullLowShiftEntry, smul_apply, smul_smul]
  congr 1
  unfold lowPartRatio
  push_cast
  field_simp [
    (negativeTotalWeight_pos parameters grade mode).ne',
    (negativeTotalWeight_pos parameters 0
      (twoFrequencyTranslation shift mode)).ne']

def negativeTotalCoefficientCLM {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (mode : ℤ × ℤ) :
    NegativeTotalTrace parameters grade dimension →L[ℂ] ComplexEuclidean dimension :=
  ((negativeTotalWeight parameters grade mode : ℂ)⁻¹) •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode

@[simp] theorem negativeTotalCoefficientCLM_apply {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (mode : ℤ × ℤ)
    (field : NegativeTotalTrace parameters grade dimension) :
    negativeTotalCoefficientCLM parameters grade mode field =
      negativeTotalCoefficient parameters grade field mode := rfl

def fullOneHighShiftValue {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (shift : ℤ × ℤ) : NegativeTotalTrace parameters grade targetDimension :=
  fullHighShiftAction parameters grade kernel shift high +
    fullLowShiftAction parameters grade kernel shift low

theorem fullOneHighShiftValue_norm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (shift : ℤ × ℤ) :
    ‖fullOneHighShiftValue parameters grade kernel high low shift‖ ≤
      2 ^ grade *
        (boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 * kernel.entryNorm shift * ‖high‖ +
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ (grade + 1) *
              kernel.entryNorm shift * ‖low‖) := by
  unfold fullOneHighShiftValue
  apply (norm_add_le _ _).trans
  have highBound := (ContinuousLinearMap.le_opNorm
    (fullHighShiftAction parameters grade kernel shift) high).trans
      (mul_le_mul_of_nonneg_right
        (fullHighShiftAction_norm_le parameters grade kernel shift)
        (norm_nonneg high))
  have lowBound := (ContinuousLinearMap.le_opNorm
    (fullLowShiftAction parameters grade kernel shift) low).trans
      (mul_le_mul_of_nonneg_right
        (fullLowShiftAction_norm_le parameters grade kernel shift)
        (norm_nonneg low))
  exact (add_le_add highBound lowBound).trans_eq (by ring)

theorem fullOneHighShiftValue_norm_summable {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    Summable (fun shift : ℤ × ℤ =>
      ‖fullOneHighShiftValue parameters grade kernel high low shift‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fullOneHighShiftValue_norm_le parameters grade kernel high low)
  have split := ((kernel.moments 1).mul_right (2 ^ grade * ‖high‖)).add
    ((kernel.moments (grade + 1)).mul_right (2 ^ grade * ‖low‖))
  exact split.congr fun shift => by
    simp only [pow_one]
    ring

theorem fullOneHighShiftValue_summable {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    Summable (fullOneHighShiftValue parameters grade kernel high low) :=
  Summable.of_norm
    (fullOneHighShiftValue_norm_summable parameters grade kernel high low)

/-- AH19 for a full absolutely summable, input-mode-dependent kernel. -/
def fullOneHighKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    NegativeTotalTrace parameters grade targetDimension :=
  ∑' shift : ℤ × ℤ,
    fullOneHighShiftValue parameters grade kernel high low shift

theorem fullOneHighKernelAction_bound {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    ‖fullOneHighKernelAction parameters grade kernel high low‖ ≤
      2 ^ grade *
        (fullKernelMoment parameters 1 kernel * ‖high‖ +
          fullKernelMoment parameters (grade + 1) kernel * ‖low‖) := by
  have normSummable : Summable (fun shift : ℤ × ℤ =>
      ‖fullOneHighShiftValue parameters grade kernel high low shift‖) :=
    fullOneHighShiftValue_norm_summable parameters grade kernel high low
  apply (norm_tsum_le_tsum_norm normSummable).trans
  have majorantSummable : Summable (fun shift : ℤ × ℤ =>
      2 ^ grade *
        (boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 * kernel.entryNorm shift * ‖high‖ +
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ (grade + 1) *
              kernel.entryNorm shift * ‖low‖)) := by
    have split := ((kernel.moments 1).mul_right (2 ^ grade * ‖high‖)).add
      ((kernel.moments (grade + 1)).mul_right (2 ^ grade * ‖low‖))
    exact split.congr fun shift => by simp only [pow_one]; ring
  apply (normSummable.tsum_le_tsum
    (fullOneHighShiftValue_norm_le parameters grade kernel high low)
    majorantSummable).trans_eq
  unfold fullKernelMoment
  calc
    (∑' shift : ℤ × ℤ,
        2 ^ grade *
          (boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 * kernel.entryNorm shift * ‖high‖ +
            boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ (grade + 1) *
                kernel.entryNorm shift * ‖low‖)) =
      (∑' shift : ℤ × ℤ,
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ 1 * kernel.entryNorm shift) *
            (2 ^ grade * ‖high‖) +
        (∑' shift : ℤ × ℤ,
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ (grade + 1) *
              kernel.entryNorm shift) * (2 ^ grade * ‖low‖) := by
        rw [← tsum_mul_right, ← tsum_mul_right,
          ← Summable.tsum_add
            ((kernel.moments 1).mul_right (2 ^ grade * ‖high‖))
            ((kernel.moments (grade + 1)).mul_right (2 ^ grade * ‖low‖))]
        apply tsum_congr
        intro shift
        simp only [pow_one]
        ring
    _ = 2 ^ grade *
        ((∑' shift : ℤ × ℤ,
            boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ 1 * kernel.entryNorm shift) * ‖high‖ +
          (∑' shift : ℤ × ℤ,
            boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ (grade + 1) *
                kernel.entryNorm shift) * ‖low‖) := by ring

theorem fullOneHighShiftValue_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (compatible : TotalTraceCompatible parameters grade high low)
    (shift mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (fullOneHighShiftValue parameters grade kernel high low shift) mode =
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (negativeTotalCoefficient parameters grade high
          (twoFrequencyTranslation shift mode)) := by
  rw [fullOneHighShiftValue, negativeTotalCoefficient_add,
    fullHighShiftAction_coefficient, fullLowShiftAction_coefficient,
    ← compatible (twoFrequencyTranslation shift mode), ← add_smul]
  have shares :
      (highInputShare grade mode shift : ℂ) +
        (lowInputShare grade mode shift : ℂ) = 1 := by
    exact_mod_cast highInputShare_add_lowInputShare grade mode shift
  rw [shares, one_smul]

theorem fullOneHighKernelAction_coefficient_hasSum
    {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (compatible : TotalTraceCompatible parameters grade high low)
    (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ × ℤ =>
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (negativeTotalCoefficient parameters grade high
          (twoFrequencyTranslation shift mode)))
      (negativeTotalCoefficient parameters grade
        (fullOneHighKernelAction parameters grade kernel high low) mode) := by
  have values :=
    (fullOneHighShiftValue_summable parameters grade kernel high low).hasSum
  have evaluated :=
    (negativeTotalCoefficientCLM parameters grade mode).hasSum values
  simpa only [negativeTotalCoefficientCLM_apply,
    fullOneHighShiftValue_coefficient parameters grade kernel high low compatible,
    fullOneHighKernelAction] using evaluated

theorem fullOneHighKernelAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (compatible : TotalTraceCompatible parameters grade high low)
    (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (fullOneHighKernelAction parameters grade kernel high low) mode =
      ∑' shift : ℤ × ℤ,
        kernel.entry shift (twoFrequencyTranslation shift mode)
          (negativeTotalCoefficient parameters grade high
            (twoFrequencyTranslation shift mode)) :=
  (fullOneHighKernelAction_coefficient_hasSum parameters grade kernel high low
    compatible mode).tsum_eq.symm

end Grad.BoundaryKernelAction
