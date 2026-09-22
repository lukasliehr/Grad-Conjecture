import BKA6OneHighKernel

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

theorem negativeTotalCoefficient_add {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (first second : NegativeTotalTrace parameters grade dimension)
    (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade (first + second) mode =
    negativeTotalCoefficient parameters grade first mode +
        negativeTotalCoefficient parameters grade second mode := by
  unfold negativeTotalCoefficient
  simp only [lp.coeFn_add, Pi.add_apply, smul_add]

theorem negativeTotalCoefficient_sum {dimension : ℕ} {Index : Type}
    (parameters : PhaseParameters) (grade : ℕ) (indices : Finset Index)
    (fields : Index → NegativeTotalTrace parameters grade dimension)
    (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade (∑ index ∈ indices, fields index) mode =
      ∑ index ∈ indices, negativeTotalCoefficient parameters grade (fields index) mode := by
  unfold negativeTotalCoefficient
  have coordinateSum :
      ((∑ index ∈ indices, fields index) mode) =
        ∑ index ∈ indices, fields index mode := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  rw [coordinateSum, Finset.smul_sum]

theorem finiteHighKernelAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (field : NegativeTotalTrace parameters grade sourceDimension) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (finiteHighKernelAction parameters grade kernel field) mode =
      ∑ shift ∈ kernel.support,
        (highInputShare grade mode shift : ℂ) •
          kernel shift (negativeTotalCoefficient parameters grade field
            (twoFrequencyTranslation shift mode)) := by
  have actionSum :
      finiteHighKernelAction parameters grade kernel field =
        ∑ shift ∈ kernel.support,
          highSingleAction parameters grade shift (kernel shift) field := by
    unfold finiteHighKernelAction
    rw [sum_apply]
  rw [actionSum, negativeTotalCoefficient_sum]
  exact Finset.sum_congr rfl fun shift _ =>
    highSingleAction_coefficient parameters grade shift (kernel shift) field mode

theorem finiteLowKernelAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (field : NegativeTotalTrace parameters 0 sourceDimension) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (finiteLowKernelAction parameters grade kernel field) mode =
      ∑ shift ∈ kernel.support,
        (lowInputShare grade mode shift : ℂ) •
          kernel shift (negativeTotalCoefficient parameters 0 field
            (twoFrequencyTranslation shift mode)) := by
  have actionSum :
      finiteLowKernelAction parameters grade kernel field =
        ∑ shift ∈ kernel.support,
          lowSingleAction parameters grade shift (kernel shift) field := by
    unfold finiteLowKernelAction
    rw [sum_apply]
  rw [actionSum, negativeTotalCoefficient_sum]
  exact Finset.sum_congr rfl fun shift _ =>
    lowSingleAction_coefficient parameters grade shift (kernel shift) field mode

def TotalTraceCompatible {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (high : NegativeTotalTrace parameters grade dimension)
    (low : NegativeTotalTrace parameters 0 dimension) : Prop :=
  ∀ mode, negativeTotalCoefficient parameters grade high mode =
    negativeTotalCoefficient parameters 0 low mode

/-- The AH19 two-part action. The compatibility condition says that `high`
and `low` are the two weighted realizations of the same physical trace. -/
def finiteOneHighKernelAction {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    NegativeTotalTrace parameters grade targetDimension :=
  finiteHighKernelAction parameters grade kernel high +
    finiteLowKernelAction parameters grade kernel low

theorem finiteOneHighKernelAction_coefficient {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (compatible : TotalTraceCompatible parameters grade high low) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
        (finiteOneHighKernelAction parameters grade kernel high low) mode =
      ∑ shift ∈ kernel.support, kernel shift
        (negativeTotalCoefficient parameters grade high
          (twoFrequencyTranslation shift mode)) := by
  rw [finiteOneHighKernelAction, negativeTotalCoefficient_add,
    finiteHighKernelAction_coefficient, finiteLowKernelAction_coefficient,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro shift _
  rw [← compatible (twoFrequencyTranslation shift mode), ← add_smul]
  have shares :
      (highInputShare grade mode shift : ℂ) +
          (lowInputShare grade mode shift : ℂ) = 1 := by
    exact_mod_cast highInputShare_add_lowInputShare grade mode shift
  rw [shares, one_smul]

/-- AH19 with no high-high product: one coefficient moment is paired with
the high trace, and the `grade+1` moment is paired with the low trace. -/
theorem finiteOneHighKernelAction_bound {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension) :
    ‖finiteOneHighKernelAction parameters grade kernel high low‖ ≤
      2 ^ grade *
        (totalKernelMoment parameters 1 kernel * ‖high‖ +
          totalKernelMoment parameters (grade + 1) kernel * ‖low‖) := by
  have highApply :
      ‖finiteHighKernelAction parameters grade kernel high‖ ≤
        (2 ^ grade * totalKernelMoment parameters 1 kernel) * ‖high‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (finiteHighKernelAction_norm_le parameters grade kernel) (norm_nonneg high))
  have lowApply :
      ‖finiteLowKernelAction parameters grade kernel low‖ ≤
        (2 ^ grade * totalKernelMoment parameters (grade + 1) kernel) * ‖low‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (finiteLowKernelAction_norm_le parameters grade kernel) (norm_nonneg low))
  unfold finiteOneHighKernelAction
  exact (norm_add_le _ _).trans
    ((add_le_add highApply lowApply).trans_eq (by ring))

end Grad.BoundaryKernelAction
