import BKB32ModeDiagonalKernel

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

def angularMeanMultiplier (mode : ℤ × ℤ) : ℂ :=
  if mode.1 = 0 then 1 else 0

def angularMeanFreeMultiplier (mode : ℤ × ℤ) : ℂ :=
  if mode.1 = 0 then 0 else 1

def angularInverseMultiplier (mode : ℤ × ℤ) : ℂ :=
  if mode.1 = 0 then 0 else (Complex.I * (mode.1 : ℂ))⁻¹

theorem angularMeanMultiplier_norm_le (mode : ℤ × ℤ) :
    ‖angularMeanMultiplier mode‖ ≤ 1 := by
  unfold angularMeanMultiplier
  split <;> simp

theorem angularMeanFreeMultiplier_norm_le (mode : ℤ × ℤ) :
    ‖angularMeanFreeMultiplier mode‖ ≤ 1 := by
  unfold angularMeanFreeMultiplier
  split <;> simp

theorem angularInverseMultiplier_norm_le (mode : ℤ × ℤ) :
    ‖angularInverseMultiplier mode‖ ≤ 1 := by
  unfold angularInverseMultiplier
  split
  · simp
  · rename_i nonzero
    have unit : (1 : ℝ) ≤ |(mode.1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs nonzero
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    exact inv_le_one_of_one_le₀ unit

def angularDoubleInverseMultiplier (mode : ℤ × ℤ) : ℂ :=
  angularInverseMultiplier mode * angularInverseMultiplier mode

theorem angularDoubleInverseMultiplier_norm_le (mode : ℤ × ℤ) :
    ‖angularDoubleInverseMultiplier mode‖ ≤ 1 := by
  rw [angularDoubleInverseMultiplier, norm_mul]
  exact (mul_le_mul (angularInverseMultiplier_norm_le mode)
    (angularInverseMultiplier_norm_le mode) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)

def angularMeanKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  scalarModeDiagonalKernel parameters dimension angularMeanMultiplier 1
    angularMeanMultiplier_norm_le

def angularMeanFreeKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  scalarModeDiagonalKernel parameters dimension angularMeanFreeMultiplier 1
    angularMeanFreeMultiplier_norm_le

def angularInverseKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  scalarModeDiagonalKernel parameters dimension angularInverseMultiplier 1
    angularInverseMultiplier_norm_le

def angularDoubleInverseKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  scalarModeDiagonalKernel parameters dimension angularDoubleInverseMultiplier 1
    angularDoubleInverseMultiplier_norm_le

def constantMatrixKernel (parameters : PhaseParameters)
    (inputDimension outputDimension : ℕ)
    (mapping : ComplexEuclidean inputDimension →L[ℂ]
      ComplexEuclidean outputDimension) :
    FullTwoFrequencyKernel parameters inputDimension outputDimension :=
  modeDiagonalKernel parameters inputDimension outputDimension (fun _ => mapping)
    ‖mapping‖ (fun _ => le_rfl)

@[simp] theorem constantMatrixKernel_entry (parameters : PhaseParameters)
    (inputDimension outputDimension : ℕ)
    (mapping : ComplexEuclidean inputDimension →L[ℂ]
      ComplexEuclidean outputDimension) (shift input : ℤ × ℤ) :
    (constantMatrixKernel parameters inputDimension outputDimension mapping).entry
        shift input = if shift = (0, 0) then mapping else 0 := rfl

end Grad.BoundaryKernelAction
