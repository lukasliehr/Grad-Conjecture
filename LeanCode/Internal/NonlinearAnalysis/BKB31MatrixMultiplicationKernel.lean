import BKB30ActualGaugeSigmaKernels

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Ledger

def matrixMultiplicationEntry (inputDimension outputDimension : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (shift _input : ℤ × ℤ) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
    coefficient row column shift • matrixUnit row column

theorem matrixMultiplicationEntry_norm_le (inputDimension outputDimension : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (shift input : ℤ × ℤ) :
    ‖matrixMultiplicationEntry inputDimension outputDimension coefficient shift input‖ ≤
      ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
        ‖coefficient row column shift‖ := by
  unfold matrixMultiplicationEntry
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro row _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro column _
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  exact (mul_le_mul_of_nonneg_left (matrixUnit_norm_le row column)
    (norm_nonneg (coefficient row column shift))).trans_eq (by ring)

theorem matrixMultiplicationMoment_summable (parameters : PhaseParameters)
    (inputDimension outputDimension moment : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ row column order,
      Summable (productMoment parameters order 1 (coefficient row column))) :
    Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment *
          ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
            ‖coefficient row column shift‖) := by
  have each (row : Fin outputDimension) (column : Fin inputDimension) :
      Summable (fun shift : ℤ × ℤ =>
        boundaryCoefficientPhaseCost parameters shift *
          annularFrequency shift.1 shift.2 ^ moment *
            ‖coefficient row column shift‖) := by
    apply ((moments row column moment).mul_left
      (Real.exp (parameters.sigma0 + parameters.gamma))).congr
    intro shift
    exact (boundaryCoefficientPhaseCost_productMoment parameters moment
      (coefficient row column) shift).symm
  simpa only [Finset.mul_sum] using
    summable_sum (s := Finset.univ) (fun row _ =>
      summable_sum (s := Finset.univ) (fun column _ => each row column))

def boundaryMatrixMultiplicationKernel (parameters : PhaseParameters)
    (inputDimension outputDimension : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ row column moment,
      Summable (productMoment parameters moment 1 (coefficient row column))) :
    FullTwoFrequencyKernel parameters inputDimension outputDimension :=
  fullKernelOfEntries parameters
    (matrixMultiplicationEntry inputDimension outputDimension coefficient)
    (fun shift => ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
      ‖coefficient row column shift‖)
    (matrixMultiplicationEntry_norm_le inputDimension outputDimension coefficient)
    (fun moment => matrixMultiplicationMoment_summable parameters inputDimension
      outputDimension moment coefficient moments)

@[simp] theorem boundaryMatrixMultiplicationKernel_entry
    (parameters : PhaseParameters) (inputDimension outputDimension : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ row column moment,
      Summable (productMoment parameters moment 1 (coefficient row column)))
    (shift input : ℤ × ℤ) :
    (boundaryMatrixMultiplicationKernel parameters inputDimension outputDimension
      coefficient moments).entry shift input =
      matrixMultiplicationEntry inputDimension outputDimension coefficient shift input := rfl

theorem boundaryMatrixMultiplicationKernel_entry_apply
    (parameters : PhaseParameters) (inputDimension outputDimension : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ row column moment,
      Summable (productMoment parameters moment 1 (coefficient row column)))
    (shift input : ℤ × ℤ) (value : ComplexEuclidean inputDimension) :
    (boundaryMatrixMultiplicationKernel parameters inputDimension outputDimension
      coefficient moments).entry shift input value =
      ∑ row : Fin outputDimension,
        (∑ column : Fin inputDimension,
          coefficient row column shift * value column) • operatorBasis row := by
  rw [boundaryMatrixMultiplicationKernel_entry]
  unfold matrixMultiplicationEntry
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro row _
  rw [sum_apply]
  simp_rw [smul_apply, matrixUnit_apply, smul_smul]
  rw [Finset.sum_smul]

theorem boundaryMatrixMultiplicationKernel_moment_le
    (parameters : PhaseParameters) (inputDimension outputDimension moment : ℕ)
    (coefficient : Fin outputDimension → Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ row column order,
      Summable (productMoment parameters order 1 (coefficient row column))) :
    fullKernelMoment parameters moment
        (boundaryMatrixMultiplicationKernel parameters inputDimension outputDimension
          coefficient moments) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
          ∑' shift, productMoment parameters moment 1
            (coefficient row column) shift := by
  unfold fullKernelMoment
  have leftSummable :=
    (boundaryMatrixMultiplicationKernel parameters inputDimension outputDimension
      coefficient moments).moments moment
  have each (row : Fin outputDimension) (column : Fin inputDimension) :
      Summable (fun shift : ℤ × ℤ =>
        Real.exp (parameters.sigma0 + parameters.gamma) *
          productMoment parameters moment 1 (coefficient row column) shift) :=
    (moments row column moment).mul_left _
  have rightSummable : Summable (fun shift : ℤ × ℤ =>
      ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
        Real.exp (parameters.sigma0 + parameters.gamma) *
          productMoment parameters moment 1 (coefficient row column) shift) :=
    summable_sum (s := Finset.univ) (fun row _ =>
      summable_sum (s := Finset.univ) (fun column _ => each row column))
  calc
    _ ≤ ∑' shift : ℤ × ℤ,
        ∑ row : Fin outputDimension, ∑ column : Fin inputDimension,
          Real.exp (parameters.sigma0 + parameters.gamma) *
            productMoment parameters moment 1
              (coefficient row column) shift := by
      apply leftSummable.tsum_le_tsum (fun shift => ?_) rightSummable
      apply (mul_le_mul_of_nonneg_left
        (fullKernelOfEntries_entryNorm_le parameters
          (matrixMultiplicationEntry inputDimension outputDimension coefficient)
          (fun current => ∑ row : Fin outputDimension,
            ∑ column : Fin inputDimension, ‖coefficient row column current‖)
          (matrixMultiplicationEntry_norm_le inputDimension outputDimension coefficient)
          (fun order => matrixMultiplicationMoment_summable parameters inputDimension
            outputDimension order coefficient moments) shift)
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
          (pow_nonneg (annularFrequency_pos shift).le moment))).trans_eq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      exact boundaryCoefficientPhaseCost_productMoment parameters moment
        (coefficient row column) shift
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun row _ =>
        summable_sum (s := Finset.univ) (fun column _ => each row column))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      rw [Summable.tsum_finsetSum (fun column _ => each row column)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      rw [tsum_mul_left]

end Grad.BoundaryKernelAction
