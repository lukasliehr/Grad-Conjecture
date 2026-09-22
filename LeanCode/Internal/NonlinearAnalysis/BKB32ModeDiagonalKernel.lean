import BKB31MatrixMultiplicationKernel

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

def modeDiagonalEntry (inputDimension outputDimension : ℕ)
    (diagonal : (ℤ × ℤ) →
      (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension))
    (shift input : ℤ × ℤ) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  if shift = (0, 0) then diagonal input else 0

theorem modeDiagonalEntry_norm_le (inputDimension outputDimension : ℕ)
    (diagonal : (ℤ × ℤ) →
      (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension))
    (bound : ℝ) (bounded : ∀ input, ‖diagonal input‖ ≤ bound)
    (shift input : ℤ × ℤ) :
    ‖modeDiagonalEntry inputDimension outputDimension diagonal shift input‖ ≤
      if shift = (0, 0) then bound else 0 := by
  by_cases zero : shift = (0, 0)
  · simp only [modeDiagonalEntry, if_pos zero]
    exact bounded input
  · simp only [modeDiagonalEntry, if_neg zero, norm_zero, le_rfl]

theorem modeDiagonalMajorant_moments (parameters : PhaseParameters)
    (bound : ℝ) (moment : ℕ) :
    Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment *
          (if shift = (0, 0) then bound else 0)) := by
  refine (hasSum_sum_of_ne_finset_zero (s := {(0, 0)}) ?_).summable
  intro shift outside
  have nonzero : shift ≠ (0, 0) := by
    simpa only [Finset.mem_singleton] using outside
  simp only [if_neg nonzero, mul_zero]

/-- An exact input-mode-dependent diagonal kernel.  Only displacement zero
is occupied; the entry may still depend on the input Fourier mode. -/
def modeDiagonalKernel (parameters : PhaseParameters)
    (inputDimension outputDimension : ℕ)
    (diagonal : (ℤ × ℤ) →
      (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension))
    (bound : ℝ) (bounded : ∀ input, ‖diagonal input‖ ≤ bound) :
    FullTwoFrequencyKernel parameters inputDimension outputDimension :=
  fullKernelOfEntries parameters
    (modeDiagonalEntry inputDimension outputDimension diagonal)
    (fun shift => if shift = (0, 0) then bound else 0)
    (modeDiagonalEntry_norm_le inputDimension outputDimension diagonal bound bounded)
    (modeDiagonalMajorant_moments parameters bound)

@[simp] theorem modeDiagonalKernel_entry (parameters : PhaseParameters)
    (inputDimension outputDimension : ℕ)
    (diagonal : (ℤ × ℤ) →
      (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension))
    (bound : ℝ) (bounded : ∀ input, ‖diagonal input‖ ≤ bound)
    (shift input : ℤ × ℤ) :
    (modeDiagonalKernel parameters inputDimension outputDimension diagonal bound
      bounded).entry shift input =
        if shift = (0, 0) then diagonal input else 0 := rfl

def scalarModeDiagonalKernel (parameters : PhaseParameters) (dimension : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ input, ‖multiplier input‖ ≤ bound) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  modeDiagonalKernel parameters dimension dimension
    (fun input => multiplier input •
      ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) bound
    (fun input => by
      calc
        ‖multiplier input •
            ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ ≤
            ‖multiplier input‖ *
              ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖multiplier input‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.norm_id_le (E := ComplexEuclidean dimension))
            (norm_nonneg (multiplier input))
        _ = ‖multiplier input‖ := mul_one _
        _ ≤ bound := bounded input)

theorem scalarModeDiagonalKernel_entry_apply (parameters : PhaseParameters)
    (dimension : ℕ) (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ input, ‖multiplier input‖ ≤ bound)
    (shift input : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    (scalarModeDiagonalKernel parameters dimension multiplier bound bounded).entry
        shift input value =
      if shift = (0, 0) then multiplier input • value else 0 := by
  unfold scalarModeDiagonalKernel
  rw [modeDiagonalKernel_entry]
  split <;> simp_all

end Grad.BoundaryKernelAction
