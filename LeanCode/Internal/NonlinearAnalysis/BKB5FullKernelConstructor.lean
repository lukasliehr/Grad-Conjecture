import BKB4FullOneHighAction

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- The literal AE20 displacement envelope: the supremum over every input
mode of the operator norm of the corresponding matrix entry. -/
def fullKernelEntrySup {sourceDimension targetDimension : ℕ}
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (shift : ℤ × ℤ) : ℝ :=
  sSup (Set.range fun input => ‖entry shift input‖)

theorem entry_norm_le_fullKernelEntrySup {sourceDimension targetDimension : ℕ}
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (majorant : (ℤ × ℤ) → ℝ)
    (bounded : ∀ shift input, ‖entry shift input‖ ≤ majorant shift)
    (shift input : ℤ × ℤ) :
    ‖entry shift input‖ ≤ fullKernelEntrySup entry shift := by
  unfold fullKernelEntrySup
  apply le_csSup
  · refine ⟨majorant shift, ?_⟩
    rintro value ⟨mode, rfl⟩
    exact bounded shift mode
  · exact Set.mem_range_self input

theorem fullKernelEntrySup_le {sourceDimension targetDimension : ℕ}
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (shift : ℤ × ℤ) (bound : ℝ)
    (bounded : ∀ input, ‖entry shift input‖ ≤ bound) :
    fullKernelEntrySup entry shift ≤ bound := by
  unfold fullKernelEntrySup
  apply csSup_le (Set.range_nonempty fun input => ‖entry shift input‖)
  rintro value ⟨input, rfl⟩
  exact bounded input

theorem fullKernelEntrySup_nonnegative {sourceDimension targetDimension : ℕ}
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (majorant : (ℤ × ℤ) → ℝ)
    (bounded : ∀ shift input, ‖entry shift input‖ ≤ majorant shift)
    (shift : ℤ × ℤ) :
    0 ≤ fullKernelEntrySup entry shift := by
  exact (norm_nonneg (entry shift (0, 0))).trans
    (entry_norm_le_fullKernelEntrySup entry majorant bounded shift (0, 0))

/-- Construct a genuine full kernel from raw input-dependent entries.  The
`majorant` is used only to prove moment summability; the stored envelope is
still the literal input-mode supremum required by AE20. -/
def fullKernelOfEntries {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (majorant : (ℤ × ℤ) → ℝ)
    (entryBound : ∀ shift input, ‖entry shift input‖ ≤ majorant shift)
    (moments : ∀ moment : ℕ, Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment * majorant shift)) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension where
  entry := entry
  entryNorm := fullKernelEntrySup entry
  entry_le := entry_norm_le_fullKernelEntrySup entry majorant entryBound
  entryNorm_le := fullKernelEntrySup_le entry
  moments moment := by
    apply Summable.of_nonneg_of_le
      (fun shift => mul_nonneg
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
          (pow_nonneg (annularFrequency_pos shift).le _))
        (fullKernelEntrySup_nonnegative entry majorant entryBound shift))
      (fun shift => mul_le_mul_of_nonneg_left
        (fullKernelEntrySup_le entry shift (majorant shift) (entryBound shift))
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
          (pow_nonneg (annularFrequency_pos shift).le _)))
      (moments moment)

@[simp] theorem fullKernelOfEntries_entry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (majorant : (ℤ × ℤ) → ℝ)
    (entryBound : ∀ shift input, ‖entry shift input‖ ≤ majorant shift)
    (moments : ∀ moment : ℕ, Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment * majorant shift))
    (shift input : ℤ × ℤ) :
    (fullKernelOfEntries parameters entry majorant entryBound moments).entry
      shift input = entry shift input := rfl

theorem fullKernelOfEntries_entryNorm_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (entry : (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension))
    (majorant : (ℤ × ℤ) → ℝ)
    (entryBound : ∀ shift input, ‖entry shift input‖ ≤ majorant shift)
    (moments : ∀ moment : ℕ, Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment * majorant shift))
    (shift : ℤ × ℤ) :
    (fullKernelOfEntries parameters entry majorant entryBound moments).entryNorm
        shift ≤ majorant shift :=
  fullKernelEntrySup_le entry shift (majorant shift) (entryBound shift)

end Grad.BoundaryKernelAction
