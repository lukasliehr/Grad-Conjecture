import BKB2FullNegativeAction

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- A finite BKA kernel, viewed as a genuine input-mode-independent full
kernel. -/
def finiteKernelAsFull {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension where
  entry shift _input := kernel shift
  entryNorm shift := ‖kernel shift‖
  entry_le _ _ := le_rfl
  entryNorm_le shift bound bounded := bounded (0, 0)
  moments moment := by
    refine (hasSum_sum_of_ne_finset_zero (s := kernel.support) ?_).summable
    intro shift outside
    have zero : kernel shift = 0 := by
      simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using outside
    rw [zero, norm_zero, mul_zero]

theorem finiteKernelAsFull_entry {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (shift input : ℤ × ℤ) :
    (finiteKernelAsFull parameters kernel).entry shift input = kernel shift := rfl

theorem finiteKernelAsFull_entryNorm {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    (finiteKernelAsFull parameters kernel).entryNorm shift = ‖kernel shift‖ := rfl

theorem fullKernelMoment_finite {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    fullKernelMoment parameters moment (finiteKernelAsFull parameters kernel) =
      ∑ shift ∈ kernel.support,
        boundaryCoefficientPhaseCost parameters shift *
          annularFrequency shift.1 shift.2 ^ moment * ‖kernel shift‖ := by
  unfold fullKernelMoment
  rw [tsum_eq_sum (s := kernel.support) (fun shift outside => by
    have zero : kernel shift = 0 := by
      simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using outside
    rw [finiteKernelAsFull_entryNorm, zero, norm_zero, mul_zero])]
  rfl

theorem fullKernelMoment_finite_negative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    fullKernelMoment parameters (angular + cell + 1)
        (finiteKernelAsFull parameters kernel) =
      finiteKernelMoment parameters angular cell kernel := by
  rw [fullKernelMoment_finite]
  unfold finiteKernelMoment negativeShiftCost
  rfl

theorem fullNegativeShiftAction_finite {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    fullNegativeShiftAction parameters angular cell
        (finiteKernelAsFull parameters kernel) shift =
      negativeSingleAction parameters angular cell shift (kernel shift) := by
  rfl

private theorem negativeSingleAction_zero {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (shift : ℤ × ℤ) :
    negativeSingleAction parameters angular cell shift
        (0 : ComplexEuclidean sourceDimension →L[ℂ]
          ComplexEuclidean targetDimension) = 0 := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  unfold negativeSingleAction
  rw [Grad.BoundaryLift.coefficientOperator_apply]
  unfold negativeKernelEntry
  simp

/-- The accepted finite AH18 action is literally the finite-support
special case of the full absolutely convergent action. -/
theorem fullNegativeKernelAction_finite {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    fullNegativeKernelAction parameters angular cell
        (finiteKernelAsFull parameters kernel) =
      finiteNegativeKernelAction parameters angular cell kernel := by
  unfold fullNegativeKernelAction finiteNegativeKernelAction
  rw [tsum_eq_sum (s := kernel.support) (fun shift outside => by
    rw [fullNegativeShiftAction_finite]
    have zero : kernel shift = 0 := by
      simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using outside
    rw [zero, negativeSingleAction_zero])]
  · apply Finset.sum_congr rfl
    intro shift _
    exact fullNegativeShiftAction_finite parameters angular cell kernel shift

end Grad.BoundaryKernelAction
