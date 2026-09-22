import BKB19KernelAssociativity

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The recursive powers may equivalently insert the new factor on the output
side.  This is the noncommutative identity needed for the two Neumann tail
equations. -/
theorem fullKernelPower_succ_left {dimension : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    ∀ exponent : ℕ,
      fullKernelPower kernel (exponent + 1) =
        fullKernelComposition kernel (fullKernelPower kernel exponent) := by
  intro exponent
  induction exponent with
  | zero => rfl
  | succ exponent hypothesis =>
      calc
        fullKernelPower kernel ((exponent + 1) + 1) =
            fullKernelComposition (fullKernelPower kernel (exponent + 1)) kernel :=
          fullKernelPower_succ kernel (exponent + 1)
        _ = fullKernelComposition
              (fullKernelComposition kernel (fullKernelPower kernel exponent))
              kernel := congrArg (fun power => fullKernelComposition power kernel)
                hypothesis
        _ = fullKernelComposition kernel
              (fullKernelComposition (fullKernelPower kernel exponent) kernel) :=
          fullKernelComposition_assoc kernel (fullKernelPower kernel exponent) kernel
        _ = fullKernelComposition kernel
              (fullKernelPower kernel (exponent + 1)) :=
          congrArg (fullKernelComposition kernel)
            (fullKernelPower_succ kernel exponent).symm

/-- Removing the zeroth strict power from the exact entrywise Neumann tail. -/
theorem fullKernelPower_shift_tsum_eq_tail_sub {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (total input : ℤ × ℤ) :
    (∑' exponent : ℕ,
        (fullKernelPower kernel (exponent + 1)).entry total input) =
      (fullKernelNeumannTail parameters kernel low lowBound lowSmall).entry
          total input - kernel.entry total input := by
  rw [fullKernelNeumannTail_entry]
  have expanded := (fullKernelPower_entry_summable parameters kernel low
    lowBound lowSmall total input).tsum_eq_zero_add
  exact eq_sub_of_add_eq' expanded.symm

end Grad.BoundaryKernelAction
