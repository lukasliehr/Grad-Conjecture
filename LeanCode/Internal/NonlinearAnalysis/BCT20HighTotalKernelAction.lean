import BCT19TotalBoundaryPrimitive

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

theorem scalarModeDiagonalKernel_comp_entry {input output : ℕ}
    (parameters : PhaseParameters) (multiplier : ℤ × ℤ → ℂ)
    (bound : ℝ) (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound)
    (kernel : FullTwoFrequencyKernel parameters input output) (shift frequency : ℤ × ℤ) :
    (fullKernelComposition
      (scalarModeDiagonalKernel parameters output multiplier bound bounded) kernel).entry shift frequency =
      multiplier (frequency + shift) • kernel.entry shift frequency := by
  rw [fullKernelComposition_entry, tsum_eq_single shift (by
    intro middle different
    have nonzero : shift - middle ≠ (0, 0) := by
      intro equality
      exact different (sub_eq_zero.mp equality).symm
    unfold scalarModeDiagonalKernel
    rw [modeDiagonalKernel_entry, if_neg nonzero, ContinuousLinearMap.zero_comp])]
  unfold scalarModeDiagonalKernel
  rw [modeDiagonalKernel_entry, sub_self,
    if_pos (show (0 : ℤ × ℤ) = (0, 0) from rfl)]
  rfl

theorem highAngularKernel_comp_entry_low {input output : ℕ}
    (parameters : PhaseParameters) (kernel : FullTwoFrequencyKernel parameters input output)
    (shift frequency : ℤ × ℤ) (low : |(frequency + shift).1| < 3) :
    (fullKernelComposition (highAngularKernel parameters output) kernel).entry shift frequency = 0 := by
  unfold highAngularKernel
  rw [scalarModeDiagonalKernel_comp_entry]
  have zero : highAngularMultiplier (frequency + shift) = 0 := if_neg (not_le.mpr low)
  rw [zero]
  exact zero_smul ℂ (kernel.entry shift frequency)

theorem fullOneHighKernelAction_high {input : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters input 1)
    (high : NegativeTotalTrace parameters grade input) (low : NegativeTotalTrace parameters 0 input)
    (compatible : TotalTraceCompatible parameters grade high low) :
    fullOneHighKernelAction parameters grade
      (fullKernelComposition (highAngularKernel parameters 1) kernel) high low ∈
      totalHighAngularSubmodule parameters grade := by
  intro mode smallMode
  rw [fullOneHighKernelAction_coefficient parameters grade _ high low compatible mode]
  trans ∑' _shift : ℤ × ℤ, (0 : ComplexEuclidean 1)
  · apply tsum_congr
    intro shift
    rw [highAngularKernel_comp_entry_low parameters kernel shift
      (twoFrequencyTranslation shift mode) (by
        change |(mode.1 - shift.1) + shift.1| < 3
        simpa only [sub_add_cancel] using smallMode), zero_apply]
  · exact tsum_zero

end Grad.ActualBoundaryPrimitives
