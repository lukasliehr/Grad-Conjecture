import BKB13WordMass

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The literal noncommutative kernel word `kernel^(exponent+1)`.  The new
factor is inserted on the input side, matching the input-mode shift in AE7. -/
def fullKernelPower {dimension : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    ℕ → FullTwoFrequencyKernel parameters dimension dimension
  | 0 => kernel
  | exponent + 1 => fullKernelComposition (fullKernelPower kernel exponent) kernel

theorem fullKernelPower_zero {dimension : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    fullKernelPower kernel 0 = kernel := rfl

theorem fullKernelPower_succ {dimension : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (exponent : ℕ) :
    fullKernelPower kernel (exponent + 1) =
      fullKernelComposition (fullKernelPower kernel exponent) kernel := rfl

/-- Pointwise domination of the exact kernel-power envelope by the scalar
two-frequency convolution word of the literal entry suprema. -/
theorem fullKernelPower_entryNorm_enorm_le {dimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    ∀ (exponent : ℕ) (total : ℤ × ℤ),
    ENNReal.ofReal ((fullKernelPower kernel exponent).entryNorm total) ≤
      twoFrequencyScalarWord
        (fun _ : Fin (exponent + 1) =>
          fun shift => ENNReal.ofReal (kernel.entryNorm shift)) total := by
  intro exponent
  induction exponent with
  | zero =>
      intro total
      exact le_rfl
  | succ exponent ih =>
      intro total
      have realEntryBound := fullKernelComposition_entryNorm_le
        (fullKernelPower kernel exponent) kernel total
      have nonnegativeTerm : ∀ middle : ℤ × ℤ,
          0 ≤ (fullKernelPower kernel exponent).entryNorm (total - middle) *
            kernel.entryNorm middle := fun middle =>
        mul_nonneg
          (fullKernelEntryNorm_nonnegative (fullKernelPower kernel exponent)
            (total - middle))
          (fullKernelEntryNorm_nonnegative kernel middle)
      have realSummable := fullKernelNormProduct_summable
        (fullKernelPower kernel exponent) kernel total
      calc
        ENNReal.ofReal
            ((fullKernelPower kernel (exponent + 1)).entryNorm total) ≤
            ENNReal.ofReal
              (fullKernelCompositionMajorant
                (fullKernelPower kernel exponent) kernel total) :=
          ENNReal.ofReal_le_ofReal realEntryBound
        _ = ∑' middle : ℤ × ℤ,
              ENNReal.ofReal
                ((fullKernelPower kernel exponent).entryNorm (total - middle) *
                  kernel.entryNorm middle) := by
          unfold fullKernelCompositionMajorant
          exact ENNReal.ofReal_tsum_of_nonneg nonnegativeTerm realSummable
        _ = ∑' middle : ℤ × ℤ,
              ENNReal.ofReal (kernel.entryNorm middle) *
                ENNReal.ofReal
                  ((fullKernelPower kernel exponent).entryNorm
                    (total - middle)) := by
          apply tsum_congr
          intro middle
          rw [ENNReal.ofReal_mul
            (fullKernelEntryNorm_nonnegative (fullKernelPower kernel exponent)
              (total - middle))]
          exact mul_comm _ _
        _ ≤ ∑' middle : ℤ × ℤ,
              ENNReal.ofReal (kernel.entryNorm middle) *
                twoFrequencyScalarWord
                  (fun _ : Fin (exponent + 1) =>
                    fun shift => ENNReal.ofReal (kernel.entryNorm shift))
                  (total - middle) := by
          apply ENNReal.tsum_le_tsum
          intro middle
          exact mul_le_mul' le_rfl (ih (total - middle))
        _ = twoFrequencyScalarWord
              (fun _ : Fin (exponent + 2) =>
                fun shift => ENNReal.ofReal (kernel.entryNorm shift)) total := rfl

end Grad.BoundaryKernelAction
