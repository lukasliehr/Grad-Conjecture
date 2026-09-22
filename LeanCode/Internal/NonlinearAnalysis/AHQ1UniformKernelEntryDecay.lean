import BCI25OriginalBoundaryInverseConsumer
import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

/-- Uniform polynomial decay follows from the actual literal kernel moment;
no independent input-mode majorant is introduced. -/
theorem fullKernelEntryNorm_decay {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters src tgt) (moment : ℕ)
    (bound : ℝ) (bounded : fullKernelMoment parameters moment kernel ≤ bound)
    (shift : ℤ × ℤ) :
    kernel.entryNorm shift ≤ bound * (annularFrequency shift.1 shift.2 ^ moment)⁻¹ := by
  have weighted : annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift ≤
      fullKernelWeightedEnvelope parameters moment kernel shift := by
    unfold fullKernelWeightedEnvelope
    calc
      _ = 1 * (annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift) := by rw [one_mul]
      _ ≤ boundaryCoefficientPhaseCost parameters shift *
          (annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift) :=
        mul_le_mul_of_nonneg_right (boundaryCoefficientPhaseCost_one_le parameters shift)
          (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (fullKernelEntryNorm_nonnegative kernel shift))
      _ = _ := by ring
  have term := (fullKernelWeightedEnvelope_summable parameters moment kernel).le_tsum shift
    (fun other _ => fullKernelWeightedEnvelope_nonnegative parameters moment kernel other)
  have product := weighted.trans (term.trans bounded)
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (annularFrequency_pos shift) moment)]
  simpa only [mul_comm] using product

theorem fullLattice_decay_summable :
    Summable (fun shift : ℤ × ℤ => (annularFrequency shift.1 shift.2 ^ 4)⁻¹) :=
  Grad.AnnularJointRegularity.annularLattice_inverse_four_summable

end Grad.AnnularKernelContinuity
