import AKC12ActualPhaseRatioJets
import AKC13ActualMatrixJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace Grad.AnnularWeightedSmoothness

theorem polynomialReserve_decay (frequency : ℝ) (one : 1 ≤ frequency)
    (rank order : ℕ) (valid : rank ≤ order) :
    frequency ^ rank * (frequency ^ (order + 4))⁻¹ ≤ (frequency ^ 4)⁻¹ := by
  have positive : 0 < frequency := lt_of_lt_of_le zero_lt_one one
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one valid)
    (inv_nonneg.mpr (pow_nonneg positive.le _))).trans_eq
  rw [pow_add]
  field_simp

/-- The finite radial cost is absorbed by a finite polynomial reserve, with
no alteration of the original exponential kernel envelope. -/
theorem phaseProductJet_reserve_bound (phase ratio shift input phaseJet matrixJet phaseConstant matrixConstant : ℝ)
    (rank order : ℕ) (valid : rank ≤ order)
    (ratioNonnegative : 0 ≤ ratio)
    (shiftOne : 1 ≤ shift) (inputOne : 1 ≤ input)
    (matrixNonnegative : 0 ≤ matrixJet) (phaseConstantNonnegative : 0 ≤ phaseConstant)
    (matrixConstantNonnegative : 0 ≤ matrixConstant)
    (phaseBound : phaseJet ≤ phaseConstant * phase * shift ^ rank * input ^ rank)
    (matrixBound : (phase * ratio) * matrixJet ≤ matrixConstant * (shift ^ (order + 4))⁻¹) :
    (input ^ (order + 4))⁻¹ * ratio * (phaseJet * matrixJet) ≤
      phaseConstant * matrixConstant * ((shift ^ 4)⁻¹ * (input ^ 4)⁻¹) := by
  have first := mul_le_mul_of_nonneg_right phaseBound (mul_nonneg ratioNonnegative matrixNonnegative)
  have combined : ratio * (phaseJet * matrixJet) ≤
      phaseConstant * shift ^ rank * input ^ rank *
        (matrixConstant * (shift ^ (order + 4))⁻¹) := by
    calc
      _ = phaseJet * (ratio * matrixJet) := by ring
      _ ≤ (phaseConstant * phase * shift ^ rank * input ^ rank) * (ratio * matrixJet) := first
      _ = phaseConstant * shift ^ rank * input ^ rank * ((phase * ratio) * matrixJet) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left matrixBound (by positivity)
  have shiftDecay := polynomialReserve_decay shift shiftOne rank order valid
  have inputDecay := polynomialReserve_decay input inputOne rank order valid
  calc
    _ = (input ^ (order + 4))⁻¹ * (ratio * (phaseJet * matrixJet)) := by ring
    _ ≤ (input ^ (order + 4))⁻¹ * (phaseConstant * shift ^ rank * input ^ rank *
        (matrixConstant * (shift ^ (order + 4))⁻¹)) :=
      mul_le_mul_of_nonneg_left combined (by positivity)
    _ = (phaseConstant * matrixConstant) *
        ((shift ^ rank * (shift ^ (order + 4))⁻¹) *
          (input ^ rank * (input ^ (order + 4))⁻¹)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul shiftDecay inputDecay (by positivity) (by positivity))
      (mul_nonneg phaseConstantNonnegative matrixConstantNonnegative)

end Grad.AnnularWeightedSmoothness
