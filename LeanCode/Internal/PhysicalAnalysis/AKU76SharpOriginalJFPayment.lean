import AKU75OriginalFiniteLiftNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation

/-- The requested original JF payment, with the low source grade fixed at six. -/
theorem originalFiniteLiftNorm_sharp_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (source : SmoothQuotient parameters),
      originalFiniteLiftNorm parameters length rho epsilon field low source grade ≤
        constant * (‖quotientEta parameters (grade+6) source‖ +
          physicalBudget parameters field rho epsilon (grade+6) * ‖quotientEta parameters 6 source‖) := by
  obtain ⟨constant,nonnegative,bound⟩ := originalFiniteLiftNorm_payment parameters length grade
  refine ⟨constant,nonnegative,fun rho epsilon field low source => (bound rho epsilon field low source).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ nonnegative
  apply add_le_add (originalSourceNorm_monotone parameters source (by omega : grade+4 ≤ grade+6))
  exact mul_le_mul
    (physicalBudget_monotone parameters field rho epsilon (by omega : grade+4 ≤ grade+6))
    (originalSourceNorm_monotone parameters source (by omega : 4 ≤ 6)) (norm_nonneg _)
    (physicalBudget_nonnegative parameters field rho epsilon _)

/-- The independent low estimate is proved directly. It is not obtained by
feeding a high current factor into a low slot of a later product estimate. -/
theorem originalFiniteLiftNorm_low_payment (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 8 ≤ 1)
      (source : SmoothQuotient parameters),
      originalFiniteLiftNorm parameters length rho epsilon field low source 4 ≤
        constant * ‖quotientEta parameters 10 source‖ := by
  obtain ⟨constant,nonnegative,bound⟩ := originalFiniteLiftNorm_payment parameters length 4
  refine ⟨2*constant,mul_nonneg (by norm_num) nonnegative,fun rho epsilon field low bounded source => ?_⟩
  have product := mul_le_mul_of_nonneg_right bounded (norm_nonneg (quotientEta parameters 4 source))
  have high := originalSourceNorm_monotone parameters source (by omega : 8 ≤ 10)
  have lowSource := originalSourceNorm_monotone parameters source (by omega : 4 ≤ 10)
  have payment : finiteLiftAxisPayment parameters field rho epsilon source 4 ≤ 2*‖quotientEta parameters 10 source‖ := by
    unfold finiteLiftAxisPayment
    norm_num only [Nat.reduceAdd] at *
    nlinarith only [product,high,lowSource]
  exact (bound rho epsilon field low source).trans
    ((mul_le_mul_of_nonneg_left payment nonnegative).trans_eq (by ring))

end Grad.FinitePhysicalJetLift
