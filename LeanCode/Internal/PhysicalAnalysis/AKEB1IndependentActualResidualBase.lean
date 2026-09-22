import AKU87OriginalReferenceNormPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation

/-- The independent ninth-grade residual slot, paid before multiplication
by the high state coefficient in the actual collar estimate. -/
theorem originalRealFiniteLiftResidual_ninth_payment (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0≤constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6≤originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 24≤1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters),
      ‖quotientEta parameters 9 (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖≤
        constant*‖quotientEta parameters 21 source‖ := by
  obtain ⟨constant,constant0,bound⟩ := originalRealFiniteLiftResidual_payment parameters length 9
  refine ⟨2*constant,mul_nonneg (by norm_num) constant0,?_⟩
  intro rho epsilon field low bounded potential source
  have unit8 := (physicalBudget_monotone parameters field rho epsilon (by norm_num : 8≤24)).trans bounded
  have unit21 := (physicalBudget_monotone parameters field rho epsilon (by norm_num : 21≤24)).trans bounded
  have actual := bound rho epsilon field low unit8 potential source
  have sourceLow := originalSourceNorm_monotone parameters source (by norm_num : 12≤21)
  have product := mul_le_mul_of_nonneg_right unit21 (norm_nonneg (quotientEta parameters 12 source))
  have paid : finiteResidualPayment parameters field rho epsilon source 9≤2*‖quotientEta parameters 21 source‖ := by
    unfold finiteResidualPayment
    norm_num only [Nat.reduceAdd]
    nlinarith only [sourceLow,product]
  exact actual.trans ((mul_le_mul_of_nonneg_left paid constant0).trans_eq (by ring))

end Grad.FinitePhysicalJetLift
