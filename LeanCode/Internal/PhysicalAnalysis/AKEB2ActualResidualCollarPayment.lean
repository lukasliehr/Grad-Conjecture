import AKEB1IndependentActualResidualBase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation

/-- Actual residual collar payment: the high coefficient multiplies the
independently controlled ninth source slot, leaving one high factor. -/
theorem originalRealFiniteLiftResidual_collar_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6≤originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 24≤1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters),
      ‖quotientEta parameters (grade+10) (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖+
        (1+physicalBudget parameters field rho epsilon (grade+16))*
          ‖quotientEta parameters 9 (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖≤
      constant*(‖quotientEta parameters (grade+24) source‖+
        (1+physicalBudget parameters field rho epsilon (grade+24))*‖quotientEta parameters 24 source‖) := by
  obtain ⟨highConstant,high0,highBound⟩ := originalRealFiniteLiftResidual_payment parameters length (grade+10)
  obtain ⟨lowConstant,low0,lowBound⟩ := originalRealFiniteLiftResidual_ninth_payment parameters length
  refine ⟨highConstant+lowConstant,add_nonneg high0 low0,?_⟩
  intro rho epsilon field low bounded potential source
  let payment := ‖quotientEta parameters (grade+24) source‖+
    (1+physicalBudget parameters field rho epsilon (grade+24))*‖quotientEta parameters 24 source‖
  have high := highBound rho epsilon field low
    ((physicalBudget_monotone parameters field rho epsilon (by norm_num : 8≤24)).trans bounded) potential source
  have lowPaid := lowBound rho epsilon field low bounded potential source
  have budget0 (order : ℕ) : 0≤1+physicalBudget parameters field rho epsilon order :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have highPayment : finiteResidualPayment parameters field rho epsilon source (grade+10)≤payment := by
    unfold finiteResidualPayment payment
    apply add_le_add (originalSourceNorm_monotone parameters source (by omega))
    exact mul_le_mul
      ((physicalBudget_monotone parameters field rho epsilon (by omega : grade+10+12≤grade+24)).trans
        (le_add_of_nonneg_left zero_le_one))
      (originalSourceNorm_monotone parameters source (by norm_num : 12≤24)) (norm_nonneg _) (budget0 _)
  have lowPayment : (1+physicalBudget parameters field rho epsilon (grade+16))*‖quotientEta parameters 21 source‖≤payment := by
    apply le_trans ?_ (le_add_of_nonneg_left (norm_nonneg (quotientEta parameters (grade+24) source)))
    exact mul_le_mul
      (add_le_add (le_refl _) (physicalBudget_monotone parameters field rho epsilon (by omega)))
      (originalSourceNorm_monotone parameters source (by norm_num : 21≤24)) (norm_nonneg _) (budget0 _)
  have highFinal := high.trans (mul_le_mul_of_nonneg_left highPayment high0)
  have lowFinal : (1+physicalBudget parameters field rho epsilon (grade+16))*
      ‖quotientEta parameters 9 (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖≤lowConstant*payment := by
    calc
      _ ≤ (1+physicalBudget parameters field rho epsilon (grade+16))*(lowConstant*‖quotientEta parameters 21 source‖) :=
        mul_le_mul_of_nonneg_left lowPaid (budget0 _)
      _ = lowConstant*((1+physicalBudget parameters field rho epsilon (grade+16))*‖quotientEta parameters 21 source‖) := by ring
      _ ≤ lowConstant*payment := mul_le_mul_of_nonneg_left lowPayment low0
  exact (add_le_add highFinal lowFinal).trans_eq (by ring)

end Grad.FinitePhysicalJetLift
