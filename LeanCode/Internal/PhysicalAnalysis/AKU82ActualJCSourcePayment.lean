import AKU81ActualPhysicalForwardBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 3000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation

def finiteResidualPayment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) : ℝ :=
  ‖quotientEta parameters (grade+12) source‖+
    physicalBudget parameters field rho epsilon (grade+12)*‖quotientEta parameters 12 source‖

theorem finiteResidualPayment_nonnegative (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) : 0 ≤ finiteResidualPayment parameters field rho epsilon source grade :=
  add_nonneg (norm_nonneg _) (mul_nonneg (physicalBudget_nonnegative parameters field rho epsilon _) (norm_nonneg _))

theorem finiteLiftAxisPayment_residual_le (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    finiteLiftAxisPayment parameters field rho epsilon source (grade+6) ≤
      finiteResidualPayment parameters field rho epsilon source grade := by
  apply add_le_add (originalSourceNorm_monotone parameters source (by omega : grade+6+4 ≤ grade+12))
  exact mul_le_mul (physicalBudget_monotone parameters field rho epsilon (by omega : grade+6+4 ≤ grade+12))
    (originalSourceNorm_monotone parameters source (by omega : 4 ≤ 12)) (norm_nonneg _)
    (physicalBudget_nonnegative parameters field rho epsilon _)

theorem finiteResidualPayment_low_product (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    (1+physicalBudget parameters field rho epsilon (grade+6))*‖quotientEta parameters 10 source‖ ≤
      finiteResidualPayment parameters field rho epsilon source grade := by
  have first := originalSourceNorm_monotone parameters source (by omega : 10 ≤ grade+12)
  have second := mul_le_mul (physicalBudget_monotone parameters field rho epsilon (by omega : grade+6 ≤ grade+12))
    (originalSourceNorm_monotone parameters source (by omega : 10 ≤ 12)) (norm_nonneg _)
    (physicalBudget_nonnegative parameters field rho epsilon (grade+12))
  unfold finiteResidualPayment
  nlinarith only [first,second]

/-- JC in the original fourfold source norm, with the source grade in the
low factor fixed at twelve. The low estimate used here is independent. -/
theorem originalRealFiniteLiftResidual_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 8 ≤ 1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters),
      ‖quotientEta parameters grade (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖ ≤
        constant*finiteResidualPayment parameters field rho epsilon source grade := by
  obtain ⟨forwardConstant,forwardNonnegative,forwardBound⟩ := actualPhysicalEtaZero_bound parameters length grade
  obtain ⟨highConstant,highNonnegative,highBound⟩ := originalFiniteLiftNorm_payment parameters length (grade+6)
  obtain ⟨lowConstant,lowNonnegative,lowBound⟩ := originalFiniteLiftNorm_low_payment parameters length
  refine ⟨1+forwardConstant*(highConstant+lowConstant),by positivity,fun rho epsilon field low bounded potential source => ?_⟩
  have high := (originalRealFiniteLift_norm_le parameters length rho epsilon field low source (grade+6)).trans
    ((highBound rho epsilon field low source).trans
      (mul_le_mul_of_nonneg_left (finiteLiftAxisPayment_residual_le parameters field rho epsilon source grade) highNonnegative))
  have small := (originalRealFiniteLift_norm_le parameters length rho epsilon field low source 4).trans
    (lowBound rho epsilon field low bounded source)
  have currentNonnegative := physicalBudget_nonnegative parameters field rho epsilon (grade+6)
  have smallTerm : (1+physicalBudget parameters field rho epsilon (grade+6)) *
      (originalGradeNorm 4 (originalRealFiniteLiftU parameters length rho epsilon field low source)+
        originalGradeNorm 4 (originalRealFiniteLiftS parameters length rho epsilon field low source)) ≤
      lowConstant*finiteResidualPayment parameters field rho epsilon source grade := by
    have smallScaled := mul_le_mul_of_nonneg_left small (by positivity : 0 ≤ 1+physicalBudget parameters field rho epsilon (grade+6))
    have product := mul_le_mul_of_nonneg_left (finiteResidualPayment_low_product parameters field rho epsilon source grade) lowNonnegative
    nlinarith only [smallScaled,product]
  have derivative : ‖quotientEta parameters grade (quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
      ![(0,originalRealFiniteLiftU parameters length rho epsilon field low source,
        originalRealFiniteLiftS parameters length rho epsilon field low source)])‖ ≤
      (forwardConstant*(highConstant+lowConstant))*finiteResidualPayment parameters field rho epsilon source grade := by
    have forward := forwardBound rho epsilon field
      (originalLiftAxis_low_four parameters length rho epsilon field low) potential
      (originalRealFiniteLiftU parameters length rho epsilon field low source)
      (originalRealFiniteLiftS parameters length rho epsilon field low source)
    have combined := mul_le_mul_of_nonneg_left (add_le_add high smallTerm) forwardNonnegative
    nlinarith only [forward,combined]
  have sourceBound : ‖quotientEta parameters grade source‖ ≤ finiteResidualPayment parameters field rho epsilon source grade :=
    (originalSourceNorm_monotone parameters source (by omega : grade ≤ grade+12)).trans
      (le_add_of_nonneg_right (mul_nonneg (physicalBudget_nonnegative parameters field rho epsilon (grade+12))
        (norm_nonneg (quotientEta parameters 12 source))))
  unfold originalRealFiniteLiftResidual
  rw [map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add sourceBound derivative).trans_eq (by ring))

/-- A separate fixed low residual estimate for the later EX product. -/
theorem originalRealFiniteLiftResidual_low_payment (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 20 ≤ 1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters),
      ‖quotientEta parameters 8 (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖ ≤
        constant*‖quotientEta parameters 20 source‖ := by
  obtain ⟨constant,nonnegative,bound⟩ := originalRealFiniteLiftResidual_payment parameters length 8
  refine ⟨2*constant,mul_nonneg (by norm_num) nonnegative,fun rho epsilon field low bounded potential source => ?_⟩
  have product := mul_le_mul_of_nonneg_right bounded (norm_nonneg (quotientEta parameters 12 source))
  have small := originalSourceNorm_monotone parameters source (by omega : 12 ≤ 20)
  have payment : finiteResidualPayment parameters field rho epsilon source 8 ≤ 2*‖quotientEta parameters 20 source‖ := by
    unfold finiteResidualPayment
    norm_num only [Nat.reduceAdd]
    nlinarith only [product,small]
  exact (bound rho epsilon field low
    ((physicalBudget_monotone parameters field rho epsilon (by omega : 8 ≤ 20)).trans bounded) potential source).trans
    ((mul_le_mul_of_nonneg_left payment nonnegative).trans_eq (by ring))

end Grad.FinitePhysicalJetLift
