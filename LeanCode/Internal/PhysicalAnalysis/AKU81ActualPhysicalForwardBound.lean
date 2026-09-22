import AKU80RealOriginalDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 3000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization

theorem physicalEtaZero_base_norm (parameters : PhaseParameters) (rho epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) :
    stateNorm grade ((epsilon : ℂ),planarReferenceCore parameters+field,(0 : ACore parameters 1)) ≤
      originalGradeNorm grade (planarReferenceCore parameters)+physicalBudget parameters field rho epsilon grade := by
  have sum := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le grade (planarReferenceCore parameters) field
  simp only [stateNorm,originalGradeNorm_zero,add_zero,Complex.norm_real,Real.norm_eq_abs]
  unfold physicalBudget
  linarith [abs_nonneg rho]

/-- Q4 applied directly to the actual physical eta-zero variation. The
potential disappears from the literal formula; no chart norm is substituted. -/
theorem actualPhysicalEtaZero_bound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (_low : physicalBudget parameters field rho epsilon 4 ≤ 1)
      (potential : ACore parameters 1) (vector : ACore parameters 3) (scalar : ACore parameters 1),
      ‖quotientEta parameters grade (quotientRowsDerivative parameters length 1
        ((epsilon : ℂ),planarReferenceCore parameters+field,potential) ![(0,vector,scalar)])‖ ≤
      constant * (originalGradeNorm (grade+6) vector+originalGradeNorm (grade+6) scalar +
        (1+physicalBudget parameters field rho epsilon (grade+6)) *
          (originalGradeNorm 4 vector+originalGradeNorm 4 scalar)) := by
  obtain ⟨constant,nonnegative,bound⟩ := quotientRowsDerivative_bound (parameters := parameters)
    length grade 1 (originalGradeNorm 4 (planarReferenceCore parameters)+1)
  refine ⟨2*constant*(1+originalGradeNorm (grade+6) (planarReferenceCore parameters)),
    mul_nonneg (mul_nonneg (by norm_num) nonnegative) (add_nonneg (by norm_num) (originalGradeNorm_nonnegative (grade+6) (planarReferenceCore parameters))),fun rho epsilon field low potential vector scalar => ?_⟩
  have baseLow := (physicalEtaZero_base_norm parameters rho epsilon field 4).trans
    (add_le_add le_rfl low)
  have derivative := bound ((epsilon : ℂ),planarReferenceCore parameters+field,(0 : ACore parameters 1))
    ![(0,vector,scalar)] baseLow
  have actual := (quotientEta_norm_le_rows parameters grade _).trans
    (mul_le_mul_of_nonneg_left derivative (by norm_num : (0 : ℝ) ≤ 2))
  have same : quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential) ![(0,vector,scalar)] =
    quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,(0 : ACore parameters 1)) ![(0,vector,scalar)] := by
    rw [quotientRowsDerivative_etaZero,quotientRowsDerivative_etaZero]
    rfl
  rw [same]
  simp only [oneHighStateExpression,oneHighArgumentSum_single,Fin.prod_univ_one] at actual
  have directionNorm (order : ℕ) : stateNorm order (![(0,vector,scalar)] 0) =
      originalGradeNorm order vector+originalGradeNorm order scalar := by
    simp [stateNorm]
  rw [directionNorm,directionNorm] at actual
  change _ ≤ 2*(constant*((1+stateNorm (grade+6)
    ((epsilon : ℂ),planarReferenceCore parameters+field,(0 : ACore parameters 1))) *
      (originalGradeNorm 4 vector+originalGradeNorm 4 scalar)+
        (originalGradeNorm (grade+6) vector+originalGradeNorm (grade+6) scalar))) at actual
  have baseHigh := physicalEtaZero_base_norm parameters rho epsilon field (grade+6)
  have lowNonnegative := add_nonneg (originalGradeNorm_nonnegative 4 vector) (originalGradeNorm_nonnegative 4 scalar)
  have highNonnegative := add_nonneg (originalGradeNorm_nonnegative (grade+6) vector) (originalGradeNorm_nonnegative (grade+6) scalar)
  have referenceNonnegative := originalGradeNorm_nonnegative (grade+6) (planarReferenceCore parameters)
  have currentNonnegative := physicalBudget_nonnegative parameters field rho epsilon (grade+6)
  have allocation : (1+stateNorm (grade+6) ((epsilon : ℂ),planarReferenceCore parameters+field,(0 : ACore parameters 1))) *
      (originalGradeNorm 4 vector+originalGradeNorm 4 scalar) +
        (originalGradeNorm (grade+6) vector+originalGradeNorm (grade+6) scalar) ≤
    (1+originalGradeNorm (grade+6) (planarReferenceCore parameters)) *
      (originalGradeNorm (grade+6) vector+originalGradeNorm (grade+6) scalar+
        (1+physicalBudget parameters field rho epsilon (grade+6))*(originalGradeNorm 4 vector+originalGradeNorm 4 scalar)) := by
    nlinarith only [mul_le_mul_of_nonneg_right baseHigh lowNonnegative,
      mul_nonneg referenceNonnegative highNonnegative,
      mul_nonneg (mul_nonneg referenceNonnegative currentNonnegative) lowNonnegative]
  have scaled := mul_le_mul_of_nonneg_left allocation (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative)
  nlinarith only [actual,scaled]

end Grad.FinitePhysicalJetLift
