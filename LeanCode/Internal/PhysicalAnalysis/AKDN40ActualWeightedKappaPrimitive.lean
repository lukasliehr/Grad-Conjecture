import AKDN39EulerTerminalSumEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.FlatSourceProjection Grad.QuotientProjection Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore
open Grad.AnnularKernelL2 Grad.GaugeCoefficients.Physical.Allocation

/-- Actual kappa/primitive products with an external ordered-word budget.
Both coefficient factors are combined before the primitive is paid. -/
theorem actualKappaPrimitive_weightedEuler (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) (component : Fin 3) (slot : Fin 4) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ source : SmoothQuotient parameters, ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
    let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
    ‖budget extra • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => radialConjugatedAction parameters lower positive bounded.le
        (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
        power 0 point (primitive power point)) radius.val‖ ≤
      constant*eulerAllocationSum (fun order inputRank =>
        ‖budget (extra+order) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (primitive power) radius.val‖+
        ‖budget (extra+order+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (primitive 0) radius.val‖)
        (eulerLeibnizTerms rank) := by
  obtain ⟨first,second,first0,second0,action⟩ := actualSourceKappaCurve_EulerAllocation parameters length compact lower
    positive bounded component power rank
  obtain ⟨coefficient,coefficientOne,uniform⟩ := finiteUniformMajorant
    (fun order : Fin (rank+1) => first order.val+second order.val)
  obtain ⟨pairConstant,pairOne,pair⟩ := uniformReferencePhysicalBudget_pair parameters 10 total
  have coefficient0 : 0 ≤ coefficient := zero_le_one.trans coefficientOne
  have pair0 : 0 ≤ pairConstant := zero_le_one.trans pairOne
  have power0 : 0 ≤ (2:ℝ)^power := by positivity
  refine ⟨(2^power*coefficient)*pairConstant,mul_nonneg (mul_nonneg power0 coefficient0) pair0,?_⟩
  intro state unit source radius inside
  dsimp only
  let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
  let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
  have budget0 (order : ℕ) : 0 ≤ budget order := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have smooth (grade : ℕ) : ContDiffOn ℝ ∞ (primitive grade) (Icc lower 1) :=
    (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth grade
  have same := (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).shift bounded
  have actual := mul_le_mul_of_nonneg_left (action state unit primitive smooth same radius inside) (budget0 extra)
  rw [norm_smul,Real.norm_of_nonneg (budget0 extra)]
  apply actual.trans
  rw [eulerAllocationSum_mul_left,eulerAllocationSum_mul_left]
  apply eulerAllocationSum_mono
  intro term member
  have allocated := eulerLeibnizTerms_rank rank term member
  have sumLe : first term.1+second term.1 ≤ coefficient :=
    (le_abs_self _).trans (uniform ⟨term.1,by omega⟩)
  have firstLe : first term.1 ≤ coefficient := by linarith [second0 term.1]
  have secondLe : second term.1 ≤ coefficient := by linarith [first0 term.1]
  let high := vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (primitive power) radius.val
  let low := vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (primitive 0) radius.val
  have coefficientBound := twoCoefficientPayments_uniform firstLe secondLe coefficient0 power0 (le_refl ((2:ℝ)^power))
    (budget0 term.1) (budget0 (term.1+power)) (norm_nonneg high) (norm_nonneg low)
  have multiplied := mul_le_mul_of_nonneg_left coefficientBound (budget0 extra)
  have firstPair := mul_le_mul_of_nonneg_right
    (pair state.val.val.field state.val.val.rho state.val.val.epsilon unit extra term.1 (by omega)) (norm_nonneg high)
  have secondPair := mul_le_mul_of_nonneg_right
    (pair state.val.val.field state.val.val.rho state.val.val.epsilon unit extra (term.1+power) (by omega)) (norm_nonneg low)
  have joint : budget extra*(budget term.1*‖high‖+budget (term.1+power)*‖low‖) ≤
      pairConstant*(budget (extra+term.1)*‖high‖+budget (extra+term.1+power)*‖low‖) := by
    dsimp only [budget] at firstPair secondPair ⊢
    rw [show extra+(term.1+power)=extra+term.1+power by omega] at secondPair
    nlinarith only [firstPair,secondPair]
  have jointPaid := mul_le_mul_of_nonneg_left joint (mul_nonneg power0 coefficient0)
  change budget extra*(2^power*(first term.1*budget term.1*‖high‖+
      second term.1*budget (term.1+power)*‖low‖)) ≤
    (2^power*coefficient)*pairConstant*(‖budget (extra+term.1) • high‖+‖budget (extra+term.1+power) • low‖)
  rw [norm_smul,norm_smul,Real.norm_of_nonneg (budget0 (extra+term.1)),Real.norm_of_nonneg (budget0 (extra+term.1+power))]
  nlinarith only [multiplied,jointPaid]

end Grad.OriginalCartesianTameEstimate
