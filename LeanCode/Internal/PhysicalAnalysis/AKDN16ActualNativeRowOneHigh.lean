import AKDN15BalancedInputEulerNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

/-- SAME native j/c/rV row, genuine Euler differentiation, and exact
complementary coefficient budgets. Kinematic derivatives only lower the
terminal Euler rank; no high coefficient is multiplied by a high input. -/
theorem actualNativeRow_EulerOneHigh (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (row : Fin 3) (grade rank : ℕ) :
    ∃ first second : ℕ → ℝ, (∀ order, 0 ≤ first order) ∧ (∀ order, 0 ≤ second order) ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
      (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
      (_curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data),
    (∀ power : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let balanced := balancedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response
    let inputSize := fun power order => eulerAllocationSum
      (fun _ terminal => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) terminal (balanced power) radius.val‖) (eulerLeibnizTerms order)
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (balancedUnknownPhysicalRow parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state response row grade) radius.val‖ ≤
      eulerAllocationSum (fun order inputRank => 2^(grade+1) *
        (first order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order))*inputSize (grade+1) inputRank+
         second order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(order+grade+1)))*inputSize 0 inputRank))
        (eulerLeibnizTerms rank) := by
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
  obtain ⟨first,second,first0,second0,rowBound⟩ := samePhysicalRowCurve_EulerAllocation parameters length compact lower positive bounded row (grade+1) rank
  obtain ⟨inputConstant,input0,inputBound⟩ := balancedInputCurve_EulerBound parameters
  refine ⟨(fun order => first order*inputConstant),(fun order => second order*inputConstant),
    (fun order => mul_nonneg (first0 order) input0),(fun order => mul_nonneg (second0 order) input0),?_⟩
  intro state unit small data curves allGrades radius inside
  dsimp only
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let balanced := balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
  let input := sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have inputSmooth := sameNativeBalancedInput_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  have inputSame := sameNativeBalancedInput_shift parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data allGrades
  have actual := rowBound state unit input inputSmooth inputSame radius inside
  have original : balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state response row grade =
      fun point => radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state row) (grade+1) 0 point (input (grade+1) point) := by
    funext point
    exact balancedUnknownPhysicalRow_sameNativeInput parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data row grade point
  rw [original]
  apply actual.trans
  apply eulerAllocationSum_mono
  intro term _
  have inputEstimate (power order : ℕ) :
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (input power) radius.val‖ ≤
        inputConstant*eulerAllocationSum
          (fun _ terminal => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) terminal (balanced power) radius.val‖) (eulerLeibnizTerms order) :=
    inputBound lower positive bounded (balanced power) order
      (contDiffOn_infty.mp (sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data curves allGrades power) order) radius inside
  have firstBudget0 : 0 ≤ 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+term.1) :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have secondBudget0 : 0 ≤ 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(term.1+(grade+1))) :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have bound := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (inputEstimate (grade+1) term.2) (mul_nonneg (first0 term.1) firstBudget0))
    (mul_le_mul_of_nonneg_left (inputEstimate 0 term.2) (mul_nonneg (second0 term.1) secondBudget0)))
      (by positivity : 0 ≤ (2:ℝ)^(grade+1))
  apply bound.trans_eq
  rw [show term.1+(grade+1)=term.1+grade+1 by omega]
  ring

end Grad.OriginalCartesianTameEstimate
