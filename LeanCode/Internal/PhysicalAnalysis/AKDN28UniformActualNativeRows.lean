import AKDN27UniformJointPhysicalBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

theorem twoCoefficientPayments_uniform {first second bound scale target highBudget lowBudget highInput lowInput : ℝ}
    (firstLe : first ≤ bound) (secondLe : second ≤ bound) (bound0 : 0 ≤ bound)
    (scale0 : 0 ≤ scale) (scaleLe : scale ≤ target)
    (highBudget0 : 0 ≤ highBudget) (lowBudget0 : 0 ≤ lowBudget)
    (highInput0 : 0 ≤ highInput) (lowInput0 : 0 ≤ lowInput) :
    scale*(first*highBudget*highInput+second*lowBudget*lowInput) ≤
      target*bound*(highBudget*highInput+lowBudget*lowInput) := by
  have firstPaid := mul_le_mul_of_nonneg_right firstLe (mul_nonneg highBudget0 highInput0)
  have secondPaid := mul_le_mul_of_nonneg_right secondLe (mul_nonneg lowBudget0 lowInput0)
  have both : first*highBudget*highInput+second*lowBudget*lowInput ≤
      bound*(highBudget*highInput+lowBudget*lowInput) := by nlinarith only [firstPaid,secondPaid]
  have payment0 := mul_nonneg bound0 (add_nonneg (mul_nonneg highBudget0 highInput0) (mul_nonneg lowBudget0 lowInput0))
  exact ((mul_le_mul_of_nonneg_left both scale0).trans
    (mul_le_mul_of_nonneg_right scaleLe payment0)).trans_eq (by ring)

/-- All three actual physical rows have one common finite coefficient
constant below the requested output rank. The complementary budgets and
the genuine lower Euler input ranks are left in the estimate. -/
theorem actualNativeRows_uniform (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (total : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
      (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
      (_curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data),
    (∀ power : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted) →
    ∀ (row : Fin 3) (grade rank : ℕ), grade ≤ total → rank ≤ total →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let balanced := balancedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response
    let inputSize := fun power order => eulerAllocationSum
      (fun _ terminal => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) terminal (balanced power) radius.val‖) (eulerLeibnizTerms order)
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (balancedUnknownPhysicalRow parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state response row grade) radius.val‖ ≤
      constant*eulerAllocationSum (fun order inputRank =>
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order))*inputSize (grade+1) inputRank+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(order+grade+1)))*inputSize 0 inputRank)
        (eulerLeibnizTerms rank) := by
  classical
  choose first second first0 second0 rowBound using
    (fun (row : Fin 3) (grade rank : ℕ) => actualNativeRow_EulerOneHigh parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength row grade rank)
  obtain ⟨bound,boundOne,uniform⟩ := finiteUniformMajorant
    (fun index : Fin 3 × Fin (total+1) × Fin (total+1) × Fin (total+1) =>
      first index.1 index.2.1.val index.2.2.1.val index.2.2.2.val+
      second index.1 index.2.1.val index.2.2.1.val index.2.2.2.val)
  have bound0 : 0 ≤ bound := zero_le_one.trans boundOne
  refine ⟨2^(total+1)*bound,mul_nonneg (by positivity) bound0,?_⟩
  intro state unit small data curves allGrades row grade rank gradeLe rankLe radius inside
  dsimp only
  have actual := rowBound row grade rank state unit small data curves allGrades radius inside
  dsimp only at actual
  apply actual.trans
  rw [eulerAllocationSum_mul_left]
  apply eulerAllocationSum_mono
  intro term member
  have ranks := eulerLeibnizTerms_rank rank term member
  have combined : first row grade rank term.1+second row grade rank term.1 ≤ bound :=
    (le_abs_self _).trans (uniform (row,⟨grade,by omega⟩,⟨rank,by omega⟩,⟨term.1,by omega⟩))
  have firstLe : first row grade rank term.1 ≤ bound := by linarith [second0 row grade rank term.1]
  have secondLe : second row grade rank term.1 ≤ bound := by linarith [first0 row grade rank term.1]
  have budget0 (order : ℕ) :
      0 ≤ 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order) :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have input0 (power order : ℕ) : 0 ≤ eulerAllocationSum
      (fun _ terminal => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) terminal
        (balancedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) power) radius.val‖)
      (eulerLeibnizTerms order) :=
    eulerAllocationSum_nonnegative _ (fun _ _ => norm_nonneg _) _
  have powerLe : (2:ℝ)^(grade+1) ≤ 2^(total+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact twoCoefficientPayments_uniform firstLe secondLe bound0 (by positivity) powerLe
    (budget0 term.1) (budget0 (term.1+grade+1)) (input0 (grade+1) term.2) (input0 0 term.2)

end Grad.OriginalCartesianTameEstimate
