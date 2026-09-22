import AKDN31FiniteEulerTerminal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

/-- The weighted Euler induction is applied to the SAME native solution
and its actual balanced source. The finite terminal sum contains only
pure-frequency native values and genuine source Euler derivatives at the
original total-rank allocations. The neighborhood is independent of rank. -/
theorem sameNativeBalanced_finiteEuler (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (total : ℕ) :
    ∃ gain : ℝ, 1 ≤ gain ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
      (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
      (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data),
    (∀ power : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let balanced := balancedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response
    let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
    let unknown := fun order grade => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced grade) radius.val‖
    let forcing := fun order grade => ‖physicalPairMeanFree parameters‖*
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order
        (fun point => balancedActualSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade
          (collarRadius lower positive (lowerHalf.trans (by norm_num)) point)) radius.val‖
    ∀ order extra grade : ℕ, extra+grade+order ≤ total →
      budget extra*unknown order grade ≤ gain^total*finiteEulerTerminal total budget unknown forcing := by
  obtain ⟨constant,constant0,recurrence⟩ := sameNativeBalanced_normRecurrence parameters length compact lower
    positive lowerHalf lengthPositive widthHalf widthLength total
  obtain ⟨pairConstant,pairOne,pair⟩ := uniformReferencePhysicalBudget_pair parameters 10 total
  obtain ⟨weightConstant,weightOne,weightBound⟩ := finiteUniformMajorant
    (fun index : Fin (total+1) × Fin (total+1) =>
      ((nativeEulerAllocations index.1.val index.2.val).length : ℝ)*constant)
  have pair0 : 0 ≤ pairConstant := zero_le_one.trans pairOne
  have weight0 : 0 ≤ weightConstant := zero_le_one.trans weightOne
  let gain := 1+pairConstant*weightConstant
  have gainOne : 1 ≤ gain := by dsimp only [gain]; linarith [mul_nonneg pair0 weight0]
  refine ⟨gain,gainOne,?_⟩
  intro state unit small data curves allGrades radius inside
  dsimp only
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let balanced := balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
  let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
  let unknown := fun order grade => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced grade) radius.val‖
  let forcing := fun order grade => ‖physicalPairMeanFree parameters‖*
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order
      (fun point => balancedActualSource parameters length compact lower positive bounded state data curves grade
        (collarRadius lower positive bounded.le point)) radius.val‖
  have budget0 (order : ℕ) : 0 ≤ budget order := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have unknown0 (order grade : ℕ) : 0 ≤ unknown order grade := norm_nonneg _
  have forcing0 (order grade : ℕ) : 0 ≤ forcing order grade := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have terminal0 := finiteEulerTerminal_nonnegative total budget unknown forcing budget0 unknown0 forcing0
  have inductionBound := jointWeightedEulerInduction total budget unknown forcing nativeEulerAllocations
    (fun _ _ _ => constant) pairConstant weightConstant (finiteEulerTerminal total budget unknown forcing)
    pair0 weight0 terminal0 budget0 unknown0
    (pair state.val.val.field state.val.val.rho state.val.val.epsilon unit)
    (finiteEulerTerminal_pure total budget unknown forcing budget0 unknown0 forcing0)
    (finiteEulerTerminal_source total budget unknown forcing budget0 unknown0 forcing0)
    nativeEulerAllocations_rank (fun _ _ _ _ => constant0) (by
      intro order grade allocated
      rw [listConstantWeight_sum]
      exact (le_abs_self _).trans (weightBound (⟨order,by omega⟩,⟨grade,by omega⟩))) (by
      intro order grade allocated
      have actual := recurrence state unit small data curves allGrades order grade allocated radius inside
      change unknown (order+1) grade ≤ forcing order grade+
        constant*((nativeEulerAllocations order grade).map (fun term => budget term.1*unknown term.2.2 term.2.1)).sum at actual
      rw [listMappedSum_mul_left] at actual
      simpa only [mul_assoc] using actual)
  intro order extra grade allocated
  have actual := inductionBound order extra grade allocated
  exact actual.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ gainOne (by omega)) terminal0)

end Grad.OriginalCartesianTameEstimate
