import AKDN29WeightedNativeCollector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

/-- The actual native SR19 norm recurrence. The coefficient constant is
chosen before the state and source. Each term has the checked exact rank
allocation and strictly lower Euler order; the forcing is the SAME actual
balanced source, and the literal outer mean-free projection is retained. -/
theorem sameNativeBalanced_normRecurrence (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (total : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
      (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
      (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data),
    (∀ power : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted) →
    ∀ (rank grade : ℕ), rank+grade+1 ≤ total →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let balanced := balancedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response
    let known := fun point => balancedActualSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade
      (collarRadius lower positive (lowerHalf.trans (by norm_num)) point)
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) (rank+1) (balanced grade) radius.val‖ ≤
      ‖physicalPairMeanFree parameters‖*‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank known radius.val‖+
      constant*((nativeEulerAllocations rank grade).map (fun term =>
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+term.1))*
          ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.2.2 (balanced term.2.1) radius.val‖)).sum := by
  obtain ⟨rowConstant,row0,rows⟩ := actualNativeRows_uniform parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength total
  obtain ⟨fluxConstant,flux0,fluxEstimate⟩ := balancedFluxCurve_EulerNormRows parameters length
  obtain ⟨phaseConstant,phaseOne,phaseUniform⟩ := finiteUniformMajorant
    (fun rank : Fin (total+1) => balancedPhaseEulerConstant parameters rank.val)
  have phase0 : 0 ≤ phaseConstant := zero_le_one.trans phaseOne
  refine ⟨‖physicalPairMeanFree parameters‖*(phaseConstant+3*fluxConstant*rowConstant),
    mul_nonneg (norm_nonneg _) (add_nonneg phase0 (mul_nonneg (mul_nonneg (by norm_num) flux0) row0)),?_⟩
  intro state unit small data curves allGrades rank grade allocated radius inside
  dsimp only
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let balanced := balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
  let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
  let unknown := fun order power => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced power) radius.val‖
  let rowCurve := balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state response
  let phaseCurve := sameNativeBalancedPhaseCurve parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data grade
  let fluxCurve := sameNativeBalancedFluxCurve parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data grade
  let knownCurve := fun point => balancedActualSource parameters length compact lower positive bounded state data curves grade
    (collarRadius lower positive bounded.le point)
  let inputSize := fun power order => eulerAllocationSum (fun _ terminal => unknown terminal power) (eulerLeibnizTerms order)
  let rowSize := fun order => eulerAllocationSum (fun coefficient inputRank =>
    budget coefficient*inputSize (grade+1) inputRank+budget (coefficient+grade+1)*inputSize 0 inputRank) (eulerLeibnizTerms order)
  have budget0 (order : ℕ) : 0 ≤ budget order := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have budgetOne : 1 ≤ budget 0 := by
    dsimp only [budget]
    linarith [physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+0)]
  have unknown0 (order power : ℕ) : 0 ≤ unknown order power := norm_nonneg _
  have phaseBound : ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank phaseCurve radius.val‖ ≤
      phaseConstant*inputSize (grade+1) rank := by
    have actual := sameNativeBalancedPhaseCurve_EulerBound parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade rank radius inside
    apply actual.trans
    rw [show inputSize (grade+1) rank = eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms rank) from rfl,
      eulerAllocationSum_mul_left]
    apply eulerAllocationSum_mono
    intro term member
    have ranks := eulerLeibnizTerms_rank rank term member
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (phaseUniform ⟨term.1,by omega⟩)) (unknown0 _ _)
  have rowBound (row : Fin 3) (order : ℕ) (orderLe : order ≤ total) :
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (rowCurve row grade) radius.val‖ ≤ rowConstant*rowSize order :=
    rows state unit small data curves allGrades row grade order (by omega) orderLe radius inside
  have rowSmooth (row : Fin 3) : ContDiffOn ℝ rank (rowCurve row grade) (Icc lower 1) :=
    contDiffOn_infty.mp (balancedUnknownPhysicalRow_nativeSmooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades row grade) rank
  have actualFlux := fluxEstimate lower positive bounded (rowCurve 0 grade) (rowCurve 1 grade) (rowCurve 2 grade)
    rank (rowSmooth 0) (rowSmooth 1) (rowSmooth 2) radius inside
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank fluxCurve radius.val‖ ≤ _ at actualFlux
  have rowSum : eulerAllocationSum (fun _ order =>
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (rowCurve 0 grade) radius.val‖+
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (rowCurve 1 grade) radius.val‖+
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (rowCurve 2 grade) radius.val‖) (eulerLeibnizTerms rank) ≤
      (3*rowConstant)*eulerAllocationSum (fun _ order => rowSize order) (eulerLeibnizTerms rank) := by
    rw [eulerAllocationSum_mul_left]
    apply eulerAllocationSum_mono
    intro term member
    have ranks := eulerLeibnizTerms_rank rank term member
    have orderLe : term.2 ≤ total := by omega
    nlinarith only [rowBound 0 term.2 orderLe,rowBound 1 term.2 orderLe,rowBound 2 term.2 orderLe]
  have fluxBound : ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank fluxCurve radius.val‖ ≤
      (3*fluxConstant*rowConstant)*eulerAllocationSum (fun _ order => rowSize order) (eulerLeibnizTerms rank) :=
    (actualFlux.trans (mul_le_mul_of_nonneg_left rowSum flux0)).trans_eq (by ring)
  have combined := nativeEulerCollector_bound budget unknown budget0 budgetOne unknown0 rank grade
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank phaseCurve radius.val‖
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank fluxCurve radius.val‖
    phaseConstant (3*fluxConstant*rowConstant) phase0 (mul_nonneg (mul_nonneg (by norm_num) flux0) row0) phaseBound fluxBound
  have actual := sameNativeBalanced_higherEuler parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades grade rank radius.val inside
  change vectorEulerWithinIteratedDerivative (Icc lower 1) (rank+1) (balanced grade) radius.val =
    physicalPairMeanFree parameters
      ((vectorEulerWithinIteratedDerivative (Icc lower 1) rank phaseCurve radius.val+
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank fluxCurve radius.val)+
       vectorEulerWithinIteratedDerivative (Icc lower 1) rank knownCurve radius.val) at actual
  rw [actual]
  have normSum := (norm_add_le
    (vectorEulerWithinIteratedDerivative (Icc lower 1) rank phaseCurve radius.val+
      vectorEulerWithinIteratedDerivative (Icc lower 1) rank fluxCurve radius.val)
    (vectorEulerWithinIteratedDerivative (Icc lower 1) rank knownCurve radius.val)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  have paid := normSum.trans (add_le_add combined (le_refl _))
  exact (((physicalPairMeanFree parameters).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left paid (norm_nonneg _))).trans_eq (by ring)

end Grad.OriginalCartesianTameEstimate
