import AJF20ActualSolverAxisBounds
import AJF21FixedDerivativeOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus Grad.ClosedJets Grad.SourceCollarDivision
open Grad.AnnularUniformBoundary Grad.GaugeCoefficients.Physical.Allocation

section TripleBound
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_constantMinusTriple_bound (lift : D →L[ℝ] E) (outer : F →L[ℝ] E) (inner : E →L[ℝ] F)
    (liftBound outerBound innerBound : ℝ) (_liftNonnegative : 0 ≤ liftBound)
    (outerNonnegative : 0 ≤ outerBound) (innerNonnegative : 0 ≤ innerBound)
    (liftEstimate : ‖lift‖ ≤ liftBound) (outerEstimate : ‖outer‖ ≤ outerBound) (innerEstimate : ‖inner‖ ≤ innerBound) :
    ‖lift - outer.comp (inner.comp lift)‖ ≤ (1 + outerBound * innerBound) * liftBound := by
  have first := (ContinuousLinearMap.opNorm_comp_le inner lift).trans
    (mul_le_mul innerEstimate liftEstimate (norm_nonneg lift) innerNonnegative)
  have second := (ContinuousLinearMap.opNorm_comp_le outer (inner.comp lift)).trans
    (mul_le_mul outerEstimate first (norm_nonneg _) outerNonnegative)
  exact (norm_sub_le _ _).trans ((add_le_add liftEstimate second).trans_eq (by ring))
end TripleBound

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem physicalIncomingLift_real_norm :
    ‖(physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ‖ ≤ 2 * uniformInnerLiftConstant L := by
  apply ContinuousLinearMap.opNorm_le_bound
    ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  exact physicalIncomingLift_bound lower L positive lowerHalf lengthPositive

theorem highIncomingSolverOrbit_norm (tau : OrbitParameter) :
    ‖highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau‖ ≤
      322 * uniformInnerLiftConstant L := by
  have source : ‖highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau‖ ≤ 32 :=
    (isometricComposition_norm
      (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) (fun _ => rfl)
      (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)).trans
      (currentHighInverseOrbit_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
  have bound := norm_constantMinusTriple_bound
    ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ)
    (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau)
    (2 * uniformInnerLiftConstant L) 32 5 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by norm_num) (by norm_num)
    (physicalIncomingLift_real_norm L lower positive lowerHalf lengthPositive) source
    (liftedTestFunctionalOrbit_zero_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
  change ‖(physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ -
    (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
      ((liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau).comp
        ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ))‖ ≤ _
  exact bound.trans_eq (by ring)

/-- The actual inverse/form composition obeys a positive one-high bound
with constants chosen before radius, state, and translation. -/
theorem highCorrectionOrbit_axis_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (axis : Bool) (order : ℕ) (orderPositive : 0 < order) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (time : ℝ),
      ‖iteratedDeriv order (fun parameter : ℝ =>
        (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (parameter • axisVector axis)).comp
        (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
          (parameter • axisVector axis))) time‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + order) := by
  classical
  choose sourceConstant sourceNonnegative sourceBound using highSourceSolverOrbit_axis_bound parameters L compact axis
  choose formConstant formNonnegative formBound using liftedTestFunctionalOrbit_axis_bound parameters L compact axis
  let pair := fun index => pairBudgetConstant 8 index (currentHighPrimitiveRadius parameters L compact)
  have pairNonnegative (index : ℕ) : 0 ≤ pair index :=
    pairBudgetConstant_nonnegative 8 index (currentHighPrimitiveRadius_positive parameters L compact).le
  let constant := ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
    sourceConstant index * formConstant (order - index) * (1 + pair order)
  refine ⟨constant, Finset.sum_nonneg (fun index _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sourceNonnegative index)) (formNonnegative _))
      (by linarith only [pairNonnegative order])), ?_⟩
  intro lower positive lowerHalf lengthPositive widthHalf widthLength state small time
  let budget := fun index => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + index)
  exact iteratedDeriv_realComposition_oneHigh _ _
    ((highSourceSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (contDiff_id.smul contDiff_const))
    ((liftedTestFunctionalOrbitJet_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0).comp
      (contDiff_id.smul contDiff_const)) budget pair sourceConstant formConstant
    (fun _ => physicalBudget_nonnegative _ _ _ _ _) pairNonnegative sourceNonnegative formNonnegative
    (fun first second => physical_budget_pair 8 (first + second) first second le_rfl
      parameters state.val.val.field state.val.val.rho state.val.val.epsilon
      (currentHighPrimitiveRadius parameters L compact) (currentHighPrimitiveRadius_positive parameters L compact).le small)
    order orderPositive time
    (fun index _ => sourceBound index lower positive lowerHalf lengthPositive widthHalf widthLength state small time)
    (fun index _ => formBound index lower positive lowerHalf lengthPositive widthHalf widthLength state small time)

/-- The genuine incoming correction, including its fixed nonzero trace
lift, has one high factor at every positive axis order. -/
theorem highIncomingSolverOrbit_axis_bound (parameters : PhaseParameters) (L compact : ℝ)
    (axis : Bool) (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (time : ℝ),
      ‖iteratedDeriv order (fun parameter : ℝ =>
        highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (parameter • axisVector axis)) time‖ ≤
        constant * positiveJetBudget
          (fun index => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + index)) order := by
  by_cases zero : order = 0
  · subst order
    refine ⟨322 * uniformInnerLiftConstant L, mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
    intro lower positive lowerHalf lengthPositive widthHalf widthLength state small time
    simpa only [iteratedDeriv_zero, positiveJetBudget, ite_true, mul_one] using
      highIncomingSolverOrbit_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (time • axisVector axis)
  have orderPositive : 0 < order := Nat.pos_of_ne_zero zero
  obtain ⟨constant, nonnegative, estimate⟩ := highCorrectionOrbit_axis_oneHigh parameters L compact axis order orderPositive
  refine ⟨constant * (2 * uniformInnerLiftConstant L), mul_nonneg nonnegative (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)), ?_⟩
  intro lower positive lowerHalf lengthPositive widthHalf widthLength state small time
  let correction := fun parameter : ℝ =>
    (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (parameter • axisVector axis)).comp
      (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 (parameter • axisVector axis))
  have smooth : ContDiff ℝ ∞ correction :=
    realOperatorComposition_contDiff _ _
      ((highSourceSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
        (contDiff_id.smul contDiff_const))
      ((liftedTestFunctionalOrbitJet_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0).comp
        (contDiff_id.smul contDiff_const))
  have differentiated := iteratedDeriv_constantMinusComposition_bound
    ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ)
    ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ)
    correction smooth order orderPositive time
  have product := mul_le_mul (estimate lower positive lowerHalf lengthPositive widthHalf widthLength state small time)
    (physicalIncomingLift_real_norm L lower positive lowerHalf lengthPositive) (norm_nonneg _)
    (mul_nonneg nonnegative (physicalBudget_nonnegative _ _ _ _ _))
  have combined := differentiated.trans product
  have same : (fun parameter : ℝ =>
      highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (parameter • axisVector axis)) =
      fun parameter => (physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ -
        (correction parameter).comp ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ) := by
    funext parameter
    rfl
  have normSame := congrArg (fun function => ‖iteratedDeriv order function time‖) same
  apply normSame.le.trans
  exact combined.trans_eq (by simp only [positiveJetBudget, if_neg zero]; ring)

end Grad.AnnularHighGenerators
