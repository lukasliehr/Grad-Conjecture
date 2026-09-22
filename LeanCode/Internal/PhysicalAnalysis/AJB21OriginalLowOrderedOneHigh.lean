import AJB20ActualLowOrderedInverse
import AJA21PositiveOrderedBounds
import GC15BudgetAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularReconstruction Grad.AnnularInverseCalculus Grad.AnnularHighInverseOrbit Grad.AnnularLowVolterra
open Grad.GaugeCoefficients.Physical.Allocation

private theorem negativeOperator_norm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (operator : E →L[ℂ] F) : ‖-operator‖ = ‖operator‖ := norm_neg operator

/-- Constants precede the inner radius, state, and translation. -/
def actualLowJetConstant (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (angular cell : ℕ) : ℝ :=
  if positive : 0 < angular + cell then
    (actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive angular cell positive).choose else 0

theorem actualLowJetConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) (angular cell : ℕ) :
    0 ≤ actualLowJetConstant parameters length compact lengthPositive angular cell := by
  unfold actualLowJetConstant
  split_ifs with positive
  · exact (actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive angular cell positive).choose_spec.1
  · exact le_rfl

theorem actualLowJetConstant_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (angular cell : ℕ)
    (orderPositive : 0 < angular + cell) (tau : OrbitParameter) :
    ‖actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state angular cell tau‖ ≤
      actualLowJetConstant parameters length compact lengthPositive angular cell *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) := by
  have bound := (actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive angular cell orderPositive).choose_spec.2
    state lower positive bounded.le tau
  change ‖-lowDataGeneratorAssembly lower length positive _‖ ≤ _
  rw [negativeOperator_norm (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)]
  apply ((lowDataGeneratorAssembly_bound lower length positive _).trans bound).trans
  have budgetBound : state.val.errorBudget (angular + cell) ≤
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) :=
    physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)
  simpa only [actualLowJetConstant, dif_pos orderPositive] using mul_le_mul_of_nonneg_left budgetBound
    (actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive angular cell orderPositive).choose_spec.1

/-- Genuine positive ordered derivatives of SAME AEI24 contain one high
physical primitive factor on the original B8 ball and original analytic width. -/
theorem actualLowInverseOrbit_ordered_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) (word : List Bool) (nonempty : word ≠ []) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RetainedInverseState parameters length compact)
        (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          lowCurrentNeighborhood parameters length compact)
        (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (tau : OrbitParameter),
      ‖orderedOrbitDerivative word
        (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) tau‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + word.length) := by
  let inverseBound := 2 * Real.sqrt (lowReferenceGraphConstant parameters length)
  let jetBound := actualLowJetConstant parameters length compact lengthPositive
  let pairBound := fun order => pairBudgetConstant 8 order (lowCurrentNeighborhood parameters length compact)
  have inverseNonnegative : 0 ≤ inverseBound := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have radiusNonnegative := (lowCurrentNeighborhood_pos parameters length compact lengthPositive).le
  have jetNonnegative := actualLowJetConstant_nonnegative parameters length compact lengthPositive
  have pairNonnegative (order : ℕ) : 0 ≤ pairBound order := pairBudgetConstant_nonnegative 8 order radiusNonnegative
  let constant := (inverseDerivativeWord word).bound inverseBound jetBound pairBound
  have constantNonnegative := (inverseDerivativeWord word).bound_nonnegative inverseBound jetBound pairBound
    inverseNonnegative jetNonnegative pairNonnegative
  refine ⟨constant, constantNonnegative, ?_⟩
  intro state small lower positive bounded tau
  rw [actualLowInverseOrbit_orderedFormula parameters length compact lower lengthPositive positive bounded state small word tau]
  let budget := fun order => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + order)
  have budgetNonnegative (order : ℕ) : 0 ≤ budget order := physicalBudget_nonnegative _ _ _ _ _
  have monotone : Monotone budget := fun _ _ ordered => physicalBudget_monotone _ _ _ _ (Nat.add_le_add_left ordered 8)
  have pairEstimate (first second : ℕ) : budget first * budget second ≤ pairBound (first + second) * budget (first + second) :=
    physical_budget_pair 8 (first + second) first second le_rfl parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (lowCurrentNeighborhood parameters length compact) radiusNonnegative small
  have estimate := InverseExpression.norm_eval_le_positive
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
    (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state)
    tau budget budgetNonnegative monotone inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative
    (actualLowInverseOrbit_bound parameters length compact lower lengthPositive positive bounded state small tau)
    (fun angular cell orderPositive => actualLowJetConstant_bound parameters length compact lower lengthPositive positive bounded state angular cell orderPositive tau)
    pairEstimate (inverseDerivativeWord word) (inverseDerivativeWord_positive nonempty)
  exact estimate.trans (mul_le_mul_of_nonneg_left (monotone (inverseDerivativeWord_degree word)) constantNonnegative)

end Grad.AnnularLowOrbit
