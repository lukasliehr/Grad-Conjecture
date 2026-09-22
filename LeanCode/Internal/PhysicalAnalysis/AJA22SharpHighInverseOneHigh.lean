import AJA20ActualOrderedHighInverse
import AJA21PositiveOrderedBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularInverseCalculus
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

/-- Every genuine ordered angular/cell derivative of the SAME high inverse
has one high primitive factor on the original B8 ball and original widths. -/
theorem currentHighInverseOrbit_positive_ordered_oneHigh (parameters : PhaseParameters) (L compact : ℝ) (word : List Bool) (nonempty : word ≠ []) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (tau : OrbitParameter),
      ‖orderedOrbitDerivative word
        (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) tau‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + word.length) := by
  let jetBound := actualHighJetConstant parameters L compact
  let pairBound := fun order => pairBudgetConstant 8 order (currentHighPrimitiveRadius parameters L compact)
  have radiusNonnegative := (currentHighPrimitiveRadius_positive parameters L compact).le
  have jetNonnegative := actualHighJetConstant_nonnegative parameters L compact
  have pairNonnegative (order : ℕ) : 0 ≤ pairBound order := pairBudgetConstant_nonnegative 8 order radiusNonnegative
  let constant := (inverseDerivativeWord word).bound 32 jetBound pairBound
  have constantNonnegative := (inverseDerivativeWord word).bound_nonnegative 32 jetBound pairBound (by norm_num) jetNonnegative pairNonnegative
  refine ⟨constant, constantNonnegative, ?_⟩
  intro lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
  rw [currentHighInverseOrbit_orderedFormula parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small word tau]
  let budget := fun order => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + order)
  have budgetNonnegative (order : ℕ) : 0 ≤ budget order := physicalBudget_nonnegative _ _ _ _ _
  have monotone : Monotone budget := fun _ _ ordered => physicalBudget_monotone _ _ _ _ (Nat.add_le_add_left ordered 8)
  have pairEstimate (first second : ℕ) : budget first * budget second ≤ pairBound (first + second) * budget (first + second) :=
    physical_budget_pair 8 (first + second) first second le_rfl parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (currentHighPrimitiveRadius parameters L compact) radiusNonnegative small
  have estimate := (inverseDerivativeWord word).norm_eval_le_positive
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    tau budget budgetNonnegative monotone 32 jetBound pairBound (by norm_num) jetNonnegative pairNonnegative
    (currentHighInverseOrbit_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (fun angular cell orderPositive => actualHighJetConstant_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell orderPositive tau)
    pairEstimate (inverseDerivativeWord_positive nonempty)
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (monotone (inverseDerivativeWord_degree word)) constantNonnegative)

end Grad.AnnularHighInverseOrbit
