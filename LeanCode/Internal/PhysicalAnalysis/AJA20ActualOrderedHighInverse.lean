import AJA17ActualFullJetOneHigh
import AJA19OrderedInverseBounds
import AJA12ActualHighInverseDerivative
import GC15BudgetAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularInverseCalculus
open Grad.GaugeCoefficients.Physical.Allocation
section GenericColumns
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [CompleteSpace E]

private theorem inverseColumns (forward : OrbitParameter → E →L[𝕜] F)
    (inverse : OrbitParameter → F →L[𝕜] E) (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F)
    (right : ∀ point, (forward point).comp (inverse point) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ point, (inverse point).comp (forward point) = ContinuousLinearMap.id 𝕜 E)
    (zero : jet 0 0 = forward) (point : OrbitParameter)
    (derivative : HasFDerivAt (jet 0 0) (orbitColumns (jet 1 0 point) (jet 0 1 point)) point) :
    HasFDerivAt inverse (orbitColumns (-((inverse point).comp ((jet 1 0 point).comp (inverse point))))
      (-((inverse point).comp ((jet 0 1 point).comp (inverse point))))) point := by
  rw [zero] at derivative
  have actual := sameInverse_hasFDerivAt forward inverse right left point _ derivative
  apply actual.congr_fderiv
  exact orbitColumns_comp (E := E →L[𝕜] F) (F := F →L[𝕜] E)
    (inverseSandwich (inverse point)) (jet 1 0 point) (jet 0 1 point)
end GenericColumns

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem currentHighInverseOrbit_columns (tau : OrbitParameter) :
    let inverse := currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    let jet := currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    HasFDerivAt inverse (orbitColumns (-((inverse tau).comp ((jet 1 0 tau).comp (inverse tau))))
      (-((inverse tau).comp ((jet 0 1 tau).comp (inverse tau))))) tau := by
  exact inverseColumns
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighInverseOrbit_right parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_left parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (funext (currentHighZeroFormOrbitJet_zero parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)) tau
    (currentHighZeroFormOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau)

theorem currentHighInverseOrbit_orderedFormula (word : List Bool) (tau : OrbitParameter) :
    orderedOrbitDerivative word
      (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) tau =
      (inverseDerivativeWord word).eval
        (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
        (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) tau :=
  orderedOrbitDerivative_inverse _ _
    (currentHighInverseOrbit_columns parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroFormOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) word tau

/-- Constants are fixed before the inner radius, state, or translation. -/
def actualHighJetConstant (parameters : PhaseParameters) (L compact : ℝ) (angular cell : ℕ) : ℝ :=
  if positive : 0 < angular + cell then (currentHighFormOrbitJet_oneHigh parameters L compact angular cell positive).choose else 0

theorem actualHighJetConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (angular cell : ℕ) :
    0 ≤ actualHighJetConstant parameters L compact angular cell := by
  unfold actualHighJetConstant
  split_ifs with positive
  · exact (currentHighFormOrbitJet_oneHigh parameters L compact angular cell positive).choose_spec.1
  · exact le_rfl

theorem actualHighJetConstant_bound (angular cell : ℕ) (orderPositive : 0 < angular + cell) (tau : OrbitParameter) :
    ‖currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
      actualHighJetConstant parameters L compact angular cell *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) := by
  have bound := (currentHighFormOrbitJet_oneHigh parameters L compact angular cell orderPositive).choose_spec.2
    lower positive lowerHalf lengthPositive widthHalf widthLength state tau
  have restricted := (currentHighZeroFormOrbitJet_norm_le parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau).trans bound
  simpa only [actualHighJetConstant, dif_pos orderPositive, AnnularReconstructionState.errorBudget,
    show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using restricted

/-- Every genuine ordered angular/cell derivative of the SAME high inverse
has one high primitive factor on the original B8 ball and original widths. -/
theorem currentHighInverseOrbit_ordered_oneHigh (parameters : PhaseParameters) (L compact : ℝ) (word : List Bool) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (tau : OrbitParameter),
      ‖orderedOrbitDerivative word
        (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) tau‖ ≤
        constant * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + word.length)) := by
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
  have estimate := (inverseDerivativeWord word).norm_eval_le
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    tau budget budgetNonnegative monotone 32 jetBound pairBound (by norm_num) jetNonnegative pairNonnegative
    (currentHighInverseOrbit_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (fun angular cell orderPositive => actualHighJetConstant_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell orderPositive tau)
    pairEstimate
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (monotone (inverseDerivativeWord_degree word)) 1) constantNonnegative)

end Grad.AnnularHighInverseOrbit
