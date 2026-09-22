import AJB11SameLowInverseDerivative
import AJB9ActualLowMixedJetDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularLowVolterra Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularInverseCalculus

private theorem operator_norm_nonnegative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (operator : E →L[ℂ] F) : 0 ≤ ‖operator‖ := norm_nonneg operator

private theorem operator_neg_norm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (operator : E →L[ℂ] F) : ‖-operator‖ = ‖operator‖ := norm_neg operator

private theorem operator_norm_sq_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (operator : E →L[ℂ] F) (constant : ℝ) (bound : ‖operator‖ ≤ constant) :
    ‖operator‖ ^ 2 ≤ constant ^ 2 := pow_le_pow_left₀ (norm_nonneg operator) bound 2

private theorem orbitDifferential_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (angular cell : E) :
    ‖orbitDifferential angular cell‖ ≤ ‖angular‖ + ‖cell‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro direction
  rw [orbitDifferential_apply]
  calc
    _ ≤ ‖(direction.1 : ℂ) • angular‖ + ‖(direction.2 : ℂ) • cell‖ := norm_add_le _ _
    _ = ‖direction.1‖ * ‖angular‖ + ‖direction.2‖ * ‖cell‖ := by simp only [norm_smul, Complex.norm_real]
    _ ≤ ‖direction‖ * ‖angular‖ + ‖direction‖ * ‖cell‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le direction) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_snd_le direction) (norm_nonneg _))
    _ = _ := by ring

/-- The physical first derivative uses only the primitive B8 moment. -/
theorem actualLowGeneratorDifferential_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter),
      ‖actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded state tau‖ ≤
        constant * state.val.errorBudget 1 := by
  obtain ⟨first, firstNonnegative, firstBound⟩ := actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive 1 0 (by norm_num)
  obtain ⟨second, secondNonnegative, secondBound⟩ := actualLowResponseOrbitJet_oneHigh parameters length compact lengthPositive 0 1 (by norm_num)
  refine ⟨first + second, add_nonneg firstNonnegative secondNonnegative, ?_⟩
  intro state lower positive bounded tau
  rw [actualLowGeneratorDifferential_columns]
  apply (orbitDifferential_norm_le _ _).trans
  exact (add_le_add (firstBound state lower positive bounded tau) (secondBound state lower positive bounded tau)).trans_eq (by ring)

theorem lowDataGeneratorAssembly_bound (lower length : ℝ) (positive : 0 < lower)
    (generator : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) :
    ‖lowDataGeneratorAssembly lower length positive generator‖ ≤ ‖generator‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro field
  change ‖lowBulkDataInjection lower (generator (field.val 0))‖ ≤ ‖generator‖ * ‖field‖
  rw [lowBulkDataInjection_norm]
  exact (generator.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lowStoredCoordinate_bound lower length positive 0 field) (norm_nonneg generator))

theorem actualLowDataOperatorDifferential_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tau direction : OrbitParameter) :
    ‖actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau direction‖ ≤
      ‖actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau‖ * ‖direction‖ := by
  change ‖-lowDataGeneratorAssembly lower length positive
    (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau direction)‖ ≤ _
  rw [operator_neg_norm (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)]
  exact (lowDataGeneratorAssembly_bound lower length positive _).trans (ContinuousLinearMap.le_opNorm _ direction)

private theorem inverseSandwich_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (inverse : F →L[ℂ] E) (direction : E →L[ℂ] F) :
    ‖inverseSandwich inverse direction‖ ≤ ‖inverse‖ ^ 2 * ‖direction‖ := by
  rw [inverseSandwich_apply, norm_neg]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg inverse)).trans_eq (by ring))

/-- Uniform first inverse jet on the SAME AEI original primitive B8 ball.
No higher-grade smallness is used in the inverse or its derivative. -/
theorem actualLowInverseDifferential_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
        lowCurrentNeighborhood parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (tau direction : OrbitParameter),
      ‖actualLowInverseDifferential parameters length compact lower lengthPositive positive bounded state tau direction‖ ≤
        constant * state.val.errorBudget 1 * ‖direction‖ := by
  obtain ⟨constant, nonnegative, bound⟩ := actualLowGeneratorDifferential_oneHigh parameters length compact lengthPositive
  let inverseBound := 2 * Real.sqrt (lowReferenceGraphConstant parameters length)
  refine ⟨inverseBound ^ 2 * constant, mul_nonneg (sq_nonneg _) nonnegative, ?_⟩
  intro state small lower positive bounded tau direction
  have budgetNonnegative : 0 ≤ state.val.errorBudget 1 :=
    physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _
  have forwardApplied := (actualLowDataOperatorDifferential_bound parameters length compact lower lengthPositive positive bounded state tau direction).trans
    (mul_le_mul_of_nonneg_right (bound state lower positive bounded.le tau) (norm_nonneg direction))
  have inverseNorm := actualLowInverseOrbit_bound parameters length compact lower lengthPositive positive bounded state small tau
  change ‖actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau‖ ≤ inverseBound at inverseNorm
  have inverseSquare := operator_norm_sq_le (E := LowEnergyData lower) (F := lowEnergyGraph lower length positive)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau) inverseBound inverseNorm
  change ‖inverseSandwich (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau)
    (actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau direction)‖ ≤ _
  apply (inverseSandwich_norm_le _ _).trans
  exact (mul_le_mul inverseSquare forwardApplied
    (operator_norm_nonnegative (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)
      (actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau direction))
    (sq_nonneg inverseBound)).trans_eq (by ring)

end Grad.AnnularLowOrbit
