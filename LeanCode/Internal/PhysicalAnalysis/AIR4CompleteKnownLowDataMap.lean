import AIR3ActualKnownLowForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

abbrev KnownLowBulkData (lower : ℝ) := WithLp 2 (HighKnownSourceBulk lower × DivisionRow 1 lower)
abbrev KnownLowData (lower : ℝ) := WithLp 2 (KnownLowBulkData lower × LowEnergyBoundary)

theorem knownLowData_component_bounds (lower : ℝ) (data : KnownLowData lower) :
    ‖data.ofLp.1.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.1.ofLp.2‖ ≤ ‖data‖ ∧ ‖data.ofLp.2‖ ≤ ‖data‖ := by
  have first := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.1
  have second := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data.ofLp.1‖ ^ 2 = ‖data.ofLp.1.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.2‖ ^ 2 at first
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at second
  have p := sq_nonneg ‖data.ofLp.1.ofLp.1‖
  have q := sq_nonneg ‖data.ofLp.1.ofLp.2‖
  have r := sq_nonneg ‖data.ofLp.2‖
  constructor
  · nlinarith [norm_nonneg data, norm_nonneg data.ofLp.1.ofLp.1]
  constructor
  · nlinarith [norm_nonneg data, norm_nonneg data.ofLp.1.ofLp.2]
  · nlinarith [norm_nonneg data, norm_nonneg data.ofLp.2]

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

/-- BF8's known low diagonal data map, retaining its exact original incoming coordinate. -/
def knownLowDataMap : KnownLowData lower →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.comp
    ((((knownLowForcingMap parameters L compact lower positive bounded state).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (HighKnownSourceBulk lower) (DivisionRow 1 lower)).toContinuousLinearMap).prodMap
      (ContinuousLinearMap.id ℂ LowEnergyBoundary)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ (KnownLowBulkData lower) LowEnergyBoundary).toContinuousLinearMap)

theorem knownLowDataMap_bulk (data : KnownLowData lower) :
    (knownLowDataMap parameters L compact lower positive bounded state data).ofLp.1 =
      knownLowForcing parameters L compact lower positive bounded state data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2 := rfl

theorem knownLowDataMap_incoming (data : KnownLowData lower) :
    (knownLowDataMap parameters L compact lower positive bounded state data).ofLp.2 = data.ofLp.2 := rfl

/-- Explicit bound in the complete Hilbert norm of the original known inputs. -/
theorem knownLowDataMap_bound (data : KnownLowData lower) :
    ‖knownLowDataMap parameters L compact lower positive bounded state data‖ ≤
      (knownLowSourceConstant parameters L compact * state.val.val.size 0 + lowBalanceConstant L parameters.gamma + 5) * ‖data‖ := by
  let result := knownLowDataMap parameters L compact lower positive bounded state data
  have square := WithLp.prod_norm_sq_eq_of_L2 result
  change ‖result‖ ^ 2 = ‖result.ofLp.1‖ ^ 2 + ‖result.ofLp.2‖ ^ 2 at square
  have triangle : ‖result‖ ≤ ‖result.ofLp.1‖ + ‖result.ofLp.2‖ := by
    nlinarith [norm_nonneg result, norm_nonneg result.ofLp.1, norm_nonneg result.ofLp.2,
      mul_nonneg (norm_nonneg result.ofLp.1) (norm_nonneg result.ofLp.2)]
  have pieces := knownLowData_component_bounds lower data
  have balance : 0 ≤ lowBalanceConstant L parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
    linarith
  have coefficient : 0 ≤ knownLowSourceConstant parameters L compact * state.val.val.size 0 + lowBalanceConstant L parameters.gamma + 2 := by
    have nonnegative := mul_nonneg (knownLowSourceConstant_nonnegative parameters L compact) (state.val.val.size_nonnegative 0)
    linarith
  have source := knownLowForcing_bound parameters L compact lower positive bounded state data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2
  have bound := add_le_add (mul_le_mul_of_nonneg_left pieces.1 coefficient)
    (mul_le_mul_of_nonneg_left pieces.2.1 (by norm_num : (0 : ℝ) ≤ 2))
  have forcing := source.trans bound
  change ‖result‖ ≤ _
  apply triangle.trans
  change ‖knownLowForcing parameters L compact lower positive bounded state data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2‖ + ‖data.ofLp.2‖ ≤ _
  linarith [pieces.2.2]

/-- One B8 ball gives a collar- and state-independent bound for the actual known data operator. -/
theorem knownLowDataMap_uniform
    (budget : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) :
    ‖knownLowDataMap parameters L compact lower positive bounded state‖ ≤
      2 * knownLowSourceConstant parameters L compact + lowBalanceConstant L parameters.gamma + 5 := by
  have size : state.val.val.size 0 ≤ 2 := by
    have monotone := physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 7 ≤ 8)
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7 ≤ 2
    linarith
  have coefficient := knownLowSourceConstant_nonnegative parameters L compact
  have balance : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro data
  apply (knownLowDataMap_bound parameters L compact lower positive bounded state data).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg data)
  nlinarith

end Grad.AnnularKnownLow
