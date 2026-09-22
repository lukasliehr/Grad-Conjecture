import AEI23OriginalUniformLowNeighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.Foundations Grad.AnnularLowVolterra

def lowCurrentInverse (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) :
    LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive :=
  perturbationInverse (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)

theorem lowCurrentInverse_left (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact) :
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state).comp
      (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state) =
        ContinuousLinearMap.id ℂ (lowEnergyGraph lower length positive) :=
  perturbationInverse_left (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)
    ((lowNormalizedCurrentError_half parameters length compact lower lengthPositive positive bounded state small).trans_lt (by norm_num))

theorem lowCurrentInverse_right (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact) :
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state).comp
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state) =
        ContinuousLinearMap.id ℂ (LowEnergyData lower) :=
  perturbationInverse_right (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)
    ((lowNormalizedCurrentError_half parameters length compact lower lengthPositive positive bounded state small).trans_lt (by norm_num))

theorem lowCurrentInverse_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact) :
    ‖lowCurrentInverse parameters length compact lower lengthPositive positive bounded state‖ ≤
      2 * Real.sqrt (lowReferenceGraphConstant parameters length) := by
  have bound := perturbationInverse_norm_half (lowReferenceContinuousEquiv parameters length lower lengthPositive positive bounded)
    (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state)
    (lowNormalizedCurrentError_half parameters length compact lower lengthPositive positive bounded state small)
  change ‖lowCurrentInverse parameters length compact lower lengthPositive positive bounded state‖ ≤
    2 * ‖lowReferenceInverse parameters length lower lengthPositive positive bounded‖ at bound
  exact bound.trans (mul_le_mul_of_nonneg_left
    (originalLowReferenceInverse_uniform parameters length lengthPositive lower positive bounded) (by norm_num))

theorem lowCurrentDataOperator_inverse (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) :
    lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) = data :=
  congrArg (fun mapping => mapping data) (lowCurrentInverse_right parameters length compact lower lengthPositive positive bounded state small)

theorem lowCurrentInverse_dataOperator (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : lowEnergyGraph lower length positive) :
    lowCurrentInverse parameters length compact lower lengthPositive positive bounded state
      (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state field) = field :=
  congrArg (fun mapping => mapping field) (lowCurrentInverse_left parameters length compact lower lengthPositive positive bounded state small)

theorem lowCurrentInverse_incoming (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) :
    lowIncomingTrace lower length positive bounded
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) = data.ofLp.2 :=
  congrArg (fun result : LowEnergyData lower => result.ofLp.2)
    (lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small data)

theorem lowCurrentInverse_endpoint (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    lowEnergyEndpoint lower length positive bounded 0
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) index =
        lowDataIncoming lower length data index := by
  apply smul_right_injective (ComplexEuclidean 1) (lowIncomingFactor_pos lower length positive index.2).ne'
  change (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) • _ = _
  rw [← lowIncomingTrace_apply, lowCurrentInverse_incoming parameters length compact lower lengthPositive positive bounded state small]
  exact (lowDataIncoming_normalization lower length positive data index).symm

end Grad.AnnularCurrentLow
