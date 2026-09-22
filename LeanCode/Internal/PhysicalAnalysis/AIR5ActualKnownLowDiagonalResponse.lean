import AIR4CompleteKnownLowDataMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow Grad.AnnularLowVolterra
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularSourceGraph

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters L compact)

/-- The actual BF8 low diagonal response to the full known source and incoming data. -/
def knownLowResponse : KnownLowData lower →L[ℂ] lowEnergyGraph lower L positive :=
  (lowCurrentInverse parameters L compact lower lengthPositive positive bounded state).comp
    (knownLowDataMap parameters L compact lower positive bounded.le state)

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters L compact)
include small

theorem knownLowResponse_equation (data : KnownLowData lower) :
    lowCurrentDataOperator parameters L compact lower lengthPositive positive bounded state
      (knownLowResponse parameters L compact lower lengthPositive positive bounded state data) =
        knownLowDataMap parameters L compact lower positive bounded.le state data :=
  lowCurrentDataOperator_inverse parameters L compact lower lengthPositive positive bounded state small _

/-- Incoming coordinate of the actual completed low graph is exactly the prescribed one. -/
theorem knownLowResponse_incoming (data : KnownLowData lower) :
    lowIncomingTrace lower L positive bounded
      (knownLowResponse parameters L compact lower lengthPositive positive bounded state data) = data.ofLp.2 :=
  lowCurrentInverse_incoming parameters L compact lower lengthPositive positive bounded state small _

/-- The slope belongs to the original closed derivative graph and obeys its genuine equation. -/
theorem knownLowResponse_normalizedEquation (data : KnownLowData lower) (index : LowAnnularIndex) :
    Grad.CircularHighRegularity.collarScalar 1 lower (lowMuInverseCurve lower L positive index.2.val.2)
      (lowEnergyDerivative lower L positive index
        (knownLowResponse parameters L compact lower lengthPositive positive bounded state data).val) =
    lowCurrentGeneratorValue parameters L compact lower lengthPositive positive bounded.le state
      (knownLowResponse parameters L compact lower lengthPositive positive bounded state data) index +
    lowDataResidual lower positive (knownLowDataMap parameters L compact lower positive bounded.le state data) index :=
  lowCurrentInverse_normalizedEquation parameters L compact lower lengthPositive positive bounded state small _ index

/-- This is uniqueness among arbitrary original low graph elements. -/
theorem knownLowResponse_unique (data : KnownLowData lower) (candidate : lowEnergyGraph lower L positive)
    (equation : lowCurrentDataOperator parameters L compact lower lengthPositive positive bounded state candidate =
      knownLowDataMap parameters L compact lower positive bounded.le state data) :
    candidate = knownLowResponse parameters L compact lower lengthPositive positive bounded state data := by
  have left := lowCurrentInverse_dataOperator parameters L compact lower lengthPositive positive bounded state small candidate
  rw [equation] at left
  exact left.symm

/-- Uniform operator norm of the actual low known response on one B8 ball. -/
theorem knownLowResponse_uniform
    (budget : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) :
    ‖knownLowResponse parameters L compact lower lengthPositive positive bounded state‖ ≤
      2 * Real.sqrt (lowReferenceGraphConstant parameters L) *
        (2 * knownLowSourceConstant parameters L compact + lowBalanceConstant L parameters.gamma + 5) := by
  have inverse := lowCurrentInverse_bound parameters L compact lower lengthPositive positive bounded state small
  have source := knownLowDataMap_uniform parameters L compact lower positive bounded.le state budget
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul inverse source (norm_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

end Grad.AnnularKnownLow
