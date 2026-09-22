import AIR7ExactKnownLowPhysicalForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow Grad.AnnularLowVolterra
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCrossMaps

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters L compact)

include small

/-- BF8 diagonal response on the SAME original derivative graph and source,
with exact incoming data and a uniform complete-Hilbert norm bound. -/
theorem knownLowResponse_exact (data : KnownLowData lower)
    (budget : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) :
    let solution := knownLowResponse parameters L compact lower lengthPositive positive bounded state data
    solution.val 1 - lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (solution.val 0) =
      knownLowForcing parameters L compact lower positive bounded.le state data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2 ∧
    lowIncomingTrace lower L positive bounded solution = data.ofLp.2 ∧
    ‖solution‖ ≤ 2 * Real.sqrt (lowReferenceGraphConstant parameters L) *
      (2 * knownLowSourceConstant parameters L compact + lowBalanceConstant L parameters.gamma + 5) * ‖data‖ := by
  dsimp only
  have forward := congrArg (fun result : LowEnergyData lower => result.ofLp.1)
    (knownLowResponse_equation parameters L compact lower lengthPositive positive bounded state small data)
  refine ⟨forward, knownLowResponse_incoming parameters L compact lower lengthPositive positive bounded state small data, ?_⟩
  exact ((knownLowResponse parameters L compact lower lengthPositive positive bounded state).le_opNorm data).trans
    (mul_le_mul_of_nonneg_right (knownLowResponse_uniform parameters L compact lower lengthPositive positive bounded state small budget) (norm_nonneg data))

end Grad.AnnularKnownLow
