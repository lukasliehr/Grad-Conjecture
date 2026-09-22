import AIQ15UniformPhysicalHighInverseConsumer
import AIR8ExactKnownLowResponseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Actual full original source response, with both components taken from
one and the same physical weak solution. -/
def fullKnownHighResponse (data : ActualHighGraphKnownData parameters lower 0 0) :
    CrossHighSpace lower L positive lengthPositive :=
  WithLp.toLp 2 (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data,
    graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)

theorem fullKnownHighResponse_energy (data : ActualHighGraphKnownData parameters lower 0 0) :
    (fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1 =
      graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := rfl

theorem fullKnownHighResponse_flux (data : ActualHighGraphKnownData parameters lower 0 0) :
    (fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.2 =
      graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := rfl

/-- The explicit component estimate precedes the literal Hilbert-data bound. -/
theorem fullKnownHighResponse_bound (data : ActualHighGraphKnownData parameters lower 0 0) :
    ‖fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      (1 + 4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|)) *
        (32 * data.functionalSize parameters L compact lower state 0 0 + 322 * uniformInnerLiftConstant L * ‖data.innerValue‖) +
      16 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖data.weighted‖ + 12 * ‖data.auxiliary‖ := by
  let response := fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have square := WithLp.prod_norm_sq_eq_of_L2 response
  change ‖response‖ ^ 2 = ‖response.ofLp.1‖ ^ 2 + ‖response.ofLp.2‖ ^ 2 at square
  have triangle : ‖response‖ ≤ ‖response.ofLp.1‖ + ‖response.ofLp.2‖ := by
    nlinarith [norm_nonneg response, norm_nonneg response.ofLp.1, norm_nonneg response.ofLp.2,
      mul_nonneg (norm_nonneg response.ofLp.1) (norm_nonneg response.ofLp.2)]
  have energy := graphDataEnergySolution_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have flux := graphDataPhysicalFlux_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  change ‖response‖ ≤ _
  apply triangle.trans
  exact (add_le_add energy flux).trans_eq (by ring)

end Grad.AnnularFullSource
