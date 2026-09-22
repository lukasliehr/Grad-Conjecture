import AXJ8ExactSplitting

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.ChartAxisProjections

open Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.ChartAxisSplit Grad.Q24Realization
open Grad.RealFixedRanges Grad.PhysicalCoordinates

/-- AL22-23 on the unchanged real smooth constrained domain and source.
The norm-losing maps are not asserted to be same-grade endomorphisms. -/
def PhysicalFlatProjectionGoal : Prop :=
  ∀ (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (cellLength : ℝ), 0 < cellLength →
    ∀ (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
      (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
      (base : RealJointCore parameters reference insideR)
      (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)),
    (LinearMap.range (realDomainProjection radius positive bounded reference insideR seed insideS base axis) =
      LinearMap.ker (realChartKappa parameters reference insideR)) ∧
    (LinearMap.range (realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis) =
      LinearMap.ker (realExtraction parameters cellLength)) ∧
    (∀ direction, realDomainProjection radius positive bounded reference insideR seed insideS base axis
        (realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) =
      realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) ∧
    (∀ source, realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis
        (realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source) =
      realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source) ∧
    (∀ direction, literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
        (realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) =
      realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction))

theorem actualPhysicalFlatProjections : PhysicalFlatProjectionGoal := by
  unfold PhysicalFlatProjectionGoal
  intro parameters radius positive bounded cellLength positiveLength reference insideR seed insideS base axis
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · with_reducible exact realDomainProjection_range radius positive bounded reference insideR seed insideS base axis
  · with_reducible exact realRangeProjection_range radius positive bounded cellLength positiveLength reference insideR seed insideS base axis
  · with_reducible exact realDomainProjection_idempotent radius positive bounded reference insideR seed insideS base axis
  · with_reducible exact realRangeProjection_idempotent radius positive bounded cellLength positiveLength reference insideR seed insideS base axis
  · with_reducible exact realForward_domainProjection radius positive bounded cellLength positiveLength reference insideR seed insideS base axis

end Grad.ChartAxisProjections
