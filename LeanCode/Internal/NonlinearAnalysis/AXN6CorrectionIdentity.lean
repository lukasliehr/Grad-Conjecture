import AXN5SourceProjectionBound
import AXJ8ExactSplitting

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.RealFixedRanges
open Grad.Q24Realization Grad.AxisSourceLift Grad.ChartAxisSplit
open Grad.ChartAxisProjections Grad.Constraints.Gauges
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds

/-- The real bundled extraction carries exactly the literal AL10 data used
by the quantitative lift estimate.  Isolating this proof keeps the subtype
instance normalization out of the public tame inequality. -/
theorem realSourceLift_extraction_eq_axisSourceLift
    {parameters : PhaseParameters} (cellLength radius : ℝ)
    (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (source : sourceSmoothRange parameters) :
    realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis
        (realExtraction parameters cellLength source) =
      axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS
        base axis (extractionData cellLength source.val) (extractionData_real cellLength source) := by
  rw [realSourceLift_eq_actual radius positive bounded cellLength reference insideR seed insideS
    base axis]
  congr 1

end Grad.ChartAxisSourceBound
