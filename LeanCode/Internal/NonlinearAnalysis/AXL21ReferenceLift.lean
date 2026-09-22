import AXL20PhysicalLift
import AXP4PhysicalConsumers
import QW4CoreEquivalence

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.ConstrainedTransfer

variable {parameters : PhaseParameters}

theorem chartKappa_transfer (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters seed insideS) :
    chartKappa parameters reference insideR
      (constrainedCoreTransfer parameters seed insideS reference insideR field) =
      chartKappa parameters seed insideS field := by
  unfold chartKappa
  rw [constrainedCoreTransfer_coe, coreTransfer_apply]

theorem stateAxis_real (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR) :
    RealTangent (smoothingToTangent parameters base.2.val.1) :=
  (stateChart_real parameters reference insideR base.2).1

/-- The AL15 moving-seed lift transported back by the accepted exact N18
inverse. It remains in the actual fixed-reference constrained source. -/
def referenceCapLift (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    stateSmoothRange parameters reference insideR :=
  constrainedCoreTransfer parameters seed insideS reference insideR
    (actualCapLift parameters radius positive bounded seed insideS
      (smoothingToTangent parameters base.2.val.1) sigma tangent
      (stateAxis_real reference insideR base) axis realS realT)

theorem chartKappa_referenceCapLift (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    chartKappa parameters reference insideR
      (referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT) =
      (sigma.val, tangent.val) := by
  unfold referenceCapLift
  rw [chartKappa_transfer]
  exact chartKappa_actualCapLift radius positive bounded seed insideS _ sigma tangent
    (stateAxis_real reference insideR base) axis realS realT

theorem referenceCapLift_transfer (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    constrainedCoreTransfer parameters reference insideR seed insideS
      (referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT) =
      actualCapLift parameters radius positive bounded seed insideS
        (smoothingToTangent parameters base.2.val.1) sigma tangent
        (stateAxis_real reference insideR base) axis realS realT :=
  constrainedCoreTransfer_reverse parameters seed insideS reference insideR _

/-- The actual physical source cap T_b=L_b E_b has extraction equal to the
prescribed pair, in every original completed extraction grade. -/
theorem completedExtraction_forward_referenceCapLift (cellLength : ℝ) (positiveLength : 0 < cellLength)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
          (referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT)))) =
      (sigma.val, tangent.val) := by
  rw [completedExtraction_literalPhysicalForward parameters cellLength positiveLength,
    chartKappa_referenceCapLift]

end Grad.ChartAxisLift
