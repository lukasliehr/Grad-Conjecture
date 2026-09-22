import AXP3PhysicalRawDerivative
import QYP21PhysicalForwardConsumer
import AXC8ExtractionGoal

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RawForward
open Grad.NonlinearRange Grad.QuotientProjection Grad.Q24Realization Grad.RealFixedRanges
open Grad.SmoothForward Grad.AxisSplit Grad.ChartAxisSplit Grad.ConstrainedGrades

theorem literalPhysicalSmoothForward_rawDerivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    HasDerivAt
      (fun scalar : ℝ => quotientEta parameters grade
        (rawPhysicalFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction)))
      (quotientEta parameters grade (rawReconstructionCore parameters
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction).val)) 0 := by
  have exactDerivative := physicalFixedSliceDerivative_rawDerivative parameters cellLength reference insideR seed insideS
    grade base axis direction
  rw [physicalFixedSliceDerivative_one] at exactDerivative
  exact exactDerivative

theorem completedExtraction_literalPhysicalForward (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters)
    (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction))) =
      chartKappa parameters reference insideR direction := by
  rw [completedExtraction_coefficients]
  exact axisExtraction_physicalFirstRows cellLength positive reference insideR seed insideS base direction

/-- The corrected actual completed forward consumer, including q=0 by the
canonical q+4 to q+3 inclusion. No replacement of the source is used. -/
theorem completedExtraction_actualPhysicalForward (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters)
    (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceLowering parameters (extractionLarge grade) (show grade + 3 ≤ grade + 4 by omega)
        (actualPhysicalSmoothForward parameters cellLength reference insideR seed (grade + 4) (by omega) base
          (stateSmoothEmbedding parameters reference insideR ((grade + 4) + 6)
            (realHighLarge (grade + 4)) direction)))) = chartKappa parameters reference insideR direction := by
  rw [actualPhysicalSmoothForward_core_value parameters cellLength reference insideR seed insideS (grade + 4)
    (by omega) base axis, sourceLowering_core]
  exact completedExtraction_literalPhysicalForward parameters cellLength positive reference insideR seed insideS grade base axis direction

def PhysicalAxisExtractionChartGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ) (_positive : 0 < cellLength)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction))) =
      chartKappa parameters reference insideR direction

theorem actualPhysicalAxisExtraction : AxisExtractionCompletionGoal ∧ PhysicalAxisExtractionChartGoal :=
  ⟨fun parameters cellLength grade => ⟨completedExtraction_core parameters cellLength grade,
      completedExtraction_bound parameters cellLength grade,
      completedExtraction_real parameters cellLength grade⟩,
    completedExtraction_literalPhysicalForward⟩

def PhysicalRawDerivativeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    HasDerivAt
      (fun scalar : ℝ => quotientEta parameters grade
        (rawPhysicalFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction)))
      (quotientEta parameters grade (rawReconstructionCore parameters
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction).val)) 0

theorem physicalRawForwardConsumer : PhysicalForwardCoreGoal ∧ PhysicalRawDerivativeGoal :=
  ⟨literalPhysicalSmoothForward_completedCLM.1, literalPhysicalSmoothForward_rawDerivative⟩

end Grad.PhysicalCoordinates
