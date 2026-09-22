import AXC10ExtractionReality

noncomputable section

namespace Grad.ChartAxisSplit

open Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

/-- The literal AL10 extraction and AL13 bound at all original source
grades q+3, with data in T^(q+1) x T^(q+1), equipped with the sum norm. -/
def AxisExtractionCompletionGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ),
    (∀ source : sourceSmoothRange parameters,
      completedExtraction parameters cellLength grade
        (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source) =
          axisDataEmbedding parameters grade (extractionData cellLength source.val)) ∧
    (∀ source : sourceRange parameters (grade + 3) (extractionLarge grade),
      ‖completedExtraction parameters cellLength grade source‖ ≤
        (4 * extractionBoundConstant cellLength) * ‖source‖) ∧
    (∀ source : sourceRange parameters (grade + 3) (extractionLarge grade),
      axisDataConjugation parameters grade (completedExtraction parameters cellLength grade source) =
        completedExtraction parameters cellLength grade source)

/-- AL11 for the actual fixed-reference chart derivative, not a changed
quotient or a chart with the transverse root direction suppressed. -/
def AxisExtractionChartGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ) (_positive : 0 < cellLength)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction))) =
      chartKappa parameters reference insideR direction

def ActualAxisExtractionGoal : Prop := AxisExtractionCompletionGoal ∧ AxisExtractionChartGoal

theorem actualAxisExtraction : ActualAxisExtractionGoal :=
  ⟨fun parameters cellLength grade => ⟨completedExtraction_core parameters cellLength grade,
      completedExtraction_bound parameters cellLength grade,
      completedExtraction_real parameters cellLength grade⟩,
    completedExtraction_literalForward⟩

end Grad.ChartAxisSplit
