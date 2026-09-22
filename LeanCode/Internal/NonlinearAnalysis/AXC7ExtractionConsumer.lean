import AXC6CompletedExtraction

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward Grad.ConstrainedGrades

def axisDataCoefficients (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisDataGrade parameters grade) :
    (ℤ → ComplexEuclidean 2) × (ℤ → ComplexEuclidean 2) :=
  (Grad.AxisCore.axisCoefficient parameters (grade + 1) data.ofLp.1,
    Grad.AxisCore.axisCoefficient parameters (grade + 1) data.ofLp.2)

theorem axisCoreEmbedding_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (data : TCore parameters) (cell : ℤ) :
    Grad.AxisCore.axisCoefficient parameters grade (axisCoreEmbedding parameters grade data) cell =
      data.val cell := by
  change (Grad.AxisCore.axisWeight parameters grade cell : ℂ)⁻¹ •
    ((Grad.AxisCore.axisWeight parameters grade cell) • data.val cell) = _
  rw [← Complex.coe_smul, inv_smul_smul₀
    (Complex.ofReal_ne_zero.mpr (Grad.AxisCore.axisWeight_pos parameters grade cell).ne')]

theorem axisDataEmbedding_coefficients (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisData parameters) :
    axisDataCoefficients parameters grade (axisDataEmbedding parameters grade data) =
      (data.1.val, data.2.val) := by
  apply Prod.ext <;> funext cell <;> exact axisCoreEmbedding_coefficient parameters (grade + 1) _ cell

/-- The completed extraction is the literal AL10 formula, on the dense
original constrained smooth source, at every q >= 0. -/
theorem completedExtraction_coefficients (parameters : PhaseParameters) (cellLength : ℝ)
    (grade : ℕ) (source : sourceSmoothRange parameters) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source)) =
        axisExtraction cellLength source.val := by
  rw [completedExtraction_core, axisDataEmbedding_coefficients]
  rfl

/-- Exact AL11 consumer through the actual normalized chart and original
quotient operator. The chart root derivative and N18 remainder are retained. -/
theorem completedExtraction_literalForward (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters)
    (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction))) =
      chartKappa parameters reference insideR direction := by
  rw [completedExtraction_coefficients]
  exact axisExtraction_literalSmoothForward cellLength positive reference insideR seed insideS base direction

/-- A completed-forward consumer valid also at q=0: take the genuine
forward at q+4, then the canonical one-grade source inclusion. -/
theorem completedExtraction_actualForward (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters)
    (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceLowering parameters (extractionLarge grade) (show grade + 3 ≤ grade + 4 by omega)
        (actualSmoothForward parameters cellLength reference insideR seed insideS (grade + 4) (by omega) base
          (stateSmoothEmbedding parameters reference insideR ((grade + 4) + 6)
            (realHighLarge (grade + 4)) direction)))) = chartKappa parameters reference insideR direction := by
  rw [actualSmoothForward_core_value parameters cellLength reference insideR seed insideS (grade + 4) (by omega) base axis,
    sourceLowering_core]
  exact completedExtraction_literalForward parameters cellLength positive reference insideR seed insideS grade base axis direction

end Grad.ChartAxisSplit
