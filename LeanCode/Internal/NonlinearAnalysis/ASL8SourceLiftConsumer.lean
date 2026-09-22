import ASL6RawDerivativeSupport
import ASL7ActualCapDirection
import AXL26LiftConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.Q24Realization Grad.RealFixedRanges Grad.ConstrainedTransfer Grad.ChartAxisSplit

/-- The literal source lift T_b=A_b E_b in the unchanged closed real source.
This definition does not cut off or project the quotient residual. -/
def axisSourceLift (parameters : PhaseParameters) (cellLength : ℝ)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) : sourceSmoothRange parameters :=
  literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
    (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data real)

variable {parameters : PhaseParameters}

/-- AL21: support is obtained from the four actual raw differentiated rows
and pointwise J_Y injectivity off-axis, not from radial-integral locality. -/
theorem axisSourceLift_support (cellLength : ℝ)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data)
    (row : Fin 4) (cell : ℤ) (point : ClosedDisk) (outside : radius / 2 ≤ ‖point.val‖) :
    (((axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real).val row).val cell).value point = 0 := by
  have sourceFormula :
      (axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real).val =
      literalPhysicalSmoothForwardRows parameters cellLength reference insideR seed insideS base
        (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data real) := rfl
  rw [sourceFormula]
  unfold literalPhysicalSmoothForwardRows axisDataCapLift
  erw [physicalFixedReferenceFamily_referenceCapLift radius positive bounded reference insideR seed insideS base axis
    (ChartAxisLift.axisToTangent parameters data.1) (ChartAxisLift.axisToTangent parameters data.2) real.1 real.2]
  apply quotientDerivative_zero_outside cellLength (radius / 2) (by positivity) _ _
    (physicalReferenceState_realCore_gauge reference insideR seed insideS base) _ rfl _ _ row cell point outside
  · exact capScalarAffine_mean_zero parameters radius positive (ChartAxisLift.axisToTangent parameters data.1)
  · exact capAffineField_firstOutsideZero radius positive seed insideS _ _
  · exact capScalarAffine_firstOutsideZero radius positive _

theorem axisSourceLift_extraction (cellLength : ℝ) (positiveLength : 0 < cellLength)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) :
    extractionData cellLength
      (axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real).val = data := by
  have coefficients := axisDataCapLift_forward_extraction parameters cellLength positiveLength radius positive bounded
    reference insideR seed insideS 0 base axis data real
  rw [completedExtraction_coefficients] at coefficients
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst coefficients
  · apply Subtype.ext
    exact congrArg Prod.snd coefficients

theorem axisSourceLift_physical_support (cellLength : ℝ)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data)
    (row : Fin 4) (point : ClosedDisk) (angle : ℝ) (outside : radius / 2 ≤ ‖point.val‖) :
    coreValue ((axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real).val row)
      point angle = 0 := by
  unfold coreValue
  calc
    _ = ∑' _ : ℤ, (0 : ComplexEuclidean 1) := by
      apply tsum_congr
      intro cell
      rw [axisSourceLift_support cellLength radius positive bounded reference insideR seed insideS base axis data real row cell point outside,
        smul_zero]
    _ = 0 := tsum_zero

/-- AL20 in the actual completed extraction target, at every original grade. -/
theorem axisSourceLift_completed_extraction (cellLength : ℝ) (positiveLength : 0 < cellLength)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) :
    completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real)) =
      axisDataEmbedding parameters grade data := by
  rw [completedExtraction_core, axisSourceLift_extraction cellLength positiveLength]

theorem axisSourceLift_actual_forward (cellLength : ℝ)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) :
    actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade)
        (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data real)) =
      sourceSmoothEmbedding parameters grade (Grad.SmoothForward.forwardLarge large)
        (axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real) :=
  actualPhysicalSmoothForward_core_value parameters cellLength reference insideR seed insideS grade large base axis _

def LocalizedSourceRightInverseGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ) (_positiveLength : 0 < cellLength)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data),
    (∀ (row : Fin 4) (cell : ℤ) (point : ClosedDisk), radius / 2 ≤ ‖point.val‖ →
      (((axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real).val row).val cell).value point = 0) ∧
    (∀ grade, completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (axisSourceLift parameters cellLength radius positive bounded reference insideR seed insideS base axis data real)) =
      axisDataEmbedding parameters grade data)

theorem actualLocalizedSourceRightInverse : LocalizedSourceRightInverseGoal := by
  intro parameters cellLength positiveLength radius positive bounded reference insideR seed insideS base axis data real
  exact ⟨axisSourceLift_support cellLength radius positive bounded reference insideR seed insideS base axis data real,
    fun grade => axisSourceLift_completed_extraction cellLength positiveLength radius positive bounded
      reference insideR seed insideS grade base axis data real⟩

end Grad.AxisSourceLift
