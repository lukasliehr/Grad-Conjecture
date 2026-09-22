import AXL25ChartKappaBound

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem chartKappaData_capLiftLinear (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base : TangentCoefficient parameters) (data : AxisData parameters) :
    chartKappaData parameters (axisDataCapLiftLinear parameters radius positive seed inside base data) = data := by
  apply Prod.ext
  · apply Subtype.ext
    funext cell
    exact capScalarAffine_originGradient radius positive (axisToTangent parameters data.1) cell
  · rfl

/-- The exact AL15 lift, in the original moving-seed constrained chart,
with canonical axis data, the actual physical first variation and cap support.
The coefficient is the actual derivative identified by AXL22's literal
negative dot divided by twice the positive root formula. -/
structure PhysicalAxisLiftRealization (parameters : PhaseParameters)
    (radius : ℝ) (positive : 0 < radius) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (base : ChartState parameters)
    (data : AxisData parameters) : Prop where
  member : axisDataCapLiftLinear parameters radius positive seed inside base.1 data ∈
    stateSmoothRange parameters seed inside
  chart : physicalChartState parameters (smoothingChartCore parameters
      (axisDataCapLiftLinear parameters radius positive seed inside base.1 data)) =
    (axisToTangent parameters data.2,
      capChartRemainder parameters radius positive seed inside
        (rootDerivativeFamily 1 base.1 (fun _ => axisToTangent parameters data.2)) (axisToTangent parameters data.2),
      capScalarAffine parameters radius positive (axisToTangent parameters data.1))
  variation : chartDerivativeFamily parameters seed inside 1 base
      (fun _ => physicalChartState parameters (smoothingChartCore parameters
        (axisDataCapLiftLinear parameters radius positive seed inside base.1 data))) =
    (capAffineField parameters radius positive seed inside
      (rootDerivativeFamily 1 base.1 (fun _ => axisToTangent parameters data.2)) (axisToTangent parameters data.2),
      capScalarAffine parameters radius positive (axisToTangent parameters data.1))
  extraction : chartKappaData parameters
    (axisDataCapLiftLinear parameters radius positive seed inside base.1 data) = data
  outside : ∀ (cell : ℤ) (point : ClosedDisk), radius / 2 ≤ ‖point.val‖ →
    ((capAffineField parameters radius positive seed inside
        (rootDerivativeFamily 1 base.1 (fun _ => axisToTangent parameters data.2))
          (axisToTangent parameters data.2)).val cell).value point = 0 ∧
      ((capScalarAffine parameters radius positive (axisToTangent parameters data.1)).val cell).value point = 0

theorem actualPhysicalAxisLift (parameters : PhaseParameters)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base : ChartState parameters) (realBase : RealTangent base.1) (axis : ChartAxisCondition base)
    (data : AxisData parameters) (real : RealAxisData data) :
    PhysicalAxisLiftRealization parameters radius positive seed inside base data where
  member := actualCapLiftState_mem radius positive bounded seed inside base.1
    (axisToTangent parameters data.1) (axisToTangent parameters data.2) realBase axis real.1 real.2
  chart := physicalChartState_capLiftState radius positive seed inside _ _ _
  variation := chartDerivative_actualCapLift radius positive seed inside base _ _
  extraction := chartKappaData_capLiftLinear radius positive seed inside base.1 data
  outside cell point outside :=
    ⟨capAffineField_zero_outside radius positive seed inside _ _ cell point outside,
      capScalarAffine_zero_outside radius positive _ cell point outside⟩

/-- Immediate actual fixed-reference forward consumer, in every completed
extraction grade. This does not claim support of the quotient source. -/
theorem axisDataCapLift_forward_extraction (parameters : PhaseParameters) (cellLength : ℝ)
    (positiveLength : 0 < cellLength) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) :
    axisDataCoefficients parameters grade (completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade)
        (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
          (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data real)))) =
      (data.1.val, data.2.val) :=
  completedExtraction_forward_referenceCapLift cellLength positiveLength radius positive bounded
    reference insideR seed insideS grade base axis
    (axisToTangent parameters data.1) (axisToTangent parameters data.2) real.1 real.2

end Grad.ChartAxisLift
