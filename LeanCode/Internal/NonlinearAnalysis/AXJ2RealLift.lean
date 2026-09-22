import AXJ1RealAxisMaps

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.ConstrainedTransfer

variable {parameters : PhaseParameters}

def referenceLiftLinear (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR) :
    AxisData parameters →ₗ[ℂ] Grad.SmoothingFamily.StateCore parameters :=
  (coreTransfer parameters seed insideS reference insideR).comp
    (axisDataCapLiftLinear parameters radius positive seed insideS (smoothingToTangent parameters base.2.val.1))

theorem referenceLiftLinear_mem (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (data : RealAxis parameters) :
    referenceLiftLinear parameters radius positive reference insideR seed insideS base data.val ∈
      stateSmoothRange parameters reference insideR :=
  (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data.val data.property).property

def realLift (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    RealAxis parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR where
  toFun data := ⟨referenceLiftLinear parameters radius positive reference insideR seed insideS base data.val,
    referenceLiftLinear_mem radius positive bounded reference insideR seed insideS base axis data⟩
  map_add' first second := Subtype.ext
    ((referenceLiftLinear parameters radius positive reference insideR seed insideS base).map_add first.val second.val)
  map_smul' scalar data := Subtype.ext
    (((referenceLiftLinear parameters radius positive reference insideR seed insideS base).restrictScalars ℝ).map_smul scalar data.val)

theorem realLift_eq_axisDataCapLift (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (data : RealAxis parameters) :
    realLift parameters radius positive bounded reference insideR seed insideS base axis data =
      axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data.val data.property := by
  apply Subtype.ext
  rw [show (realLift parameters radius positive bounded reference insideR seed insideS base axis data).val =
      coreTransfer parameters seed insideS reference insideR
        (axisDataCapLiftLinear parameters radius positive seed insideS
          (smoothingToTangent parameters base.2.val.1) data.val) from rfl]
  rfl

theorem realChartKappa_realLift (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (data : RealAxis parameters) :
    realChartKappa parameters reference insideR
      (realLift parameters radius positive bounded reference insideR seed insideS base axis data) = data := by
  apply Subtype.ext
  apply axisData_ext
  rw [show ((realChartKappa parameters reference insideR
        (realLift parameters radius positive bounded reference insideR seed insideS base axis data)).val.1.val,
      (realChartKappa parameters reference insideR
        (realLift parameters radius positive bounded reference insideR seed insideS base axis data)).val.2.val) =
      chartKappa parameters reference insideR
        (realLift parameters radius positive bounded reference insideR seed insideS base axis data) from
      chartKappaData_coefficients reference insideR _, realLift_eq_axisDataCapLift]
  exact chartKappa_axisDataCapLift radius positive bounded reference insideR seed insideS base axis data.val data.property

theorem realExtraction_forward (cellLength : ℝ) (positiveLength : 0 < cellLength)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    realExtraction parameters cellLength
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction) =
      realChartKappa parameters reference insideR direction := by
  apply Subtype.ext
  apply axisData_ext
  change axisExtraction cellLength
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction).val =
    ((chartKappaData parameters direction.val).1.val, (chartKappaData parameters direction.val).2.val)
  rw [chartKappaData_coefficients]
  exact axisExtraction_physicalFirstRows cellLength positiveLength reference insideR seed insideS base direction

end Grad.ChartAxisProjections
