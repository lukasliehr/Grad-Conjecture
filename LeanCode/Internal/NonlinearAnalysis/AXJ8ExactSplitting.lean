import AXJ4Coordinates
import AXJ7DomainFlatJets
import ASL8SourceLiftConsumer
import AXJ0RealAlgebra
import AXJ0BlockAlgebra

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}
variable (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
variable (cellLength : ℝ) (positiveLength : 0 < cellLength)
variable (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
variable (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
variable (base : RealJointCore parameters reference insideR)
variable (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))

/-- The additive module formula is literally the original subtraction;
only proof elaboration avoids the real-submodule additive-instance diamond. -/
theorem realDomainProjection_sub (direction : stateSmoothRange parameters reference insideR) :
    realDomainProjection radius positive bounded reference insideR seed insideS base axis direction =
      direction - realLift parameters radius positive bounded reference insideR seed insideS base axis
        (realChartKappa parameters reference insideR direction) := by
  rw [realDomainProjection_apply]
  apply Subtype.ext
  exact stateCore_real_sub direction.val _

theorem realRangeProjection_sub (source : sourceSmoothRange parameters) :
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source =
      source - realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis
        (realExtraction parameters cellLength source) := by
  unfold realRangeProjection
  rw [splittingProjection_apply]
  generalize realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis
    (realExtraction parameters cellLength source) = correction
  exact sourceRange_real_sub (parameters := parameters) source correction

theorem realSourceLift_eq_actual (data : RealAxis parameters) :
    realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis data =
      Grad.AxisSourceLift.axisSourceLift parameters cellLength radius positive bounded
        reference insideR seed insideS base axis data.val data.property := by
  unfold realSourceLift Grad.AxisSourceLift.axisSourceLift
  rw [LinearMap.comp_apply, realLift_eq_axisDataCapLift]

theorem realSourceLift_apply (data : RealAxis parameters) :
    realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis data =
      literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
        (realLift parameters radius positive bounded reference insideR seed insideS base axis data) := by
  unfold realSourceLift
  rw [LinearMap.comp_apply]

include positiveLength in
def realFlatForward : LinearMap.ker (realChartKappa parameters reference insideR) →ₗ[ℝ]
    LinearMap.ker (realExtraction parameters cellLength) where
  toFun direction := ⟨literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction.val, by
    change realExtraction parameters cellLength
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction.val) = 0
    rw [realExtraction_forward cellLength positiveLength]
    exact direction.property⟩
  map_add' first second := Subtype.ext
    ((literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis).map_add first.val second.val)
  map_smul' scalar direction := Subtype.ext
    ((literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis).map_smul scalar direction.val)

theorem realFlatForward_apply
    (direction : LinearMap.ker (realChartKappa parameters reference insideR)) :
    (realFlatForward cellLength positiveLength reference insideR seed insideS base axis direction).val =
      literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction.val := rfl

include positiveLength in
theorem realRangeProjection_sourceLift (data : RealAxis parameters) :
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis
      (realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis data) = 0 := by
  unfold realRangeProjection
  rw [splittingProjection_apply,
    realExtraction_realSourceLift radius positive bounded cellLength positiveLength]
  exact module_cancel _

/-- AL26: the actual linearization in the explicit coordinates is precisely
diag(id,A_flat). This does not assert that A_flat is invertible. -/
theorem realForward_coordinates
    (data : RealAxis parameters × LinearMap.ker (realChartKappa parameters reference insideR)) :
    realRangeCoordinates radius positive bounded cellLength positiveLength reference insideR seed insideS base axis
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
        ((realDomainCoordinates radius positive bounded reference insideR seed insideS base axis).symm data)) =
      (data.1, realFlatForward cellLength positiveLength reference insideR seed insideS base axis data.2) := by
  have block := splitting_forward_coordinates_subtype
    (X := stateSmoothRange parameters reference insideR) (Y := sourceSmoothRange parameters) (D := RealAxis parameters)
    (realChartKappa parameters reference insideR) (realExtraction parameters cellLength)
    (realLift parameters radius positive bounded reference insideR seed insideS base axis)
    (realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis)
    (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis)
    (realChartKappa_realLift radius positive bounded reference insideR seed insideS base axis)
    (realExtraction_realSourceLift radius positive bounded cellLength positiveLength reference insideR seed insideS base axis)
    (realExtraction_forward cellLength positiveLength reference insideR seed insideS base axis)
    (realSourceLift_apply radius positive bounded cellLength reference insideR seed insideS base axis)
    (realFlatForward cellLength positiveLength reference insideR seed insideS base axis)
    (realFlatForward_apply cellLength positiveLength reference insideR seed insideS base axis) data
  unfold realRangeCoordinates realDomainCoordinates
  with_reducible exact block

end Grad.ChartAxisProjections
