import AXJ3FlatProjections

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

section LinearSplitting

variable {X D : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid D] [Module ℝ D]

def splittingCoordinates (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X)
    (rightInverse : ∀ d, extraction (lift d) = d) : X ≃ₗ[ℝ] D × LinearMap.ker extraction where
  toFun x := (extraction x, ⟨splittingProjection extraction lift x,
    splittingProjection_mem extraction lift rightInverse x⟩)
  invFun data := lift data.1 + data.2.val
  left_inv x := by
    change lift (extraction x) + (x + (-1 : ℝ) • lift (extraction x)) = x
    rw [add_left_comm, module_cancel, add_zero]
  right_inv data := by
    apply Prod.ext
    · change extraction (lift data.1 + data.2.val) = data.1
      rw [map_add, rightInverse, show extraction data.2.val = 0 from data.2.property, add_zero]
    · apply Subtype.ext
      change (lift data.1 + data.2.val) + (-1 : ℝ) • lift (extraction (lift data.1 + data.2.val)) = data.2.val
      rw [map_add, rightInverse, show extraction data.2.val = 0 from data.2.property, add_zero]
      rw [add_right_comm, module_cancel, zero_add]
  map_add' first second := by
    apply Prod.ext
    · exact map_add extraction first second
    · exact Subtype.ext ((splittingProjection extraction lift).map_add first second)
  map_smul' scalar x := by
    apply Prod.ext
    · exact map_smul extraction scalar x
    · exact Subtype.ext ((splittingProjection extraction lift).map_smul scalar x)

end LinearSplitting

variable {parameters : PhaseParameters}
variable (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
variable (cellLength : ℝ) (positiveLength : 0 < cellLength)
variable (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
variable (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
variable (base : RealJointCore parameters reference insideR)
variable (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))

def realDomainCoordinates : stateSmoothRange parameters reference insideR ≃ₗ[ℝ]
    RealAxis parameters × LinearMap.ker (realChartKappa parameters reference insideR) :=
  splittingCoordinates (X := stateSmoothRange parameters reference insideR) (D := RealAxis parameters)
    (realChartKappa parameters reference insideR)
    (realLift parameters radius positive bounded reference insideR seed insideS base axis)
    (realChartKappa_realLift radius positive bounded reference insideR seed insideS base axis)

def realRangeCoordinates : sourceSmoothRange parameters ≃ₗ[ℝ]
    RealAxis parameters × LinearMap.ker (realExtraction parameters cellLength) :=
  splittingCoordinates (X := sourceSmoothRange parameters) (D := RealAxis parameters)
    (realExtraction parameters cellLength)
    (realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis)
    (realExtraction_realSourceLift radius positive bounded cellLength positiveLength reference insideR seed insideS base axis)

end Grad.ChartAxisProjections
