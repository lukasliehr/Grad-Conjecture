import AXJ2RealLift

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 300000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

section LinearSplitting

variable {X D : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid D] [Module ℝ D]

theorem module_cancel (x : X) : x + (-1 : ℝ) • x = 0 := by
  calc
    x + (-1 : ℝ) • x = ((1 : ℝ) + (-1)) • x := by rw [add_smul, one_smul]
    _ = 0 := by norm_num

def splittingProjection (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X) : X →ₗ[ℝ] X :=
  LinearMap.id + (-1 : ℝ) • lift.comp extraction

theorem splittingProjection_apply (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X) (x : X) :
    splittingProjection extraction lift x = x + (-1 : ℝ) • lift (extraction x) := rfl

theorem splittingProjection_mem (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X)
    (rightInverse : ∀ d, extraction (lift d) = d) (x : X) :
    splittingProjection extraction lift x ∈ LinearMap.ker extraction := by
  change extraction (x + (-1 : ℝ) • lift (extraction x)) = 0
  rw [map_add, map_smul, rightInverse]
  exact module_cancel _

theorem splittingProjection_fixes (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X)
    (x : X) (flat : x ∈ LinearMap.ker extraction) :
    splittingProjection extraction lift x = x := by
  change x + (-1 : ℝ) • lift (extraction x) = x
  rw [show extraction x = 0 from flat, map_zero, smul_zero, add_zero]

theorem splittingProjection_idempotent (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X)
    (rightInverse : ∀ d, extraction (lift d) = d) (x : X) :
    splittingProjection extraction lift (splittingProjection extraction lift x) =
      splittingProjection extraction lift x :=
  splittingProjection_fixes extraction lift _ (splittingProjection_mem extraction lift rightInverse x)

theorem splittingProjection_range (extraction : X →ₗ[ℝ] D) (lift : D →ₗ[ℝ] X)
    (rightInverse : ∀ d, extraction (lift d) = d) :
    LinearMap.range (splittingProjection extraction lift) = LinearMap.ker extraction := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact splittingProjection_mem extraction lift rightInverse y
  · intro flat
    exact ⟨x, splittingProjection_fixes extraction lift x flat⟩

end LinearSplitting

variable {parameters : PhaseParameters}
variable (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
variable (cellLength : ℝ) (positiveLength : 0 < cellLength)
variable (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
variable (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
variable (base : RealJointCore parameters reference insideR)
variable (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))

def realSourceLift : RealAxis parameters →ₗ[ℝ] sourceSmoothRange parameters :=
  (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis).comp
    (realLift parameters radius positive bounded reference insideR seed insideS base axis)

include positiveLength in
theorem realExtraction_realSourceLift (data : RealAxis parameters) :
    realExtraction parameters cellLength
      (realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis data) = data := by
  change realExtraction parameters cellLength
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
        (realLift parameters radius positive bounded reference insideR seed insideS base axis data)) = data
  rw [realExtraction_forward cellLength positiveLength]
  exact realChartKappa_realLift radius positive bounded reference insideR seed insideS base axis data

def realDomainProjection : stateSmoothRange parameters reference insideR →ₗ[ℝ]
    stateSmoothRange parameters reference insideR :=
  splittingProjection (X := stateSmoothRange parameters reference insideR) (D := RealAxis parameters)
    (realChartKappa parameters reference insideR)
    (realLift parameters radius positive bounded reference insideR seed insideS base axis)

def realRangeProjection : sourceSmoothRange parameters →ₗ[ℝ] sourceSmoothRange parameters :=
  splittingProjection (X := sourceSmoothRange parameters) (D := RealAxis parameters)
    (realExtraction parameters cellLength)
    (realSourceLift radius positive bounded cellLength reference insideR seed insideS base axis)

theorem realDomainProjection_apply (direction : stateSmoothRange parameters reference insideR) :
    realDomainProjection radius positive bounded reference insideR seed insideS base axis direction =
      direction + (-1 : ℝ) • realLift parameters radius positive bounded reference insideR seed insideS base axis
        (realChartKappa parameters reference insideR direction) := rfl

theorem realDomainProjection_mem (direction : stateSmoothRange parameters reference insideR) :
    realChartKappa parameters reference insideR
      (realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) = 0 := by
  rw [realDomainProjection_apply, map_add, map_smul, realChartKappa_realLift]
  exact module_cancel _

include positiveLength in
theorem realRangeProjection_mem (source : sourceSmoothRange parameters) :
    realExtraction parameters cellLength
      (realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source) = 0 := by
  unfold realRangeProjection
  rw [splittingProjection_apply, map_add, map_smul,
    realExtraction_realSourceLift radius positive bounded cellLength positiveLength]
  exact module_cancel _

theorem realDomainProjection_fixes (direction : stateSmoothRange parameters reference insideR)
    (flat : realChartKappa parameters reference insideR direction = 0) :
    realDomainProjection radius positive bounded reference insideR seed insideS base axis direction = direction := by
  rw [realDomainProjection_apply, flat, map_zero, smul_zero, add_zero]

theorem realRangeProjection_fixes (source : sourceSmoothRange parameters)
    (flat : realExtraction parameters cellLength source = 0) :
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source = source := by
  unfold realRangeProjection
  rw [splittingProjection_apply, flat, map_zero, smul_zero, add_zero]

theorem realDomainProjection_range :
    LinearMap.range (realDomainProjection radius positive bounded reference insideR seed insideS base axis) =
      LinearMap.ker (realChartKappa parameters reference insideR) := by
  ext direction
  constructor
  · rintro ⟨other, rfl⟩
    exact realDomainProjection_mem radius positive bounded reference insideR seed insideS base axis other
  · intro flat
    exact ⟨direction, realDomainProjection_fixes radius positive bounded reference insideR seed insideS base axis direction flat⟩

include positiveLength in
theorem realRangeProjection_range :
    LinearMap.range (realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis) =
      LinearMap.ker (realExtraction parameters cellLength) := by
  ext source
  constructor
  · rintro ⟨other, rfl⟩
    exact realRangeProjection_mem radius positive bounded cellLength positiveLength reference insideR seed insideS base axis other
  · intro flat
    exact ⟨source, realRangeProjection_fixes radius positive bounded cellLength reference insideR seed insideS base axis source flat⟩

theorem realDomainProjection_idempotent (direction : stateSmoothRange parameters reference insideR) :
    realDomainProjection radius positive bounded reference insideR seed insideS base axis
      (realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) =
    realDomainProjection radius positive bounded reference insideR seed insideS base axis direction := by
  apply realDomainProjection_fixes
  exact realDomainProjection_mem radius positive bounded reference insideR seed insideS base axis direction

include positiveLength in
theorem realRangeProjection_idempotent (source : sourceSmoothRange parameters) :
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis
      (realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source) =
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis source := by
  apply realRangeProjection_fixes
  exact realRangeProjection_mem radius positive bounded cellLength positiveLength reference insideR seed insideS base axis source

include positiveLength in
theorem realForward_domainProjection (direction : stateSmoothRange parameters reference insideR) :
    literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis
      (realDomainProjection radius positive bounded reference insideR seed insideS base axis direction) =
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS base axis
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction) := by
  unfold realDomainProjection realRangeProjection
  rw [splittingProjection_apply, splittingProjection_apply, map_add, map_smul,
    realExtraction_forward cellLength positiveLength]
  simp only [realSourceLift, LinearMap.comp_apply]

end Grad.ChartAxisProjections
