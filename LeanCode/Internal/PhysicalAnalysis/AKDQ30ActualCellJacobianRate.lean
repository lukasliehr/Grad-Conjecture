import AKDQ29DeterminantNondegeneracy

noncomputable section
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling

theorem actual_cell_jacobian_rate_zero (length : ℝ) (family : CellSolutionFamily length)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    let mapping := family.v epsilon parameter.val
    tripleDeterminant (diskEuler (diskAngular mapping) point time) (diskAngular mapping point time)
        (affineStateDerivative length epsilon mapping point time) +
      tripleDeterminant (diskEuler mapping point time) (diskAngular (diskAngular mapping) point time)
        (affineStateDerivative length epsilon mapping point time) +
      tripleDeterminant (diskEuler mapping point time) (diskAngular mapping point time)
        (cellDerivative (diskAngular mapping) point time + epsilon • tangentGenerator (diskAngular mapping point time)) = 0 := by
  have mappingSmooth := fixed_cell_joint_smooth family.vSmooth epsilon epsilonIn parameter.val
    (parameter_mem_open length family parameter)
  have pointIn : point ∈ Metric.ball (0 : Plane) family.collarRadius := by
    simpa using pointBound.trans_lt family.collarLarge
  have eulerDiff := smooth_spatial_differentiable (diskEuler_joint_smooth mappingSmooth) point pointIn time
  have angularDiff := smooth_spatial_differentiable (diskAngular_joint_smooth mappingSmooth) point pointIn time
  have affineDiff := smooth_spatial_differentiable (affineStateDerivative_joint_smooth length epsilon mappingSmooth) point pointIn time
  have determinant := (actual_cell_integrated_equations length family epsilon epsilonIn parameter point pointBound time).2.2
  rw [diskAngular_tripleDeterminant _ _ _ point time eulerDiff angularDiff affineDiff,
    diskAngular_diskEuler mappingSmooth point pointIn time,
    diskAngular_affineStateDerivative length epsilon mappingSmooth point pointIn time] at determinant
  exact determinant

end Grad.PhysicalEquilibrium
