import AKDT4ActualFieldZeros

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding Grad.NonlinearQuotient Grad.GeometryClosure

/-- The actual disk rotation orbit stays at the same radius for all time. -/
theorem diskOrbit_norm (angle : ℝ) (point : Plane) : ‖planeRotationAction angle point‖ = ‖point‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [disk_norm_sq, disk_norm_sq]
  simp [planeRotationAction, planarRotation, dotProduct, Fin.sum_univ_two]
  calc
    _ = (Real.sin angle ^ 2 + Real.cos angle ^ 2) * (point 0 ^ 2 + point 1 ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem diskOrbit_smooth (point : Plane) : ContDiff ℝ ∞ (fun angle => planeRotationAction angle point) := by
  simp_rw [planeRotationAction_eq_cos_sin]
  fun_prop

theorem physicalDiskOrbit_smooth (point : Plane) (time : ℝ) :
    ContDiff ℝ ∞ (fun angle => coordinateDirection (planeRotationAction angle point) time) := by
  have identity : (fun angle => coordinateDirection (planeRotationAction angle point) time) =
      fun angle => physicalDiskCLM (planeRotationAction angle point) + coordinateDirection 0 time := by
    funext angle
    exact coordinateDirection_add _ _
  rw [identity]
  exact ((physicalDiskCLM.contDiff).comp (diskOrbit_smooth point)).add contDiff_const

theorem physicalDiskOrbit_hasDerivAt (point : Plane) (time : ℝ) :
    HasDerivAt (fun angle => coordinateDirection (planeRotationAction angle point) time)
      (coordinateDirection (planeQuarterTurn point) 0) 0 := by
  have identity : (fun angle => coordinateDirection (planeRotationAction angle point) time) =
      fun angle => physicalDiskCLM (planeRotationAction angle point) + coordinateDirection 0 time := by
    funext angle
    exact coordinateDirection_add _ _
  rw [identity]
  simpa only [Function.comp_def, physicalDiskCLM_apply] using
    ((physicalDiskCLM.hasFDerivAt.comp_hasDerivAt 0 (planeRotationAction_hasDerivAt_zero point)).add_const
      (coordinateDirection 0 time))

end Grad.PhysicalGeometry
