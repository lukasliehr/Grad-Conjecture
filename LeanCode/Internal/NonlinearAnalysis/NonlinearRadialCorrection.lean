import RadialDivision
import SmoothRowFields
import RotationAverageAlgebra

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints

theorem complexAngularAverage_eq_rotationAverage (field : Plane → ℝ → ℂ)
    (point : Plane) (time : ℝ) :
    complexAngularAverage field point time = rotationAverage (fun argument => field argument time) point := rfl

theorem meanEulerAngularProduct_joint_smooth {field : Plane → ℝ → ComplexVec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (meanEulerAngularProduct field))
      (Metric.ball 0 radius ×ˢ univ) :=
  rotationAverage_joint_smooth
    (field := fun point time => complexDot (diskEuler field point time) (diskAngular field point time))
    (radius := radius) (eulerAngularProduct_joint_smooth smooth)

theorem meanEulerAngularProduct_origin (field : Plane → ℝ → ComplexVec) (time : ℝ) :
    meanEulerAngularProduct field 0 time = 0 := by
  simp [meanEulerAngularProduct, complexAngularAverage, physicalRotation_origin, complexDot]

theorem meanEulerAngularProduct_rotation (field : Plane → ℝ → ComplexVec)
    (angle : ℝ) (point : Plane) (time : ℝ) :
    meanEulerAngularProduct field (planeRotationAction angle point) time =
      meanEulerAngularProduct field point time := by
  exact rotationAverage_rotation
    (fun argument => complexDot (diskEuler field argument time) (diskAngular field argument time)) angle point

/-- Actual O13: the correction is the specified integral of the Cartesian
Laplacian of the actual averaged Euler/angular product. -/
theorem nonlinearRadialQuotient_identity {field : Plane → ℝ → ComplexVec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    meanEulerAngularProduct field point time =
      (‖point‖ ^ 2) • nonlinearRadialQuotient field point time := by
  have identity := radialIntegral_laplacian (fun argument => meanEulerAngularProduct field argument time)
    radius (cellSection_smooth (meanEulerAngularProduct_joint_smooth smooth) time)
    (fun angle argument _ => meanEulerAngularProduct_rotation field angle argument time) point pointIn
  simpa only [meanEulerAngularProduct_origin, sub_zero, nonlinearRadialQuotient] using identity

end Grad.NonlinearQuotient
