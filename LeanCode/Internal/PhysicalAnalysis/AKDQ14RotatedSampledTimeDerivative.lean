import AKDQ13RotatedSampledFields

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem physical_time_section_fderiv (field : Vec → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ field (coordinateDirection point time)) :
    fderiv ℝ (fun current => field (coordinateDirection point current)) time 1 =
      fderiv ℝ field (coordinateDirection point time) (coordinateDirection 0 1) := by
  have sectionDerivative : HasFDerivAt (fun current => coordinateDirection point current) physicalToroidalCLM time := by
    have identity : (fun current => coordinateDirection point current) =
        (fun _ : ℝ => coordinateDirection point 0) + physicalToroidalCLM := by
      funext current
      ext coordinate
      fin_cases coordinate <;> simp [physicalToroidalCLM_apply, coordinateDirection, vector]
    rw [identity]
    simpa only [zero_add] using (hasFDerivAt_const (coordinateDirection point 0) time).add physicalToroidalCLM.hasFDerivAt
  exact congrArg (fun linear : ℝ →L[ℝ] Value => linear 1)
    (differentiable.hasFDerivAt.comp time sectionDerivative).fderiv

theorem rotatedSampledField_time_hasDerivAt (period : ℕ) {field : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    HasDerivAt (fun current => rotatedSampledField period field (coordinateDirection point current))
      (rotation time (tangentGenerator (field point ((period : ℝ) * time)) +
        (period : ℝ) • cellDerivative field point ((period : ℝ) * time))) time := by
  have cellDerivative : HasDerivAt (field point) (cellDerivative field point ((period : ℝ) * time))
      ((period : ℝ) * time) := by
    simpa [Grad.PhysicalFamily.cellDerivative] using
      (smooth_time_differentiable smooth point pointIn ((period : ℝ) * time)).hasDerivAt
  have scaleDerivative : HasDerivAt (fun current : ℝ => (period : ℝ) * current) (period : ℝ) time := by
    simpa using (hasDerivAt_id time).const_mul (period : ℝ)
  have pathDerivative : HasDerivAt (fun current => field point ((period : ℝ) * current))
      ((period : ℝ) • Grad.PhysicalFamily.cellDerivative field point ((period : ℝ) * time)) time := by
    have chain := (cellDerivative.hasFDerivAt.comp time scaleDerivative.hasFDerivAt).hasDerivAt
    have derivativeIdentity : (ContinuousLinearMap.toSpanSingleton ℝ
        (Grad.PhysicalFamily.cellDerivative field point ((period : ℝ) * time)) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (period : ℝ)) 1 =
        (period : ℝ) • Grad.PhysicalFamily.cellDerivative field point ((period : ℝ) * time) := by
      ext coordinate
      simp [smul_eq_mul]
    rw [derivativeIdentity] at chain
    exact chain
  simpa only [rotatedSampledField_coordinateDirection] using
    rotation_path_hasDerivAt _ time _ pathDerivative

theorem rotatedSampledField_fderiv_time (period : ℕ) {field : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    fderiv ℝ (rotatedSampledField period field) (coordinateDirection point time) (coordinateDirection 0 1) =
      rotation time (tangentGenerator (field point ((period : ℝ) * time)) +
        (period : ℝ) • cellDerivative field point ((period : ℝ) * time)) := by
  have domainOpen : IsOpen (planarPart ⁻¹' Metric.ball (0 : Plane) radius) :=
    Metric.isOpen_ball.preimage planarPart_contDiff.continuous
  have membership : coordinateDirection point time ∈ planarPart ⁻¹' Metric.ball (0 : Plane) radius := by
    simpa using pointIn
  have fullDiff := ((rotatedSampledField_contDiffOn period smooth).contDiffAt
    (domainOpen.mem_nhds membership)).differentiableAt (by simp)
  rw [← physical_time_section_fderiv _ point time fullDiff]
  simpa using congrArg (fun linear : ℝ →L[ℝ] Vec => linear 1)
    (rotatedSampledField_time_hasDerivAt period smooth point pointIn time).hasFDerivAt.fderiv

end Grad.PhysicalEquilibrium
