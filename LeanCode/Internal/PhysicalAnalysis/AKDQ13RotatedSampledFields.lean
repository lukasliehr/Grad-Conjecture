import AKDQ12AmbientForcePairing

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding

/-- The literal rotation/resampling used by the physical magnetic lift. -/
def rotatedSampledField (period : ℕ) (field : Plane → ℝ → Vec) (point : Vec) : Vec :=
  rotation (point 2) (field (planarPart point) ((period : ℝ) * point 2))

@[simp] theorem rotatedSampledField_coordinateDirection (period : ℕ) (field : Plane → ℝ → Vec)
    (point : Plane) (time : ℝ) :
    rotatedSampledField period field (coordinateDirection point time) =
      rotation time (field point ((period : ℝ) * time)) := by
  unfold rotatedSampledField
  rw [planarPart_coordinateDirection]
  simp [coordinateDirection, vector]

theorem rotatedSampledField_contDiffOn (period : ℕ) {field : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (rotatedSampledField period field) (planarPart ⁻¹' Metric.ball 0 radius) := by
  have inputSmooth : ContDiff ℝ ∞ (fun point : Vec => (planarPart point, (period : ℝ) * point 2)) :=
    planarPart_contDiff.prodMk (contDiff_const.mul (by fun_prop))
  have cellSmooth : ContDiffOn ℝ ∞ (fun point : Vec => field (planarPart point) ((period : ℝ) * point 2))
      (planarPart ⁻¹' Metric.ball 0 radius) := by
    apply (smooth.comp inputSmooth.contDiffOn (fun point pointIn => ⟨pointIn, mem_univ _⟩)).congr
    intro point _
    rfl
  change ContDiffOn ℝ ∞ (uncurriedRotation ∘ (fun point : Vec =>
    (point 2, field (planarPart point) ((period : ℝ) * point 2)))) _
  exact uncurriedRotation_contDiff.comp_contDiffOn
    ((show ContDiff ℝ ∞ (fun point : Vec => point 2) from by fun_prop).contDiffOn.prodMk cellSmooth)

theorem rotation_inner (time : ℝ) (first second : Vec) :
    inner ℝ (rotation time first) (rotation time second) = inner ℝ first second := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, rotation, vector]
  calc
    _ = (Real.sin time ^ 2 + Real.cos time ^ 2) * (first 0 * second 0 + first 1 * second 1) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]; ring

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem physical_disk_section_fderiv (field : Vec → Value) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ field (coordinateDirection point time)) (direction : Plane) :
    fderiv ℝ (fun argument : Plane => field (coordinateDirection argument time)) point direction =
      fderiv ℝ field (coordinateDirection point time) (coordinateDirection direction 0) := by
  have sectionDerivative : HasFDerivAt (fun argument : Plane => coordinateDirection argument time) physicalDiskCLM point := by
    have identity : (fun argument : Plane => coordinateDirection argument time) =
        (fun _ : Plane => coordinateDirection 0 time) + physicalDiskCLM := by
      funext argument
      ext coordinate
      fin_cases coordinate <;> simp [physicalDiskCLM_apply, coordinateDirection, vector]
    rw [identity]
    simpa only [zero_add] using (hasFDerivAt_const (coordinateDirection 0 time) point).add physicalDiskCLM.hasFDerivAt
  exact congrArg (fun linear : Plane →L[ℝ] Value => linear direction)
    (differentiable.hasFDerivAt.comp point sectionDerivative).fderiv

theorem rotatedSampledField_fderiv_disk (period : ℕ) {field : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) (direction : Plane) :
    fderiv ℝ (rotatedSampledField period field) (coordinateDirection point time) (coordinateDirection direction 0) =
      rotation time (fderiv ℝ (fun argument => field argument ((period : ℝ) * time)) point direction) := by
  have domainOpen : IsOpen (planarPart ⁻¹' Metric.ball (0 : Plane) radius) :=
    Metric.isOpen_ball.preimage planarPart_contDiff.continuous
  have membership : coordinateDirection point time ∈ planarPart ⁻¹' Metric.ball (0 : Plane) radius := by
    simpa using pointIn
  have fullDiff := ((rotatedSampledField_contDiffOn period smooth).contDiffAt
    (domainOpen.mem_nhds membership)).differentiableAt (by simp)
  rw [← physical_disk_section_fderiv _ point time fullDiff direction]
  have sectionIdentity : (fun argument : Plane => rotatedSampledField period field (coordinateDirection argument time)) =
      rotationCLM time ∘ (fun argument : Plane => field argument ((period : ℝ) * time)) := by
    funext argument
    simp
  rw [sectionIdentity, fderiv_comp (x := point) (rotationCLM time).differentiableAt
    (smooth_spatial_differentiable smooth point pointIn ((period : ℝ) * time)), (rotationCLM time).fderiv]
  rfl

end Grad.PhysicalEquilibrium
