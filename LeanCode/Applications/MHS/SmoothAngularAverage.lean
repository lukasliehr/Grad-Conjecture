import CompactSmoothIntegral
import CellSolutionFamily
import GC13Angular
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.MainTarget Grad.PhysicalFamily Grad.GeometryClosure
open Grad.GaugeCoefficients.Radial

theorem physicalRotation_eq_orthogonal (angle : ℝ) (point : Plane) :
    planeRotationAction angle point = planeRotationEquiv angle point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeRotationAction, planarRotation, planeRotationEquiv, planeRotation,
      Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]

@[simp] theorem physicalRotation_norm (angle : ℝ) (point : Plane) :
    ‖planeRotationAction angle point‖ = ‖point‖ := by
  rw [physicalRotation_eq_orthogonal]
  exact (planeRotationEquiv angle).norm_map point

@[simp] theorem physicalRotation_origin (angle : ℝ) :
    planeRotationAction angle 0 = 0 := by
  rw [physicalRotation_eq_orthogonal]
  exact map_zero _

theorem physicalRotation_contDiff :
    ContDiff ℝ ∞ (fun argument : ℝ × Plane =>
      planeRotationAction argument.1 argument.2) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotationAction, planarRotation, Matrix.vecHead, Matrix.vecTail] <;>
    fun_prop

theorem physicalRotation_add (first second : ℝ) (point : Plane) :
    planeRotationAction first (planeRotationAction second point) =
      planeRotationAction (first + second) point := by
  simp only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [planeRotation, Real.cos_add, Real.sin_add] <;> ring

theorem physicalRotation_periodic (point : Plane) :
    Function.Periodic (fun angle => planeRotationAction angle point) (2 * Real.pi) := by
  intro angle
  simp only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply]
  ext coordinate
  fin_cases coordinate <;> simp [planeRotation]

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]

/-- The original angular average, using the original angle and normalization. -/
def rotationAverage (field : Plane → Value) (point : Plane) : Value :=
  (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
    field (planeRotationAction angle point)

omit [CompleteSpace Value] in
theorem rotationAverage_eq_compactIntegral (field : Plane → Value) (point : Plane) :
    rotationAverage field point = (2 * Real.pi)⁻¹ •
      ∫ angle in Icc (0 : ℝ) (2 * Real.pi), field (planeRotationAction angle point) := by
  rw [rotationAverage, intervalIntegral.integral_of_le (by positivity)]
  rw [integral_Icc_eq_integral_Ioc]

theorem rotationAverage_smooth {field : Plane → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball 0 radius)) :
    ContDiffOn ℝ ∞ (rotationAverage field) (Metric.ball 0 radius) := by
  have integrandSmooth : ContDiffOn ℝ ∞
      (fun argument : Plane × ℝ => field (planeRotationAction argument.2 argument.1))
      (Metric.ball 0 radius ×ˢ univ) := by
    apply smooth.comp (physicalRotation_contDiff.comp
      (contDiff_snd.prodMk contDiff_fst)).contDiffOn
    intro argument argumentIn
    simpa [Metric.mem_ball, dist_zero_right] using argumentIn.1
  have integralSmooth := contDiffOn_compactIntegral Metric.isOpen_ball integrandSmooth
    (0 : ℝ) (2 * Real.pi)
  change ContDiffOn ℝ ∞ (fun point => rotationAverage field point) (Metric.ball 0 radius)
  simp_rw [rotationAverage_eq_compactIntegral]
  exact contDiffOn_const.smul integralSmooth

theorem rotationAverage_joint_smooth {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun argument : Plane × ℝ =>
      rotationAverage (fun point => field point argument.2) argument.1)
      (Metric.ball 0 radius ×ˢ univ) := by
  have integrandSmooth : ContDiffOn ℝ ∞
      (fun argument : (Plane × ℝ) × ℝ =>
        field (planeRotationAction argument.2 argument.1.1) argument.1.2)
      ((Metric.ball 0 radius ×ˢ univ) ×ˢ univ) := by
    apply smooth.comp ((physicalRotation_contDiff.comp
      (contDiff_snd.prodMk contDiff_fst.fst)).prodMk contDiff_fst.snd).contDiffOn
    intro argument argumentIn
    exact ⟨by simpa [Metric.mem_ball, dist_zero_right] using argumentIn.1.1, mem_univ _⟩
  have integralSmooth := contDiffOn_compactIntegral (Metric.isOpen_ball.prod isOpen_univ)
    integrandSmooth (0 : ℝ) (2 * Real.pi)
  simp_rw [rotationAverage_eq_compactIntegral]
  exact contDiffOn_const.smul integralSmooth

theorem angularAverage_eq_rotationAverage (field : Plane → ℝ → ℝ)
    (point : Plane) (time : ℝ) :
    angularAverage field point time = rotationAverage (fun argument => field argument time) point := rfl

theorem angularAverage_smooth {field : Plane → ℝ → ℝ} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (angularAverage field))
      (Metric.ball 0 radius ×ˢ univ) :=
  rotationAverage_joint_smooth smooth

end Grad.Constraints
