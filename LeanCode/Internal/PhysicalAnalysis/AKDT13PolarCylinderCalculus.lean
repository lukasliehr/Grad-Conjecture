import AKDT12ReferenceFoliation

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily.SampledFullGeometry

def polarCylinderLift (point : Vec) : Vec :=
  vector (point 0 * Real.cos (point 1)) (point 0 * Real.sin (point 1)) (point 2)

theorem polarCylinderLift_smooth : ContDiff ℝ ∞ polarCylinderLift := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [polarCylinderLift, vector] <;> fun_prop

/-- The actual full polar differential, with input coordinates r,theta,phi. -/
theorem polarCylinderLift_fderiv (point direction : Vec) :
    fderiv ℝ polarCylinderLift point direction =
      vector (direction 0 * Real.cos (point 1) - point 0 * Real.sin (point 1) * direction 1)
        (direction 0 * Real.sin (point 1) + point 0 * Real.cos (point 1) * direction 1) (direction 2) := by
  have full := (polarCylinderLift_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := point)
  have coordinateDerivative (coordinate : Fin 3) := (vecCoordinateCLM coordinate).hasFDerivAt.comp point full
  ext coordinate
  fin_cases coordinate
  · have first := coordinateDerivative 0
    change HasFDerivAt (fun argument : Vec => argument 0 * Real.cos (argument 1)) _ point at first
    have computed := ((vecCoordinateCLM 0).hasFDerivAt (x := point)).mul ((vecCoordinateCLM 1).hasFDerivAt.cos)
    have equality := congrArg (fun linear : Vec →L[ℝ] ℝ => linear direction) (first.unique computed)
    simpa [vector, add_comm, ContinuousLinearMap.comp_apply, sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm] using equality
  · have second := coordinateDerivative 1
    change HasFDerivAt (fun argument : Vec => argument 0 * Real.sin (argument 1)) _ point at second
    have computed := ((vecCoordinateCLM 0).hasFDerivAt (x := point)).mul ((vecCoordinateCLM 1).hasFDerivAt.sin)
    have equality := congrArg (fun linear : Vec →L[ℝ] ℝ => linear direction) (second.unique computed)
    simpa [vector, add_comm, ContinuousLinearMap.comp_apply, mul_assoc, mul_comm, mul_left_comm] using equality
  · have third := coordinateDerivative 2
    change HasFDerivAt (fun argument : Vec => argument 2) _ point at third
    have equality := congrArg (fun linear : Vec →L[ℝ] ℝ => linear direction)
      (third.unique (vecCoordinateCLM 2).hasFDerivAt)
    exact equality

/-- The polar coordinates have full rank exactly where the radius is nonzero. -/
theorem polarCylinderLift_fderiv_injective (point : Vec) (nonzero : point 0 ≠ 0) :
    Function.Injective (fderiv ℝ polarCylinderLift point) := by
  apply (fderiv ℝ polarCylinderLift point).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro direction zero
  change fderiv ℝ polarCylinderLift point direction = 0 at zero
  rw [polarCylinderLift_fderiv] at zero
  have components := congrArg (fun value : Vec => (value 0, value 1, value 2)) zero
  have first : direction 0 * Real.cos (point 1) - point 0 * Real.sin (point 1) * direction 1 = 0 := congrArg (fun value : ℝ × ℝ × ℝ => value.1) components
  have second : direction 0 * Real.sin (point 1) + point 0 * Real.cos (point 1) * direction 1 = 0 := congrArg (fun value : ℝ × ℝ × ℝ => value.2.1) components
  have third : direction 2 = 0 := congrArg (fun value : ℝ × ℝ × ℝ => value.2.2) components
  have radialEquation : direction 0 * (Real.sin (point 1) ^ 2 + Real.cos (point 1) ^ 2) = 0 := by
    linear_combination Real.cos (point 1) * first + Real.sin (point 1) * second
  have angularEquation : (point 0 * direction 1) * (Real.sin (point 1) ^ 2 + Real.cos (point 1) ^ 2) = 0 := by
    linear_combination -Real.sin (point 1) * first + Real.cos (point 1) * second
  have radial : direction 0 = 0 := by simpa only [Real.sin_sq_add_cos_sq, mul_one] using radialEquation
  have angular : point 0 * direction 1 = 0 := by simpa only [Real.sin_sq_add_cos_sq, mul_one] using angularEquation
  have angleZero := (mul_eq_zero.mp angular).resolve_left nonzero
  ext coordinate
  fin_cases coordinate <;> simp [radial, angleZero, third]

end Grad.PhysicalGeometry
