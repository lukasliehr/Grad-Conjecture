import AKDQ9SecondIntegratedForce

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

variable {Domain : Type} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]

theorem tripleDeterminant_eq (first second third : Vec) :
    tripleDeterminant first second third =
      first 0 * second 1 * third 2 - first 0 * second 2 * third 1 -
      first 1 * second 0 * third 2 + first 1 * second 2 * third 0 +
      first 2 * second 0 * third 1 - first 2 * second 1 * third 0 := by
  change Matrix.det !![first 0, second 0, third 0;
    first 1, second 1, third 1; first 2, second 2, third 2] = _
  rw [Matrix.det_fin_three]
  change first 0 * second 1 * third 2 - first 0 * third 1 * second 2 -
    second 0 * first 1 * third 2 + second 0 * third 1 * first 2 +
    third 0 * first 1 * second 2 - third 0 * second 1 * first 2 = _
  ring

theorem tripleDeterminant_contDiffOn {first second third : Domain → Vec} {domain : Set Domain}
    (firstSmooth : ContDiffOn ℝ ∞ first domain) (secondSmooth : ContDiffOn ℝ ∞ second domain)
    (thirdSmooth : ContDiffOn ℝ ∞ third domain) :
    ContDiffOn ℝ ∞ (fun point => tripleDeterminant (first point) (second point) (third point)) domain := by
  have firstCoordinates (coordinate : Fin 3) : ContDiffOn ℝ ∞ (fun point => first point coordinate) domain :=
    (Grad.PhysicalFamily.SampledFullGeometry.vecCoordinateCLM coordinate).contDiff.comp_contDiffOn firstSmooth
  have secondCoordinates (coordinate : Fin 3) : ContDiffOn ℝ ∞ (fun point => second point coordinate) domain :=
    (Grad.PhysicalFamily.SampledFullGeometry.vecCoordinateCLM coordinate).contDiff.comp_contDiffOn secondSmooth
  have thirdCoordinates (coordinate : Fin 3) : ContDiffOn ℝ ∞ (fun point => third point coordinate) domain :=
    (Grad.PhysicalFamily.SampledFullGeometry.vecCoordinateCLM coordinate).contDiff.comp_contDiffOn thirdSmooth
  have term (a b c : Fin 3) : ContDiffOn ℝ ∞ (fun point => first point a * second point b * third point c) domain :=
    ((firstCoordinates a).mul (secondCoordinates b)).mul (thirdCoordinates c)
  simp only [tripleDeterminant_eq]
  exact (((((term 0 1 2).sub (term 0 2 1)).sub (term 1 0 2)).add (term 1 2 0)).add (term 2 0 1)).sub (term 2 1 0)

/-- The fourth literal cell equation fixes the angular derivative of the
actual coordinate determinant, without a division at the axis. -/
theorem literal_determinant_angular_zero (length epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (radius : ℝ) (radiusLarge : 1 < radius)
    (mappingSmooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (fourthZero : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time,
      fourthCellRow length epsilon mapping point time = 0)
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    diskAngular (fun argument cell => tripleDeterminant (diskEuler mapping argument cell)
      (diskAngular mapping argument cell) (affineStateDerivative length epsilon mapping argument cell))
      point time = 0 := by
  have smooth : ContDiffOn ℝ ∞ (Function.uncurry (fun argument cell =>
      tripleDeterminant (diskEuler mapping argument cell) (diskAngular mapping argument cell)
        (affineStateDerivative length epsilon mapping argument cell))) (Metric.ball 0 radius ×ˢ univ) :=
    tripleDeterminant_contDiffOn (diskEuler_joint_smooth mappingSmooth)
    (diskAngular_joint_smooth mappingSmooth) (affineStateDerivative_joint_smooth length epsilon mappingSmooth)
  exact projected_zero_diskAngular _ time (fun argument bound => fourthZero argument bound time)
    point pointBound (smooth_spatial_differentiable smooth point (by simpa using pointBound.trans_lt radiusLarge) time)

end Grad.PhysicalEquilibrium
