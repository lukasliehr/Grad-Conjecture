import AKDQ10IntegratedDeterminant

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.IntegerSampling

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem fixed_cell_joint_smooth {field : ℝ → ℝ → Plane → ℝ → Value}
    {epsilonZero lower upper radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (uncurriedCell field)
      (Ioo (-epsilonZero) epsilonZero ×ˢ (Ioo lower upper ×ˢ coordinateCollar radius)))
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-epsilonZero) epsilonZero)
    (parameter : ℝ) (parameterIn : parameter ∈ Ioo lower upper) :
    ContDiffOn ℝ ∞ (Function.uncurry (field epsilon parameter)) (Metric.ball 0 radius ×ˢ univ) := by
  let insertion : Plane × ℝ → CellArgument := fun point =>
    (epsilon, (parameter, coordinatePoint point.1 point.2))
  have insertionSmooth : ContDiff ℝ ∞ insertion :=
    contDiff_const.prodMk (contDiff_const.prodMk coordinatePoint_uncurried_contDiff)
  have maps : MapsTo insertion (Metric.ball 0 radius ×ˢ (univ : Set ℝ))
      (Ioo (-epsilonZero) epsilonZero ×ˢ (Ioo lower upper ×ˢ coordinateCollar radius)) := by
    intro point pointIn
    refine ⟨epsilonIn, parameterIn, ?_⟩
    change ‖coordinateDisk (coordinatePoint point.1 point.2)‖ < radius
    rw [coordinateDisk_coordinatePoint]
    simpa using pointIn.1
  apply (smooth.comp insertionSmooth.contDiffOn maps).congr
  intro point _
  simp [Function.uncurry, insertion, uncurriedCell]

/-- All three integrated identities for the SAME literal family, with no
additional differential equation, gauge or derivative premise. -/
theorem actual_cell_integrated_equations (length : ℝ) (family : CellSolutionFamily length)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    let mapping := family.v epsilon parameter.val
    (inner ℝ (diskEuler mapping point time) (diskAngular (diskAngular mapping) point time) -
      inner ℝ (diskAngular mapping point time) (diskEuler (diskAngular mapping) point time) +
      2 * ‖point‖ ^ 2 = 0) ∧
    (inner ℝ (diskAngular mapping point time) (cellDerivative (diskAngular mapping) point time) -
      inner ℝ (affineStateDerivative length epsilon mapping point time)
        (diskAngular (diskAngular mapping) point time) = 0) ∧
    diskAngular (fun argument cell => tripleDeterminant (diskEuler mapping argument cell)
      (diskAngular mapping argument cell) (affineStateDerivative length epsilon mapping argument cell))
      point time = 0 := by
  have mappingSmooth := fixed_cell_joint_smooth family.vSmooth epsilon epsilonIn parameter.val
    (parameter_mem_open length family parameter)
  have potentialSmooth := fixed_cell_joint_smooth family.wSmooth epsilon epsilonIn parameter.val
    (parameter_mem_open length family parameter)
  exact ⟨literal_first_force_numerator _ _ family.collarRadius family.collarLarge mappingSmooth potentialSmooth
      (family.firstRowZero epsilon epsilonIn parameter.val parameter.property)
      (family.secondRowZero epsilon epsilonIn parameter.val parameter.property) point pointBound time,
    literal_second_force_numerator length epsilon _ _ family.collarRadius family.collarLarge mappingSmooth potentialSmooth
      (family.firstRowZero epsilon epsilonIn parameter.val parameter.property)
      (family.thirdRowZero epsilon epsilonIn parameter.val parameter.property) point pointBound time,
    literal_determinant_angular_zero length epsilon _ family.collarRadius family.collarLarge mappingSmooth
      (family.fourthRowZero epsilon epsilonIn parameter.val parameter.property) point pointBound time⟩

end Grad.PhysicalEquilibrium
