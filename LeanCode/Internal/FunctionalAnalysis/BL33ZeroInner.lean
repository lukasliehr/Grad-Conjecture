import BL32JetEvaluation

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem finiteKernelField_zero_inner {dimension : ℕ} (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane)
    (inside : ‖point‖ ≤ (7 / 8 : ℝ)) : finiteKernelField cell modes values point = 0 := by
  unfold finiteKernelField
  simp_rw [boundaryKernel_zero_inner _ point inside, zero_smul]
  exact Finset.sum_const_zero

theorem finiteBoundaryJet_derivative_zero_inner {dimension : ℕ} (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension)
    (order : ℕ) (word : CartesianWord order) (point : ClosedDisk)
    (inside : ‖point.val‖ ≤ (3 / 4 : ℝ)) :
    closedDerivative (finiteBoundaryJet cell modes values) order word point = 0 := by
  have pointIn : point.val ∈ Metric.ball (0 : SpatialPlane) (7 / 8 : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have agreement : finiteKernelField cell modes values =ᶠ[𝓝 point.val]
      (0 : SpatialPlane → ComplexEuclidean dimension) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds pointIn] with source sourceIn
    apply finiteKernelField_zero_inner
    simpa only [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp sourceIn).le
  have derivative := (agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds
  rw [finiteBoundaryJet, globalClosedJet_derivative, cartesianDerivative, derivative]
  simp only [iteratedFDeriv_zero, Pi.zero_apply, zero_apply]

theorem completedLiftCellDerivative_zero_inner {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) (point : ClosedDisk)
    (inside : ‖point.val‖ ≤ (3 / 4 : ℝ))
    (values : BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3)) :
    completedLiftCellDerivative parameters order word cell values point = 0 := by
  let evaluation := (ContinuousMap.evalCLM ℂ point).comp
    (completedLiftCellDerivative (dimension := dimension) parameters order word cell)
  have equalFunctions := (finiteBoundaryToGrade_dense (dimension := dimension)
    parameters (order + 3) (by omega)).equalizer evaluation.continuous
      (continuous_const : Continuous (fun _ : BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3) =>
        (0 : ComplexEuclidean dimension))) (by
        funext data
        change completedLiftCellDerivative parameters order word cell
          (finiteBoundaryToGrade parameters (order + 3) (by omega) data) point = 0
        rw [completedLiftCellDerivative_finite]
        exact finiteBoundaryJet_derivative_zero_inner cell (data cell).support (data cell)
          order word point inside)
  exact congrFun equalFunctions values

theorem boundaryLift_zero_inner_all_derivatives {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (cell : ℤ) (order : ℕ) (word : CartesianWord order)
    (point : ClosedDisk) (inside : ‖point.val‖ ≤ (3 / 4 : ℝ)) :
    closedDerivative ((boundaryLift parameters values).1 cell) order word point = 0 := by
  rw [← completedLiftCellDerivative_core parameters order word cell values]
  exact completedLiftCellDerivative_zero_inner parameters order word cell point inside _

theorem boundaryLift_zero_inner {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (cell : ℤ)
    (point : ClosedDisk) (inside : ‖point.val‖ ≤ (3 / 4 : ℝ)) :
    ((boundaryLift parameters values).1 cell).value point = 0 := by
  rw [← closedDerivative_zero_order]
  exact boundaryLift_zero_inner_all_derivatives parameters values cell 0 emptyCartesianWord point inside

end Grad.BoundaryLift
