import BL34KernelSeries

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem boundaryLift_angular_derivative_hasSum {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (order : ℕ) (word : CartesianWord order) (cell : ℤ) :
    HasSum (fun mode : ℤ => closedDerivative (boundaryModeJet (mode, cell) (values.1 (mode, cell))) order word)
      (closedDerivative ((boundaryLift parameters values).1 cell) order word) := by
  classical
  have doubleSum := boundaryLift_derivative_hasSum parameters values order word cell
  have injection : Function.Injective (fun mode : ℤ => (mode, cell)) := fun _ _ equal => congrArg Prod.fst equal
  have summable : Summable (fun mode : ℤ =>
      closedDerivative (boundaryModeJet (mode, cell) (values.1 (mode, cell))) order word) := by
    exact (doubleSum.summable.comp_injective injection).congr (fun mode => by
      simp only [Function.comp_apply, ite_true])
  have inner (mode : ℤ) :
      (∑' other : ℤ, if cell = other then
        closedDerivative (boundaryModeJet (mode, other) (values.1 (mode, other))) order word else 0) =
      closedDerivative (boundaryModeJet (mode, cell) (values.1 (mode, cell))) order word := by
    rw [tsum_eq_single cell]
    · rw [if_pos rfl]
    · intro other different
      rw [if_neg (Ne.symm different)]
  have identity := doubleSum.summable.tsum_prod
  simp_rw [inner] at identity
  rw [doubleSum.tsum_eq] at identity
  exact identity.symm ▸ summable.hasSum

theorem boundaryLift_angular_value_hasSum {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    HasSum (fun mode : ℤ => boundaryKernel (mode, cell) point.val • values.1 (mode, cell))
      (((boundaryLift parameters values).1 cell).value point) := by
  have sum := (ContinuousMap.evalCLM ℂ point).hasSum
    (boundaryLift_angular_derivative_hasSum parameters values 0 emptyCartesianWord cell)
  simpa only [closedDerivative_zero_order, ContinuousMap.evalCLM_apply, boundaryModeJet_value] using sum

theorem boundaryLift_angular_value {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((boundaryLift parameters values).1 cell).value point =
      ∑' mode : ℤ, boundaryKernel (mode, cell) point.val • values.1 (mode, cell) :=
  (boundaryLift_angular_value_hasSum parameters values cell point).tsum_eq.symm

theorem boundaryLift_literal_cell {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (cell : ℤ) (point : ClosedDisk)
    (time : ℝ) (timeLe : time ≤ (1 / 4 : ℝ)) (angle : CellCircle)
    (pointLaw : point.val = (1 - time) • boundaryCirclePoint angle) :
    ((boundaryLift parameters values).1 cell).value point =
      literalBoundaryCell values.1 time angle cell := by
  rw [boundaryLift_angular_value, literalBoundaryCell, ← tsum_const_smul'']
  apply tsum_congr
  intro mode
  rw [pointLaw, boundaryKernel_polar (mode, cell) time (by linarith)]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

end Grad.BoundaryLift
