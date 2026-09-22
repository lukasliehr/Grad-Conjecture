import BL33ZeroInner

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def boundarySingleData {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    FiniteBoundaryData dimension := Finsupp.single mode.2 (Finsupp.single mode.1 value)

theorem finiteLiftLinear_single_cell {dimension : ℕ} (parameters : PhaseParameters)
    (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) (cell : ℤ) :
    (finiteLiftLinear parameters dimension (boundarySingleData mode value)).1 cell =
      if cell = mode.2 then boundaryModeJet mode value else 0 := by
  classical
  rw [finiteLiftLinear_cell]
  by_cases equal : cell = mode.2
  · subst cell
    simp only [boundarySingleData, Finsupp.single_eq_same, if_true]
    rw [angularFiniteJetLinear, Finsupp.lsum_single]
    rfl
  · simp [boundarySingleData, equal]

def boundaryDerivativeSummand {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ)
    (values : BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3))
    (mode : ℤ × ℤ) : C(ClosedDisk, ComplexEuclidean dimension) :=
  if cell = mode.2 then closedDerivative
    (boundaryModeJet mode (boundaryCoefficient parameters (order + 3) values mode)) order word else 0

theorem completedLiftCellDerivative_single {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ)
    (values : BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3)) (mode : ℤ × ℤ) :
    completedLiftCellDerivative parameters order word cell (lp.single 2 mode (values mode)) =
      boundaryDerivativeSummand parameters order word cell values mode := by
  classical
  rw [← finiteBoundaryToGrade_single parameters (order + 3) (by omega) mode (values mode)]
  rw [completedLiftCellDerivative, ContinuousLinearMap.comp_apply, completedBoundaryLift_finite,
    completedCellDerivative_eta]
  change closedDerivative
    ((finiteLiftLinear parameters dimension (boundarySingleData mode
      (boundaryCoefficient parameters (order + 3) values mode))).1 cell) order word = _
  rw [finiteLiftLinear_single_cell]
  by_cases equal : cell = mode.2
  · rw [if_pos equal, boundaryDerivativeSummand, if_pos equal]
  · rw [if_neg equal, boundaryDerivativeSummand, if_neg equal]
    exact (closedDerivativeLinear order word).map_zero

theorem completedLiftCellDerivative_hasSum {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ)
    (values : BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3)) :
    HasSum (boundaryDerivativeSummand parameters order word cell values)
      (completedLiftCellDerivative parameters order word cell values) := by
  have sum := (completedLiftCellDerivative parameters order word cell).hasSum
    (lp.hasSum_single (by norm_num) values)
  simpa only [completedLiftCellDerivative_single] using sum

theorem boundaryLift_derivative_hasSum {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (order : ℕ) (word : CartesianWord order) (cell : ℤ) :
    HasSum (fun mode : ℤ × ℤ => if cell = mode.2 then
        closedDerivative (boundaryModeJet mode (values.1 mode)) order word else 0)
      (closedDerivative ((boundaryLift parameters values).1 cell) order word) := by
  have sum := completedLiftCellDerivative_hasSum parameters order word cell
    (boundaryToGrade parameters (order + 3) (by omega) values)
  change HasSum (fun mode : ℤ × ℤ => if cell = mode.2 then
    closedDerivative (boundaryModeJet mode (boundaryCoefficient parameters (order + 3)
      (boundaryToGrade parameters (order + 3) (by omega) values) mode)) order word else 0)
    (completedLiftCellDerivative parameters order word cell
      (boundaryToGrade parameters (order + 3) (by omega) values)) at sum
  simp_rw [boundaryToGrade_coefficient] at sum
  simpa only [completedLiftCellDerivative_core] using sum

end Grad.BoundaryLift
