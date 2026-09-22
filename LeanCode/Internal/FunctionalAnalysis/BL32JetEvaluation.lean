import BL31SmoothCore
import OriginalCoefficientCore
import TangentialZeroJets

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def originalCellDerivativeLinear {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) :
    GradeCore parameters dimension (order + 3) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (closedDerivativeLinear order word).comp
    ((originalCellEvaluation parameters cell).comp GradeCore.toCoreLinear)

theorem originalCellDerivativeLinear_norm_le {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ)
    (field : GradeCore parameters dimension (order + 3)) :
    ‖originalCellDerivativeLinear parameters order word cell field‖ ≤
      originalDerivativeSumConstant parameters order * ‖field‖ := by
  have summable := originalClosedDerivative_frequency_summable parameters field.toCore word 0
  simp only [pow_zero, one_mul] at summable
  have bound := originalClosedDerivative_frequency_tsum_bound parameters field word 0 (by omega)
  simp only [pow_zero, one_mul] at bound
  exact (summable.le_tsum cell (fun _ _ => norm_nonneg _)).trans bound

def completedCellDerivative {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) :
    AGrade parameters dimension (order + 3) →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  denseCoreExtension parameters (originalCellDerivativeLinear parameters order word cell)
    (originalDerivativeSumConstant parameters order)
    (originalCellDerivativeLinear_norm_le parameters order word cell)

theorem completedCellDerivative_eta {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ)
    (field : GradeCore parameters dimension (order + 3)) :
    completedCellDerivative parameters order word cell (aGradeEta parameters field) =
      closedDerivative (field.toCore.1 cell) order word :=
  denseCoreExtension_apply_eta parameters _ _ _ field

def completedLiftCellDerivative {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) :
    BoundaryGrade parameters (ComplexEuclidean dimension) (order + 3) →L[ℂ]
      C(ClosedDisk, ComplexEuclidean dimension) :=
  (completedCellDerivative parameters order word cell).comp
    (completedBoundaryLift parameters (order + 3) (by omega))

theorem completedLiftCellDerivative_core {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) (values : BoundaryCore parameters dimension) :
    completedLiftCellDerivative parameters order word cell
      (boundaryToGrade parameters (order + 3) (by omega) values) =
        closedDerivative ((boundaryLift parameters values).1 cell) order word := by
  rw [completedLiftCellDerivative, ContinuousLinearMap.comp_apply, ← boundaryLift_component,
    completedCellDerivative_eta]
  rfl

theorem completedLiftCellDerivative_finite {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (word : CartesianWord order) (cell : ℤ) (values : FiniteBoundaryData dimension) :
    completedLiftCellDerivative parameters order word cell
      (finiteBoundaryToGrade parameters (order + 3) (by omega) values) =
        closedDerivative (finiteBoundaryJet cell (values cell).support (values cell)) order word := by
  rw [completedLiftCellDerivative, ContinuousLinearMap.comp_apply, completedBoundaryLift_finite,
    completedCellDerivative_eta]
  change closedDerivative ((finiteLiftLinear parameters dimension values).1 cell) order word = _
  rw [finiteLiftLinear_cell, angularFiniteJetLinear_eq]

end Grad.BoundaryLift
