import BL23OriginalCell
import Mathlib.LinearAlgebra.Finsupp.LSum

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def jetValueLinear {dimension : ℕ} (point : ClosedDisk) : ClosedJet dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun field := field.value point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def boundaryModeJetLinear (dimension : ℕ) (mode : ℤ × ℤ) :
    ComplexEuclidean dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := boundaryModeJet mode
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_add _ _ _
  map_smul' scalar value := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_comm _ _ _

def angularFiniteJetLinear (dimension : ℕ) (cell : ℤ) :
    (ℤ →₀ ComplexEuclidean dimension) →ₗ[ℂ] ClosedJet dimension :=
  Finsupp.lsum ℂ (fun mode => boundaryModeJetLinear dimension (mode, cell))

theorem angularFiniteJetLinear_eq {dimension : ℕ} (cell : ℤ) (values : ℤ →₀ ComplexEuclidean dimension) :
    angularFiniteJetLinear dimension cell values = finiteBoundaryJet cell values.support values := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change jetValueLinear point (angularFiniteJetLinear dimension cell values) = _
  rw [angularFiniteJetLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  rfl

def singletonOriginalCore {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) : ACore parameters dimension := by
  refine ⟨fun output => if output = cell then field else 0, ?_⟩
  intro grade
  rw [memlp_iff_summable_sq]
  apply ((hasSum_ite_eq cell (‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2)).summable).congr
  intro output
  by_cases equal : output = cell
  · subst output
    simp [rawCartesianGradeCoordinates]
  · simp [rawCartesianGradeCoordinates, equal]

def singletonOriginalCoreLinear (parameters : PhaseParameters) (dimension : ℕ) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] ACore parameters dimension where
  toFun := singletonOriginalCore parameters cell
  map_add' first second := by
    apply Subtype.ext
    funext output
    by_cases equal : output = cell <;> simp [singletonOriginalCore, equal]
  map_smul' scalar field := by
    apply Subtype.ext
    funext output
    by_cases equal : output = cell <;> simp [singletonOriginalCore, equal]

abbrev FiniteBoundaryData (dimension : ℕ) := ℤ →₀ ℤ →₀ ComplexEuclidean dimension

def finiteLiftLinear (parameters : PhaseParameters) (dimension : ℕ) :
    FiniteBoundaryData dimension →ₗ[ℂ] ACore parameters dimension :=
  Finsupp.lsum ℂ (fun cell =>
    (singletonOriginalCoreLinear parameters dimension cell).comp (angularFiniteJetLinear dimension cell))

def originalCellEvaluation {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    ACore parameters dimension →ₗ[ℂ] ClosedJet dimension where
  toFun field := field.1 cell
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteLiftLinear_cell {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (output : ℤ) :
    (finiteLiftLinear parameters dimension values).1 output = angularFiniteJetLinear dimension output (values output) := by
  classical
  change originalCellEvaluation parameters output (finiteLiftLinear parameters dimension values) = _
  rw [finiteLiftLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ cell ∈ values.support,
    if output = cell then angularFiniteJetLinear dimension cell (values cell) else 0) = _
  rw [Finset.sum_ite_eq]
  by_cases member : output ∈ values.support
  · rw [if_pos member]
  · have zeroValue : values output = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
    rw [if_neg member, zeroValue, map_zero]

theorem finiteLiftLinear_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) (finiteLiftLinear parameters dimension values)‖ ^ 2 =
      ∑ cell ∈ values.support, ‖cellGradeRowLinear (grade := grade) parameters cell
        (angularFiniteJetLinear dimension cell (values cell))‖ ^ 2 := by
  rw [originalGrade_norm_sq_eq_rows]
  simp_rw [finiteLiftLinear_cell]
  apply tsum_eq_sum
  intro cell notIn
  have zeroValue : values cell = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using notIn
  rw [zeroValue, map_zero, map_zero, norm_zero, zero_pow (by norm_num)]

theorem finiteLiftLinear_original_bound {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖GradeCore.ofCoreLinear (grade := grade) (finiteLiftLinear parameters dimension values)‖ ^ 2 ≤
      originalLiftCellConstant parameters grade * ∑ cell ∈ values.support, ∑ mode ∈ (values cell).support,
        Real.exp (2 * boundaryPhase parameters cell) * boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
          ‖values cell mode‖ ^ 2 := by
  rw [finiteLiftLinear_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro cell _
  rw [angularFiniteJetLinear_eq]
  exact finiteBoundaryJet_original_bound parameters cell (values cell).support (values cell) grade gradePositive

end Grad.BoundaryLift
