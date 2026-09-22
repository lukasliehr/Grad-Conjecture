import BL28FiniteTrace
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def finiteLiftToCompletion {dimension grade : ℕ} (parameters : PhaseParameters) :
    FiniteBoundaryData dimension →ₗ[ℂ] AGrade parameters dimension grade :=
  (aGradeEta parameters).toLinearMap.comp
    (GradeCore.ofCoreLinear.comp (finiteLiftLinear parameters dimension))

theorem finiteLiftToCompletion_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) :
    ‖finiteLiftToCompletion (grade := grade) parameters values‖ ≤
      Real.sqrt (originalLiftCellConstant parameters grade) *
        ‖finiteBoundaryToGrade parameters grade gradePositive values‖ := by
  change ‖aGradeEta parameters (GradeCore.ofCoreLinear (finiteLiftLinear parameters dimension values))‖ ≤ _
  rw [aGradeEta_norm]
  exact finiteLiftLinear_relative_norm parameters values grade gradePositive

/-- Bounded extension of the literal finite Fourier/exponential lift into
the original A-grade completion, with the exact half-order boundary domain. -/
def completedBoundaryLift {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
      AGrade parameters dimension grade :=
  (finiteLiftToCompletion parameters).extendOfNorm
    (finiteBoundaryToGrade parameters grade gradePositive)

theorem completedBoundaryLift_finite {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) :
    completedBoundaryLift parameters grade gradePositive
      (finiteBoundaryToGrade parameters grade gradePositive values) =
        aGradeEta parameters (GradeCore.ofCoreLinear (finiteLiftLinear parameters dimension values)) := by
  exact LinearMap.extendOfNorm_eq (finiteBoundaryToGrade_dense parameters grade gradePositive)
    ⟨Real.sqrt (originalLiftCellConstant parameters grade),
      finiteLiftToCompletion_norm_le parameters gradePositive⟩ values

theorem completedBoundaryLift_norm_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    ‖completedBoundaryLift (dimension := dimension) parameters grade gradePositive‖ ≤
      Real.sqrt (originalLiftCellConstant parameters grade) :=
  LinearMap.opNorm_extendOfNorm_le (finiteBoundaryToGrade_dense parameters grade gradePositive)
    (Real.sqrt_nonneg _) (finiteLiftToCompletion_norm_le parameters gradePositive)

theorem completedBoundaryLift_trace {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    (completedTrace parameters grade gradePositive).comp
      (completedBoundaryLift (dimension := dimension) parameters grade gradePositive) =
        ContinuousLinearMap.id ℂ (BoundaryGrade parameters (ComplexEuclidean dimension) grade) := by
  apply DFunLike.ext
  have equalFunctions := (finiteBoundaryToGrade_dense (dimension := dimension)
    parameters grade gradePositive).equalizer
      ((completedTrace parameters grade gradePositive).comp
        (completedBoundaryLift parameters grade gradePositive)).continuous
      (ContinuousLinearMap.id ℂ (BoundaryGrade parameters (ComplexEuclidean dimension) grade)).continuous (by
        funext values
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          completedBoundaryLift_finite, finiteLiftLinear_completed_trace,
          ContinuousLinearMap.id_apply])
  exact congrFun equalFunctions

theorem completedBoundaryLift_trace_apply {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryGrade parameters (ComplexEuclidean dimension) grade) :
    completedTrace parameters grade gradePositive
      (completedBoundaryLift parameters grade gradePositive values) = values :=
  DFunLike.congr_fun (completedBoundaryLift_trace parameters grade gradePositive) values

end Grad.BoundaryLift
