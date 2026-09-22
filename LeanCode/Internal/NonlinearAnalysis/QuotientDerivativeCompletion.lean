import QuotientDerivativeCore

noncomputable section

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def partialGradeCore {dimension grade : ℕ} (parameters : PhaseParameters) (direction : Fin 2) :
    GradeCore parameters dimension (grade + 1) →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((partialCore parameters direction).comp GradeCore.toCoreLinear)

theorem partialGradeCore_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : GradeCore parameters dimension (grade + 1)) :
    ‖partialGradeCore parameters direction field‖ ≤ partialGradeConstant grade * ‖field‖ :=
  partialCore_bound parameters direction field.toCore grade

def partialCompleted {dimension grade : ℕ} (parameters : PhaseParameters) (direction : Fin 2) :
    AGrade parameters dimension (grade + 1) →L[ℂ] AGrade parameters dimension grade :=
  denseCoreExtension parameters
    ((aGradeEta parameters).toLinearMap.comp (partialGradeCore parameters direction))
    (partialGradeConstant grade) (fun field => by
      change ‖aGradeEta parameters (partialGradeCore parameters direction field)‖ ≤ _
      rw [aGradeEta_norm]
      exact partialGradeCore_bound parameters direction field)

theorem partialCompleted_eta {dimension grade : ℕ} (parameters : PhaseParameters) (direction : Fin 2)
    (field : ACore parameters dimension) :
    partialCompleted (grade := grade) parameters direction
        (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (partialCore parameters direction field)) :=
  denseCoreExtension_apply_eta parameters _ _ _ _

theorem partialCompleted_bound {dimension grade : ℕ} (parameters : PhaseParameters) (direction : Fin 2)
    (field : AGrade parameters dimension (grade + 1)) :
    ‖partialCompleted parameters direction field‖ ≤ partialGradeConstant grade * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

theorem partialCompleted_unique {dimension grade : ℕ} (parameters : PhaseParameters) (direction : Fin 2)
    (other : AGrade parameters dimension (grade + 1) →L[ℂ] AGrade parameters dimension grade)
    (coreLaw : ∀ field : ACore parameters dimension,
      other (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
        aGradeEta parameters (GradeCore.ofCoreLinear (partialCore parameters direction field))) :
    other = partialCompleted parameters direction := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  exact (coreLaw field.toCore).trans (partialCompleted_eta parameters direction field.toCore).symm

theorem actual_cartesian_derivative_completed : CartesianDerivativeCompletedGoal := by
  refine ⟨partialGradeConstant, partialGradeConstant_nonnegative, ?_⟩
  intro parameters dimension direction
  refine ⟨partialCore parameters direction, partialCore_actual parameters direction, ?_⟩
  intro grade
  exact ⟨partialCompleted parameters direction, partialCompleted_eta parameters direction,
    partialCompleted_bound parameters direction⟩

end Grad.NonlinearQuotientBounds
