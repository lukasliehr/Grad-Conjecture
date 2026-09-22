import AngularGradeBound
import OrthogonalCore

noncomputable section

open Grad.ClosedJets Grad.CartesianState
open scoped BigOperators

namespace Grad.Constraints

theorem angular_core_membership {dimension : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : ACore parameters dimension) :
    (fun cell => angularClosedJet mode (field.1 cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (original.mul_left (orthogonalGradeConstant grade ^ 2))
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (angular_grade_row_bound (grade := grade) parameters cell mode (field.1 cell)) 2
  simpa only [mul_pow, rawCartesianGradeCoordinates] using bound

/-- N1 on the original all-grade coefficient space; values are not rotated. -/
def angularCore {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => angularClosedJet mode (field.1 cell),
    angular_core_membership parameters mode field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact angularClosedJet_add mode (first.1 cell) (second.1 cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact angularClosedJet_smul mode scalar (field.1 cell)

@[simp] theorem angularCore_apply {dimension : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : ACore parameters dimension) (cell : ℤ) :
    (angularCore parameters mode field).1 cell = angularClosedJet mode (field.1 cell) := rfl

theorem angularCore_projection {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ℤ) (field : ACore parameters dimension) :
    angularCore parameters first (angularCore parameters second field) =
      if first = second then angularCore parameters first field else 0 := by
  apply Subtype.ext
  funext cell
  by_cases equalModes : first = second
  · simp only [equalModes, ite_true, angularCore_apply]
    simpa only [ite_true] using angularClosedJet_projection second second (field.1 cell)
  · simp only [equalModes, ite_false, angularCore_apply]
    exact (angularClosedJet_projection first second (field.1 cell)).trans (if_neg equalModes)

theorem angularCore_coordinates_bound {dimension : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : ACore parameters dimension) (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (angularCore parameters mode field)‖ ≤
      orthogonalGradeConstant grade * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (orthogonalGradeConstant_nonnegative grade)
    (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have transformed := (memlp_iff_summable_sq _).mp
    ((angularCore parameters mode field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, angularCore_apply] using pow_le_pow_left₀ (norm_nonneg _)
      (angular_grade_row_bound (grade := grade) parameters cell mode (field.1 cell)) 2)
    (original.mul_left (orthogonalGradeConstant grade ^ 2))
  rw [tsum_mul_left] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

def angularGradeCore {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ) :
    GradeCore parameters dimension grade →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((angularCore parameters mode).comp GradeCore.toCoreLinear)

theorem angularGradeCore_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : GradeCore parameters dimension grade) :
    ‖angularGradeCore parameters mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ := by
  change ‖GradeCore.ofCoreLinear (angularCore parameters mode field.toCore)‖ ≤ _
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact angularCore_coordinates_bound parameters mode field.toCore grade

def angularGradeCoreContinuous {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ) :
    GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade :=
  (angularGradeCore parameters mode).mkContinuous (orthogonalGradeConstant grade)
    (angularGradeCore_norm_le parameters mode)

end Grad.Constraints
