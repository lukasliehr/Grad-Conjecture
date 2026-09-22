import OrthogonalGradeBound
import FC5Proof

noncomputable section

open Grad.ClosedJets Grad.CartesianState
open scoped BigOperators

namespace Grad.Constraints

theorem orthogonal_core_membership {dimension : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ACore parameters dimension) :
    (fun cell => orthogonalJet orthogonal (field.1 cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (original.mul_left (orthogonalGradeConstant grade ^ 2))
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (orthogonal_grade_row_bound (grade := grade) parameters cell orthogonal (field.1 cell)) 2
  simpa only [mul_pow, rawCartesianGradeCoordinates] using bound

/-- Rotation or reflection of the original coefficients, before any phase
weighting; one map preserves every integer grade. -/
def orthogonalCore {dimension : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => orthogonalJet orthogonal (field.1 cell),
    orthogonal_core_membership parameters orthogonal field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact (orthogonalJetLinear dimension orthogonal).map_add (first.1 cell) (second.1 cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact (orthogonalJetLinear dimension orthogonal).map_smul scalar (field.1 cell)

@[simp] theorem orthogonalCore_apply {dimension : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ACore parameters dimension) (cell : ℤ) :
    (orthogonalCore parameters orthogonal field).1 cell = orthogonalJet orthogonal (field.1 cell) := rfl

theorem orthogonalCore_coordinates_bound {dimension : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ACore parameters dimension)
    (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (orthogonalCore parameters orthogonal field)‖ ≤
      orthogonalGradeConstant grade * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (orthogonalGradeConstant_nonnegative grade)
    (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have transformed := (memlp_iff_summable_sq _).mp
    ((orthogonalCore parameters orthogonal field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, orthogonalCore_apply] using pow_le_pow_left₀ (norm_nonneg _)
      (orthogonal_grade_row_bound (grade := grade) parameters cell orthogonal (field.1 cell)) 2)
    (original.mul_left (orthogonalGradeConstant grade ^ 2))
  rw [tsum_mul_left] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

def orthogonalGradeCore {dimension grade : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    GradeCore parameters dimension grade →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((orthogonalCore parameters orthogonal).comp GradeCore.toCoreLinear)

theorem orthogonalGradeCore_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : GradeCore parameters dimension grade) :
    ‖orthogonalGradeCore parameters orthogonal field‖ ≤ orthogonalGradeConstant grade * ‖field‖ := by
  change ‖GradeCore.ofCoreLinear (orthogonalCore parameters orthogonal field.toCore)‖ ≤ _
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact orthogonalCore_coordinates_bound parameters orthogonal field.toCore grade

def orthogonalGradeCoreContinuous {dimension grade : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade :=
  (orthogonalGradeCore parameters orthogonal).mkContinuous (orthogonalGradeConstant grade)
    (orthogonalGradeCore_norm_le parameters orthogonal)

end Grad.Constraints
