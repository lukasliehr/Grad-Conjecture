import MultiplierGrade

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState

def cellTranslation (shift : ℤ) : ℤ ≃ ℤ where
  toFun cell := cell - shift
  invFun cell := cell + shift
  left_inv cell := by simp
  right_inv cell := by simp

def shiftBound (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ) : ℝ :=
  multiplierConstant grade parameters.gamma *
    Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade

theorem shiftBound_nonnegative (parameters : PhaseParameters) (grade : ℕ) (shift : ℤ) :
    0 ≤ shiftBound parameters grade shift :=
  mul_nonneg (mul_nonneg (multiplierConstant_nonnegative _ _ parameters.gamma_pos.le)
    (Real.exp_pos _).le) (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _)

theorem translated_grade_row_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell shift : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ≤
      shiftBound parameters grade shift * ‖cellGradeRowLinear (grade := grade) parameters (cell - shift) field‖ := by
  simpa only [sub_add_cancel, shiftBound] using
    shifted_grade_row_bound (grade := grade) parameters (cell - shift) shift field

theorem shift_core_membership {dimension : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (field : ACore parameters dimension) :
    (fun cell => field.1 (cell - shift)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have shifted : Summable (fun cell =>
      ‖rawCartesianGradeCoordinates parameters grade field.1 (cell - shift)‖ ^ 2) :=
    (cellTranslation shift).summable_iff.mpr original
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (shifted.mul_left (shiftBound parameters grade shift ^ 2))
  simpa only [mul_pow, rawCartesianGradeCoordinates] using pow_le_pow_left₀ (norm_nonneg _)
    (translated_grade_row_bound (grade := grade) parameters cell shift (field.1 (cell - shift))) 2

/-- Reindex the actual original unweighted coefficients. The phase still
belongs to the output cell when any original grade is measured. -/
def shiftCore {dimension : ℕ} (parameters : PhaseParameters) (shift : ℤ) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => field.1 (cell - shift), shift_core_membership parameters shift field⟩
  map_add' first second := by apply Subtype.ext; rfl
  map_smul' scalar field := by apply Subtype.ext; rfl

@[simp] theorem shiftCore_apply {dimension : ℕ} (parameters : PhaseParameters) (shift : ℤ)
    (field : ACore parameters dimension) (cell : ℤ) :
    (shiftCore parameters shift field).1 cell = field.1 (cell - shift) := rfl

theorem shiftCore_coordinates_bound {dimension : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (field : ACore parameters dimension) (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (shiftCore parameters shift field)‖ ≤
      shiftBound parameters grade shift * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (shiftBound_nonnegative _ _ _) (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have shifted : Summable (fun cell =>
      ‖rawCartesianGradeCoordinates parameters grade field.1 (cell - shift)‖ ^ 2) :=
    (cellTranslation shift).summable_iff.mpr original
  have transformed := (memlp_iff_summable_sq _).mp ((shiftCore parameters shift field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, shiftCore_apply] using pow_le_pow_left₀ (norm_nonneg _)
      (translated_grade_row_bound (grade := grade) parameters cell shift (field.1 (cell - shift))) 2)
    (shifted.mul_left (shiftBound parameters grade shift ^ 2))
  rw [tsum_mul_left] at sumBound
  have sumTranslation := (cellTranslation shift).tsum_eq
    (fun cell => ‖rawCartesianGradeCoordinates parameters grade field.1 cell‖ ^ 2)
  change (∑' cell, ‖rawCartesianGradeCoordinates parameters grade field.1 (cell - shift)‖ ^ 2) = _ at sumTranslation
  rw [sumTranslation] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

def shiftGradeCore {dimension grade : ℕ} (parameters : PhaseParameters) (shift : ℤ) :
    GradeCore parameters dimension grade →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((shiftCore parameters shift).comp GradeCore.toCoreLinear)

theorem shiftGradeCore_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (field : GradeCore parameters dimension grade) :
    ‖shiftGradeCore parameters shift field‖ ≤ shiftBound parameters grade shift * ‖field‖ := by
  change ‖GradeCore.ofCoreLinear (shiftCore parameters shift field.toCore)‖ ≤ _
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact shiftCore_coordinates_bound parameters shift field.toCore grade

def singleModeGradeCore {sourceDimension targetDimension grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    GradeCore parameters sourceDimension grade →ₗ[ℂ] GradeCore parameters targetDimension grade :=
  GradeCore.ofCoreLinear.comp
    ((valueMapCore mapping parameters).comp (GradeCore.toCoreLinear.comp (shiftGradeCore parameters shift)))

theorem singleModeGradeCore_norm_le {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : GradeCore parameters sourceDimension grade) :
    ‖singleModeGradeCore parameters shift mapping field‖ ≤
      shiftBound parameters grade shift * ‖mapping‖ * ‖field‖ := by
  have valueBound : ‖singleModeGradeCore parameters shift mapping field‖ ≤
      ‖mapping‖ * ‖shiftGradeCore parameters shift field‖ := by
    rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
      cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
      gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
    exact valueMapCore_coordinates_bound mapping parameters (shiftCore parameters shift field.toCore) grade
  apply valueBound.trans
  calc
    _ ≤ ‖mapping‖ * (shiftBound parameters grade shift * ‖field‖) :=
      mul_le_mul_of_nonneg_left (shiftGradeCore_norm_le parameters shift field) (norm_nonneg _)
    _ = _ := by ring

end Grad.Constraints.Multipliers
