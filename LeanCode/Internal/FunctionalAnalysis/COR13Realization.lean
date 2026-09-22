import COR13Maps

noncomputable section

namespace Grad.COR13Completion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension

/-- The actual bounded projection onto the completed Fourier realization. -/
def realizationProjection {dimension grade : ℕ} (parameters : PhaseParameters) :
    JGrade (ComplexEuclidean dimension) grade →L[ℂ] JGrade (ComplexEuclidean dimension) grade :=
  (completedExtension parameters).comp (completedRetraction parameters)

theorem realizationProjection_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (values : JGrade (ComplexEuclidean dimension) grade) :
    realizationProjection parameters values =
      completedExtension parameters (completedRetraction parameters values) := rfl

theorem realizationProjection_idempotent {dimension grade : ℕ} (parameters : PhaseParameters) :
    (realizationProjection parameters).comp (realizationProjection parameters) =
      realizationProjection (dimension := dimension) (grade := grade) parameters := by
  ext values
  simp only [ContinuousLinearMap.comp_apply, realizationProjection_apply,
    completedRetraction_extension_apply]

theorem realizationProjection_extension {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension grade) :
    realizationProjection parameters (completedExtension parameters field) =
      completedExtension parameters field := by
  rw [realizationProjection_apply, completedRetraction_extension_apply]

theorem realizationProjection_norm_le {dimension grade : ℕ} (parameters : PhaseParameters) :
    ‖realizationProjection (dimension := dimension) (grade := grade) parameters‖ ≤
      (sameGradeConstant grade) ^ 2 := by
  calc
    _ ≤ ‖completedExtension (dimension := dimension) (grade := grade) parameters‖ *
        ‖completedRetraction parameters‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ sameGradeConstant grade * sameGradeConstant grade :=
      mul_le_mul (completedExtension_norm_le parameters) (completedRetraction_norm_le parameters)
        (norm_nonneg (completedRetraction (dimension := dimension) (grade := grade) parameters))
        (sameGradeConstant_nonnegative grade)
    _ = _ := (sq _).symm

/-- The fixed range with its inherited literal Fourier-grade norm. -/
def fixedRealization {dimension grade : ℕ} (parameters : PhaseParameters) :
    Submodule ℂ (JGrade (ComplexEuclidean dimension) grade) :=
  (realizationProjection parameters - ContinuousLinearMap.id ℂ _).ker

theorem mem_fixedRealization_iff {dimension grade : ℕ} (parameters : PhaseParameters)
    (values : JGrade (ComplexEuclidean dimension) grade) :
    values ∈ fixedRealization parameters ↔ realizationProjection parameters values = values := by
  change realizationProjection parameters values - values = 0 ↔ _
  exact sub_eq_zero

theorem fixedRealization_closed {dimension grade : ℕ} (parameters : PhaseParameters) :
    IsClosed ((fixedRealization (dimension := dimension) (grade := grade) parameters).carrier) :=
  (realizationProjection parameters - ContinuousLinearMap.id ℂ _).isClosed_ker

theorem fixedRealization_eq_range {dimension grade : ℕ} (parameters : PhaseParameters) :
    fixedRealization parameters =
      (completedExtension (dimension := dimension) (grade := grade) parameters).range := by
  ext values
  rw [mem_fixedRealization_iff]
  constructor
  · intro fixed
    exact ⟨completedRetraction parameters values, fixed⟩
  · rintro ⟨field, rfl⟩
    exact realizationProjection_extension parameters field

/-- A bounded equivalence, not an isometry: the source keeps exactly the
original completion norm and the target keeps the Fourier subspace norm. -/
def completedRealizationEquiv {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension grade ≃L[ℂ]
      fixedRealization (dimension := dimension) (grade := grade) parameters where
  toFun field := ⟨completedExtension parameters field,
    (mem_fixedRealization_iff parameters _).2 (realizationProjection_extension parameters field)⟩
  invFun values := completedRetraction parameters values
  left_inv := completedRetraction_extension_apply parameters
  right_inv values := by
    apply Subtype.ext
    exact (mem_fixedRealization_iff parameters values.1).1 values.2
  map_add' first second := by
    apply Subtype.ext
    exact map_add (completedExtension parameters) first second
  map_smul' scalar field := by
    apply Subtype.ext
    exact map_smul (completedExtension parameters) scalar field
  continuous_toFun := (completedExtension parameters).continuous.subtype_mk _
  continuous_invFun := (completedRetraction parameters).continuous.comp continuous_subtype_val

theorem completedRealizationEquiv_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension grade) :
    (completedRealizationEquiv parameters field).1 = completedExtension parameters field := rfl

theorem completedRealizationEquiv_symm_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (values : fixedRealization (dimension := dimension)
      (grade := grade) parameters) :
    (completedRealizationEquiv parameters).symm values = completedRetraction parameters values := rfl

theorem completedRealizationEquiv_norm_le {dimension grade : ℕ} (parameters : PhaseParameters) :
    ‖(completedRealizationEquiv (dimension := dimension) (grade := grade)
      parameters).toContinuousLinearMap‖ ≤ sameGradeConstant grade := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sameGradeConstant_nonnegative grade)
  intro field
  change ‖completedExtension parameters field‖ ≤ _
  exact (completedExtension parameters).le_of_opNorm_le (completedExtension_norm_le parameters) field

theorem completedRealizationEquiv_symm_norm_le {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    ‖(completedRealizationEquiv (dimension := dimension) (grade := grade)
      parameters).symm.toContinuousLinearMap‖ ≤ sameGradeConstant grade := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sameGradeConstant_nonnegative grade)
  intro values
  change ‖completedRetraction parameters values.1‖ ≤ sameGradeConstant grade * ‖values.1‖
  exact (completedRetraction parameters).le_of_opNorm_le (completedRetraction_norm_le parameters) _

end Grad.COR13Completion
