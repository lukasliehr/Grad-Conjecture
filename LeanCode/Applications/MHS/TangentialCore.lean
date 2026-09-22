import EquivariantAverageProjection

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

def equivariantAverageCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 2 :=
  (valueMapCore positiveHelicity parameters).comp (angularCore parameters 1) +
    (valueMapCore negativeHelicity parameters).comp (angularCore parameters (-1))

def reflectedVectorCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 2 :=
  (valueMapCore reflectionValueMap parameters).comp
    (orthogonalCore parameters cartesianReflectionEquiv)

/-- The actual N3 tangential projection on original, all-grade coefficients. -/
def tangentialCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 2 :=
  (1 / 2 : ℂ) • ((LinearMap.id - reflectedVectorCore parameters).comp
    (equivariantAverageCore parameters))

@[simp] theorem equivariantAverageCore_apply (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    (equivariantAverageCore parameters field).1 cell = equivariantAverageJet (field.1 cell) := rfl

@[simp] theorem reflectedVectorCore_apply (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    (reflectedVectorCore parameters field).1 cell = reflectedVectorJet (field.1 cell) := rfl

@[simp] theorem tangentialCore_apply (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    (tangentialCore parameters field).1 cell = tangentialJet (field.1 cell) := rfl

theorem tangentialCore_idempotent (parameters : PhaseParameters) (field : ACore parameters 2) :
    tangentialCore parameters (tangentialCore parameters field) = tangentialCore parameters field := by
  apply Subtype.ext
  funext cell
  exact tangentialJet_idempotent (field.1 cell)

def valueMapGradeCore {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) :
    GradeCore parameters sourceDimension grade →ₗ[ℂ] GradeCore parameters targetDimension grade :=
  GradeCore.ofCoreLinear.comp ((valueMapCore mapping parameters).comp GradeCore.toCoreLinear)

theorem valueMapGradeCore_norm_le {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (field : GradeCore parameters sourceDimension grade) :
    ‖valueMapGradeCore mapping parameters field‖ ≤ ‖mapping‖ * ‖field‖ := by
  change ‖GradeCore.ofCoreLinear (valueMapCore mapping parameters field.toCore)‖ ≤ _
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact valueMapCore_coordinates_bound mapping parameters field.toCore grade

def valueMapGradeCoreContinuous {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) :
    GradeCore parameters sourceDimension grade →L[ℂ] GradeCore parameters targetDimension grade :=
  (valueMapGradeCore mapping parameters).mkContinuous ‖mapping‖
    (valueMapGradeCore_norm_le mapping parameters)

def equivariantAverageGradeCore {grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters 2 grade →L[ℂ] GradeCore parameters 2 grade :=
  (valueMapGradeCoreContinuous positiveHelicity parameters).comp
      (angularGradeCoreContinuous parameters 1) +
    (valueMapGradeCoreContinuous negativeHelicity parameters).comp
      (angularGradeCoreContinuous parameters (-1))

def reflectedVectorGradeCore {grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters 2 grade →L[ℂ] GradeCore parameters 2 grade :=
  (valueMapGradeCoreContinuous reflectionValueMap parameters).comp
    (orthogonalGradeCoreContinuous parameters cartesianReflectionEquiv)

def tangentialGradeCore {grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters 2 grade →L[ℂ] GradeCore parameters 2 grade :=
  (1 / 2 : ℂ) • ((ContinuousLinearMap.id ℂ _ - reflectedVectorGradeCore parameters).comp
    (equivariantAverageGradeCore parameters))

@[simp] theorem tangentialGradeCore_toCore {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    (tangentialGradeCore parameters field).toCore = tangentialCore parameters field.toCore := rfl

theorem tangentialGradeCore_idempotent {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    tangentialGradeCore parameters (tangentialGradeCore parameters field) =
      tangentialGradeCore parameters field := by
  apply GradeCore.toCore_injective
  exact tangentialCore_idempotent parameters field.toCore

def averageGradeConstant (grade : ℕ) : ℝ :=
  (‖positiveHelicity‖ + ‖negativeHelicity‖) * orthogonalGradeConstant grade

def tangentialGradeConstant (grade : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 + ‖reflectionValueMap‖ * orthogonalGradeConstant grade) *
    averageGradeConstant grade

theorem averageGradeConstant_nonnegative (grade : ℕ) : 0 ≤ averageGradeConstant grade :=
  mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (orthogonalGradeConstant_nonnegative grade)

theorem tangentialGradeConstant_nonnegative (grade : ℕ) : 0 ≤ tangentialGradeConstant grade := by
  have averageNonnegative := averageGradeConstant_nonnegative grade
  have orthogonalNonnegative := orthogonalGradeConstant_nonnegative grade
  unfold tangentialGradeConstant
  positivity

theorem equivariantAverageGradeCore_norm_le {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    ‖equivariantAverageGradeCore parameters field‖ ≤ averageGradeConstant grade * ‖field‖ := by
  change ‖valueMapGradeCore positiveHelicity parameters (angularGradeCore parameters 1 field) +
    valueMapGradeCore negativeHelicity parameters (angularGradeCore parameters (-1) field)‖ ≤ _
  calc
    _ ≤ ‖valueMapGradeCore positiveHelicity parameters (angularGradeCore parameters 1 field)‖ +
        ‖valueMapGradeCore negativeHelicity parameters (angularGradeCore parameters (-1) field)‖ :=
      norm_add_le _ _
    _ ≤ ‖positiveHelicity‖ * (orthogonalGradeConstant grade * ‖field‖) +
        ‖negativeHelicity‖ * (orthogonalGradeConstant grade * ‖field‖) :=
      add_le_add
        ((valueMapGradeCore_norm_le _ _ _).trans (mul_le_mul_of_nonneg_left
          (angularGradeCore_norm_le parameters 1 field) (norm_nonneg _)))
        ((valueMapGradeCore_norm_le _ _ _).trans (mul_le_mul_of_nonneg_left
          (angularGradeCore_norm_le parameters (-1) field) (norm_nonneg _)))
    _ = _ := by unfold averageGradeConstant; ring

theorem reflectedVectorGradeCore_norm_le {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    ‖reflectedVectorGradeCore parameters field‖ ≤
      (‖reflectionValueMap‖ * orthogonalGradeConstant grade) * ‖field‖ := by
  exact (valueMapGradeCore_norm_le reflectionValueMap parameters _).trans
    ((mul_le_mul_of_nonneg_left
      (orthogonalGradeCore_norm_le parameters cartesianReflectionEquiv field) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _).symm)

theorem tangentialGradeCore_norm_le {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    ‖tangentialGradeCore parameters field‖ ≤ tangentialGradeConstant grade * ‖field‖ := by
  have reflectedNonnegative : 0 ≤ ‖reflectionValueMap‖ * orthogonalGradeConstant grade :=
    mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative grade)
  change ‖(1 / 2 : ℂ) • (equivariantAverageGradeCore parameters field -
    reflectedVectorGradeCore parameters (equivariantAverageGradeCore parameters field))‖ ≤ _
  rw [norm_smul]
  rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖equivariantAverageGradeCore parameters field‖ +
        ‖reflectedVectorGradeCore parameters (equivariantAverageGradeCore parameters field)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (averageGradeConstant grade * ‖field‖ +
        (‖reflectionValueMap‖ * orthogonalGradeConstant grade) *
          (averageGradeConstant grade * ‖field‖)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (equivariantAverageGradeCore_norm_le parameters field)
          ((reflectedVectorGradeCore_norm_le parameters _).trans (mul_le_mul_of_nonneg_left
            (equivariantAverageGradeCore_norm_le parameters field) reflectedNonnegative))) (by norm_num)
    _ = _ := by unfold tangentialGradeConstant; ring

end Grad.Constraints
