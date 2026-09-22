import QuotientConstantFields

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

theorem cellGradeRow_valueMap_bound {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (jet : ClosedJet sourceDimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (valueMapJet mapping jet)‖ ≤
      ‖mapping‖ * ‖cellGradeRowLinear (grade := grade) parameters cell jet‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cellGradeRow_norm_sq, cellGradeRow_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  have derivativeForm :
      closedMultiDerivative (phaseWeightedJet parameters cell (valueMapJet mapping jet))
        index.toCartesian =
      valueMapClosed mapping
        (closedMultiDerivative (phaseWeightedJet parameters cell jet) index.toCartesian) := by
    rw [← valueMapJet_phaseWeighted]
    exact valueMapJet_derivative mapping (phaseWeightedJet parameters cell jet) _
  rw [derivativeForm]
  have entryBound := closedValueL2_valueMap_norm_le mapping
    (closedMultiDerivative (phaseWeightedJet parameters cell jet) index.toCartesian)
  calc cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
        ‖closedContinuousToDiskL2 (valueMapClosed mapping
          (closedMultiDerivative (phaseWeightedJet parameters cell jet) index.toCartesian))‖ ^ 2 ≤
      cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
        (‖mapping‖ * ‖closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters cell jet) index.toCartesian)‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) entryBound 2)
          (pow_nonneg (cellFrequency_pos cell).le _)
    _ = ‖mapping‖ ^ 2 * (cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
        ‖closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters cell jet) index.toCartesian)‖ ^ 2) := by
        ring

theorem valueMap_mem_originalCore {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) :
    (fun cell => valueMapJet mapping (field.val cell)) ∈
      originalCoreSubmodule parameters targetDimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (original.mul_left (‖mapping‖ ^ 2))
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (cellGradeRow_valueMap_bound (grade := grade) parameters cell mapping (field.val cell)) 2
  simpa only [mul_pow, rawCartesianGradeCoordinates] using bound

/-- Application of a fixed complex-linear value map in the original core:
same grade, operator-norm constant. -/
def valueMapCore (parameters : PhaseParameters) {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ACore parameters sourceDimension →ₗ[ℂ] ACore parameters targetDimension where
  toFun field := ⟨fun cell => valueMapJet mapping (field.val cell),
    valueMap_mem_originalCore parameters mapping field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact (valueMapJetLinear sourceDimension targetDimension mapping).map_add
      (first.val cell) (second.val cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact (valueMapJetLinear sourceDimension targetDimension mapping).map_smul
      scalar (field.val cell)

theorem valueMapCore_val {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) (cell : ℤ) :
    (valueMapCore parameters mapping field).val cell = valueMapJet mapping (field.val cell) := rfl

theorem valueMapCore_value {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) (cell : ℤ) (point : ClosedDisk) :
    ((valueMapCore parameters mapping field).val cell).value point =
      mapping ((field.val cell).value point) :=
  valueMapJet_value mapping (field.val cell) point

theorem valueMapCore_coordinates_bound {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (valueMapCore parameters mapping field)‖ ≤
      ‖mapping‖ * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have transformed := (memlp_iff_summable_sq _).mp
    ((valueMapCore parameters mapping field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, valueMapCore_val] using
      pow_le_pow_left₀ (norm_nonneg _)
        (cellGradeRow_valueMap_bound (grade := grade) parameters cell mapping (field.val cell)) 2)
    (original.mul_left (‖mapping‖ ^ 2))
  rw [tsum_mul_left] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

theorem valueMapCore_bound {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) (grade : ℕ) :
    originalGradeNorm grade (valueMapCore parameters mapping field) ≤
      ‖mapping‖ * originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact valueMapCore_coordinates_bound parameters mapping field grade

/-- The fixed tangent generator `A x = (-x₁, x₀, 0)` of the affine state. -/
def tangentGeneratorMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 0).smulRight (EuclideanSpace.single 1 1) -
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 1).smulRight (EuclideanSpace.single 0 1)

theorem tangentGeneratorMap_value (vector : ComplexEuclidean 3) :
    tangentGeneratorMap vector = Grad.NonlinearQuotient.complexTangentGenerator vector := by
  unfold tangentGeneratorMap Grad.NonlinearQuotient.complexTangentGenerator
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.smulRight_apply]

end Grad.NonlinearQuotientBounds
