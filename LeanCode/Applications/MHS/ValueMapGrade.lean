import ClosedJetValueMap
import OrthogonalCore

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

theorem valueMap_grade_coordinate_bound {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet sourceDimension)
    (index : GradeMultiIndex grade) :
    ‖cellGradeRowLinear parameters cell (valueMapJet mapping field) index‖ ≤
      ‖mapping‖ * ‖cellGradeRowLinear parameters cell field index‖ := by
  rw [cellGradeRowLinear_apply, cellGradeRowLinear_apply, ← valueMapJet_phaseWeighted]
  change ‖(cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
    closedContinuousToDiskL2 (closedDerivative (valueMapJet mapping
      (phaseWeightedJet parameters cell field)) _ (cartesianMultiIndexWord index.toCartesian))‖ ≤ _
  rw [valueMapJet_derivative, norm_smul, norm_smul]
  calc
    _ ≤ ‖(cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian)‖ *
        (‖mapping‖ * ‖closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters cell field) index.toCartesian)‖) :=
      mul_le_mul_of_nonneg_left (closedValueL2_valueMap_norm_le mapping _) (norm_nonneg _)
    _ = _ := by ring

theorem valueMap_grade_row_bound {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet sourceDimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (valueMapJet mapping field)‖ ≤
      ‖mapping‖ * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (valueMap_grade_coordinate_bound mapping parameters cell field index) 2

theorem valueMap_core_membership {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (field : ACore parameters sourceDimension) :
    (fun cell => valueMapJet mapping (field.1 cell)) ∈
      originalCoreSubmodule parameters targetDimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (original.mul_left (‖mapping‖ ^ 2))
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (valueMap_grade_row_bound (grade := grade) mapping parameters cell (field.1 cell)) 2
  simpa only [mul_pow, rawCartesianGradeCoordinates] using bound

def valueMapCore {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) :
    ACore parameters sourceDimension →ₗ[ℂ] ACore parameters targetDimension where
  toFun field := ⟨fun cell => valueMapJet mapping (field.1 cell),
    valueMap_core_membership mapping parameters field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact (valueMapJetLinear _ _ mapping).map_add (first.1 cell) (second.1 cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact (valueMapJetLinear _ _ mapping).map_smul scalar (field.1 cell)

@[simp] theorem valueMapCore_apply {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (field : ACore parameters sourceDimension) (cell : ℤ) :
    (valueMapCore mapping parameters field).1 cell = valueMapJet mapping (field.1 cell) := rfl

theorem valueMapCore_coordinates_bound {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (field : ACore parameters sourceDimension) (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (valueMapCore mapping parameters field)‖ ≤
      ‖mapping‖ * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have transformed := (memlp_iff_summable_sq _).mp
    ((valueMapCore mapping parameters field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, valueMapCore_apply] using pow_le_pow_left₀ (norm_nonneg _)
      (valueMap_grade_row_bound (grade := grade) mapping parameters cell (field.1 cell)) 2)
    (original.mul_left (‖mapping‖ ^ 2))
  rw [tsum_mul_left] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

end Grad.Constraints
