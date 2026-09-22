import BT5CollarDerivatives

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.DiskExtension.Operator

def planarWordCoefficientSum (order : ℕ) : ℝ :=
  ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖

theorem planarWordCoefficientSum_nonnegative (order : ℕ) : 0 ≤ planarWordCoefficientSum order :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem smoothClosedExtension_higherDerivative {dimension order : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    iteratedFDeriv ℝ order (smoothClosedExtension field) point.val =
      closedPlaneHigherDerivative field point.val := by
  apply continuousMultilinearMap_ext_spatialPlaneBasis
  intro word
  rw [closedPlaneHigherDerivative_basis]
  have ambientEquality : ambientClosedDisk point.val = point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem point.property
  rw [ambientEquality]
  exact smoothClosedExtension_derivative field word point

def densityGradeIndex {grade order : ℕ} (upper : order ≤ grade) (word : CartesianWord order) :
    GradeMultiIndex grade :=
  (gradeMultiIndexEquiv grade).symm ⟨cartesianWordIndex word, by rw [cartesianWordIndex_order]; exact upper⟩

theorem densityGradeIndex_order {grade order : ℕ} (upper : order ≤ grade) (word : CartesianWord order) :
    cartesianOrder (densityGradeIndex upper word).toCartesian = order := cartesianWordIndex_order word

/-- Literal original derivative density of a single weighted cell coefficient. -/
def cartesianPointDensity {dimension : ℕ} (frequency : ℝ) (grade : ℕ)
    (field : ClosedJet dimension) (point : ClosedDisk) : ℝ :=
  ∑ index : GradeMultiIndex grade, frequency ^ (2 * (grade - cartesianOrder index.toCartesian)) *
    ‖closedMultiDerivative field index.toCartesian point‖ ^ 2

theorem cartesianPointDensity_nonnegative {dimension : ℕ} (frequency : ℝ) (positive : 0 ≤ frequency)
    (grade : ℕ) (field : ClosedJet dimension) (point : ClosedDisk) :
    0 ≤ cartesianPointDensity frequency grade field point :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (pow_nonneg positive _) (sq_nonneg _))

theorem weighted_word_sq_le_density {dimension grade order : ℕ} (frequency : ℝ) (oneLe : 1 ≤ frequency)
    (upper : order ≤ grade) (field : ClosedJet dimension) (point : ClosedDisk) (word : CartesianWord order) :
    frequency ^ (2 * (grade - order)) * ‖closedDerivative field order word point‖ ^ 2 ≤
      cartesianPointDensity frequency grade field point := by
  have term := Finset.single_le_sum (s := (Finset.univ : Finset (GradeMultiIndex grade)))
    (f := fun index => frequency ^ (2 * (grade - cartesianOrder index.toCartesian)) *
      ‖closedMultiDerivative field index.toCartesian point‖ ^ 2)
    (fun _ _ => mul_nonneg (pow_nonneg (zero_le_one.trans oneLe) _) (sq_nonneg _))
    (Finset.mem_univ (densityGradeIndex upper word))
  rw [densityGradeIndex_order] at term
  rw [closedDerivative_eq_closedMultiDerivative_wordIndex]
  exact term

theorem weighted_higherDerivative_sq_le_density {dimension grade order : ℕ}
    (frequency : ℝ) (oneLe : 1 ≤ frequency) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    frequency ^ (2 * (grade - order)) *
      ‖iteratedFDeriv ℝ order (smoothClosedExtension field) point.val‖ ^ 2 ≤
      planarWordCoefficientSum order ^ 2 * cartesianPointDensity frequency grade field point := by
  rw [smoothClosedExtension_higherDerivative]
  have ambientEquality : ambientClosedDisk point.val = point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem point.property
  have normBound : ‖closedPlaneHigherDerivative (order := order) field point.val‖ ≤
      ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        ‖closedDerivative field order word point‖ := by
    unfold closedPlaneHigherDerivative
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro word _
    rw [ContinuousMultilinearMap.norm_smulRight, ambientEquality]
  have cauchy := weighted_cauchy_finset (Finset.univ : Finset (CartesianWord order))
    (fun word => ‖spatialPlaneWordCoefficient word‖)
    (fun word => ‖closedDerivative field order word point‖) (fun _ _ => norm_nonneg _)
  have weightedSum : frequency ^ (2 * (grade - order)) *
      (∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        ‖closedDerivative field order word point‖ ^ 2) ≤
      planarWordCoefficientSum order * cartesianPointDensity frequency grade field point := by
    rw [Finset.mul_sum, planarWordCoefficientSum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro word _
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
      (weighted_word_sq_le_density frequency oneLe upper field point word)
      (norm_nonneg (spatialPlaneWordCoefficient word))
  calc
    _ ≤ frequency ^ (2 * (grade - order)) *
        (∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
          ‖closedDerivative field order word point‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) normBound 2)
        (pow_nonneg (zero_le_one.trans oneLe) _)
    _ ≤ frequency ^ (2 * (grade - order)) * (planarWordCoefficientSum order *
        ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
          ‖closedDerivative field order word point‖ ^ 2) :=
      mul_le_mul_of_nonneg_left cauchy (pow_nonneg (zero_le_one.trans oneLe) _)
    _ = planarWordCoefficientSum order * (frequency ^ (2 * (grade - order)) *
        ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
          ‖closedDerivative field order word point‖ ^ 2) := by ring
    _ ≤ planarWordCoefficientSum order * (planarWordCoefficientSum order *
        cartesianPointDensity frequency grade field point) :=
      mul_le_mul_of_nonneg_left weightedSum (planarWordCoefficientSum_nonnegative order)
    _ = _ := by ring

def planarTensorConstant (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), planarWordCoefficientSum index ^ 2

theorem weighted_spatialJetSquaredDensity_le {dimension grade order : ℕ}
    (frequency : ℝ) (oneLe : 1 ≤ frequency) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    frequency ^ (2 * (grade - order)) * spatialJetSquaredDensity (smoothClosedExtension field) order point.val ≤
      planarTensorConstant order * cartesianPointDensity frequency grade field point := by
  rw [spatialJetSquaredDensity, Finset.mul_sum, planarTensorConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index indexIn
  have indexOrder : index ≤ order := by have := Finset.mem_range.mp indexIn; omega
  have powerBound : frequency ^ (2 * (grade - order)) ≤ frequency ^ (2 * (grade - index)) :=
    pow_le_pow_right₀ oneLe (by omega)
  exact (mul_le_mul_of_nonneg_right powerBound (sq_nonneg _)).trans
    (weighted_higherDerivative_sq_le_density frequency oneLe (indexOrder.trans upper) field point)

theorem weighted_collarDerivative_sq_le_density {dimension grade order : ℕ}
    (frequency : ℝ) (oneLe : 1 ≤ frequency) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    frequency ^ (2 * (grade - order)) *
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension field)) point‖ ^ 2 ≤
      (collarDerivativeConstant order order ^ 2 * (order + 1 : ℝ) * planarTensorConstant order) *
        cartesianPointDensity frequency grade field ⟨collarPlane point, (collarPlane_radius inside).2⟩ := by
  have collarBound := collarField_derivative_sq_bound (smoothClosedExtension field)
    (smoothClosedExtension_smooth field) order order le_rfl point inside
  have sourceBound := weighted_spatialJetSquaredDensity_le frequency oneLe upper field
    ⟨collarPlane point, (collarPlane_radius inside).2⟩
  have densityNonnegative := cartesianPointDensity_nonnegative frequency (zero_le_one.trans oneLe)
    grade field ⟨collarPlane point, (collarPlane_radius inside).2⟩
  calc
    _ ≤ frequency ^ (2 * (grade - order)) *
        ((collarDerivativeConstant order order ^ 2 * (order + 1 : ℝ)) *
          spatialJetSquaredDensity (smoothClosedExtension field) order (collarPlane point)) :=
      mul_le_mul_of_nonneg_left collarBound (pow_nonneg (zero_le_one.trans oneLe) _)
    _ = (collarDerivativeConstant order order ^ 2 * (order + 1 : ℝ)) *
        (frequency ^ (2 * (grade - order)) *
          spatialJetSquaredDensity (smoothClosedExtension field) order (collarPlane point)) := by ring
    _ ≤ (collarDerivativeConstant order order ^ 2 * (order + 1 : ℝ)) *
        (planarTensorConstant order * cartesianPointDensity frequency grade field
          ⟨collarPlane point, (collarPlane_radius inside).2⟩) :=
      mul_le_mul_of_nonneg_left sourceBound (by positivity)
    _ = _ := by ring

end Grad.BoundaryTrace
