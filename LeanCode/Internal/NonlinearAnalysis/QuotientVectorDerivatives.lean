import QuotientCoordinateCore

noncomputable section

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def eulerCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (coordinateCore parameters 0).comp (partialCore parameters 0) +
    (coordinateCore parameters 1).comp (partialCore parameters 1)

def rotationCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (coordinateCore parameters 0).comp (partialCore parameters 1) -
    (coordinateCore parameters 1).comp (partialCore parameters 0)

theorem eulerCore_actual {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((eulerCore parameters field).val cell).value point =
      point.val 0 • partialCoefficient 0 (field.val cell) point +
        point.val 1 • partialCoefficient 1 (field.val cell) point := rfl

theorem rotationCore_actual {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((rotationCore parameters field).val cell).value point =
      -(point.val 1 • partialCoefficient 0 (field.val cell) point) +
        point.val 0 • partialCoefficient 1 (field.val cell) point := by
  change ((coordinateJet 0 (partialJet 1 (field.val cell))) -
    (coordinateJet 1 (partialJet 0 (field.val cell)))).value point = _
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value, partialJet_value]
  abel

def vectorDerivativeGradeConstant (grade : ℕ) : ℝ :=
  2 * coordinateGradeConstant grade * partialGradeConstant grade

theorem vectorDerivativeGradeConstant_nonnegative (grade : ℕ) :
    0 ≤ vectorDerivativeGradeConstant grade :=
  mul_nonneg (mul_nonneg (by norm_num) (coordinateGradeConstant_nonnegative _))
    (partialGradeConstant_nonnegative _)

theorem coordinatePartial_bound {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate direction : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (coordinateCore parameters coordinate (partialCore parameters direction field)) ≤
      coordinateGradeConstant grade * partialGradeConstant grade * originalGradeNorm (grade + 1) field := by
  exact (coordinateCore_bound parameters coordinate _ grade).trans
    ((mul_le_mul_of_nonneg_left (partialCore_bound parameters direction field grade)
      (coordinateGradeConstant_nonnegative _)).trans_eq (mul_assoc _ _ _).symm)

theorem eulerCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (eulerCore parameters field) ≤
      vectorDerivativeGradeConstant grade * originalGradeNorm (grade + 1) field := by
  exact (originalGradeNorm_add_le grade _ _).trans
    ((add_le_add (coordinatePartial_bound parameters 0 0 field grade)
      (coordinatePartial_bound parameters 1 1 field grade)).trans_eq (by
        unfold vectorDerivativeGradeConstant
        ring))

theorem originalGradeNorm_sub_le {dimension : ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (first second : ACore parameters dimension) :
    originalGradeNorm grade (first - second) ≤
      originalGradeNorm grade first + originalGradeNorm grade second := by
  unfold originalGradeNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem rotationCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (rotationCore parameters field) ≤
      vectorDerivativeGradeConstant grade * originalGradeNorm (grade + 1) field := by
  exact (originalGradeNorm_sub_le grade _ _).trans
    ((add_le_add (coordinatePartial_bound parameters 0 1 field grade)
      (coordinatePartial_bound parameters 1 0 field grade)).trans_eq (by
        unfold vectorDerivativeGradeConstant
        ring))

end Grad.NonlinearQuotientBounds
