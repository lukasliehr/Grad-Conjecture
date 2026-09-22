import AKDB5GenuineScalarOriginalCore
import QuotientPolynomialTerms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.Constraints
open Grad.GaugeCoefficients.Physical.Ledger

def scalarTangentialPolynomialConstant (grade : ℕ) : ℝ :=
  coordinateGradeConstant grade *
    (‖matrixUnit (0 : Fin 1) (1 : Fin 3)‖ + ‖matrixUnit (0 : Fin 1) (0 : Fin 3)‖)

theorem scalarTangentialPolynomialConstant_nonnegative (grade : ℕ) :
    0 ≤ scalarTangentialPolynomialConstant grade :=
  mul_nonneg (coordinateGradeConstant_nonnegative _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The actual polynomial used in S recovery is bounded at the same original
grade. Its fixed coordinate multiplications introduce no derivative loss. -/
theorem scalarTangentialPolynomialCore_bound (parameters : PhaseParameters)
    (grade : ℕ) (covariant : ACore parameters 3) :
    originalGradeNorm grade (scalarTangentialPolynomialCore parameters covariant) ≤
      scalarTangentialPolynomialConstant grade * originalGradeNorm grade covariant := by
  apply (originalGradeNorm_sub_le grade _ _).trans
  have first := (coordinateCore_bound parameters 0 _ grade).trans
    (mul_le_mul_of_nonneg_left
      (valueMapCore_bound (matrixUnit (0 : Fin 1) (1 : Fin 3)) covariant grade)
      (coordinateGradeConstant_nonnegative _))
  have second := (coordinateCore_bound parameters 1 _ grade).trans
    (mul_le_mul_of_nonneg_left
      (valueMapCore_bound (matrixUnit (0 : Fin 1) (0 : Fin 3)) covariant grade)
      (coordinateGradeConstant_nonnegative _))
  exact (add_le_add first second).trans_eq (by unfold scalarTangentialPolynomialConstant; ring)

def scalarRecoveryConstant (grade : ℕ) : ℝ :=
  (1 + orthogonalGradeConstant grade) * scalarTangentialPolynomialConstant grade

theorem scalarRecoveryConstant_nonnegative (grade : ℕ) :
    0 ≤ scalarRecoveryConstant grade :=
  mul_nonneg (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative _))
    (scalarTangentialPolynomialConstant_nonnegative _)

/-- Literal S=Xi+P[(Jy)·a_C], in the unchanged original norm and width. -/
theorem recoveredScalarOriginalCore_bound (parameters : PhaseParameters)
    (grade : ℕ) (covariant : ACore parameters 3) (xi : ACore parameters 1) :
    originalGradeNorm grade (recoveredScalarOriginalCore parameters covariant xi) ≤
      originalGradeNorm grade xi + scalarRecoveryConstant grade * originalGradeNorm grade covariant := by
  apply (originalGradeNorm_add_le grade _ _).trans
  apply add_le_add (le_refl _)
  exact ((removeAngularCore_bound _ grade).trans
    (mul_le_mul_of_nonneg_left (scalarTangentialPolynomialCore_bound parameters grade covariant)
      (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative _)))).trans_eq
        (mul_assoc _ _ _).symm

end Grad.OriginalCoreRealization
