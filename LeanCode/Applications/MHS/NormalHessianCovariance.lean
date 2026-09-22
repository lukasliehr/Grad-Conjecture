import PhysicalHessianCovariance
import CircleIsometryClassificationConsumer
import TensorAngleRigidity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace Grad.MainAssembly.NormalHessianCovariance

open Grad.MainTarget
open Grad.MainAssembly.PhysicalHessianCovariance
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.TensorAngleRigidity
open Matrix

/-- The radial/vertical orthonormal frame normal to the distinguished circle. -/
def normalFrame (angle : ℝ) : Fin 2 → Vec
  | 0 => axisRadial angle
  | 1 => axisVertical

/-- Restriction of the ambient pressure Hessian to the moving normal frame. -/
def normalHessianMatrix (pressure : Vec → ℝ) (radius angle : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column =>
    pressureHessian pressure (radius • axisRadial angle)
      ![normalFrame angle row, normalFrame angle column]

/-- The signs by which the classified ambient isometry acts on the two normal
coordinates: radial is fixed, while vertical receives the independent normal
sign. -/
def normalCoordinateSign (verticalSign : ℝ) : Fin 2 → ℝ
  | 0 => 1
  | 1 => verticalSign

/-- Trace-normalized inverse of the negative physical normal Hessian. -/
def normalizedInverseShape (hessian : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ((-hessian)⁻¹).trace⁻¹ • (-hessian)⁻¹

theorem normalSignMatrix_transpose (verticalSign : ℝ) :
    (normalSignMatrix verticalSign)ᵀ = normalSignMatrix verticalSign := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [normalSignMatrix]

theorem normalSignMatrix_square (verticalSign : ℝ)
    (verticalSignValue : verticalSign = 1 ∨ verticalSign = -1) :
    normalSignMatrix verticalSign * normalSignMatrix verticalSign = 1 := by
  rcases verticalSignValue with rfl | rfl
  · funext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalSignMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · funext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalSignMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Solve a signed congruence for its middle matrix, using that the normal-sign
matrix is a symmetric involution. -/
theorem solve_signed_matrix_covariance
    (source target : Matrix (Fin 2) (Fin 2) ℝ)
    (scalar verticalSign : ℝ)
    (verticalSignValue : verticalSign = 1 ∨ verticalSign = -1)
    (covariance :
      normalSignMatrix verticalSign * target *
          (normalSignMatrix verticalSign)ᵀ = scalar • source) :
    target = scalar •
      (normalSignMatrix verticalSign * source * normalSignMatrix verticalSign) := by
  let signMatrix := normalSignMatrix verticalSign
  have signTranspose : signMatrixᵀ = signMatrix :=
    normalSignMatrix_transpose verticalSign
  have signSquare : signMatrix * signMatrix = 1 :=
    normalSignMatrix_square verticalSign verticalSignValue
  change signMatrix * target * signMatrixᵀ = scalar • source at covariance
  rw [signTranspose] at covariance
  calc
    target = 1 * target * 1 := by simp
    _ = (signMatrix * signMatrix) * target *
        (signMatrix * signMatrix) := by rw [signSquare]
    _ = signMatrix * (signMatrix * target * signMatrix) * signMatrix := by
      noncomm_ring
    _ = signMatrix * (scalar • source) * signMatrix := by rw [covariance]
    _ = scalar • (signMatrix * source * signMatrix) := by
      simp

theorem orthogonal_normalFrame
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (sourceAngle targetAngle verticalSign : ℝ)
    (radialAction : orthogonal (axisRadial sourceAngle) =
      axisRadial targetAngle)
    (verticalAction : orthogonal axisVertical = verticalSign • axisVertical) :
    ∀ index,
      orthogonal (normalFrame sourceAngle index) =
        normalCoordinateSign verticalSign index • normalFrame targetAngle index := by
  intro index
  fin_cases index
  · simpa [normalFrame, normalCoordinateSign] using radialAction
  · simpa [normalFrame, normalCoordinateSign] using verticalAction

/-- Entrywise normal-frame form of the ambient Hessian covariance. -/
theorem normalHessian_entry_covariance
    (firstPressure secondPressure : Vec → ℝ)
    (radius sourceAngle targetAngle amplitude verticalSign : ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (radialAction : orthogonal (axisRadial sourceAngle) =
      axisRadial targetAngle)
    (verticalAction : orthogonal axisVertical = verticalSign • axisVertical)
    (ambientCovariance :
      (pressureHessian secondPressure
          (orthogonal (radius • axisRadial sourceAngle))).compContinuousLinearMap
          (fun _ => orthogonal.toContinuousLinearMap) =
        amplitude ^ 2 • pressureHessian firstPressure
          (radius • axisRadial sourceAngle)) :
    ∀ row column,
      normalCoordinateSign verticalSign row *
          normalCoordinateSign verticalSign column *
          normalHessianMatrix secondPressure radius targetAngle row column =
        amplitude ^ 2 *
          normalHessianMatrix firstPressure radius sourceAngle row column := by
  intro row column
  have evaluated := congrArg
    (fun tensor : Vec [×2]→L[ℝ] ℝ =>
      tensor ![normalFrame sourceAngle row, normalFrame sourceAngle column])
    ambientCovariance
  have radialPoint :
      orthogonal (radius • axisRadial sourceAngle) =
        radius • axisRadial targetAngle := by
    rw [map_smul, radialAction]
  rw [radialPoint] at evaluated
  have frameAction := orthogonal_normalFrame orthogonal sourceAngle targetAngle
    verticalSign radialAction verticalAction
  have mappedPair :
      (fun index => orthogonal.toContinuousLinearMap
        (![normalFrame sourceAngle row, normalFrame sourceAngle column] index)) =
      (fun index =>
        (![normalCoordinateSign verticalSign row,
            normalCoordinateSign verticalSign column] index) •
          (![normalFrame targetAngle row, normalFrame targetAngle column] index)) := by
    funext index
    fin_cases index <;> simp [frameAction]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at evaluated
  rw [mappedPair, ContinuousMultilinearMap.map_smul_univ] at evaluated
  simpa [normalHessianMatrix, Fin.prod_univ_two, smul_eq_mul,
    mul_assoc] using evaluated

/-- Matrix form needed for normalization: the signed target normal Hessian is
the squared-amplitude multiple of the source normal Hessian. -/
theorem signed_normalHessian_covariance
    (firstPressure secondPressure : Vec → ℝ)
    (radius sourceAngle targetAngle amplitude verticalSign : ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (radialAction : orthogonal (axisRadial sourceAngle) =
      axisRadial targetAngle)
    (verticalAction : orthogonal axisVertical = verticalSign • axisVertical)
    (ambientCovariance :
      (pressureHessian secondPressure
          (orthogonal (radius • axisRadial sourceAngle))).compContinuousLinearMap
          (fun _ => orthogonal.toContinuousLinearMap) =
        amplitude ^ 2 • pressureHessian firstPressure
          (radius • axisRadial sourceAngle)) :
    normalSignMatrix verticalSign *
        normalHessianMatrix secondPressure radius targetAngle *
        (normalSignMatrix verticalSign)ᵀ =
      amplitude ^ 2 •
        normalHessianMatrix firstPressure radius sourceAngle := by
  have entries := normalHessian_entry_covariance firstPressure secondPressure
    radius sourceAngle targetAngle amplitude verticalSign orthogonal
    radialAction verticalAction ambientCovariance
  funext i j
  fin_cases i <;> fin_cases j
  · simpa [normalSignMatrix, normalCoordinateSign, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul] using entries 0 0
  · simpa [normalSignMatrix, normalCoordinateSign, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        entries 0 1
  · simpa [normalSignMatrix, normalCoordinateSign, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul] using entries 1 0
  · simpa [normalSignMatrix, normalCoordinateSign, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        entries 1 1

/-- Trace normalization cancels every nonzero scalar from a signed Hessian
congruence.  Invertibility is required only for the source negative Hessian;
the covariance supplies an explicit inverse for the target. -/
theorem normalizedInverseShape_signed_covariance
    (source target : Matrix (Fin 2) (Fin 2) ℝ)
    (scalar verticalSign : ℝ) (scalarNonzero : scalar ≠ 0)
    (verticalSignValue : verticalSign = 1 ∨ verticalSign = -1)
    (sourceInvertible : IsUnit (-source).det)
    (covariance :
      normalSignMatrix verticalSign * target *
          (normalSignMatrix verticalSign)ᵀ = scalar • source) :
    normalizedInverseShape target =
      normalSignMatrix verticalSign * normalizedInverseShape source *
        (normalSignMatrix verticalSign)ᵀ := by
  let signMatrix := normalSignMatrix verticalSign
  have signTranspose : signMatrixᵀ = signMatrix :=
    normalSignMatrix_transpose verticalSign
  have signSquare : signMatrix * signMatrix = 1 :=
    normalSignMatrix_square verticalSign verticalSignValue
  have targetFormula :
      target = scalar • (signMatrix * source * signMatrix) := by
    exact solve_signed_matrix_covariance source target scalar verticalSign
      verticalSignValue covariance
  have negativeTarget :
      -target = scalar • (signMatrix * (-source) * signMatrix) := by
    rw [targetFormula]
    simp
  have targetInverseProduct :
      (-target) *
          (scalar⁻¹ • (signMatrix * (-source)⁻¹ * signMatrix)) = 1 := by
    rw [negativeTarget, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ scalarNonzero, one_smul]
    calc
      (signMatrix * (-source) * signMatrix) *
          (signMatrix * (-source)⁻¹ * signMatrix) =
        signMatrix * ((-source) * (signMatrix * signMatrix) *
          (-source)⁻¹) * signMatrix := by noncomm_ring
      _ = signMatrix * ((-source) * (-source)⁻¹) * signMatrix := by
        rw [signSquare, Matrix.mul_one]
      _ = signMatrix * 1 * signMatrix := by
        rw [Matrix.mul_nonsing_inv _ sourceInvertible]
      _ = 1 := by rw [Matrix.mul_one, signSquare]
  have targetInverse :
      (-target)⁻¹ = scalar⁻¹ •
        (signMatrix * (-source)⁻¹ * signMatrix) :=
    Matrix.inv_eq_right_inv targetInverseProduct
  have traceConjugation (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
      (signMatrix * matrix * signMatrix).trace = matrix.trace := by
    calc
      (signMatrix * matrix * signMatrix).trace =
          (signMatrix * signMatrix * matrix).trace :=
        Matrix.trace_mul_cycle signMatrix matrix signMatrix
      _ = matrix.trace := by rw [signSquare, Matrix.one_mul]
  have targetTrace :
      ((-target)⁻¹).trace =
        scalar⁻¹ * ((-source)⁻¹).trace := by
    rw [targetInverse, Matrix.trace_smul, traceConjugation]
    rfl
  have scalarCancellation :
      (scalar⁻¹ * ((-source)⁻¹).trace)⁻¹ * scalar⁻¹ =
        ((-source)⁻¹).trace⁻¹ := by
    by_cases traceZero : ((-source)⁻¹).trace = 0
    · simp [traceZero]
    · field_simp
  unfold normalizedInverseShape
  change ((-target)⁻¹).trace⁻¹ • (-target)⁻¹ =
    signMatrix * (((-source)⁻¹).trace⁻¹ • (-source)⁻¹) * signMatrixᵀ
  rw [targetTrace, targetInverse, signTranspose, smul_smul,
    Matrix.mul_smul, Matrix.smul_mul, scalarCancellation]

end Grad.MainAssembly.NormalHessianCovariance
