import ACP10AngularMoments

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
namespace Grad.ActualCurrentPrimitives
open Grad.SourceCollar Grad.SourceCollarCoefficients

def polarDomainMatrix (angle : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row column => if column = 0 then physicalRadialVector angle row
    else if column = 1 then physicalTangentialVector angle row else physicalToroidalVector row

def polarDomainDerivative (angle : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row column => if column = 0 then physicalTangentialVector angle row
    else if column = 1 then -physicalRadialVector angle row else 0

theorem polarDomainMatrix_orthogonal (angle : ℝ) :
    (polarDomainMatrix angle).transpose * polarDomainMatrix angle = 1 ∧
      polarDomainMatrix angle * (polarDomainMatrix angle).transpose = 1 := by
  have circle := Complex.sin_sq_add_cos_sq (angle : ℂ)
  constructor <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    simp [polarDomainMatrix, Matrix.mul_apply, Fin.sum_univ_three, physicalRadialVector,
      physicalTangentialVector, physicalToroidalVector]
  all_goals ring_nf
  all_goals linear_combination circle

/-- The original polar covariant force rows AD10, before reference removal. -/
def rawPolarForceRow (kind : Fin 2) (rotated inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (component : Fin 3) : ℂ :=
  (if kind = 0 then 2 else -2) *
    (rotated.transpose * inverse.transpose) (if kind = 0 then 1 else 2) component

theorem polarForceProduct (frame inverse rotated : Matrix (Fin 3) (Fin 3) ℂ)
    (leftInverse : inverse * frame = 1) (angle : ℝ) :
    (rotated * polarDomainMatrix angle + frame * polarDomainDerivative angle).transpose *
      ((polarDomainMatrix angle).transpose * inverse).transpose =
        (polarDomainMatrix angle).transpose * (rotated.transpose * inverse.transpose) * polarDomainMatrix angle +
          (polarDomainDerivative angle).transpose * polarDomainMatrix angle := by
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (polarDomainMatrix angle).transpose * (rotated.transpose * inverse.transpose) * polarDomainMatrix angle +
        (polarDomainDerivative angle).transpose * (inverse * frame).transpose * polarDomainMatrix angle := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [leftInverse, Matrix.transpose_one, Matrix.mul_one]

/-- Exact circular cancellation: delta r0 and r2 are the finite Laurent
contractions of (R F_C)^T F_C^{-T}; the non-small -2e1 term is retained. -/
theorem rawPolarForceRow_exact (frame inverse rotated : Matrix (Fin 3) (Fin 3) ℂ)
    (leftInverse : inverse * frame = 1) (kind : Fin 2) (angle : ℝ) (component : Fin 3) :
    rawPolarForceRow kind
      (rotated * polarDomainMatrix angle + frame * polarDomainDerivative angle)
      ((polarDomainMatrix angle).transpose * inverse) component =
        forcePolarComponent kind angle (rotated.transpose * inverse.transpose) component +
          if kind = 0 ∧ component = 0 then -2 else 0 := by
  unfold rawPolarForceRow
  rw [polarForceProduct frame inverse rotated leftInverse angle]
  have circle := Complex.sin_sq_add_cos_sq (angle : ℂ)
  fin_cases kind <;> fin_cases component <;>
    simp [forcePolarComponent, polarDomainMatrix, polarDomainDerivative,
      Matrix.mul_apply, Fin.sum_univ_three, physicalRadialVector, physicalTangentialVector,
      physicalToroidalVector, matrixPairing, Matrix.mulVec, dotProduct]
  all_goals ring_nf
  all_goals linear_combination -2 * circle

end Grad.ActualCurrentPrimitives
