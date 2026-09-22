import GSP7ScalarMoments

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives

theorem polarMatrixEntry_matrix (row column : Fin 3) (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) :
    polarMatrixEntry row column angle matrix =
      ((polarDomainMatrix angle).transpose * matrix * polarDomainMatrix angle) row column := by
  rw [Matrix.mul_assoc]
  simp only [polarMatrixEntry, matrixPairing, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, polarDomainMatrix, polarVector, ite_apply]

theorem polarMatrixEntry_one (row column : Fin 3) (angle : ℝ) :
    polarMatrixEntry row column angle 1 = if row = column then 1 else 0 := by
  rw [polarMatrixEntry_matrix, Matrix.mul_one, (polarDomainMatrix_orthogonal angle).1, Matrix.one_apply]

theorem polarMatrixEntry_add (row column : Fin 3) (angle : ℝ)
    (first second : Matrix (Fin 3) (Fin 3) ℂ) :
    polarMatrixEntry row column angle (first + second) =
      polarMatrixEntry row column angle first + polarMatrixEntry row column angle second := by
  simp only [polarMatrixEntry_matrix, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

theorem polarMatrixEntry_sub (row column : Fin 3) (angle : ℝ)
    (first second : Matrix (Fin 3) (Fin 3) ℂ) :
    polarMatrixEntry row column angle (first - second) =
      polarMatrixEntry row column angle first - polarMatrixEntry row column angle second := by
  simp only [polarMatrixEntry_matrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]

theorem polarMatrixEntry_symmetric (row column : Fin 3) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (symmetric : matrix.transpose = matrix) :
    polarMatrixEntry row column angle matrix = polarMatrixEntry column row angle matrix := by
  have transformed : ((polarDomainMatrix angle).transpose * matrix * polarDomainMatrix angle).transpose =
      (polarDomainMatrix angle).transpose * matrix * polarDomainMatrix angle := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, symmetric, Matrix.mul_assoc]
  simp only [polarMatrixEntry_matrix]
  exact congrFun (congrFun transformed column) row

theorem originalPhysicalSignedCofactor_symmetric (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    (originalPhysicalSignedCofactor parameters L epsilon field angle point).transpose =
      originalPhysicalSignedCofactor parameters L epsilon field angle point := by
  unfold originalPhysicalSignedCofactor
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Literal AF1 first row of the signed polar inverse Gram, not its absolute determinant. -/
def originalSigmaRow (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) (column : Fin 3) : ℂ :=
  polarMatrixEntry 0 column polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle point)

/-- Exact AF2 symmetry linking the already-accepted kappa1 to sigma2. -/
theorem originalSigma_kappa (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) :
    physicalKappa polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle point) 0 =
      originalSigmaRow parameters L epsilon field axialAngle polarAngle point 1 := by
  change polarMatrixEntry 1 0 polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle point) = _
  exact polarMatrixEntry_symmetric 1 0 polarAngle _ (originalPhysicalSignedCofactor_symmetric parameters L epsilon field axialAngle point)

end Grad.ActualGaugeSigmaPrimitives
