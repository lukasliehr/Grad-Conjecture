import AKU43SameFullAxisCovector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Ledger

def physicalColumn (matrix : Matrix (Fin 3) (Fin 3) ℂ) (column : Fin 3) : ComplexEuclidean 3 :=
  WithLp.toLp 2 (fun row => matrix row column)

def physicalColumns (first second third : ComplexEuclidean 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![first 0,second 0,third 0;first 1,second 1,third 1;first 2,second 2,third 2]

theorem physicalColumns_det (first second third : ComplexEuclidean 3) :
    (physicalColumns first second third).det = Grad.NonlinearQuotient.complexDeterminant first second third := by
  rw [Grad.NonlinearQuotient.complexDeterminant_eq]
  simp [physicalColumns,Matrix.det_fin_three]
  ring

def replacementColumn (column : Fin 3) (value : ComplexEuclidean 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row slot => if slot = column then value row else if row = slot then 1 else 0

theorem replacementColumn_det (column : Fin 3) (value : ComplexEuclidean 3) :
    (replacementColumn column value).det = value column := by
  fin_cases column <;> simp [replacementColumn,Matrix.det_fin_three]

theorem physicalColumns_first_product (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    physicalColumns (matrixOperator matrix value) (physicalColumn matrix 1) (physicalColumn matrix 2) =
      matrix * replacementColumn 0 value := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [physicalColumns,physicalColumn,replacementColumn,Matrix.mul_apply,Fin.sum_univ_three,
      threeColumnOperator_apply,operatorMatrix_matrixOperator]

theorem physicalColumns_second_product (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    physicalColumns (physicalColumn matrix 0) (matrixOperator matrix value) (physicalColumn matrix 2) =
      matrix * replacementColumn 1 value := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [physicalColumns,physicalColumn,replacementColumn,Matrix.mul_apply,Fin.sum_univ_three,
      threeColumnOperator_apply,operatorMatrix_matrixOperator]

theorem determinant_replace_first (matrix inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : matrix*inverse=1) (value : ComplexEuclidean 3) :
    Grad.NonlinearQuotient.complexDeterminant value (physicalColumn matrix 1) (physicalColumn matrix 2) =
      matrix.det * matrixOperator inverse value 0 := by
  have recover : matrixOperator matrix (matrixOperator inverse value) = value := by
    rw [matrixOperator_comp_apply,law,matrixOperator_one_apply]
  calc
    _ = Grad.NonlinearQuotient.complexDeterminant (matrixOperator matrix (matrixOperator inverse value))
        (physicalColumn matrix 1) (physicalColumn matrix 2) := congrArg
      (fun vector => Grad.NonlinearQuotient.complexDeterminant vector (physicalColumn matrix 1) (physicalColumn matrix 2)) recover.symm
    _ = _ := by
      rw [← physicalColumns_det,physicalColumns_first_product,Matrix.det_mul,replacementColumn_det]

theorem determinant_replace_second (matrix inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : matrix*inverse=1) (value : ComplexEuclidean 3) :
    Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0) value (physicalColumn matrix 2) =
      matrix.det * matrixOperator inverse value 1 := by
  have recover : matrixOperator matrix (matrixOperator inverse value) = value := by
    rw [matrixOperator_comp_apply,law,matrixOperator_one_apply]
  calc
    _ = Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0)
        (matrixOperator matrix (matrixOperator inverse value)) (physicalColumn matrix 2) := congrArg
      (fun vector => Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0) vector (physicalColumn matrix 2)) recover.symm
    _ = _ := by
      rw [← physicalColumns_det,physicalColumns_second_product,Matrix.det_mul,replacementColumn_det]

theorem complexDeterminant_smul_third (first second third : ComplexEuclidean 3) (scalar : ℂ) :
    Grad.NonlinearQuotient.complexDeterminant first second (scalar • third) =
      scalar * Grad.NonlinearQuotient.complexDeterminant first second third := by
  simp only [Grad.NonlinearQuotient.complexDeterminant_eq,PiLp.smul_apply,smul_eq_mul]
  ring

end Grad.FinitePhysicalJetLift
