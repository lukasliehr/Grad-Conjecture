import AKBI16ActualOriginalAffinePiola
import AKU57ActualColumnDeterminantAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger

theorem originalPhysicalColumns_third_product (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    physicalColumns (physicalColumn matrix 0) (physicalColumn matrix 1) (matrixOperator matrix value)=
      matrix*replacementColumn 2 value := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [physicalColumns,physicalColumn,replacementColumn,Matrix.mul_apply,Fin.sum_univ_three,
      threeColumnOperator_apply,operatorMatrix_matrixOperator]

theorem originalDeterminant_replace_third (matrix inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : matrix*inverse=1) (value : ComplexEuclidean 3) :
    Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0) (physicalColumn matrix 1) value=
      matrix.det*matrixOperator inverse value 2 := by
  have recover : matrixOperator matrix (matrixOperator inverse value)=value := by
    rw [matrixOperator_comp_apply,law,matrixOperator_one_apply]
  calc
    _=Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0) (physicalColumn matrix 1)
        (matrixOperator matrix (matrixOperator inverse value)) := congrArg
      (fun vector => Grad.NonlinearQuotient.complexDeterminant (physicalColumn matrix 0) (physicalColumn matrix 1) vector) recover.symm
    _=_ := by rw [← physicalColumns_det,originalPhysicalColumns_third_product,Matrix.det_mul,replacementColumn_det]

theorem originalSignedCofactor_frameTranspose (matrix inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : matrix*inverse=1) :
    (matrix.det • (inverse*inverse.transpose))*matrix.transpose=matrix.det • inverse := by
  have transpose : inverse.transpose*matrix.transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_one] using congrArg Matrix.transpose law
  rw [Matrix.smul_mul,Matrix.mul_assoc,transpose,Matrix.mul_one]

theorem originalSignedCofactor_action (matrix inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : matrix*inverse=1) (value : ComplexEuclidean 3) :
    WithLp.toLp 2 ((matrix.det • (inverse*inverse.transpose)).mulVec (matrix.transpose.mulVec value))=
      matrix.det • matrixOperator inverse value := by
  rw [Matrix.mulVec_mulVec,originalSignedCofactor_frameTranspose matrix inverse law]
  apply PiLp.ext
  intro component
  simp [Matrix.mulVec,Matrix.smul_apply,Fin.sum_univ_three,dotProduct,
    threeColumnOperator_apply,operatorMatrix_matrixOperator]
  ring

end Grad.OriginalKernelHomogeneousGraph
