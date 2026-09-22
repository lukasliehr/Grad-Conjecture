import GC17FiniteSums

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def matrixOperator {input output : ℕ} (matrix : Matrix (Fin output) (Fin input) ℂ) : OperatorValue input output :=
  ∑ pair : Fin output × Fin input, matrix pair.1 pair.2 • matrixUnit pair.1 pair.2

theorem operatorMatrix_matrixOperator {input output : ℕ} (matrix : Matrix (Fin output) (Fin input) ℂ) :
    operatorMatrix (matrixOperator matrix) = matrix := by
  unfold matrixOperator
  rw [operatorMatrix_sum]
  simp_rw [operatorMatrix_smul, operatorMatrix_matrixUnit, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  exact Matrix.sum_sum_single matrix

theorem constantMatrix_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (matrix : Matrix (Fin output) (Fin input) ℂ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    operatorMatrix (coefficientPhysicalValue
      (constantFamily L sigma gamma ell (matrixOperator matrix) grade) angle point) = matrix := by
  rw [constantFamily_physicalValue admissible, operatorMatrix_matrixOperator]

def spatialColumnFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 1 2 :=
  fun grade => coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 1) (output := 2) 0 0) grade +
    coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 1) (output := 2) 1 0) grade

def spatialColumnProfile : EstimateProfile :=
  (fixedJetProfile (coordinateOperatorJet 0 (matrixUnit (input := 1) (output := 2) 0 0))).add
    (fixedJetProfile (coordinateOperatorJet 1 (matrixUnit (input := 1) (output := 2) 1 0)))

theorem spatialColumnFamily_coherent (L sigma gamma ell : ℝ) :
    FamilyCoherent (spatialColumnFamily L sigma gamma ell) :=
  (fixedJetFamily_coherent L sigma gamma ell _).add (fixedJetFamily_coherent L sigma gamma ell _)

theorem spatialColumnFamily_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ) :
    FamilyEstimate parameters field rho epsilon offset spatialColumnProfile
      (spatialColumnFamily L parameters.sigma0 parameters.gamma ell)
      (spatialColumnFamily L parameters.sigma0 parameters.gamma ell) :=
  (fixedJetFamily_estimate parameters field rho epsilon offset
    (coordinateOperatorJet 0 (matrixUnit (input := 1) (output := 2) 0 0))).add
    (fixedJetFamily_estimate parameters field rho epsilon offset
      (coordinateOperatorJet 1 (matrixUnit (input := 1) (output := 2) 1 0)))

theorem spatialColumnFamily_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    operatorMatrix (coefficientPhysicalValue (spatialColumnFamily L sigma gamma ell grade) angle point) =
      spatialColumn point := by
  have firstCoherent : FamilyCoherent (coordinateFamily L sigma gamma ell 0
      (matrixUnit (input := 1) (output := 2) 0 0)) := fixedJetFamily_coherent L sigma gamma ell _
  have secondCoherent : FamilyCoherent (coordinateFamily L sigma gamma ell 1
      (matrixUnit (input := 1) (output := 2) 1 0)) := fixedJetFamily_coherent L sigma gamma ell _
  unfold spatialColumnFamily
  rw [family_physicalValue_add admissible _ _ firstCoherent secondCoherent, coordinateFamily_physicalValue,
    coordinateFamily_physicalValue, operatorMatrix_add, operatorMatrix_smul, operatorMatrix_smul,
    operatorMatrix_matrixUnit, operatorMatrix_matrixUnit]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [spatialColumn]

theorem referenceFrame_matrix : operatorMatrix referenceFrame = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [operatorMatrix, referenceFrame_apply]

theorem referenceFrame_matrix_transpose : (operatorMatrix referenceFrame).transpose = operatorMatrix referenceFrame := by
  rw [referenceFrame_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem referenceFrame_matrix_det : (operatorMatrix referenceFrame).det = -1 := by
  rw [referenceFrame_matrix, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two]

theorem referenceFrame_matrix_square : operatorMatrix referenceFrame * operatorMatrix referenceFrame = 1 :=
  (operatorMatrix_comp referenceFrame referenceFrame).symm.trans
    ((congrArg operatorMatrix referenceFrame_square).trans (operatorMatrix_one 3))

theorem circleTrace_matrix (point : ClosedDisk) :
    (spatialColumn point).transpose * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      planarPhysicalInclusion.transpose * (operatorMatrix referenceFrame).transpose = circleTraceCovector point := by
  rw [Matrix.mul_one, referenceFrame_matrix]
  ext row column
  fin_cases row
  fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      spatialColumn, planarPhysicalInclusion, circleTraceCovector]

end Grad.GaugeCoefficients.Physical.Ledger
