import GC18FixedComplement

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem tangentColumn_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (tangentColumnFamily L sigma gamma ell) grade angle point =
      (point.val 0 : ℂ) • (Matrix.single 1 0 1 : Matrix (Fin 3) (Fin 1) ℂ) -
      (point.val 1 : ℂ) • (Matrix.single 0 0 1 : Matrix (Fin 3) (Fin 1) ℂ) := by
  unfold familyMatrix tangentColumnFamily
  rw [family_physicalValue_sub admissible
    (coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 1) (output := 3) 1 0))
    (coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 1) (output := 3) 0 0))
    (fixedJetFamily_coherent L sigma gamma ell _) (fixedJetFamily_coherent L sigma gamma ell _),
    coordinateFamily_physicalValue, coordinateFamily_physicalValue,
    operatorMatrix_sub, operatorMatrix_smul, operatorMatrix_smul,
    operatorMatrix_matrixUnit, operatorMatrix_matrixUnit]

theorem tangentRow_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (tangentRowFamily L sigma gamma ell) grade angle point =
      (point.val 0 : ℂ) • (Matrix.single 0 1 1 : Matrix (Fin 1) (Fin 3) ℂ) -
      (point.val 1 : ℂ) • (Matrix.single 0 0 1 : Matrix (Fin 1) (Fin 3) ℂ) := by
  unfold familyMatrix tangentRowFamily
  rw [family_physicalValue_sub admissible
    (coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 3) (output := 1) 0 1))
    (coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 3) (output := 1) 0 0))
    (fixedJetFamily_coherent L sigma gamma ell _) (fixedJetFamily_coherent L sigma gamma ell _),
    coordinateFamily_physicalValue, coordinateFamily_physicalValue,
    operatorMatrix_sub, operatorMatrix_smul, operatorMatrix_smul,
    operatorMatrix_matrixUnit, operatorMatrix_matrixUnit]

/-- The actual full Fourier realization of JYᵀJY is the literal radius
squared, with the stored coordinate convention and original Hilbert norm. -/
theorem radiusSquaredFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (radiusSquaredFamily admissible) grade angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  unfold radiusSquaredFamily
  rw [familyMatrix_comp admissible _ _ (tangentRow_coherent L sigma gamma ell)
      (tangentColumn_coherent L sigma gamma ell), tangentRow_matrix admissible, tangentColumn_matrix admissible]
  ext row column
  fin_cases row
  fin_cases column
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.single_apply, Matrix.one_apply_eq, mul_one]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  norm_num [show (1 : Fin 3) ≠ 2 from by decide, show (0 : Fin 3) ≠ 2 from by decide]
  push_cast
  ring

end Grad.GaugeCoefficients.Physical.RadialLedger
