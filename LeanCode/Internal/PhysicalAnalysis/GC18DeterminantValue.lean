import GC18CoordinateMatrices

noncomputable section

set_option maxHeartbeats 1500000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState

theorem determinantFamily_value {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (determinantFamily admissible gauge) grade angle point 0 0 =
      blockDeterminant
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point := by
  have muCoherent : FamilyCoherent (muCoefficient admissible gauge) :=
    (identityFamily_coherent L sigma gamma ell 1).add (muDeviation_coherent admissible gauge coherent)
  have deltaCoherent : FamilyCoherent (deltaCoefficient admissible gauge) :=
    (identityFamily_coherent L sigma gamma ell 1).add (deltaDeviation_coherent admissible gauge coherent)
  have etaCoherent := etaCoefficient_coherent admissible gauge coherent
  have nuCoherent := nuCoefficient_coherent admissible gauge coherent
  have radiusCoherent : FamilyCoherent (radiusSquaredFamily admissible) :=
    (tangentRow_coherent L sigma gamma ell).comp admissible (tangentColumn_coherent L sigma gamma ell)
  unfold determinantFamily
  rw [familyMatrix_sub admissible
    (composeFamily admissible (muCoefficient admissible gauge) (deltaCoefficient admissible gauge))
    (composeFamily admissible (radiusSquaredFamily admissible)
      (composeFamily admissible (etaCoefficient admissible gauge) (nuCoefficient admissible gauge)))
    (muCoherent.comp admissible deltaCoherent)
    (radiusCoherent.comp admissible (etaCoherent.comp admissible nuCoherent)),
    familyMatrix_comp admissible _ _ muCoherent deltaCoherent,
    familyMatrix_comp admissible (radiusSquaredFamily admissible)
      (composeFamily admissible (etaCoefficient admissible gauge) (nuCoefficient admissible gauge))
      radiusCoherent (etaCoherent.comp admissible nuCoherent),
    familyMatrix_comp admissible _ _ etaCoherent nuCoherent, radiusSquaredFamily_matrix admissible]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one]
  unfold blockDeterminant
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  push_cast
  ring

/-- The constructed Neumann scalar is the inverse of the literal block
determinant. Its inverse property is a conclusion, not an AP27 hypothesis. -/
theorem actualBlockDeterminantInverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (determinantInverseFamily admissible gauge) grade angle point 0 0 *
      blockDeterminant
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point = 1 := by
  have inverse := (determinantInverse_two_sided parameters admissible field rho epsilon gauge coherent
    constants nonnegative low bound small grade angle point).2
  have scalar := congrArg (fun matrix : Matrix (Fin 1) (Fin 1) ℂ => matrix 0 0) inverse
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at scalar
  rw [determinantFamily_value admissible gauge coherent grade angle point] at scalar
  exact scalar

end Grad.GaugeCoefficients.Physical.RadialLedger
