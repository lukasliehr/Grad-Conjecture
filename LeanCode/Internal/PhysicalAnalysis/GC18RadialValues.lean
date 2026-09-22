import GC18CartesianContinuity

noncomputable section

set_option maxHeartbeats 1500000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem radialDivisionFamily_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (family : CoefficientFamily L sigma gamma ell 1 1)
    (coherent : FamilyCoherent family) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (radialDivisionFamily admissible family) grade angle point 0 0) := by
  intro rotation point
  dsimp only
  unfold familyMatrix
  rw [radialDivisionFamily_physical_rotation admissible family coherent]

theorem angularFamily_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (family : CoefficientFamily L sigma gamma ell 1 1)
    (coherent : FamilyCoherent family) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (angularFamily family) grade angle point 0 0) := by
  intro rotation point
  dsimp only
  unfold familyMatrix
  rw [angularFamily_physical_rotation admissible family coherent]

theorem muCoefficient_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (muCoefficient admissible gauge) grade angle point 0 0) := by
  intro rotation point
  dsimp only
  unfold familyMatrix
  rw [muCoefficient_full_formula admissible gauge coherent, muCoefficient_full_formula admissible gauge coherent,
    radialDivisionFamily_physical_rotation admissible _ (sandwichFamily_coherent admissible _ _ _
      (tangentRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell))]

theorem etaCoefficient_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0) :=
  radialDivisionFamily_entry_radial admissible _ (sandwichFamily_coherent admissible _ _ _
    (tangentRow_coherent L sigma gamma ell) coherent (scalarColumn_coherent L sigma gamma ell)) grade angle

theorem nuCoefficient_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0) :=
  radialDivisionFamily_entry_radial admissible _ (sandwichFamily_coherent admissible _ _ _
    (scalarRow_coherent L sigma gamma ell) coherent (tangentColumn_coherent L sigma gamma ell)) grade angle

theorem deltaCoefficient_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) := by
  intro rotation point
  dsimp only
  unfold familyMatrix
  rw [deltaCoefficient_full_formula admissible gauge coherent, deltaCoefficient_full_formula admissible gauge coherent,
    angularFamily_physical_rotation admissible _ (sandwichFamily_coherent admissible _ _ _
      (scalarRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell))]

theorem blockDeterminant_radiusScalar (mu eta nu delta : ℂ) (point : ClosedDisk) :
    blockDeterminant mu eta nu delta point = mu * delta - radiusScalar point * eta * nu := by
  rw [radiusScalar, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  unfold blockDeterminant
  push_cast
  ring

theorem determinantFamily_entry_radial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (determinantFamily admissible gauge) grade angle point 0 0) := by
  intro rotation point
  dsimp only
  rw [determinantFamily_value admissible gauge coherent, determinantFamily_value admissible gauge coherent,
    blockDeterminant_radiusScalar, blockDeterminant_radiusScalar]
  have mu := muCoefficient_entry_radial admissible gauge coherent grade angle rotation point
  have eta := etaCoefficient_entry_radial admissible gauge coherent grade angle rotation point
  have nu := nuCoefficient_entry_radial admissible gauge coherent grade angle rotation point
  have delta := deltaCoefficient_entry_radial admissible gauge coherent grade angle rotation point
  dsimp only at mu eta nu delta
  rw [mu, eta, nu, delta, radiusScalar_rotation rotation point]

theorem diskRadial_inverse (determinant inverse : ClosedDisk → ℂ) (radial : IsDiskRadial determinant)
    (identity : ∀ point, inverse point * determinant point = 1) : IsDiskRadial inverse := by
  intro rotation point
  have atPoint := identity point
  have atRotated := identity (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point)
  rw [radial rotation point] at atRotated
  linear_combination inverse point * atRotated - inverse (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point) * atPoint

/-- Radiality of the actual Neumann inverse follows from its proved scalar
inverse identity; no complement inverse or radiality is an input premise. -/
theorem determinantInverseFamily_entry_radial {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) :
    IsDiskRadial (fun point => familyMatrix (determinantInverseFamily admissible gauge) grade angle point 0 0) := by
  apply diskRadial_inverse (fun point => familyMatrix (determinantFamily admissible gauge) grade angle point 0 0) _
    (determinantFamily_entry_radial admissible gauge coherent grade angle)
  intro point
  rw [determinantFamily_value admissible gauge coherent]
  exact actualBlockDeterminantInverse parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small grade angle point

end Grad.GaugeCoefficients.Physical.RadialLedger
