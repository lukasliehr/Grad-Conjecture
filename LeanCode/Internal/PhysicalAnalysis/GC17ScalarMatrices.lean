import GC17TraceProducts

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def scalarMatrix (value : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => value

theorem scalarMatrix_mul (first second : ℂ) : scalarMatrix first * scalarMatrix second = scalarMatrix (first * second) := by
  ext row column
  simp [Matrix.mul_apply, scalarMatrix]

def scalarEntryFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (row : Fin output) (column : Fin input)
    (family : CoefficientFamily L sigma gamma ell input output) : CoefficientFamily L sigma gamma ell 1 1 :=
  composeFamily admissible (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 row))
    (composeFamily admissible family (constantFamily L sigma gamma ell (matrixUnit (input := 1) column 0)))

def scalarEntryProfile {input output : ℕ} (row : Fin output) (column : Fin input)
    (profile : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixUnit (output := 1) 0 row)).comp 4
    (profile.comp 4 (constantProfile (matrixUnit (input := 1) column 0)))

theorem scalarEntryFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (row : Fin output) (column : Fin input)
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    FamilyCoherent (scalarEntryFamily admissible row column family) :=
  (constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 row)).comp admissible
    (coherent.comp admissible (constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) column 0)))

theorem scalarEntryFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1) (row : Fin output) (column : Fin input)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (scalarEntryProfile row column profile)
      (scalarEntryFamily admissible row column actual) (scalarEntryFamily admissible row column reference) :=
  FamilyEstimate.comp admissible low
    (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixUnit (output := 1) 0 row))
    (FamilyEstimate.comp admissible low estimate
      (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixUnit (input := 1) column 0)))

theorem scalarEntryFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (row : Fin output) (column : Fin input)
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (scalarEntryFamily admissible row column family) grade angle point =
      scalarMatrix (familyMatrix family grade angle point row column) := by
  have rowCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 row)
  have columnCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) column 0)
  have innerCoherent : FamilyCoherent (composeFamily admissible family
      (constantFamily L sigma gamma ell (matrixUnit (input := 1) column 0))) := coherent.comp admissible columnCoherent
  unfold scalarEntryFamily
  rw [familyMatrix_comp admissible _ _ rowCoherent innerCoherent,
    familyMatrix_comp admissible _ _ coherent columnCoherent]
  unfold familyMatrix
  rw [constantFamily_physicalValue admissible, constantFamily_physicalValue admissible,
    operatorMatrix_matrixUnit, operatorMatrix_matrixUnit, ← Matrix.mul_assoc,
    Matrix.single_mul_mul_single, one_mul, mul_one]
  ext first second
  fin_cases first
  fin_cases second
  rfl

def scalarLiftFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (family : CoefficientFamily L sigma gamma ell 1 1) :
    CoefficientFamily L sigma gamma ell dimension dimension :=
  fun grade => ∑ row : Fin dimension,
    composeFamily admissible (constantFamily L sigma gamma ell (matrixUnit (input := 1) row 0))
      (composeFamily admissible family (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 row))) grade

def scalarLiftProfile (dimension : ℕ) (profile : EstimateProfile) : EstimateProfile :=
  EstimateProfile.sum (fun row : Fin dimension =>
    (constantProfile (matrixUnit (input := 1) row 0)).comp 4
      (profile.comp 4 (constantProfile (matrixUnit (output := 1) 0 row))))

theorem scalarLiftFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (family : CoefficientFamily L sigma gamma ell 1 1) (coherent : FamilyCoherent family) :
    FamilyCoherent (scalarLiftFamily admissible dimension family) :=
  familyCoherent_sum _ (fun row =>
    (constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) row 0)).comp admissible
      (coherent.comp admissible (constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 row))))

theorem scalarLiftFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 1 1}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1) (dimension : ℕ)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (scalarLiftProfile dimension profile)
      (scalarLiftFamily admissible dimension actual) (scalarLiftFamily admissible dimension reference) :=
  familyEstimate_sum _ _ _ (fun row => FamilyEstimate.comp admissible low
    (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixUnit (input := 1) row 0))
    (FamilyEstimate.comp admissible low estimate
      (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixUnit (output := 1) 0 row))))

theorem scalarLiftFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (family : CoefficientFamily L sigma gamma ell 1 1) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (scalar : ℂ)
    (value : familyMatrix family grade angle point = scalarMatrix scalar) :
    familyMatrix (scalarLiftFamily admissible dimension family) grade angle point = scalar • 1 := by
  have termCoherent (row : Fin dimension) : FamilyCoherent (composeFamily admissible
      (constantFamily L sigma gamma ell (matrixUnit (input := 1) row 0))
      (composeFamily admissible family (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 row)))) :=
    (constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) row 0)).comp admissible
      (coherent.comp admissible (constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 row)))
  unfold familyMatrix scalarLiftFamily
  rw [family_physicalValue_sum admissible _ termCoherent, operatorMatrix_sum]
  calc
    _ = ∑ row : Fin dimension, Matrix.single row row scalar := by
      apply Finset.sum_congr rfl
      intro row _
      have rowCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) row 0)
      have columnCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 row)
      have innerCoherent : FamilyCoherent (composeFamily admissible family
          (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 row))) := coherent.comp admissible columnCoherent
      change familyMatrix (composeFamily admissible _ _) grade angle point = _
      rw [familyMatrix_comp admissible _ _ rowCoherent innerCoherent,
        familyMatrix_comp admissible _ _ coherent columnCoherent, value]
      unfold familyMatrix
      rw [constantFamily_physicalValue admissible, constantFamily_physicalValue admissible,
        operatorMatrix_matrixUnit, operatorMatrix_matrixUnit, ← Matrix.mul_assoc,
        Matrix.single_mul_mul_single, one_mul, mul_one]
      rfl
    _ = scalar • 1 := by
      rw [Matrix.sum_single_eq_diagonal]
      ext row column
      simp [Matrix.diagonal_apply, Matrix.one_apply]

end Grad.GaugeCoefficients.Physical.Ledger
