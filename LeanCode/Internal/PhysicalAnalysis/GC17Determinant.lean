import GC17ScalarMatrices

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def determinantPermutation (term : Fin 6) : Fin 3 × Fin 3 × Fin 3 :=
  if term = 0 then (0, 1, 2) else if term = 1 then (0, 2, 1) else
  if term = 2 then (1, 0, 2) else if term = 3 then (1, 2, 0) else
  if term = 4 then (2, 0, 1) else (2, 1, 0)

def determinantSign (term : Fin 6) : ℂ := if term = 0 ∨ term = 3 ∨ term = 4 then 1 else -1

theorem determinant_six_terms (matrix : Matrix (Fin 3) (Fin 3) ℂ) :
    (∑ term : Fin 6, determinantSign term *
      (matrix 0 (determinantPermutation term).1 * matrix 1 (determinantPermutation term).2.1 *
        matrix 2 (determinantPermutation term).2.2)) = matrix.det := by
  rw [Matrix.det_fin_three]
  simp [Fin.sum_univ_succ, determinantPermutation, determinantSign]
  ring

def determinantTermFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) (term : Fin 6) : CoefficientFamily L sigma gamma ell 1 1 :=
  composeFamily admissible
    (composeFamily admissible (scalarEntryFamily admissible 0 (determinantPermutation term).1 family)
      (scalarEntryFamily admissible 1 (determinantPermutation term).2.1 family))
    (scalarEntryFamily admissible 2 (determinantPermutation term).2.2 family)

def determinantTermProfile (profile : EstimateProfile) (term : Fin 6) : EstimateProfile :=
  ((scalarEntryProfile (0 : Fin 3) (determinantPermutation term).1 profile).comp 4
    (scalarEntryProfile (1 : Fin 3) (determinantPermutation term).2.1 profile)).comp 4
      (scalarEntryProfile (2 : Fin 3) (determinantPermutation term).2.2 profile)

def determinantFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  fun grade => ∑ term : Fin 6, determinantSign term • determinantTermFamily admissible family term grade

def determinantProfile (profile : EstimateProfile) : EstimateProfile :=
  EstimateProfile.sum (fun term : Fin 6 => (determinantTermProfile profile term).smul (determinantSign term))

theorem determinantTermFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent family) (term : Fin 6) :
    FamilyCoherent (determinantTermFamily admissible family term) :=
  ((scalarEntryFamily_coherent admissible 0 _ family coherent).comp admissible
    (scalarEntryFamily_coherent admissible 1 _ family coherent)).comp admissible
      (scalarEntryFamily_coherent admissible 2 _ family coherent)

theorem determinantFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent family) :
    FamilyCoherent (determinantFamily admissible family) :=
  familyCoherent_sum _ (fun term => (determinantTermFamily_coherent admissible family coherent term).smul (determinantSign term))

theorem determinantFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (determinantProfile profile)
      (determinantFamily admissible actual) (determinantFamily admissible reference) :=
  familyEstimate_sum _ _ _ (fun term =>
    (FamilyEstimate.comp admissible low
      (FamilyEstimate.comp admissible low
        (scalarEntryFamily_estimate admissible low 0 (determinantPermutation term).1 estimate)
        (scalarEntryFamily_estimate admissible low 1 (determinantPermutation term).2.1 estimate))
      (scalarEntryFamily_estimate admissible low 2 (determinantPermutation term).2.2 estimate)).smul (determinantSign term))

theorem determinantTermFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent family) (term : Fin 6)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (determinantTermFamily admissible family term) grade angle point =
      scalarMatrix (familyMatrix family grade angle point 0 (determinantPermutation term).1 *
        familyMatrix family grade angle point 1 (determinantPermutation term).2.1 *
        familyMatrix family grade angle point 2 (determinantPermutation term).2.2) := by
  have first := scalarEntryFamily_coherent admissible 0 (determinantPermutation term).1 family coherent
  have second := scalarEntryFamily_coherent admissible 1 (determinantPermutation term).2.1 family coherent
  have third := scalarEntryFamily_coherent admissible 2 (determinantPermutation term).2.2 family coherent
  have firstProduct : FamilyCoherent (composeFamily admissible
      (scalarEntryFamily admissible 0 (determinantPermutation term).1 family)
      (scalarEntryFamily admissible 1 (determinantPermutation term).2.1 family)) := first.comp admissible second
  unfold determinantTermFamily
  rw [familyMatrix_comp admissible _ _ firstProduct third, familyMatrix_comp admissible _ _ first second,
    scalarEntryFamily_matrix admissible _ _ family coherent, scalarEntryFamily_matrix admissible _ _ family coherent,
    scalarEntryFamily_matrix admissible _ _ family coherent, scalarMatrix_mul, scalarMatrix_mul]

theorem determinantFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (determinantFamily admissible family) grade angle point =
      scalarMatrix (familyMatrix family grade angle point).det := by
  have signedCoherent (term : Fin 6) :=
    (determinantTermFamily_coherent admissible family coherent term).smul (determinantSign term)
  unfold familyMatrix determinantFamily
  rw [family_physicalValue_sum admissible _ signedCoherent, operatorMatrix_sum]
  have each (term : Fin 6) :
      operatorMatrix (coefficientPhysicalValue
        (determinantSign term • determinantTermFamily admissible family term grade) angle point) =
      determinantSign term • scalarMatrix (familyMatrix family grade angle point 0 (determinantPermutation term).1 *
        familyMatrix family grade angle point 1 (determinantPermutation term).2.1 *
        familyMatrix family grade angle point 2 (determinantPermutation term).2.2) := by
    rw [family_physicalValue_smul admissible _ (determinantTermFamily_coherent admissible family coherent term),
      operatorMatrix_smul]
    exact congrArg (fun matrix : Matrix (Fin 1) (Fin 1) ℂ => determinantSign term • matrix)
      (determinantTermFamily_matrix admissible family coherent term grade angle point)
  simp_rw [each]
  ext row column
  change (∑ term : Fin 6, determinantSign term *
    (familyMatrix family grade angle point 0 (determinantPermutation term).1 *
      familyMatrix family grade angle point 1 (determinantPermutation term).2.1 *
      familyMatrix family grade angle point 2 (determinantPermutation term).2.2)) = _
  exact determinant_six_terms _

end Grad.GaugeCoefficients.Physical.Ledger
