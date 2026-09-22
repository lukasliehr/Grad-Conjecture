import GC18NumeratorBounds

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def muConstant (gauge : ℕ → ℝ) := numeratorConstant tangentRowConstant tangentColumnConstant gauge
def etaConstant (gauge : ℕ → ℝ) := numeratorConstant tangentRowConstant scalarColumnConstant gauge
def nuConstant (gauge : ℕ → ℝ) := numeratorConstant scalarRowConstant tangentColumnConstant gauge
def deltaConstant (gauge : ℕ → ℝ) (grade : ℕ) :=
  angularBound grade * sandwichConstant scalarRowConstant scalarColumnConstant grade * gauge grade

theorem muConstant_nonnegative {gauge : ℕ → ℝ} (nonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ muConstant gauge grade :=
  numeratorConstant_nonnegative tangentRowConstant_nonnegative tangentColumnConstant_nonnegative nonnegative grade
theorem etaConstant_nonnegative {gauge : ℕ → ℝ} (nonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ etaConstant gauge grade :=
  numeratorConstant_nonnegative tangentRowConstant_nonnegative scalarColumnConstant_nonnegative nonnegative grade
theorem nuConstant_nonnegative {gauge : ℕ → ℝ} (nonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ nuConstant gauge grade :=
  numeratorConstant_nonnegative scalarRowConstant_nonnegative tangentColumnConstant_nonnegative nonnegative grade
theorem deltaConstant_nonnegative {gauge : ℕ → ℝ} (nonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ deltaConstant gauge grade := by
  have angularNonnegative : 0 ≤ angularBound grade := by unfold angularBound; positivity
  exact mul_nonneg (mul_nonneg angularNonnegative
    (sandwichConstant_nonnegative scalarRowConstant_nonnegative scalarColumnConstant_nonnegative grade)) (nonnegative grade)

theorem muDeviation_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3) (constants : ℕ → ℝ)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) : ‖muDeviation admissible gauge grade‖ ≤
      muConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) :=
  radialNumerator_bound parameters admissible field rho epsilon _ gauge _
    tangentRowConstant tangentColumnConstant constants tangentRowConstant_nonnegative tangentColumnConstant_nonnegative
    (tangentRow_bound L parameters.sigma0 parameters.gamma ell)
    (tangentColumn_bound L parameters.sigma0 parameters.gamma ell) bound grade

theorem etaCoefficient_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3) (constants : ℕ → ℝ)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) : ‖etaCoefficient admissible gauge grade‖ ≤
      etaConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) :=
  radialNumerator_bound parameters admissible field rho epsilon _ gauge _
    tangentRowConstant scalarColumnConstant constants tangentRowConstant_nonnegative scalarColumnConstant_nonnegative
    (tangentRow_bound L parameters.sigma0 parameters.gamma ell) (scalarColumn_bound admissible) bound grade

theorem nuCoefficient_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3) (constants : ℕ → ℝ)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) : ‖nuCoefficient admissible gauge grade‖ ≤
      nuConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) :=
  radialNumerator_bound parameters admissible field rho epsilon _ gauge _
    scalarRowConstant tangentColumnConstant constants scalarRowConstant_nonnegative tangentColumnConstant_nonnegative
    (scalarRow_bound admissible) (tangentColumn_bound L parameters.sigma0 parameters.gamma ell) bound grade

theorem deltaDeviation_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3) (constants : ℕ → ℝ)
    (nonnegative : ∀ grade, 0 ≤ constants grade)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) : ‖deltaDeviation admissible gauge grade‖ ≤
      deltaConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) := by
  have angularNonnegative : 0 ≤ angularBound grade := by unfold angularBound; positivity
  have sandwich := sandwichFamily_bound admissible _ gauge _ scalarRowConstant scalarColumnConstant
    scalarRowConstant_nonnegative scalarColumnConstant_nonnegative (scalarRow_bound admissible)
    (scalarColumn_bound admissible) grade
  have productNonnegative := sandwichConstant_nonnegative scalarRowConstant_nonnegative scalarColumnConstant_nonnegative grade
  apply (coefficientAngular_bound L parameters.sigma0 parameters.gamma ell grade 1 1 _).trans
  apply (mul_le_mul_of_nonneg_left (sandwich.trans (mul_le_mul_of_nonneg_left (bound grade) productNonnegative))
    angularNonnegative).trans
  calc
    _ = deltaConstant constants grade * physicalBudget parameters field rho epsilon (grade + 4) := by
      unfold deltaConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters field rho epsilon (by omega))
      (deltaConstant_nonnegative nonnegative grade)

/-- Convert an actual zero-centered family estimate into the accepted
one-high algebra interface, without adding a realization assumption. -/
theorem zeroReference_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ) {input output : ℕ}
    (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (coherent : FamilyCoherent family) (constants : ℕ → ℝ)
    (nonnegative : ∀ grade, 0 ≤ constants grade)
    (bound : ∀ grade, ‖family grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + offset)) :
    FamilyEstimate parameters field rho epsilon offset ⟨fun _ => 0, constants⟩
      family (zeroFamily L parameters.sigma0 parameters.gamma ell input output) where
  actualCoherent := coherent
  referenceCoherent := zeroFamily_coherent L parameters.sigma0 parameters.gamma ell input output
  fixedNonnegative _ := le_rfl
  deviationNonnegative := nonnegative
  referenceBound grade := by change ‖(0 : Coefficient L parameters.sigma0 parameters.gamma ell grade input output)‖ ≤ 0; rw [norm_zero]
  deviationBound grade := by simpa only [zeroFamily, sub_zero, Nat.add_comm] using bound grade

def unitProfile (constants : ℕ → ℝ) : EstimateProfile :=
  ⟨fun grade => Fintype.card (DerivativeIndex grade), constants⟩

theorem unitPerturbation_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset dimension : ℕ)
    (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent family) (constants : ℕ → ℝ)
    (nonnegative : ∀ grade, 0 ≤ constants grade)
    (bound : ∀ grade, ‖family grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + offset)) :
    FamilyEstimate parameters field rho epsilon offset (unitProfile constants)
      (fun grade => identityFamily L parameters.sigma0 parameters.gamma ell dimension grade + family grade)
      (identityFamily L parameters.sigma0 parameters.gamma ell dimension) where
  actualCoherent := (identityFamily_coherent L parameters.sigma0 parameters.gamma ell dimension).add coherent
  referenceCoherent := identityFamily_coherent L parameters.sigma0 parameters.gamma ell dimension
  fixedNonnegative _ := Nat.cast_nonneg _
  deviationNonnegative := nonnegative
  referenceBound := identityFamily_norm_le L parameters.sigma0 parameters.gamma ell dimension
  deviationBound grade := by rw [add_sub_cancel_left]; simpa only [unitProfile, Nat.add_comm] using bound grade

end Grad.GaugeCoefficients.Physical.RadialLedger
