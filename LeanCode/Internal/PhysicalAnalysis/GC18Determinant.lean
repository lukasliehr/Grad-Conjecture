import GC18Algebra

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.InverseAllocation

def zeroProfile (constants : ℕ → ℝ) : EstimateProfile := ⟨fun _ => 0, constants⟩

def radiusSquaredConstant (grade : ℕ) : ℝ :=
  gradeProductConstant grade * tangentRowConstant grade * tangentColumnConstant grade

theorem radiusSquaredConstant_nonnegative (grade : ℕ) : 0 ≤ radiusSquaredConstant grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade) (tangentRowConstant_nonnegative grade))
    (tangentColumnConstant_nonnegative grade)

def radiusSquaredProfile : EstimateProfile := ⟨radiusSquaredConstant, fun _ => 0⟩

theorem radiusSquared_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ) :
    FamilyEstimate parameters field rho epsilon offset radiusSquaredProfile
      (radiusSquaredFamily admissible) (radiusSquaredFamily admissible) where
  actualCoherent := (tangentRow_coherent L parameters.sigma0 parameters.gamma ell).comp admissible
    (tangentColumn_coherent L parameters.sigma0 parameters.gamma ell)
  referenceCoherent := (tangentRow_coherent L parameters.sigma0 parameters.gamma ell).comp admissible
    (tangentColumn_coherent L parameters.sigma0 parameters.gamma ell)
  fixedNonnegative := radiusSquaredConstant_nonnegative
  deviationNonnegative _ := le_rfl
  referenceBound grade := (coefficientComposition_norm_le admissible grade _ _).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (tangentRow_bound L parameters.sigma0 parameters.gamma ell grade)
      (gradeProductConstant_nonnegative grade)) (tangentColumn_bound L parameters.sigma0 parameters.gamma ell grade)
      (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade) (tangentRowConstant_nonnegative grade)))
  deviationBound grade := by rw [sub_self, norm_zero]; change (0 : ℝ) ≤ 0 * _; rw [zero_mul]

def determinantProfile (gauge : ℕ → ℝ) : EstimateProfile :=
  ((unitProfile (muConstant gauge)).comp 6 (unitProfile (deltaConstant gauge))).add
    ((radiusSquaredProfile.comp 6 ((zeroProfile (etaConstant gauge)).comp 6 (zeroProfile (nuConstant gauge)))).smul (-1))

def determinantConstant (gauge : ℕ → ℝ) (grade : ℕ) : ℝ := |(determinantProfile gauge).deviation grade|

theorem determinantConstant_nonnegative (gauge : ℕ → ℝ) (grade : ℕ) : 0 ≤ determinantConstant gauge grade := abs_nonneg _

theorem determinant_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4)) :
    FamilyEstimate parameters field rho epsilon 6 (determinantProfile constants)
      (determinantFamily admissible gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 1) := by
  have muEstimate := unitPerturbation_estimate parameters field rho epsilon 6 1 _
    (muDeviation_coherent admissible gauge coherent) (muConstant constants) (muConstant_nonnegative nonnegative)
    (muDeviation_bound parameters admissible field rho epsilon gauge constants bound)
  have deltaEstimate := unitPerturbation_estimate parameters field rho epsilon 6 1 _
    (deltaDeviation_coherent admissible gauge coherent) (deltaConstant constants) (deltaConstant_nonnegative nonnegative)
    (deltaDeviation_bound parameters admissible field rho epsilon gauge constants nonnegative bound)
  have etaEstimate := zeroReference_estimate parameters field rho epsilon 6 _
    (etaCoefficient_coherent admissible gauge coherent) (etaConstant constants) (etaConstant_nonnegative nonnegative)
    (etaCoefficient_bound parameters admissible field rho epsilon gauge constants bound)
  have nuEstimate := zeroReference_estimate parameters field rho epsilon 6 _
    (nuCoefficient_coherent admissible gauge coherent) (nuConstant constants) (nuConstant_nonnegative nonnegative)
    (nuCoefficient_bound parameters admissible field rho epsilon gauge constants bound)
  have first := muEstimate.comp admissible low deltaEstimate
  have second := (radiusSquared_estimate parameters admissible field rho epsilon 6).comp admissible low
    (etaEstimate.comp admissible low nuEstimate)
  have result := first.add (second.smul (-1))
  change FamilyEstimate parameters field rho epsilon 6 (determinantProfile constants)
    (fun grade => composeFamily admissible (muCoefficient admissible gauge) (deltaCoefficient admissible gauge) grade +
      (-1 : ℂ) • composeFamily admissible (radiusSquaredFamily admissible)
        (composeFamily admissible (etaCoefficient admissible gauge) (nuCoefficient admissible gauge)) grade)
    (fun grade => composeFamily admissible (identityFamily L parameters.sigma0 parameters.gamma ell 1)
      (identityFamily L parameters.sigma0 parameters.gamma ell 1) grade +
      (-1 : ℂ) • composeFamily admissible (radiusSquaredFamily admissible)
        (composeFamily admissible (zeroFamily L parameters.sigma0 parameters.gamma ell 1 1)
          (zeroFamily L parameters.sigma0 parameters.gamma ell 1 1)) grade) at result
  change FamilyEstimate parameters field rho epsilon 6 (determinantProfile constants)
    (fun grade => composeFamily admissible (muCoefficient admissible gauge) (deltaCoefficient admissible gauge) grade -
      composeFamily admissible (radiusSquaredFamily admissible)
        (composeFamily admissible (etaCoefficient admissible gauge) (nuCoefficient admissible gauge)) grade)
    (fun grade => identityFamily L parameters.sigma0 parameters.gamma ell 1 grade)
  simpa only [composeFamily_identity_identity, composeFamily_zero_right, zeroFamily, smul_zero, add_zero,
    neg_one_smul, ← sub_eq_add_neg] using result

theorem determinant_deviation_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) :
    ‖determinantFamily admissible gauge grade - identityFamily L parameters.sigma0 parameters.gamma ell 1 grade‖ ≤
      determinantConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) :=
  (determinant_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound).absoluteBound grade

def determinantLowRadius (constants : ℕ → ℝ) : ℝ := (2 * (determinantConstant constants 0 + 1))⁻¹

theorem determinantLowRadius_positive (constants : ℕ → ℝ) : 0 < determinantLowRadius constants := by
  have := determinantConstant_nonnegative constants 0
  unfold determinantLowRadius
  positivity

theorem determinant_base_margin {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants) :
    ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2 := by
  change ‖identityFamily L parameters.sigma0 parameters.gamma ell 1 0 - determinantFamily admissible gauge 0‖ ≤ _
  rw [norm_sub_rev]
  apply (determinant_deviation_bound parameters admissible field rho epsilon gauge coherent constants nonnegative low bound 0).trans
  have constantNonnegative := determinantConstant_nonnegative constants 0
  apply (mul_le_mul_of_nonneg_left small constantNonnegative).trans
  unfold determinantLowRadius
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (determinantConstant constants 0 + 1))).mpr
  linarith

end Grad.GaugeCoefficients.Physical.RadialLedger
