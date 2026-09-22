import AKAL1MatrixUniformFirstBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Neumann.Regularity

/-- Constants are chosen before ell and the actual ledger. Both graph
 realizations use the inherited norm, without a grade-dependent ball. -/
def startupGaugeMatrixConstant (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  startupFirstUniformConstant L sigma gamma *
    ((Fintype.card (DerivativeIndex 0) : ℝ) + four 0 +
      ((Fintype.card (DerivativeIndex 1) : ℝ) + four 1))

def startupExtensionMatrixConstant (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  startupFirstUniformConstant L sigma gamma *
    ((Fintype.card (DerivativeIndex 0) : ℝ) + complementExtensionConstant four 0 +
      ((Fintype.card (DerivativeIndex 1) : ℝ) + complementExtensionConstant four 1))

def startupDeviationMatrixConstant (L sigma gamma : ℝ) (constants : ℕ → ℝ) : ℝ :=
  startupFirstUniformConstant L sigma gamma * (constants 0 + constants 1)

variable {L ell : ℝ} {parameters : PhaseParameters}
  {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
  {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}

/-- The genuine planar-force, third-force and flux families all have one
 common two-grade bound, taken directly from their actual ledger sums. -/
theorem startupActual_deviation_coefficients
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (grade : ℕ) (smallGrade : grade ≤ 1) :
    ‖ledger.val.gaugeDeviation grade‖ ≤ four grade * physicalBudget parameters base rho epsilon 10 ∧
    ‖ledger.val.fluxDeviation grade‖ ≤ four grade * physicalBudget parameters base rho epsilon 10 ∧
    ‖ledger.val.rotatedPlanarProduct grade‖ ≤ five grade * physicalBudget parameters base rho epsilon 10 ∧
    ‖ledger.val.rotatedThirdProduct grade‖ ≤ five grade * physicalBudget parameters base rho epsilon 10 := by
  have fourBound := (bounds grade).1.trans (mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters base rho epsilon (by omega : grade + 4 ≤ 10)) (fourNonnegative grade))
  have fiveBound := (bounds grade).2.trans (mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters base rho epsilon (by omega : grade + 5 ≤ 10)) (fiveNonnegative grade))
  have gauge := (actualGaugeDeviation_bound ledger grade).trans fourBound
  have flux : ‖ledger.val.fluxDeviation grade‖ ≤ ledgerSizeFour ledger grade := by
    unfold ledgerSizeFour
    linarith [norm_nonneg (ledger.val.inverseTransposeDeviation grade),
      norm_nonneg (ledger.val.seedInverse grade - gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2),
      norm_nonneg (ledger.val.gaugeDeviation grade), norm_nonneg (ledger.val.traceDeviation grade)]
  have planar : ‖ledger.val.rotatedPlanarProduct grade‖ ≤ ledgerSizeFive ledger grade := by
    unfold ledgerSizeFive
    linarith [norm_nonneg (ledger.val.rotatedFrame grade), norm_nonneg (ledger.val.rotatedPlanarProduct grade),
      norm_nonneg (ledger.val.rotatedThirdProduct grade)]
  have third : ‖ledger.val.rotatedThirdProduct grade‖ ≤ ledgerSizeFive ledger grade := by
    unfold ledgerSizeFive
    linarith [norm_nonneg (ledger.val.rotatedFrame grade), norm_nonneg (ledger.val.rotatedPlanarProduct grade),
      norm_nonneg (ledger.val.rotatedThirdProduct grade)]
  exact ⟨gauge, flux.trans fourBound, planar.trans fiveBound, third.trans fiveBound⟩

/-- Both actual full-gauge operators and both completed complement-extension
 operators are uniformly bounded on the same fixed B10 unit neighborhood. -/
theorem startupActual_gauge_extension_bounds
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) :
    (‖originalMatrixKernel admissible (fullGaugeFamily ledger.val.gaugeDeviation)
        (fullGaugeFamily_coherent _ ledger.property.1.2.2.2.1)‖ ≤ startupGaugeMatrixConstant L parameters.sigma0 parameters.gamma four ∧
      ‖startupMatrixFirstGraphCLM admissible (fullGaugeFamily ledger.val.gaugeDeviation)
        (fullGaugeFamily_coherent _ ledger.property.1.2.2.2.1)‖ ≤ startupGaugeMatrixConstant L parameters.sigma0 parameters.gamma four) ∧
    (‖originalMatrixKernel admissible (complementExtensionFamily admissible ledger.val.gaugeDeviation)
        (complementExtensionFamily_coherent _ _ ledger.property.1.2.2.2.1 inverseCoherent)‖ ≤
        startupExtensionMatrixConstant L parameters.sigma0 parameters.gamma four ∧
      ‖startupMatrixFirstGraphCLM admissible (complementExtensionFamily admissible ledger.val.gaugeDeviation)
        (complementExtensionFamily_coherent _ _ ledger.property.1.2.2.2.1 inverseCoherent)‖ ≤
        startupExtensionMatrixConstant L parameters.sigma0 parameters.gamma four) := by
  have gaugeBound (grade : ℕ) := (actualGaugeDeviation_bound ledger grade).trans (bounds grade)
  have low := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans unit
  have gaugeUnit (grade : ℕ) (ordered : grade ≤ 1) : ‖ledger.val.gaugeDeviation grade‖ ≤ four grade := by
    exact (gaugeBound grade).trans ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters base rho epsilon (by omega : grade + 4 ≤ 10)).trans unit)
      (fourNonnegative grade)).trans_eq (mul_one _))
  have extensionUnit (grade : ℕ) (ordered : grade ≤ 1) :
      ‖complementExtensionFamily admissible ledger.val.gaugeDeviation grade‖ ≤
        (Fintype.card (DerivativeIndex grade) : ℝ) + complementExtensionConstant four grade := by
    apply (startupExtension_coefficient_bound admissible base ledger.val.gaugeDeviation
      ledger.property.1.2.2.2.1 four fourNonnegative low gaugeBound small grade).trans
    have coeffPositive : 0 ≤ complementExtensionConstant four grade := abs_nonneg _
    exact add_le_add_right ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters base rho epsilon (by omega : grade + 6 ≤ 10)).trans unit)
      coeffPositive).trans_eq (mul_one _)) _
  exact ⟨startupMatrix_uniform_bound admissible _ _
      (startupFullGauge_coefficient_bound _ 0 (gaugeUnit 0 (by norm_num)))
      (startupFullGauge_coefficient_bound _ 1 (gaugeUnit 1 le_rfl)),
    startupMatrix_uniform_bound admissible _ _ (extensionUnit 0 (by norm_num)) (extensionUnit 1 le_rfl)⟩

/-- A source-sized coefficient yields a source-sized actual matrix action
 simultaneously on L2 and the genuine first graph. -/
theorem startupDeviationMatrix_bounds {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (constants : ℕ → ℝ) (budget : ℝ)
    (zeroth : ‖family 0‖ ≤ constants 0 * budget) (first : ‖family 1‖ ≤ constants 1 * budget) :
    ‖originalMatrixKernel admissible family coherent‖ ≤ startupDeviationMatrixConstant L sigma gamma constants * budget ∧
    ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤ startupDeviationMatrixConstant L sigma gamma constants * budget := by
  have result := startupMatrix_uniform_bound admissible family coherent zeroth first
  have equality : startupFirstUniformConstant L sigma gamma * (constants 0 * budget + constants 1 * budget) =
      startupDeviationMatrixConstant L sigma gamma constants * budget := by
    unfold startupDeviationMatrixConstant
    ring
  rw [equality] at result
  exact result

end Grad.CartesianStartup
