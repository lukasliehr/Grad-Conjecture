import AKDP4ActualMatrixRemainderOneHigh
import AKAL2ActualUniformCoefficientBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.CartesianStartup
open Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Neumann.Regularity

def startupDeviationProfile (constants : ℕ → ℝ) : EstimateProfile := ⟨fun _ => 0,constants⟩

theorem startupDeviationFamily_estimate {L ell : ℝ} {input output : ℕ}
    (parameters : PhaseParameters) (baseField : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ)
    (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (coherent : FamilyCoherent family) (constants : ℕ → ℝ) (nonnegative : ∀ grade,0≤constants grade)
    (bound : ∀ grade, ‖family grade‖≤constants grade*physicalBudget parameters baseField rho epsilon (offset+grade)) :
    FamilyEstimate parameters baseField rho epsilon offset (startupDeviationProfile constants) family
      (zeroFamily L parameters.sigma0 parameters.gamma ell input output) where
  actualCoherent := coherent
  referenceCoherent := zeroFamily_coherent _ _ _ _ _ _
  fixedNonnegative _ := le_rfl
  deviationNonnegative := nonnegative
  referenceBound := zeroFamily_norm _ _ _ _ _ _
  deviationBound grade := by simpa only [zeroFamily,sub_zero,startupDeviationProfile] using bound grade

/-- Exact original ledger rows acquire the BZ30 quantitative profiles
from their retained original all-grade bounds. No new derivative bound is
assumed for the operator or the unknown. -/
theorem startupActualLedger_deviationProfiles {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {baseField : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon baseField)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade≤four grade*physicalBudget parameters baseField rho epsilon (grade+4) ∧
      ledgerSizeFive ledger grade≤five grade*physicalBudget parameters baseField rho epsilon (grade+5)) :
    FamilyEstimate parameters baseField rho epsilon 12 (startupDeviationProfile four) ledger.val.gaugeDeviation
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3) ∧
    FamilyEstimate parameters baseField rho epsilon 12 (startupDeviationProfile four) ledger.val.fluxDeviation
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3) ∧
    FamilyEstimate parameters baseField rho epsilon 12 (startupDeviationProfile five) ledger.val.rotatedPlanarProduct
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 2) ∧
    FamilyEstimate parameters baseField rho epsilon 12 (startupDeviationProfile five) ledger.val.rotatedThirdProduct
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 1) := by
  have fourBound (grade : ℕ) : ledgerSizeFour ledger grade≤four grade*physicalBudget parameters baseField rho epsilon (12+grade) :=
    (bounds grade).1.trans (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters baseField rho epsilon (by omega)) (fourNonnegative grade))
  have fiveBound (grade : ℕ) : ledgerSizeFive ledger grade≤five grade*physicalBudget parameters baseField rho epsilon (12+grade) :=
    (bounds grade).2.trans (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters baseField rho epsilon (by omega)) (fiveNonnegative grade))
  refine ⟨startupDeviationFamily_estimate parameters baseField rho epsilon 12 _ ledger.property.1.2.2.2.1 four fourNonnegative
      (fun grade => (actualGaugeDeviation_bound ledger grade).trans (fourBound grade)),?_,?_,?_⟩
  · apply startupDeviationFamily_estimate parameters baseField rho epsilon 12 _ ledger.property.1.2.2.2.2.1 four fourNonnegative
    intro grade
    apply (show ‖ledger.val.fluxDeviation grade‖≤ledgerSizeFour ledger grade from ?_).trans (fourBound grade)
    unfold ledgerSizeFour
    linarith [norm_nonneg (ledger.val.inverseTransposeDeviation grade),
      norm_nonneg (ledger.val.seedInverse grade - gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2),
      norm_nonneg (ledger.val.gaugeDeviation grade),norm_nonneg (ledger.val.traceDeviation grade)]
  · apply startupDeviationFamily_estimate parameters baseField rho epsilon 12 _ ledger.property.1.2.2.2.2.2.2.2.1 five fiveNonnegative
    intro grade
    apply (show ‖ledger.val.rotatedPlanarProduct grade‖≤ledgerSizeFive ledger grade from ?_).trans (fiveBound grade)
    unfold ledgerSizeFive
    linarith [norm_nonneg (ledger.val.rotatedFrame grade),norm_nonneg (ledger.val.rotatedPlanarProduct grade),
      norm_nonneg (ledger.val.rotatedThirdProduct grade)]
  · apply startupDeviationFamily_estimate parameters baseField rho epsilon 12 _ ledger.property.1.2.2.2.2.2.2.2.2 five fiveNonnegative
    intro grade
    apply (show ‖ledger.val.rotatedThirdProduct grade‖≤ledgerSizeFive ledger grade from ?_).trans (fiveBound grade)
    unfold ledgerSizeFive
    linarith [norm_nonneg (ledger.val.rotatedFrame grade),norm_nonneg (ledger.val.rotatedPlanarProduct grade),
      norm_nonneg (ledger.val.rotatedThirdProduct grade)]

end Grad.CartesianStartup
