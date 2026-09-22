import AKBW16OriginalPrincipalRankTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRankOperator

def currentBudget (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  1 + (2 * |startupExtensionMatrixConstant L sigma gamma four|) *
    ((complement 0).bound * (2 * |startupGaugeMatrixConstant L sigma gamma four|))

theorem currentBudget_nonnegative (L sigma gamma : ℝ) (four : ℕ → ℝ) :
    0 ≤ currentBudget L sigma gamma four := by
  unfold currentBudget
  positivity [(complement 0).nonnegative]

theorem matrix_bound_of_pair {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (constant : ℝ)
    (bounds : ‖originalMatrixKernel admissible family coherent‖ ≤ constant ∧
      ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤ constant) :
    (matrix admissible rank family coherent).bound ≤ 2 * |constant| := by
  rw [matrix_bound]
  have combined := add_le_add bounds.1 bounds.2
  linarith [le_abs_self constant]

theorem matrix_bound_of_scaled_pair {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (constant budget : ℝ) (positive : 0 ≤ budget)
    (bounds : ‖originalMatrixKernel admissible family coherent‖ ≤ constant * budget ∧
      ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤ constant * budget) :
    (matrix admissible rank family coherent).bound ≤ (2 * |constant|) * budget := by
  have result := matrix_bound_of_pair admissible rank family coherent (constant * budget) bounds
  simpa only [abs_mul, abs_of_nonneg positive, mul_assoc] using result

variable {parameters : PhaseParameters} {L ell rho alpha delta parameter epsilon : ℝ}
    {base : ACore parameters 3} {admissible : Admissible L parameters.sigma0 parameters.gamma ell}

theorem actual_current_bound (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) (rank : ℕ) :
    (current admissible rank ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent).bound ≤
      currentBudget L parameters.sigma0 parameters.gamma four := by
  have boundsBoth := startupActual_gauge_extension_bounds ledger four fourNonnegative bounds unit small inverseCoherent
  have gauge := matrix_bound_of_pair admissible rank (fullGaugeFamily ledger.val.gaugeDeviation)
    (fullGaugeFamily_coherent _ ledger.property.1.2.2.2.1) (startupGaugeMatrixConstant L parameters.sigma0 parameters.gamma four) boundsBoth.1
  have extension := matrix_bound_of_pair admissible rank (complementExtensionFamily admissible ledger.val.gaugeDeviation)
    (complementExtensionFamily_coherent _ _ ledger.property.1.2.2.2.1 inverseCoherent)
    (startupExtensionMatrixConstant L parameters.sigma0 parameters.gamma four) boundsBoth.2
  change 1 + (matrix admissible rank (complementExtensionFamily admissible ledger.val.gaugeDeviation)
    (complementExtensionFamily_coherent _ _ ledger.property.1.2.2.2.1 inverseCoherent)).bound *
    ((complement rank).bound * (matrix admissible rank (fullGaugeFamily ledger.val.gaugeDeviation)
      (fullGaugeFamily_coherent _ ledger.property.1.2.2.2.1)).bound) ≤ _
  unfold currentBudget
  rw [complement_bound_independent]
  exact add_le_add_right (mul_le_mul extension
    (mul_le_mul_of_nonneg_left gauge (complement 0).nonnegative)
    (mul_nonneg (complement 0).nonnegative (matrix admissible rank (fullGaugeFamily ledger.val.gaugeDeviation)
      (fullGaugeFamily_coherent _ ledger.property.1.2.2.2.1)).nonnegative)
    (mul_nonneg (by norm_num) (abs_nonneg _))) 1

/-- The three genuine variable coefficient factors have the same linear B10
payment at every covector rank, before any fixed angular action. -/
theorem actual_deviation_bounds (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade) (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5)) (rank : ℕ) :
    (matrix admissible rank ledger.val.rotatedPlanarProduct ledger.property.1.2.2.2.2.2.2.2.1).bound ≤
        (2 * |startupDeviationMatrixConstant L parameters.sigma0 parameters.gamma five|) * physicalBudget parameters base rho epsilon 10 ∧
    (matrix admissible rank ledger.val.rotatedThirdProduct ledger.property.1.2.2.2.2.2.2.2.2).bound ≤
        (2 * |startupDeviationMatrixConstant L parameters.sigma0 parameters.gamma five|) * physicalBudget parameters base rho epsilon 10 ∧
    (matrix admissible rank ledger.val.fluxDeviation ledger.property.1.2.2.2.2.1).bound ≤
        (2 * |startupDeviationMatrixConstant L parameters.sigma0 parameters.gamma four|) * physicalBudget parameters base rho epsilon 10 := by
  have d0 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 0 (by norm_num)
  have d1 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 1 le_rfl
  have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
  exact ⟨matrix_bound_of_scaled_pair admissible rank _ _ _ _ budgetPositive
      (startupDeviationMatrix_bounds admissible _ _ five _ d0.2.2.1 d1.2.2.1),
    matrix_bound_of_scaled_pair admissible rank _ _ _ _ budgetPositive
      (startupDeviationMatrix_bounds admissible _ _ five _ d0.2.2.2 d1.2.2.2),
    matrix_bound_of_scaled_pair admissible rank _ _ _ _ budgetPositive
      (startupDeviationMatrix_bounds admissible _ _ four _ d0.2.1 d1.2.1)⟩

end StartupRankOperator
end Grad.CartesianStartup
